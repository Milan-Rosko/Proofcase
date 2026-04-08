#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
ANALYSIS_ROOT="$ROOT_DIR/_tools/Dump/analysis"
TS="$(date -u +"%Y%m%dT%H%M%SZ")"
RUN_DIR="$ANALYSIS_ROOT/$TS"
LATEST_LINK="$ANALYSIS_ROOT/latest"

SELECT_FILE="_tools/_Select"

FIRST_SELECTED="$(
  awk '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    {
      line = $0
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", line)
      if (line ~ /\.v$/) {
        print line
        exit
      }
    }
  ' "$ROOT_DIR/$SELECT_FILE" 2>/dev/null || true
)"

QED_FILE="${QED_FILE:-$FIRST_SELECTED}"

SCOPE="${SCOPE:-}"
if [[ -z "$SCOPE" ]]; then
  if [[ -n "$FIRST_SELECTED" ]]; then
    IFS='/' read -r c1 c2 _ <<< "$FIRST_SELECTED"
    if [[ -n "$c1" && -n "$c2" ]]; then
      SCOPE="$c1/$c2"
    fi
  fi
fi

SCOPE="${SCOPE:-theories/}"
SHADOW_ROOT="${SHADOW_ROOT:-scratch/shadow/$SCOPE}"

PY_ARGS=(
  --root-dir "$ROOT_DIR"
  --scope "$SCOPE"
  --select-file "$SELECT_FILE"
  --shadow-root "$SHADOW_ROOT"
  --root-name-regex '(?i).*_qed$'
  --out-dir "$RUN_DIR"
)
if [[ -n "$QED_FILE" ]]; then
  PY_ARGS+=(--qed-file "$QED_FILE")
fi

python3 - "${PY_ARGS[@]}" <<'PY'
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


DECL_RE = re.compile(
    r"^\s*(Lemma|Theorem|Proposition|Corollary|Fact|Remark|Example)\s+([A-Za-z0-9_']+)\b"
)

# Typical .glob patterns seen in Coq/Rocq shadow artifacts.
OBJ_RE = re.compile(r"^(def|prf|ax)\s+(\d+):(\d+)\s+<>\s+(\S+)")
REF_RE = re.compile(r"^R(\d+):(\d+)\s+(\S+)\s+<>\s+(\S+)\s+(\S+)")
MOD_RE = re.compile(r"^F(\S+)")
REF_POS_RE = re.compile(r"^R\d+:\d+$")

# Keep graph edges focused on declaration/proof dependencies.
EDGE_REF_KINDS = {
    "def",
    "thm",
    "prf",
    "ax",
    "defax",
    "prfax",
    "proj",
    "rec",
}

DEFAULT_SCOPE = "theories/"
DEFAULT_SHADOW = "scratch/shadow/theories/"
DEFAULT_QED_NAME_RE = r"(?i).*_qed$"


@dataclass(frozen=True)
class Decl:
    file_rel: str
    line_no: int
    kind: str
    name: str
    qname: str


@dataclass(frozen=True)
class Obj:
    qname: str
    kind: str  # def | prf | ax
    module: str
    name: str
    src_file_rel: Optional[str]


def read_text(path: pathlib.Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def normalize_rel(root: pathlib.Path, path: pathlib.Path) -> str:
    return path.relative_to(root).as_posix()


def load_selected_files(root: pathlib.Path, scope: str, select_file: Optional[pathlib.Path]) -> List[str]:
    selected: Set[str] = set()

    if select_file and select_file.is_file():
        for line in read_text(select_file).splitlines():
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            if s.startswith(scope + "/") and s.endswith(".v"):
                abs_path = root / s
                if abs_path.is_file():
                    selected.add(s)

    if not selected:
        scope_root = root / scope
        for p in scope_root.rglob("*.v"):
            selected.add(normalize_rel(root, p))

    return sorted(selected)


def choose_qed_file(
    selected_files: List[str],
    explicit_qed_file: Optional[str],
) -> Tuple[Optional[str], List[str]]:
    warnings: List[str] = []

    if explicit_qed_file:
        if explicit_qed_file in selected_files:
            return explicit_qed_file, warnings
        warnings.append(f"explicit ORIGO file not in selected scope: {explicit_qed_file}")
        return None, warnings

    if selected_files:
        return selected_files[0], warnings

    warnings.append("no selected files available to choose ORIGO file")
    return None, warnings


def parse_declarations(root: pathlib.Path, rel_file: str) -> List[Tuple[int, str, str]]:
    path = root / rel_file
    out: List[Tuple[int, str, str]] = []
    for i, line in enumerate(read_text(path).splitlines(), start=1):
        m = DECL_RE.match(line)
        if m:
            out.append((i, m.group(1), m.group(2)))
    return out


def discover_shadow_globs(
    root: pathlib.Path,
    scope: str,
    shadow_root_rel: str,
    selected_files: Set[str],
) -> Dict[str, pathlib.Path]:
    """
    Returns map:
        source_file_rel -> glob_path
    Only for selected files.
    """
    shadow_root = root / shadow_root_rel
    if not shadow_root.exists():
        return {}

    out: Dict[str, pathlib.Path] = {}
    scope_root = root / scope

    for glob_path in shadow_root.rglob("*.glob"):
        rel_under_shadow = glob_path.relative_to(shadow_root).with_suffix(".v").as_posix()
        src_abs = scope_root / rel_under_shadow
        if not src_abs.is_file():
            continue
        src_rel = normalize_rel(root, src_abs)
        if src_rel in selected_files:
            out[src_rel] = glob_path

    return out


def parse_glob_file(
    glob_path: pathlib.Path,
    src_file_rel: str,
) -> Tuple[Optional[str], Dict[str, Obj], Dict[str, Set[Tuple[str, str]]]]:
    """
    Returns:
      module_name
      objects: qname -> Obj
      raw_edges: owner_qname -> set((raw ref qname, ref kind))
    """
    module: Optional[str] = None
    objects: Dict[str, Obj] = {}
    raw_edges: Dict[str, Set[Tuple[str, str]]] = collections.defaultdict(set)
    owner: Optional[str] = None

    for line in read_text(glob_path).splitlines():
        if module is None:
            mm = MOD_RE.match(line)
            if mm:
                module = mm.group(1)
                continue

        if module is None:
            continue

        om = OBJ_RE.match(line)
        obj_kind: Optional[str] = None
        obj_name: Optional[str] = None
        if om:
            obj_kind, _, _, obj_name = om.groups()
        else:
            parts = line.split()
            if (
                len(parts) >= 4
                and parts[0] in {"def", "prf", "ax"}
                and ":" in parts[1]
            ):
                obj_kind = parts[0]
                obj_name = parts[3] if parts[2] == "<>" and len(parts) >= 4 else parts[-1]

        if obj_kind and obj_name:
            kind = obj_kind
            name = obj_name
            qname = f"{module}.{name}"
            objects[qname] = Obj(
                qname=qname,
                kind=kind,
                module=module,
                name=name,
                src_file_rel=src_file_rel,
            )
            owner = qname
            continue

        rm = REF_RE.match(line)
        ref_module: Optional[str] = None
        ref_name: Optional[str] = None
        ref_kind: Optional[str] = None
        if rm:
            ref_module = rm.group(3)
            ref_name = rm.group(4)
            ref_kind = rm.group(5)
        else:
            parts = line.split()
            if (
                len(parts) >= 4
                and REF_POS_RE.match(parts[0])
            ):
                payload = parts[1:-1]
                if payload:
                    ref_module = payload[0]
                    ref_name = payload[-1]
                    ref_kind = parts[-1]

        if (
            owner is not None
            and ref_module is not None
            and ref_name is not None
            and ref_kind is not None
            and ref_name != "<>"
        ):
            ref_qname = f"{ref_module}.{ref_name}"
            raw_edges[owner].add((ref_qname, ref_kind))

    return module, objects, raw_edges


def build_object_graph(
    root: pathlib.Path,
    scope: str,
    selected_files: List[str],
    shadow_root_rel: str,
) -> Tuple[
    Dict[str, Obj],
    Dict[str, Set[str]],
    Dict[str, str],
    List[str],
    Dict[str, int],
]:
    """
    Returns:
      objects: qname -> Obj
      edges: qname -> set(qname)
      file_to_module: source .v rel -> module
      warnings
      counters
    """
    selected_set = set(selected_files)
    glob_map = discover_shadow_globs(root, scope, shadow_root_rel, selected_set)

    warnings: List[str] = []
    objects: Dict[str, Obj] = {}
    raw_edges: Dict[str, Set[Tuple[str, str]]] = collections.defaultdict(set)
    file_to_module: Dict[str, str] = {}

    for src_file_rel, glob_path in sorted(glob_map.items()):
        module, objs, edges = parse_glob_file(glob_path, src_file_rel)
        if module is None:
            warnings.append(f"no module line found in {glob_path}")
            continue
        file_to_module[src_file_rel] = module
        objects.update(objs)
        for src, dsts in edges.items():
            raw_edges[src].update(dsts)

    name_index: Dict[str, List[str]] = collections.defaultdict(list)
    for qname, obj in objects.items():
        name_index[obj.name].append(qname)

    edges: Dict[str, Set[str]] = collections.defaultdict(set)
    alias_resolved = 0
    ambiguous = 0
    unresolved = 0
    ignored_ref_kinds = 0

    for src, raw_dsts in raw_edges.items():
        if src not in objects:
            continue
        for raw_dst, ref_kind in raw_dsts:
            if ref_kind not in EDGE_REF_KINDS:
                ignored_ref_kinds += 1
                continue
            if raw_dst in objects:
                edges[src].add(raw_dst)
                continue

            bare_name = raw_dst.rsplit(".", 1)[-1]
            candidates = name_index.get(bare_name, [])

            if len(candidates) == 1:
                edges[src].add(candidates[0])
                alias_resolved += 1
            elif len(candidates) > 1:
                ambiguous += 1
            else:
                unresolved += 1

    counters = {
        "active_glob_files": len(glob_map),
        "objects_total": len(objects),
        "edges_total": sum(len(v) for v in edges.values()),
        "alias_resolved": alias_resolved,
        "ambiguous_refs": ambiguous,
        "unresolved_refs": unresolved,
        "ignored_ref_kinds": ignored_ref_kinds,
    }

    if not glob_map:
        warnings.append(f"no .glob files discovered under {shadow_root_rel}")

    return objects, edges, file_to_module, warnings, counters


def choose_root_decls(
    decls: List[Decl],
    root_name_re: str,
) -> Tuple[List[Decl], List[str]]:
    warnings: List[str] = []
    pattern = re.compile(root_name_re)

    matched = [d for d in decls if pattern.match(d.name)]
    if matched:
        return matched, warnings

    theorem_like = [d for d in decls if d.kind in {"Theorem", "Corollary", "Proposition"}]
    if theorem_like:
        warnings.append(
            f"no declarations matched root regex {root_name_re!r}; falling back to theorem-like declarations"
        )
        return theorem_like, warnings

    if decls:
        warnings.append(
            f"no declarations matched root regex {root_name_re!r}; falling back to all declarations"
        )
        return list(decls), warnings

    warnings.append("no declarations found in ORIGO file")
    return [], warnings


def bfs(edges: Dict[str, Set[str]], roots: List[str]) -> Set[str]:
    seen: Set[str] = set()
    q = collections.deque(roots)
    while q:
        u = q.popleft()
        if u in seen:
            continue
        seen.add(u)
        for v in edges.get(u, ()): 
            if v not in seen:
                q.append(v)
    return seen


def cluster_decls_by_weak_connectivity(
    decls: List[Decl],
    edges: Dict[str, Set[str]],
) -> List[List[Decl]]:
    if not decls:
        return []

    by_qname: Dict[str, Decl] = {d.qname: d for d in decls}
    nodes: Set[str] = set(by_qname.keys())
    undirected: Dict[str, Set[str]] = {q: set() for q in nodes}

    for src, dsts in edges.items():
        if src not in nodes:
            continue
        for dst in dsts:
            if dst in nodes and dst != src:
                undirected[src].add(dst)
                undirected[dst].add(src)

    ordered_nodes = [d.qname for d in sorted(decls, key=lambda d: (d.line_no, d.name))]
    seen: Set[str] = set()
    clusters: List[List[Decl]] = []

    for start in ordered_nodes:
        if start in seen:
            continue
        q = collections.deque([start])
        seen.add(start)
        component: List[Decl] = []

        while q:
            u = q.popleft()
            component.append(by_qname[u])
            neighbors = sorted(
                undirected[u],
                key=lambda x: (by_qname[x].line_no, by_qname[x].name),
            )
            for v in neighbors:
                if v not in seen:
                    seen.add(v)
                    q.append(v)

        clusters.append(sorted(component, key=lambda d: (d.line_no, d.name)))

    clusters.sort(key=lambda c: (c[0].line_no, c[0].name))
    return clusters


def try_file_closure(
    root: pathlib.Path,
    selected_files: List[str],
    root_file: str,
    scope: str,
) -> Tuple[Dict[str, object], List[str]]:
    warnings: List[str] = []

    tool = shutil.which("rocqdep") or shutil.which("coqdep")
    if not tool:
        return {
            "available": False,
            "tool": None,
            "reachable_files": [],
            "isolated_files": [],
        }, ["rocqdep/coqdep not found; file closure skipped"]

    selected_set = set(selected_files)
    graph: Dict[str, Set[str]] = {f: set() for f in selected_files}

    # Use scope basename as logical root, e.g. theories/P002 -> P002.
    scope_name = pathlib.PurePosixPath(scope).name or "Scope"
    cmd = [tool, "-Q", scope, scope_name, *selected_files]

    try:
        out = subprocess.check_output(cmd, cwd=root, text=True, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError as ex:
        warnings.append(f"{pathlib.Path(tool).name} failed: {ex.output.strip()}")
        return {
            "available": False,
            "tool": tool,
            "reachable_files": [],
            "isolated_files": [],
        }, warnings

    for line in out.splitlines():
        if ":" not in line:
            continue
        _, rhs = line.split(":", 1)
        toks = rhs.split()

        self_v = None
        for tok in toks:
            if tok.endswith(".v") and tok in selected_set:
                self_v = tok
                break
            if tok.endswith(".vo"):
                cand = tok[:-3] + ".v"
                if cand in selected_set:
                    self_v = cand
                    break
        if self_v is None:
            continue

        for tok in toks:
            dep = None
            if tok.endswith(".v") and tok in selected_set:
                dep = tok
            elif tok.endswith(".vo"):
                cand = tok[:-3] + ".v"
                if cand in selected_set:
                    dep = cand
            if dep and dep != self_v:
                graph[self_v].add(dep)

    reachable = bfs(graph, [root_file])
    isolated = sorted(f for f in selected_files if f not in reachable)

    return {
        "available": True,
        "tool": tool,
        "reachable_files": sorted(reachable),
        "isolated_files": isolated,
    }, warnings


def write_dot(path: pathlib.Path, objects: Dict[str, Obj], edges: Dict[str, Set[str]], reachable: Set[str], roots: Set[str]) -> None:
    with path.open("w", encoding="utf-8") as f:
        f.write("digraph qed_relevance {\n")
        f.write("  rankdir=LR;\n")
        f.write("  node [shape=box,fontsize=10];\n")
        for q in sorted(reachable):
            fill = "lightblue" if q in roots else "white"
            label = q.replace('"', '\\"')
            f.write(f'  "{q}" [style=filled,fillcolor="{fill}",label="{label}"];\n')
        for src in sorted(reachable):
            for dst in sorted(edges.get(src, ())):
                if dst in reachable:
                    f.write(f'  "{src}" -> "{dst}";\n')
        f.write("}\n")


def write_subset_dot(
    path: pathlib.Path,
    edges: Dict[str, Set[str]],
    nodes: Set[str],
    title: str,
) -> None:
    with path.open("w", encoding="utf-8") as f:
        f.write("digraph subset {\n")
        f.write("  rankdir=LR;\n")
        f.write('  graph [label="%s", labelloc=t, fontsize=14];\n' % title.replace('"', '\\"'))
        f.write("  node [shape=box,fontsize=10,style=filled,fillcolor=\"white\"];\n")
        for q in sorted(nodes):
            label = q.replace('"', '\\"')
            f.write(f'  "{q}" [label="{label}"];\n')
        for src in sorted(nodes):
            for dst in sorted(edges.get(src, ())):
                if dst in nodes:
                    f.write(f'  "{src}" -> "{dst}";\n')
        f.write("}\n")


def weak_components(nodes: Set[str], edges: Dict[str, Set[str]]) -> List[List[str]]:
    undirected: Dict[str, Set[str]] = {n: set() for n in nodes}
    for src in nodes:
        for dst in edges.get(src, ()):
            if dst in nodes:
                undirected[src].add(dst)
                undirected[dst].add(src)

    seen: Set[str] = set()
    components: List[List[str]] = []
    for start in sorted(nodes):
        if start in seen:
            continue
        q = collections.deque([start])
        seen.add(start)
        comp: List[str] = []
        while q:
            u = q.popleft()
            comp.append(u)
            for v in sorted(undirected[u]):
                if v not in seen:
                    seen.add(v)
                    q.append(v)
        components.append(sorted(comp))

    components.sort(key=lambda c: (-len(c), c[0] if c else ""))
    return components


def render_component_tree(label: str, components: List[List[str]]) -> str:
    lines: List[str] = []
    total = sum(len(c) for c in components)
    lines.append(f"{label}: {total} objects across {len(components)} components")
    for i, comp in enumerate(components, start=1):
        lines.append(f"+- component {i} (size={len(comp)})")
        for j, q in enumerate(comp, start=1):
            leaf = "`-" if j == len(comp) else "|-"
            lines.append(f"   {leaf} {q}")
    return "\n".join(lines) + "\n"


def render_svg_and_html(dot_path: pathlib.Path) -> Tuple[Optional[pathlib.Path], Optional[pathlib.Path], Optional[str]]:
    dot_bin = shutil.which("dot")
    if not dot_bin:
        return None, None, "Graphviz 'dot' not found; SVG/HTML rendering skipped"

    svg_path = dot_path.with_suffix(".svg")
    html_path = dot_path.with_suffix(".html")
    try:
        subprocess.check_call([dot_bin, "-Tsvg", str(dot_path), "-o", str(svg_path)])
    except subprocess.CalledProcessError as ex:
        return None, None, f"dot failed for {dot_path.name}: {ex}"

    html = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>{title}</title>
  <style>
    html, body {{ margin: 0; padding: 0; width: 100%; height: 100%; }}
    .wrap {{
      width: 100%;
      min-height: 100%;
      overflow: auto;
      background: #fff;
    }}
    img {{
      display: block;
      width: 100%;
      height: auto;
      max-width: 100%;
    }}
  </style>
</head>
<body>
  <div class="wrap">
    <img src="{svg}" alt="{title}" />
  </div>
</body>
</html>
""".format(title=dot_path.stem, svg=svg_path.name)
    html_path.write_text(html, encoding="utf-8")
    return svg_path, html_path, None


def render_summary(report: Dict[str, object]) -> str:
    qfa = report["qed_file_analysis"]
    pg = report["proof_graph"]
    sec = report["secondary"]
    dead = report["dead_branch_analysis"]

    lines: List[str] = []
    lines.append("# Rocq ORIGO relevance summary")
    lines.append("")
    lines.append("Analyzed file:")
    lines.append(f"- {qfa['file']}")
    lines.append("")
    lines.append("Root declarations:")
    for x in qfa["root_declarations"]:
        lines.append(f"- {x}")
    lines.append("")
    lines.append(f"Declarations found in ORIGO file: {qfa['declarations_total']}")
    lines.append(f"Relevant to ORIGO roots: {qfa['reachable_same_file_total']}")
    lines.append(f"Isolated within ORIGO file: {qfa['isolated_same_file_total']}")
    lines.append(f"Dead objects outside ORIGO-reachable closure: {dead['dead_objects_total']}")
    lines.append(f"Disconnected weak components in full object graph: {dead['full_components_total']}")
    lines.append("")
    lines.append("Isolated declarations in ORIGO file:")
    if qfa["isolated_same_file_declarations"]:
        for x in qfa["isolated_same_file_declarations"]:
            lines.append(f"- {x}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("Clusters of unconnected declarations in ORIGO file:")
    if qfa["isolated_same_file_clusters"]:
        for i, cluster in enumerate(qfa["isolated_same_file_clusters"], start=1):
            lines.append(f"- Cluster {i}: {', '.join(cluster)}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("Dead-Branch Components:")
    if dead["dead_components"]:
        for i, comp in enumerate(dead["dead_components"], start=1):
            lines.append(f"- Component {i} (size {len(comp)}): {', '.join(comp)}")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("Warnings:")
    warnings = list(report["warnings"])
    if pg["ambiguous_refs"] > 0:
        warnings.append(f"{pg['ambiguous_refs']} ambiguous proof references were ignored conservatively")
    if pg["unresolved_refs"] > 0:
        warnings.append(f"{pg['unresolved_refs']} proof references could not be resolved")
    if sec["file_closure"]["available"]:
        warnings.append("file-level closure succeeded")
    else:
        warnings.append("file-level closure unavailable")
    if warnings:
        for w in warnings:
            lines.append(f"- {w}")
    else:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="Analyze same-file lemma relevance for a Rocq ORIGO file.")
    ap.add_argument("--root-dir", required=True, help="Project root")
    ap.add_argument("--scope", default=DEFAULT_SCOPE, help="Analysis scope, default theories/T002")
    ap.add_argument("--select-file", default="builders/_Select", help="Selection file relative to root")
    ap.add_argument("--qed-file", default=None, help="Explicit ORIGO .v file relative to root")
    ap.add_argument("--shadow-root", default=DEFAULT_SHADOW, help="Shadow tree containing .glob files")
    ap.add_argument("--root-name-regex", default=DEFAULT_QED_NAME_RE, help="Regex to choose root declarations inside the ORIGO file")
    ap.add_argument("--out-dir", required=True, help="Output directory")
    args = ap.parse_args()

    root = pathlib.Path(args.root_dir).resolve()
    out_dir = pathlib.Path(args.out_dir).resolve()

    select_path = root / args.select_file if args.select_file else None

    selected_files = load_selected_files(root, args.scope, select_path)
    if not selected_files:
        print("ERROR: no selected .v files found", file=sys.stderr)
        return 2

    qed_file, warn_qed = choose_qed_file(selected_files, args.qed_file)
    if not qed_file:
        print("ERROR: could not determine ORIGO file", file=sys.stderr)
        return 2

    out_dir.mkdir(parents=True, exist_ok=True)

    decl_rows = parse_declarations(root, qed_file)
    objects, edges, file_to_module, warn_graph, graph_counts = build_object_graph(
        root=root,
        scope=args.scope,
        selected_files=selected_files,
        shadow_root_rel=args.shadow_root,
    )

    module = file_to_module.get(qed_file)
    warnings: List[str] = []
    warnings.extend(warn_qed)
    warnings.extend(warn_graph)

    if not module:
        warnings.append(
            f"no module mapping found for {qed_file}; same-file declaration reachability may be empty"
        )

    decls: List[Decl] = []
    for line_no, kind, name in decl_rows:
        qname = f"{module}.{name}" if module else name
        decls.append(Decl(file_rel=qed_file, line_no=line_no, kind=kind, name=name, qname=qname))

    root_decls, warn_roots = choose_root_decls(decls, args.root_name_regex)
    warnings.extend(warn_roots)

    root_qnames = [d.qname for d in root_decls if d.qname in objects]
    missing_root_objs = [d.qname for d in root_decls if d.qname not in objects]
    if missing_root_objs:
        warnings.append(
            "some root declarations were not found in the proof-object graph: "
            + ", ".join(missing_root_objs)
        )

    reachable = bfs(edges, root_qnames)
    all_nodes = set(objects.keys())
    dead_nodes = set(sorted(all_nodes - reachable))
    full_components = weak_components(all_nodes, edges) if all_nodes else []
    dead_components = weak_components(dead_nodes, edges) if dead_nodes else []

    same_file_decls = sorted(decls, key=lambda d: d.line_no)
    reachable_same_file = [d for d in same_file_decls if d.qname in reachable]
    isolated_same_file = [d for d in same_file_decls if d.qname not in reachable]
    isolated_same_file_clusters = cluster_decls_by_weak_connectivity(
        isolated_same_file,
        edges,
    )
    isolated_same_file_lemmas = [d for d in isolated_same_file if d.kind == "Lemma"]
    isolated_same_file_lemma_clusters = cluster_decls_by_weak_connectivity(
        isolated_same_file_lemmas,
        edges,
    )

    file_closure, warn_closure = try_file_closure(root, selected_files, qed_file, args.scope)
    warnings.extend(warn_closure)

    proof_graph_dot = out_dir / "proof_graph.dot"
    proof_graph_svg: Optional[pathlib.Path] = None
    proof_graph_html: Optional[pathlib.Path] = None
    if reachable:
        write_dot(proof_graph_dot, objects, edges, reachable, set(root_qnames))
        proof_graph_svg, proof_graph_html, warn_dot = render_svg_and_html(proof_graph_dot)
        if warn_dot:
            warnings.append(warn_dot)

    dead_graph_dot = out_dir / "dead_branches.dot"
    dead_graph_svg: Optional[pathlib.Path] = None
    dead_graph_html: Optional[pathlib.Path] = None
    dead_tree_txt = out_dir / "dead_branches.tree.txt"
    dead_tree_txt.write_text(render_component_tree("dead_branches", dead_components), encoding="utf-8")
    if dead_nodes:
        write_subset_dot(dead_graph_dot, edges, dead_nodes, "Dead branches (not reachable from ORIGO roots)")
        dead_graph_svg, dead_graph_html, warn_dead_dot = render_svg_and_html(dead_graph_dot)
        if warn_dead_dot:
            warnings.append(warn_dead_dot)

    report = {
        "run": {
            "root_dir": str(root),
            "scope": args.scope,
            "scope_source": args.select_file if select_path and select_path.is_file() else "fallback_all_scope_files",
        },
        "selection": {
            "files": selected_files,
            "selected_files_total": len(selected_files),
        },
        "roots": {
            "root_file": qed_file,
            "root_declarations": [d.qname for d in root_decls],
            "root_declarations_present_in_graph": root_qnames,
        },
        "qed_file_analysis": {
            "file": qed_file,
            "module": module,
            "declarations_total": len(same_file_decls),
            "declared_declarations": [d.qname for d in same_file_decls],
            "declared_lemmas": [d.qname for d in same_file_decls if d.kind == "Lemma"],
            "declared_theorems": [d.qname for d in same_file_decls if d.kind == "Theorem"],
            "root_declarations": [d.qname for d in root_decls],
            "reachable_same_file_total": len(reachable_same_file),
            "reachable_same_file_declarations": [d.qname for d in reachable_same_file],
            "isolated_same_file_total": len(isolated_same_file),
            "isolated_same_file_declarations": [d.qname for d in isolated_same_file],
            "isolated_same_file_clusters_total": len(isolated_same_file_clusters),
            "isolated_same_file_clusters": [
                [d.qname for d in cluster] for cluster in isolated_same_file_clusters
            ],
            "isolated_same_file_lemmas_total": len(isolated_same_file_lemmas),
            "isolated_same_file_lemmas": [d.qname for d in isolated_same_file_lemmas],
            "isolated_same_file_lemma_clusters_total": len(isolated_same_file_lemma_clusters),
            "isolated_same_file_lemma_clusters": [
                [d.qname for d in cluster] for cluster in isolated_same_file_lemma_clusters
            ],
        },
        "proof_graph": {
            "available": bool(objects),
            "object_source": args.shadow_root,
            "objects_total": graph_counts["objects_total"],
            "edges_total": graph_counts["edges_total"],
            "active_glob_files": graph_counts["active_glob_files"],
            "alias_resolved": graph_counts["alias_resolved"],
            "ambiguous_refs": graph_counts["ambiguous_refs"],
            "unresolved_refs": graph_counts["unresolved_refs"],
            "ignored_ref_kinds": graph_counts["ignored_ref_kinds"],
            "reachable_objects_total": len(reachable),
        },
        "dead_branch_analysis": {
            "dead_objects_total": len(dead_nodes),
            "dead_objects": sorted(dead_nodes),
            "dead_components_total": len(dead_components),
            "dead_components": dead_components,
            "largest_dead_component_size": (len(dead_components[0]) if dead_components else 0),
            "full_components_total": len(full_components),
            "full_components_sizes": [len(c) for c in full_components],
        },
        "secondary": {
            "file_closure": file_closure,
            "proof_graph_dot": str(proof_graph_dot) if proof_graph_dot.exists() else None,
            "proof_graph_svg": str(proof_graph_svg) if proof_graph_svg and proof_graph_svg.exists() else None,
            "proof_graph_html": str(proof_graph_html) if proof_graph_html and proof_graph_html.exists() else None,
            "dead_branches_dot": str(dead_graph_dot) if dead_graph_dot.exists() else None,
            "dead_branches_svg": str(dead_graph_svg) if dead_graph_svg and dead_graph_svg.exists() else None,
            "dead_branches_html": str(dead_graph_html) if dead_graph_html and dead_graph_html.exists() else None,
            "dead_branches_tree": str(dead_tree_txt),
        },
        "warnings": warnings,
    }

    report_path = out_dir / "report.json"
    summary_path = out_dir / "summary.md"

    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    summary_path.write_text(render_summary(report), encoding="utf-8")

    print(f"Wrote {summary_path}")
    print(f"Wrote {report_path}")
    if proof_graph_dot.exists():
        print(f"Wrote {proof_graph_dot}")
    if proof_graph_svg and proof_graph_svg.exists():
        print(f"Wrote {proof_graph_svg}")
    if proof_graph_html and proof_graph_html.exists():
        print(f"Wrote {proof_graph_html}")
    if dead_graph_dot.exists():
        print(f"Wrote {dead_graph_dot}")
    if dead_graph_svg and dead_graph_svg.exists():
        print(f"Wrote {dead_graph_svg}")
    if dead_graph_html and dead_graph_html.exists():
        print(f"Wrote {dead_graph_html}")
    if dead_tree_txt.exists():
        print(f"Wrote {dead_tree_txt}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY

ln -sfn "$RUN_DIR" "$LATEST_LINK"

echo "Analysis written to: $RUN_DIR"
echo "Latest link: $LATEST_LINK"
echo "Summary: $RUN_DIR/summary.md"
echo "Report: $RUN_DIR/report.json"
