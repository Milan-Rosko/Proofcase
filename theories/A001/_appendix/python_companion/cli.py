from __future__ import annotations

import argparse
from pathlib import Path
from typing import Sequence

try:
    from .probes import (
        exhaustive_tests,
        ladder_probe,
        large_random_tests,
        random_tests,
        scan_stable_stats,
        stable_set_probe,
        surjectivity_probe,
    )
except ImportError:
    from probes import (
        exhaustive_tests,
        ladder_probe,
        large_random_tests,
        random_tests,
        scan_stable_stats,
        stable_set_probe,
        surjectivity_probe,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="carryless_pairing",
        description="Empirical probes and plots for the T001 carryless pairing construction.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    suite = subparsers.add_parser("suite", help="Run the notebook-style empirical suite.")
    suite.add_argument("--exhaustive-lo", type=int, default=1)
    suite.add_argument("--exhaustive-hi", type=int, default=100)
    suite.add_argument("--random-samples", type=int, default=5_000)
    suite.add_argument("--random-lo", type=int, default=1)
    suite.add_argument("--random-hi", type=int, default=10_000)
    suite.add_argument("--random-seed", type=int, default=12_345)
    suite.add_argument("--large-samples", type=int, default=200)
    suite.add_argument("--large-max-index", type=int, default=900)
    suite.add_argument("--large-density", type=float, default=0.12)
    suite.add_argument("--large-seed", type=int, default=999)
    suite.add_argument("--surjectivity-N", type=int, default=50_000)

    probe = subparsers.add_parser(
        "probe", help="Report stable-set density and the first stable gaps."
    )
    probe.add_argument("--N", type=int, default=50_000)
    probe.add_argument("--show-first", type=int, default=25)

    ladder = subparsers.add_parser("ladder", help="Run the ladder probe.")
    ladder.add_argument(
        "Ns",
        nargs="*",
        type=int,
        default=[1_000, 10_000, 50_000, 100_000, 200_000],
    )

    scan = subparsers.add_parser(
        "scan-stable", help="Scan stable numbers up to N and report milestones."
    )
    scan.add_argument("--N", type=int, default=1_000_000)
    scan.add_argument(
        "--report-points",
        nargs="*",
        type=int,
        default=[10_000, 50_000, 100_000, 200_000, 500_000, 1_000_000],
    )

    plot = subparsers.add_parser(
        "plot", help="Plot a pairing path ordered by pairing value."
    )
    plot.add_argument("pairing", help="Pairing name.")
    plot.add_argument("--max-x", type=int, default=100)
    plot.add_argument("--max-y", type=int, default=50)
    plot.add_argument("--output", default=None)
    plot.add_argument("--usetex", action="store_true")
    plot.add_argument("--linewidth", type=float, default=0.3)

    return parser


def _print_failures(label: str, failures: list[str]) -> None:
    if not failures:
        return
    print(f"   first failure in {label} (if any):")
    print("------------------------------------------------------------")
    print(failures[0])
    print("------------------------------------------------------------")


def command_suite(args: argparse.Namespace) -> int:
    print("Running carryless pairing empirical tests (pure integer arithmetic).")
    print("Fibonacci table will grow dynamically as needed.\n")

    exhaustive = exhaustive_tests(args.exhaustive_lo, args.exhaustive_hi)
    print(
        f"1) Exhaustive roundtrip + injectivity on (x, y) in "
        f"[{args.exhaustive_lo}..{args.exhaustive_hi}]^2"
    )
    print(f"   tested_pairs   = {exhaustive.tested_pairs}")
    print(f"   stable_pairs   = {exhaustive.stable_pairs}")
    print(f"   unstable_pairs = {exhaustive.unstable_pairs}")
    print(
        f"   injective_on_stable_pairs = "
        f"{exhaustive.injective_on_stable_pairs}"
    )
    _print_failures("exhaustive tests", exhaustive.failures)
    print()

    random_report = random_tests(
        num_samples=args.random_samples,
        lo=args.random_lo,
        hi=args.random_hi,
        seed=args.random_seed,
    )
    print(
        f"2) Random roundtrip tests on (x, y) with "
        f"x, y in [{args.random_lo}..{args.random_hi}]"
    )
    print(
        f"   samples = {random_report.samples} "
        f"(seed={random_report.seed})"
    )
    print(f"   stable  = {random_report.stable}")
    print(f"   unstable= {random_report.unstable}")
    _print_failures("random tests", random_report.failures)
    print()

    large_report = large_random_tests(
        num_samples=args.large_samples,
        max_index=args.large_max_index,
        density=args.large_density,
        seed=args.large_seed,
    )
    print("3) Large random tests (huge x, y from random Zeckendorf supports)")
    print(
        f"   samples = {large_report.samples} "
        f"(seed={large_report.seed})"
    )
    print(
        f"   support max index = {large_report.max_support_index}, "
        f"density={large_report.density}"
    )
    print(f"   stable  = {large_report.stable}")
    print(f"   unstable= {large_report.unstable}")
    print(
        "   max bit-lengths: "
        f"x={large_report.max_bit_length['x']}, "
        f"y={large_report.max_bit_length['y']}, "
        f"n={large_report.max_bit_length['n']}"
    )
    _print_failures("large random tests", large_report.failures)
    print()

    surjectivity = surjectivity_probe(args.surjectivity_N)
    print("4) Surjectivity probe: stability of n -> unpair -> pair on n in [1..N]")
    print(f"   N = {surjectivity.N}")
    print(f"   stable_n   = {surjectivity.stable_n}")
    print(f"   unstable_n = {surjectivity.unstable_n}")
    print(f"   stable_fraction ≈ {surjectivity.stable_fraction:.6f}")
    if surjectivity.examples_unstable:
        print("   examples (unstable n):")
        for example in surjectivity.examples_unstable[:5]:
            print(f"   - {example}")

    return 0


def command_probe(args: argparse.Namespace) -> int:
    report = stable_set_probe(N=args.N, show_first=args.show_first)
    print(f"N = {report.N}")
    print(f"stable_count = {report.stable_count}")
    print(f"stable_fraction = {report.stable_fraction:.6f}")
    print("\nfirst stable n:")
    print(report.first_stable)
    print("\nfirst gaps:")
    print(report.first_gaps)
    if report.mean_gap is not None:
        print(f"\nmean_gap (within <=N) = {report.mean_gap:.3f}")
        print(f"max_gap  (within <=N) = {report.max_gap}")
    return 0


def command_ladder(args: argparse.Namespace) -> int:
    for point in ladder_probe(args.Ns):
        mean_gap = "inf" if point.mean_gap is None else f"{point.mean_gap:>9.3f}"
        print(
            f"N={point.N:>8}  stable={point.stable_count:>6}  "
            f"frac={point.stable_fraction:.6f}  mean_gap={mean_gap}  "
            f"max_gap={point.max_gap}"
        )
    return 0


def command_scan_stable(args: argparse.Namespace) -> int:
    for point in scan_stable_stats(N=args.N, report_points=args.report_points):
        print(
            f"N={point.N:>9}  A={point.stable_count:>7}  "
            f"frac={point.stable_fraction:>10.6f}  "
            f"A/sqrtN={point.a_over_sqrt_n:>8.3f}  "
            f"max_gap={point.max_gap:>7}  "
            f"t={point.elapsed_seconds:.1f}s"
        )
    return 0


def command_plot(args: argparse.Namespace) -> int:
    try:
        try:
            from .plotting import available_pairing_names, get_pairing, plot_pairing_path
        except ImportError:
            from plotting import available_pairing_names, get_pairing, plot_pairing_path
    except ImportError as exc:
        raise SystemExit(
            "Plotting requires the optional matplotlib dependency. "
            "Install it with: pip install -e '.[plot]'"
        ) from exc

    output = args.output or f"{args.pairing}_{args.max_x}x{args.max_y}.pdf"
    pairing = get_pairing(args.pairing)
    path = plot_pairing_path(
        pairing,
        max_x=args.max_x,
        max_y=args.max_y,
        output_path=output,
        usetex=args.usetex,
        linewidth=args.linewidth,
    )
    print(f"Wrote {path}")
    print("Available pairings:", ", ".join(available_pairing_names()))
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.command == "suite":
        return command_suite(args)
    if args.command == "probe":
        return command_probe(args)
    if args.command == "ladder":
        return command_ladder(args)
    if args.command == "scan-stable":
        return command_scan_stable(args)
    if args.command == "plot":
        return command_plot(args)

    parser.error(f"Unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
