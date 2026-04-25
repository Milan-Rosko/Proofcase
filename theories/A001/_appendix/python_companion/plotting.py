from __future__ import annotations

from pathlib import Path
from typing import Callable, Dict, Iterable

try:
    from .core import pair
except ImportError:
    from core import pair

PairingFunction = Callable[[int, int], int]


def cantor_pair(x: int, y: int) -> int:
    return ((x + y) * (x + y + 1)) // 2 + y


def bit_interleave_pair(x: int, y: int) -> int:
    value = 0
    bit = 0
    while x or y:
        value |= (x & 1) << (2 * bit)
        value |= (y & 1) << (2 * bit + 1)
        x >>= 1
        y >>= 1
        bit += 1
    return value


def elegant_pair(x: int, y: int) -> int:
    return x * x + y if x >= y else y * y + x


def godel_pair(x: int, y: int) -> int:
    return (2**x) * (2 * y + 1) - 1


def rosenberg_strong_pair(x: int, y: int) -> int:
    return x * x + x + y if x >= y else y * y + x


AVAILABLE_PAIRINGS: Dict[str, PairingFunction] = {
    "carryless": pair,
    "cantor": cantor_pair,
    "bit-interleave": bit_interleave_pair,
    "elegant": elegant_pair,
    "godel": godel_pair,
    "rosenberg-strong": rosenberg_strong_pair,
}


def available_pairing_names() -> Iterable[str]:
    return sorted(AVAILABLE_PAIRINGS)


def get_pairing(name: str) -> PairingFunction:
    try:
        return AVAILABLE_PAIRINGS[name]
    except KeyError as exc:
        names = ", ".join(available_pairing_names())
        raise ValueError(f"Unknown pairing '{name}'. Available pairings: {names}.") from exc


def plot_pairing_path(
    pairing: PairingFunction,
    max_x: int,
    max_y: int,
    output_path: str | Path,
    *,
    usetex: bool = False,
    linewidth: float = 0.3,
) -> Path:
    import matplotlib as mpl
    import matplotlib.pyplot as plt

    mpl.rcParams.update(
        {
            "font.family": "serif",
            "text.usetex": usetex,
            "axes.labelsize": 9,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "figure.figsize": (5.5, 2.8),
            "savefig.bbox": "tight",
            "axes.grid": True,
            "grid.linewidth": 0.2,
            "grid.color": "0.85",
            "lines.linewidth": linewidth,
        }
    )

    triples = sorted(
        (pairing(x, y), x, y)
        for x in range(max_x + 1)
        for y in range(max_y + 1)
    )
    xs = [x for _, x, _ in triples]
    ys = [y for _, _, y in triples]
    colors = ("tab:red", "tab:green", "tab:blue")

    figure, axis = plt.subplots()
    for index in range(len(xs) - 1):
        axis.plot(
            xs[index : index + 2],
            ys[index : index + 2],
            color=colors[index % len(colors)],
            linewidth=linewidth,
        )

    axis.set_aspect("equal", "box")
    axis.set_xlabel("$x$" if usetex else "x")
    axis.set_ylabel("$y$" if usetex else "y")

    output = Path(output_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(output)
    plt.close(figure)
    return output
