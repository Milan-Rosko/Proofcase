from __future__ import annotations

import math
import random
from dataclasses import dataclass
from time import perf_counter
from typing import Dict, List, Sequence, Tuple

try:
    from .core import (
        PairEncoding,
        UnpairDecoding,
        fib,
        pair,
        stable,
        unpair,
        verify_roundtrip,
    )
except ImportError:
    from core import (
        PairEncoding,
        UnpairDecoding,
        fib,
        pair,
        stable,
        unpair,
        verify_roundtrip,
    )


@dataclass(frozen=True)
class ExhaustiveReport:
    domain: Tuple[int, int]
    tested_pairs: int
    stable_pairs: int
    unstable_pairs: int
    injective_on_stable_pairs: bool
    failures: List[str]


@dataclass(frozen=True)
class RandomReport:
    domain: Tuple[int, int]
    samples: int
    stable: int
    unstable: int
    failures: List[str]
    seed: int


@dataclass(frozen=True)
class LargeRandomReport:
    samples: int
    max_support_index: int
    density: float
    stable: int
    unstable: int
    max_bit_length: Dict[str, int]
    failures: List[str]
    seed: int


@dataclass(frozen=True)
class SurjectivityReport:
    N: int
    stable_n: int
    unstable_n: int
    stable_fraction: float
    examples_unstable: List[str]


@dataclass(frozen=True)
class StableProbeReport:
    N: int
    stable_count: int
    stable_fraction: float
    first_stable: List[int]
    first_gaps: List[int]
    mean_gap: float | None
    max_gap: int | None


@dataclass(frozen=True)
class LadderPoint:
    N: int
    stable_count: int
    stable_fraction: float
    mean_gap: float | None
    max_gap: int | None


@dataclass(frozen=True)
class ScanPoint:
    N: int
    stable_count: int
    stable_fraction: float
    a_over_sqrt_n: float
    max_gap: int
    elapsed_seconds: float


@dataclass(frozen=True)
class NotebookSuiteReport:
    exhaustive: ExhaustiveReport
    random: RandomReport
    large_random: LargeRandomReport
    surjectivity: SurjectivityReport


def _format_pair(x: int, y: int) -> str:
    return f"(x={x}, y={y})"


def _format_counterexample(
    x: int,
    y: int,
    reason: str,
    first: PairEncoding,
    decoded: UnpairDecoding,
    repaired: PairEncoding,
) -> str:
    lines = [
        f"Counterexample for {_format_pair(x, y)}",
        f"Reason: {reason}",
        "",
        f"first.n = {first.n}",
        (
            "Z(x)={z_x}, r(x)={rank}, B={base}, evenBand={even_band}".format(
                z_x=first.z_x,
                rank=first.rank,
                base=first.delimiter_base,
                even_band=first.even_band,
            )
        ),
        f"Z(y)={first.z_y}, oddBand={first.odd_band}",
        "",
        f"unpair(first.n) -> x'={decoded.x}, y'={decoded.y}",
        f"Z(n)={decoded.z_n}",
        (
            "X={x_support}, r(x')={rank}, B={base}, Y={y_support}".format(
                x_support=decoded.x_support,
                rank=decoded.rank,
                base=decoded.delimiter_base,
                y_support=decoded.y_support,
            )
        ),
        "",
        f"repaired.n = {repaired.n}",
    ]
    return "\n".join(lines)


def exhaustive_tests(lo: int = 1, hi: int = 100) -> ExhaustiveReport:
    n_to_xy: Dict[int, Tuple[int, int]] = {}
    failures: List[str] = []
    stable_pairs = 0

    for x in range(lo, hi + 1):
        for y in range(lo, hi + 1):
            ok, reason, first, decoded, repaired = verify_roundtrip(x, y)
            if not ok:
                failures.append(
                    _format_counterexample(x, y, reason, first, decoded, repaired)
                )
                continue

            stable_pairs += 1
            previous = n_to_xy.get(first.n)
            if previous is not None and previous != (x, y):
                failures.append(
                    "\n".join(
                        [
                            "Injectivity collision:",
                            f"  n = {first.n}",
                            f"  first  -> (x, y) = {previous}",
                            f"  second -> (x, y) = {(x, y)}",
                        ]
                    )
                )
            else:
                n_to_xy[first.n] = (x, y)

    tested_pairs = (hi - lo + 1) ** 2
    return ExhaustiveReport(
        domain=(lo, hi),
        tested_pairs=tested_pairs,
        stable_pairs=stable_pairs,
        unstable_pairs=tested_pairs - stable_pairs,
        injective_on_stable_pairs=not any(
            failure.startswith("Injectivity collision:") for failure in failures
        ),
        failures=failures[:10],
    )


def random_tests(
    num_samples: int = 5_000,
    lo: int = 1,
    hi: int = 10_000,
    seed: int = 12_345,
) -> RandomReport:
    rng = random.Random(seed)
    failures: List[str] = []
    stable_count = 0

    for _ in range(num_samples):
        x = rng.randint(lo, hi)
        y = rng.randint(lo, hi)
        ok, reason, first, decoded, repaired = verify_roundtrip(x, y)
        if ok:
            stable_count += 1
            continue
        failures.append(_format_counterexample(x, y, reason, first, decoded, repaired))

    return RandomReport(
        domain=(lo, hi),
        samples=num_samples,
        stable=stable_count,
        unstable=num_samples - stable_count,
        failures=failures[:10],
        seed=seed,
    )


def random_zeckendorf_support(
    max_index: int, density: float, rng: random.Random
) -> List[int]:
    support: List[int] = []
    index = 2
    while index <= max_index:
        if rng.random() < density:
            support.append(index)
            index += 2
        else:
            index += 1
    return support


def from_support(support: Sequence[int]) -> int:
    return sum(fib(index) for index in support)


def large_random_tests(
    num_samples: int = 200,
    max_index: int = 900,
    density: float = 0.12,
    seed: int = 999,
) -> LargeRandomReport:
    rng = random.Random(seed)
    failures: List[str] = []
    stable_count = 0
    max_n_bits = 0
    max_x_bits = 0
    max_y_bits = 0

    for _ in range(num_samples):
        z_x = random_zeckendorf_support(max_index=max_index, density=density, rng=rng)
        z_y = random_zeckendorf_support(max_index=max_index, density=density, rng=rng)
        x = from_support(z_x)
        y = from_support(z_y)

        ok, reason, first, decoded, repaired = verify_roundtrip(x, y)
        if not ok:
            failures.append(_format_counterexample(x, y, reason, first, decoded, repaired))
            continue

        stable_count += 1
        max_n_bits = max(max_n_bits, first.n.bit_length())
        max_x_bits = max(max_x_bits, x.bit_length())
        max_y_bits = max(max_y_bits, y.bit_length())

    return LargeRandomReport(
        samples=num_samples,
        max_support_index=max_index,
        density=density,
        stable=stable_count,
        unstable=num_samples - stable_count,
        max_bit_length={"x": max_x_bits, "y": max_y_bits, "n": max_n_bits},
        failures=failures[:10],
        seed=seed,
    )


def surjectivity_probe(N: int = 50_000) -> SurjectivityReport:
    stable_count = 0
    examples_unstable: List[str] = []

    for n in range(1, N + 1):
        x, y = unpair(n)
        repaired = pair(x, y)
        if repaired == n:
            stable_count += 1
        elif len(examples_unstable) < 10:
            examples_unstable.append(f"n={n}: unpair->(x={x}, y={y}), repair->n'={repaired}")

    return SurjectivityReport(
        N=N,
        stable_n=stable_count,
        unstable_n=N - stable_count,
        stable_fraction=stable_count / N if N else 0.0,
        examples_unstable=examples_unstable,
    )


def stable_set_probe(N: int = 50_000, show_first: int = 25) -> StableProbeReport:
    stable_numbers = [n for n in range(1, N + 1) if stable(n)]
    stable_count = len(stable_numbers)
    first_stable = stable_numbers[:show_first]
    gaps = [
        stable_numbers[index + 1] - stable_numbers[index]
        for index in range(len(stable_numbers) - 1)
    ]
    first_gaps = gaps[:show_first]

    if gaps:
        mean_gap = sum(gaps) / len(gaps)
        max_gap = max(gaps)
    else:
        mean_gap = None
        max_gap = None

    return StableProbeReport(
        N=N,
        stable_count=stable_count,
        stable_fraction=stable_count / N if N else 0.0,
        first_stable=first_stable,
        first_gaps=first_gaps,
        mean_gap=mean_gap,
        max_gap=max_gap,
    )


def ladder_probe(Ns: Sequence[int]) -> List[LadderPoint]:
    reports: List[LadderPoint] = []
    for N in Ns:
        probe = stable_set_probe(N)
        reports.append(
            LadderPoint(
                N=N,
                stable_count=probe.stable_count,
                stable_fraction=probe.stable_fraction,
                mean_gap=probe.mean_gap,
                max_gap=probe.max_gap,
            )
        )
    return reports


def scan_stable_stats(
    N: int = 1_000_000,
    report_points: Sequence[int] = (
        10_000,
        50_000,
        100_000,
        200_000,
        500_000,
        1_000_000,
    ),
) -> List[ScanPoint]:
    normalized_points = sorted(
        {int(point) for point in report_points if 1 <= int(point) <= N}
    )
    report_index = 0
    stable_count = 0
    last_stable: int | None = None
    max_gap = 0
    started = perf_counter()
    results: List[ScanPoint] = []

    for n in range(1, N + 1):
        if stable(n):
            stable_count += 1
            if last_stable is not None:
                max_gap = max(max_gap, n - last_stable)
            last_stable = n

        if report_index < len(normalized_points) and n == normalized_points[report_index]:
            elapsed = perf_counter() - started
            results.append(
                ScanPoint(
                    N=n,
                    stable_count=stable_count,
                    stable_fraction=stable_count / n,
                    a_over_sqrt_n=stable_count / math.sqrt(n),
                    max_gap=max_gap,
                    elapsed_seconds=elapsed,
                )
            )
            report_index += 1

    if not normalized_points or normalized_points[-1] != N:
        elapsed = perf_counter() - started
        results.append(
            ScanPoint(
                N=N,
                stable_count=stable_count,
                stable_fraction=stable_count / N if N else 0.0,
                a_over_sqrt_n=stable_count / math.sqrt(N) if N else 0.0,
                max_gap=max_gap,
                elapsed_seconds=elapsed,
            )
        )

    return results


def run_default_suite() -> NotebookSuiteReport:
    return NotebookSuiteReport(
        exhaustive=exhaustive_tests(1, 100),
        random=random_tests(num_samples=5_000, lo=1, hi=10_000, seed=12_345),
        large_random=large_random_tests(
            num_samples=200, max_index=900, density=0.12, seed=999
        ),
        surjectivity=surjectivity_probe(N=50_000),
    )
