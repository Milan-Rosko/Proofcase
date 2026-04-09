from __future__ import annotations

from dataclasses import dataclass
from typing import List, Tuple, Union

NatInput = Union[int, str]

_FIBONACCI = [0, 1]


def fib(index: int) -> int:
    if index < 0:
        raise ValueError(f"fib({index}) is out of range.")
    while len(_FIBONACCI) <= index:
        _FIBONACCI.append(_FIBONACCI[-1] + _FIBONACCI[-2])
    return _FIBONACCI[index]


def to_nat(value: NatInput) -> int:
    if isinstance(value, bool):
        raise TypeError("Expected a natural number, not bool.")
    if isinstance(value, int):
        if value < 0:
            raise ValueError("Expected a natural integer.")
        return value
    if isinstance(value, str):
        candidate = value.strip()
        if not candidate.isdigit():
            raise ValueError("Expected a natural decimal string.")
        return int(candidate)
    raise TypeError("Unsupported input type for natural number.")


def zeckendorf_decompose(n_in: NatInput) -> List[int]:
    n = to_nat(n_in)
    if n == 0:
        return []

    support: List[int] = []
    remainder = n

    max_index = 2
    while fib(max_index + 1) <= remainder:
        max_index += 1

    while remainder > 0:
        index = 2
        while index + 1 <= max_index and fib(index + 1) <= remainder:
            index += 1
        support.append(index)
        remainder -= fib(index)
        max_index = index - 2
        if remainder > 0 and max_index < 2:
            raise RuntimeError(
                "Zeckendorf decomposition failed: remainder left without an admissible index."
            )

    return support


def delimiter_rank(x_in: NatInput) -> int:
    x = to_nat(x_in)
    index = 1
    while fib(index) <= x:
        index += 1
    return index


@dataclass(frozen=True)
class PairEncoding:
    n: int
    z_x: List[int]
    z_y: List[int]
    rank: int
    delimiter_base: int
    even_band: List[int]
    odd_band: List[int]


@dataclass(frozen=True)
class UnpairDecoding:
    x: int
    y: int
    z_n: List[int]
    x_support: List[int]
    y_support: List[int]
    rank: int
    delimiter_base: int


def pair_details(x_in: NatInput, y_in: NatInput) -> PairEncoding:
    x = to_nat(x_in)
    y = to_nat(y_in)

    z_x = zeckendorf_decompose(x)
    z_y = zeckendorf_decompose(y)
    rank = delimiter_rank(x)
    delimiter_base = 2 * rank

    even_band = [2 * index for index in z_x]
    odd_band = [delimiter_base + (2 * index - 1) for index in z_y]

    n = 0
    for index in even_band:
        n += fib(index)
    for index in odd_band:
        n += fib(index)

    return PairEncoding(
        n=n,
        z_x=z_x,
        z_y=z_y,
        rank=rank,
        delimiter_base=delimiter_base,
        even_band=even_band,
        odd_band=odd_band,
    )


def pair(x_in: NatInput, y_in: NatInput) -> int:
    return pair_details(x_in, y_in).n


def carryless_pair(x_in: NatInput, y_in: NatInput) -> PairEncoding:
    return pair_details(x_in, y_in)


def unpair_details(n_in: NatInput) -> UnpairDecoding:
    n = to_nat(n_in)
    z_n = zeckendorf_decompose(n)

    x_support = [index // 2 for index in z_n if index % 2 == 0]
    x = sum(fib(index) for index in x_support)

    rank = delimiter_rank(x)
    delimiter_base = 2 * rank

    y_support = [
        (index - delimiter_base + 1) // 2
        for index in z_n
        if index % 2 == 1 and index >= delimiter_base + 1
    ]
    y = sum(fib(index) for index in y_support)

    return UnpairDecoding(
        x=x,
        y=y,
        z_n=z_n,
        x_support=x_support,
        y_support=y_support,
        rank=rank,
        delimiter_base=delimiter_base,
    )


def unpair(n_in: NatInput) -> Tuple[int, int]:
    details = unpair_details(n_in)
    return details.x, details.y


def carryless_unpair(n_in: NatInput) -> UnpairDecoding:
    return unpair_details(n_in)


def stable(n_in: NatInput) -> bool:
    x, y = unpair(n_in)
    return pair(x, y) == to_nat(n_in)


def verify_roundtrip(
    x_in: NatInput, y_in: NatInput
) -> Tuple[bool, str, PairEncoding, UnpairDecoding, PairEncoding]:
    x = to_nat(x_in)
    y = to_nat(y_in)

    first = pair_details(x, y)
    decoded = unpair_details(first.n)
    repaired = pair_details(decoded.x, decoded.y)

    if decoded.x != x or decoded.y != y:
        return (
            False,
            "Round-trip mismatch: unpair(pair(x, y)) != (x, y).",
            first,
            decoded,
            repaired,
        )
    if repaired.n != first.n:
        return (
            False,
            "Round-trip mismatch: pair(unpair(n)) != n.",
            first,
            decoded,
            repaired,
        )

    return True, "OK", first, decoded, repaired
