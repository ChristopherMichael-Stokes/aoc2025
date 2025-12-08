# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from functools import cache
from math import sqrt
from typing import Sequence


def distance(x: Sequence[int], y: Sequence[int]) -> float:
    return sqrt(sum((a - b) ** 2 for (a, b) in zip(x, y)))


def merge_circuits(circuits: list[set[int]]) -> list[set[int]]:
    made_merges = True
    while made_merges:
        made_merges = False
        for i in range(len(circuits)):
            j = i + 1
            while j < len(circuits):
                if circuits[i] & circuits[j]:
                    circuits[i] |= circuits[j]
                    circuits.pop(j)
                    made_merges = True
                else:
                    j += 1
    return circuits


@cache
def get_connection_lengths(
    junctions: tuple[tuple[int, ...]],
) -> dict[float, tuple[int, int]]:
    adjacency_matrix: list[list[float]] = [
        [distance(box, other) for other in junctions] for box in junctions
    ]

    values = dict()  # Flat list of right hand side of matrix (past diagonal)
    for i, row in enumerate(adjacency_matrix):
        for j, v in enumerate(row):
            if j > i:
                values[v] = (i, j)

    return values


def part01(inputs: list[str]) -> None:
    assert len(inputs) == 20 or len(inputs) == 1000
    N_PAIRS = 10 if len(inputs) == 20 else 1000

    junctions = [tuple(int(i) for i in l.split(",")) for l in inputs]
    values = get_connection_lengths(tuple(junctions))

    ordered_connections = sorted(list(values.keys()), reverse=True)
    circuits = merge_circuits([set(values[v]) for v in ordered_connections[-N_PAIRS:]])
    final_connections = sorted(circuits, key=len)

    print(
        len(final_connections[-3])
        * len(final_connections[-2])
        * len(final_connections[-1])
    )


def part02(inputs: list[str]) -> None:
    assert len(inputs) == 20 or len(inputs) == 1000
    N_PAIRS = 10 if len(inputs) == 20 else 1000

    junctions = [tuple(int(i) for i in l.split(",")) for l in inputs]
    values = get_connection_lengths(tuple(junctions))

    ordered_connections = sorted(list(values.keys()), reverse=True)
    circuits = merge_circuits(
        [set(values[v]) for v in ordered_connections[-N_PAIRS:]]
    )  # Initial circuit / same as part 1

    # Add each subsequent pair until we have all ids in a single circuit
    for n_connections in range(N_PAIRS + 1, len(ordered_connections)):
        new_pair = set(values[ordered_connections[-n_connections]])
        circuits.append(new_pair)
        circuits = merge_circuits(circuits)

        if len(circuits) == 1 and len(circuits[0]) == len(junctions):
            pair = values[ordered_connections[-n_connections]]
            print(junctions[pair[0]][0] * junctions[pair[1]][0])
            break


if __name__ == "__main__":
    input_file = "sample.txt"
    input_file = "inputs.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
