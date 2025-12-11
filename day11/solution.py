# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "matplotlib",
#     "networkx",
# ]
# ///
from collections import defaultdict
from typing import Mapping, TypeAlias

NodeMap: TypeAlias = Mapping[str, list[str]]


def get_node_map(inputs: list[str], verbose: bool = False) -> NodeMap:
    node_map = defaultdict(list)
    for line in inputs:
        name, rest = line.split(":")
        node_map[name].extend(rest.split())

    # Used to double check graph properties, not part of solution
    import matplotlib.pyplot as plt
    import networkx as nx

    G = nx.DiGraph()
    nx.find_induced_nodes
    for src, dests in node_map.items():
        for dst in dests:
            G.add_edge(src, dst)
    try:
        nx.find_cycle(G, orientation="original")
        print("Graph has cycles")
    except nx.NetworkXNoCycle:
        print("Graph contains no cycles - yay!!!")

    if verbose:
        pos = nx.spring_layout(G)
        nx.draw(G, pos, with_labels=True, arrows=True)
        plt.show()

    return node_map


def count_paths(current: str, target: str, node_map: NodeMap, visited: set[str]):
    # Cycle catching DFS
    if current == target:
        return 1
    elif current in visited:
        return 0

    visited.add(current)
    n_paths = sum(
        count_paths(neighbour, target, node_map, visited)
        for neighbour in node_map[current]
    )
    visited.remove(current)
    return n_paths


def part01(inputs: list[str]) -> None:
    node_map = get_node_map(inputs)
    n = count_paths("you", "out", node_map, set())
    print(n)


def part02(inputs: list[str]) -> None:
    node_map = get_node_map(inputs)

    # Pretty sure cycle catching DFS is intractible for this part?
    # luckily there's no cycles in the source graph even though it looks like there could be,
    # so can swap out visited set with dp cache
    def count_paths(current: str, target: str, n_paths_to: dict[str, int]):
        if current == target:
            return 1
        if current in n_paths_to:
            return n_paths_to[current]

        n_paths_to[current] = sum(
            count_paths(edge, target, n_paths_to) for edge in node_map[current]
        )
        return n_paths_to[current]

    # Count out route combinations crossing required nodes
    svr_fft = count_paths("svr", "fft", {})
    fft_dac = count_paths("fft", "dac", {})
    dac_out = count_paths("dac", "out", {})

    svr_dac = count_paths("svr", "dac", {})
    dac_fft = count_paths("dac", "fft", {})
    fft_out = count_paths("fft", "out", {})

    print((svr_fft * fft_dac * dac_out) + (svr_dac * dac_fft * fft_out))


if __name__ == "__main__":
    input_file = "sample.txt"
    input_file = "sample2.txt"
    input_file = "inputs.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
