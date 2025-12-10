# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "z3-solver>=4,<5",
# ]
# ///
from collections import deque
from functools import reduce
from operator import add
from typing import Generator

from z3 import z3

OFF = "."
ON = "#"
STATE_MAP: dict[str, int] = {OFF: 0, ON: 1}
SOLVED = "sat"


def next_machine(
    inputs: list[str],
) -> Generator[tuple[list[int], list[int], list[list[int]], list[int]], None, None]:
    for line in inputs:
        groups = line.split()
        diagram, *buttons_, requirements_ = groups

        desired_state: list[int] = [STATE_MAP[led] for led in list(diagram[1:-1])]
        initial_state: list[int] = [0 for _ in desired_state]

        buttons: list[list[int]] = []
        for b in buttons_:
            buttons.append([int(x) for x in b[1:-1].split(",")])

        requirements: list[int] = [int(x) for x in requirements_[1:-1].split(",")]

        yield initial_state, desired_state, buttons, requirements


def part01(inputs: list[str]) -> None:
    # I think we need a dynamic programming approach, firstly exhaustively checking
    # all combinations of all buttons, but storing the common states of button effect on state xyz
    n_switches = 0
    for machine in next_machine(inputs):
        initial_state, desired_state, buttons, requirements = machine
        # thought 1. turn everything into bit masks
        state = 0
        target_state = 0
        for i, v in enumerate(desired_state):
            target_state = target_state | (v << i)

        button_masks: list[int] = []
        for button in buttons:
            button_mask = 0
            for b in button:
                button_mask = button_mask | (1 << b)
            button_masks.append(button_mask)
        # xor button with state to see its effect
        # -> maybe don't need dp as the lookup would take longer than xor?
        # start with button A, do some DFS combining other buttons until we get to either
        # 0, target or itself (e.g. first move).  If we hit 0, backtrack and choose the next branch
        # -> actually BFS might be more optimal as the first target we find is
        # guaranteed to be the min?
        q = deque(button_masks)  # List of actions to try
        visited = set([0, *button_masks])  # If we've tried a state
        distance_map: dict[int, int] = {
            b: 1 for b in button_masks
        }  # Distance of state from start
        while q:
            current = q.popleft()
            distance = distance_map[current]
            if current == target_state:
                n_switches += distance
                break

            for bm in button_masks:
                next_state = current ^ bm
                if next_state not in visited:
                    visited.add(next_state)
                    q.append(next_state)
                    distance_map[next_state] = distance + 1

        else:
            print("not found")

    print(f"{n_switches=}")


def part02(inputs: list[str]) -> None:
    n_switches = 0
    for machine in next_machine(inputs):
        initial_state, desired_state, buttons, requirements = machine
        possible_characters: list[str] = [chr(ord("a") + i) for i in range(26)]

        # Each button has an unkown coefficient and we want to find the minimum sum of coefficients
        # such that the effect of all button presses results in the desired_state
        # --> how do we represent state & state transitions numerically?
        button_coefficients = [
            z3.Int(possible_characters[i]) for i, _ in enumerate(buttons)
        ]

        # build constraints
        actions = [[] for _ in requirements]
        for button, coefficient in zip(buttons, button_coefficients):
            # Link all buttons that effect each requirement
            for requirement_idx in button:
                actions[requirement_idx].append(coefficient)

        solver = z3.Optimize()
        for action, requirement in zip(actions, requirements):
            # The effect of all button presses on requirement X must equal the requirement target value
            reduced = reduce(add, action)
            solver.add(reduced == requirement)

        for coefficient in button_coefficients:
            # Buttons can only be pressed 0 or more times
            solver.add(coefficient >= 0)

        solver.minimize(sum(button_coefficients))
        assert solver.check() == z3.sat

        model = solver.model()
        solution = {str(coeff): model[coeff].as_long() for coeff in button_coefficients}
        # print(solution)
        n_switches += sum(solution.values())

    print(f"{n_switches=}")


if __name__ == "__main__":
    input_file = "sample.txt"
    input_file = "inputs.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    # part01(inputs)
    part02(inputs)
