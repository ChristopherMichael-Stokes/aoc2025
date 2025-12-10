# [Advent of Code 2025](https://adventofcode.com/2025)

Solutions repo to the 2025 advent of code challenges.  The goal this year is to favour simplicity and readability of solutions over runtime optimisation and not to worry about making the code look "too" pretty.

Plus no fancy algorithms, data structures, or obscure language features unless I already have some understanding of them.

## Code

The primary tool I'm learning this year is uv scripts, so astral-uv is a requirement of this repo.

To run a solution:
```sh
cd day01 && uv run solution.py
```

To setup the dev environment for code completions (not required for running solutions):
```sh
uv sync
```

To add a solution:
```sh
make day=2
```

To run python type checking & linting:
```
uvx ty check

uvx ruff check
```
