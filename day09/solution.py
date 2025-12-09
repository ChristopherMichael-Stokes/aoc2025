# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "matplotlib",
#     "numpy",
#     "shapely",
#     "tqdm",
# ]
# ///
import matplotlib.pyplot as plt
import numpy as np
from shapely.geometry import Polygon
from tqdm.auto import tqdm


def part01(inputs: list[str]) -> None:
    points = [[int(p) for p in l.split(",")] for l in inputs]

    max_area = 0
    best_pair = points[0]
    for i, (x1, y1) in enumerate(points):
        for j in range(i + 1, len(points)):
            x1, y1 = points[i]
            x2, y2 = points[j]

            area = (abs(x2 - x1) + 1) * (abs(y2 - y1) + 1)
            if area > max_area:
                max_area = area
                best_pair = [i, j]

    print(f"{max_area=}")
    print(points[best_pair[0]], points[best_pair[1]])


def print_points(points: list[list[int]]):
    points_ = np.array(points)
    plt.plot(points_[:, 0], points_[:, 1])
    plt.xlabel("x")
    plt.ylabel("y")
    plt.gca().set_aspect("equal", adjustable="box")
    plt.show()


def part02(inputs: list[str]) -> None:
    points = [[int(p) for p in l.split(",")] for l in inputs]
    print_points(points)
    carpet_space = Polygon(points)

    max_area = 0
    #  Took me waaaaaaaay too long to realise part 2 only needs to consider rectangles between input points
    #  --> original approach was to try every single inner coordinate pair
    for i, (x1, y1) in enumerate(tqdm(points)):
        for j in range(i + 1, len(points)):
            x1, y1 = points[i]
            x2, y2 = points[j]
            rectangle = Polygon([(x1, y1), (x1, y2), (x2, y2), (x2, y1)])
            area = (abs(x2 - x1) + 1) * (abs(y2 - y1) + 1)

            if area > max_area and carpet_space.contains(rectangle):
                max_area = area

    print(max_area)


if __name__ == "__main__":
    input_file = "sample.txt"
    input_file = "inputs.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
