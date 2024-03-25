import argparse
import pickle
from .eval_binary_type_inference import ComparisonData
import itertools
from dataclasses import dataclass


@dataclass
class AggregateScores:
    total_diff: float
    average_diff: float
    total_time: float
    average_time: float
    time_by_size: list[tuple[int, float]]


def main():
    prser = argparse.ArgumentParser("merge_eval_files")
    prser.add_argument("file1")
    prser.add_argument("file2")

    args = prser.parse_args()

    with open(args.file1, "rb") as f:
        lst1: list[ComparisonData] = pickle.load(f)

    with open(args.file2, "rb") as f:
        lst2: list[ComparisonData] = pickle.load(f)

    shared_tgts = set()
    for x in itertools.chain(lst1, lst2):
        shared_tgts.add((x.binary_name, x.func_addr))

    def get_dist_total_and_average(lst: list[ComparisonData]) -> AggregateScores:
        fltered: list[ComparisonData] = [x for x in lst if (
            x.binary_name, x.func_addr) in shared_tgts]
        tot_dist = sum(map(lambda x: x.type_distance, fltered))
        average_dist = tot_dist/len(fltered)
        tot_time = sum(
            map(lambda x: x.ns_time_spent_during_inference, fltered))
        average_time = tot_time/len(fltered)

        time_by_size = list(
            map(lambda x: (x.func_size, x.ns_time_spent_during_inference), fltered))

        return AggregateScores(tot_dist, average_dist, tot_time, average_time, time_by_size)

    print(get_dist_total_and_average(lst1))
    print(get_dist_total_and_average(lst2))


if __name__ == "__main__":
    main()
