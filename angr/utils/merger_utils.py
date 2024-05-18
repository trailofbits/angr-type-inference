import argparse
import pickle
from .eval_binary_type_inference import ComparisonData
import itertools
from dataclasses import dataclass
import matplotlib.pyplot as plt
import numpy as np


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
    prser.add_argument("--out", default=None, required=False, type=str)

    args = prser.parse_args()

    def load_all(fl) -> list[ComparisonData]:
        tot = []
        while True:
            try:
                tot.append(pickle.load(fl))
            except EOFError:
                return tot

    with open(args.file1, "rb") as f:
        lst1: list[ComparisonData] = load_all(f)

    with open(args.file2, "rb") as f:
        lst2: list[ComparisonData] = load_all(f)

    tgts_1 = set([(x.binary_name, x.func_addr) for x in lst1])
    tgts_2 = set([(x.binary_name, x.func_addr) for x in lst2])
    shared_tgts = set.intersection(tgts_1, tgts_2)

    print("Number of comparable targets: ", len(shared_tgts))

    def get_dist_total_and_average(lst: list[ComparisonData]) -> AggregateScores:
        seen_set = set()
        fltered: list[ComparisonData] = [x for x in lst if (
            x.binary_name, x.func_addr) in shared_tgts]
        for x in fltered:
            assert (x.binary_name, x.func_addr) not in seen_set
            seen_set.add((x.binary_name, x.func_addr))

        print(np.std([x.type_distance for x in fltered]))
        tot_dist = sum(map(lambda x: x.type_distance, fltered))
        average_dist = tot_dist/len(fltered)
        print(len(fltered))
        tot_time = sum(
            map(lambda x: x.ns_time_spent_during_inference, fltered))
        average_time = tot_time/len(fltered)
        print(len(fltered))

        print([(x.binary_name, x.func_addr, x.ns_time_spent_during_inference)
              for x in fltered if x.func_size > 500])

        time_by_size = list(
            map(lambda x: (x.func_size, x.ns_time_spent_during_inference), fltered))

        return AggregateScores(tot_dist, average_dist, tot_time, average_time, time_by_size)

    
    plt.xlabel("Number of Constraints")
    plt.ylabel("Time (ns)")
    def plot_agg(agg, label, color):
        plt.plot([x for (x, _) in agg.time_by_size],
                 [y for (_, y) in agg.time_by_size], color, label=label)
    agg1 = get_dist_total_and_average(lst1)
    if args.out:
        plot_agg(agg1, "Typehoon", 'ro')

    agg2 = get_dist_total_and_average(lst2)
    if args.out:
        plot_agg(agg2, "BinSub", 'bo')
        plt.legend(loc="best")
        plt.savefig(args.out, format="svg")
        plt.close()

    print("Tgt1 average diff: ", agg1.average_diff)
    print("Tgt2 average diff: ", agg2.average_diff)

    print("Tgt1 average time: ", agg1.average_time)
    print("Tgt2 average time: ", agg2.average_time)


if __name__ == "__main__":
    main()
