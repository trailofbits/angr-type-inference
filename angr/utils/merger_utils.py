import argparse
import pickle

import scipy.stats
from .eval_binary_type_inference import ComparisonData
import itertools
from dataclasses import dataclass
import matplotlib.pyplot as plt
import numpy as np
import scipy
import os
@dataclass
class AggregateScores:
    total_diff: float
    average_diff: float
    total_time: float
    average_time: float
    time_by_size: list[tuple[int, float]]
    time_by_size_by_binary: list[tuple[int, float]]


def main():
    prser = argparse.ArgumentParser("merge_eval_files")
    prser.add_argument("file1")
    prser.add_argument("file2")
    prser.add_argument("--disable_plot_file1", default=False, action="store_true")
    prser.add_argument("--disable_plot_file2", default=False, action="store_true")
    prser.add_argument("--out", default=None, required=False, type=str)
    prser.add_argument("--out_csv")
    prser.add_argument("--extract_func_size_stats", type=str)
    prser.add_argument("--trimmed_fail_log", type=str)

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

    with open(args.extract_func_size_stats, "rb") as f1:
        sizes = pickle.load(f1)
        with open(args.trimmed_fail_log,"r") as f:
            size_by_addr_input = [(bin_name, int(sz)) for (bin_name, sz) in [ln.split(":") for ln in f.readlines()]]
            size_by_addr = dict([((os.path.basename(pth), int(linked_addr)), btsize) for ((pth, symbo_name, linked_addr, rel_addr), btsize) in sizes.items()])
            #print(size_by_addr)
            szs = []
            for (bin_name, func_addr) in size_by_addr_input:
                if (bin_name, func_addr) in size_by_addr:
                    szs.append(size_by_addr[(bin_name,func_addr)])
            print(np.mean(szs))
            print(np.median(szs))
            print(np.max(szs))
            assert False

    samps = []

    samps_by_func = []
    def get_dist_total_and_average(lst: list[ComparisonData], use_min: bool) -> AggregateScores:
        time_sel = min if use_min else max
        get_time_for_comp = lambda x: np.mean(x.time_list) if hasattr(x, "time_list") else x.ns_time_spent_during_inference
        seen_set = set()
        fltered: list[ComparisonData] = [x for x in lst if (
            x.binary_name, x.func_addr) in shared_tgts]
        sampsdict = {}
        for x in fltered:
            assert (x.binary_name, x.func_addr) not in seen_set
            seen_set.add((x.binary_name, x.func_addr))
            sampsdict[(x.binary_name, x.func_addr)] = get_time_for_comp(x)
        samps_by_func.append(sampsdict)
        #samps.append(fltered)
        var_total = []
        for lst in fltered:
            var_total.append(np.std(x.time_list)/np.mean(x.time_list))
        
        average_stdev = np.mean(var_total)
        print("Average % stddev for microbenches ", average_stdev)

        print("stddev type distance: ",np.std([x.type_distance for x in fltered]))
        print("stddev time distance: ",np.std([x.ns_time_spent_during_inference for x in fltered]))
        tot_dist = sum(map(lambda x: x.type_distance, fltered))
        average_dist = tot_dist/len(fltered)
        print(len(fltered))
        tot_time = sum(
            map(lambda x:  get_time_for_comp(x), fltered))
        average_time = tot_time/len(fltered)
        print(len(fltered))

        print([(x.binary_name, x.func_addr, x.func_size, x.ns_time_spent_during_inference)
              for x in fltered if x.func_size > 600])

        time_for_binary = {}
        total_cons_for_binary = {}
        for x in fltered:
            time_for_binary[x.binary_name] = time_for_binary.get(x.binary_name,0.0) + x.ns_time_spent_during_inference
            total_cons_for_binary[x.binary_name] = total_cons_for_binary.get(x.binary_name,0) + x.func_size
        

        time_by_size_by_binary = [(v, time_for_binary[k]) for (k,v) in total_cons_for_binary.items()]
        time_by_size = list(
            map(lambda x: (x.func_size, get_time_for_comp(x)), fltered))
        samps.append(time_by_size)

        return AggregateScores(tot_dist, average_dist, tot_time, average_time, time_by_size, time_by_size_by_binary)

    
    plt.xlabel("Number of Constraints")
    plt.ylabel("Time (ns)")
    def plot_agg(agg, label, color):
        plt.plot([x for (x, _) in agg.time_by_size],
                 [y for (_, y) in agg.time_by_size], color, label=label)
    agg1 = get_dist_total_and_average(lst1, True)
    if args.out:
        if not args.disable_plot_file1:
            plot_agg(agg1, "Typehoon", 'ro')

    agg2 = get_dist_total_and_average(lst2, False)
    if args.out:
        if not args.disable_plot_file2:
            plot_agg(agg2, "BinSub", 'bo')
        plt.legend(loc="best")
        plt.savefig(args.out, format="svg")
        plt.close()

    print("Scipy ttest relative on the alternative that the first sample is greater", scipy.stats.ttest_rel([time for (_, time) in samps[0]], [time for (_, time) in samps[1]],alternative="greater"))

    print("Tgt1 average diff: ", agg1.average_diff)
    print("Tgt2 average diff: ", agg2.average_diff)

    print("Tgt1 average time: ", agg1.average_time)
    print("Tgt2 average time: ", agg2.average_time)
    dist = []
    for k in samps_by_func[0]:
        binsub_time = float(samps_by_func[1][k])
        typehoon_time = float(samps_by_func[0][k])
        dist.append(binsub_time/typehoon_time)

    #counts, bins = np.histogram(dist,bins=200)
    #plt.stairs(counts, bins)
    #plt.savefig(args.out, format="svg")


    differences = dist
    iterations = 75000
    bootstrap_means = []

    time_1 = [time for (_,time) in agg1.time_by_size]
    size_1 = [sz for (sz,_) in agg1.time_by_size ]

    time_2 = [time for (_,time) in agg2.time_by_size]
    size_2 = [sz for (sz,_) in agg2.time_by_size]

    for _ in range(iterations):
        sample_diffs = np.random.choice(differences, size=len(differences))
        #sample_diffs1 = np.random.choice(time_1, size=len(time_1), replace=True)
        #sample_diffs2 = np.random.choice(time_2, size=len(time_2), replace=True)
        bootstrap_means.append(np.mean(sample_diffs))

    lower_bound = np.percentile(bootstrap_means, 2.5)
    upper_bound = np.percentile(bootstrap_means, 97.5)
    mean_diff = np.mean(bootstrap_means)

    print("95% Confidence Interval for the mean ratio in performance:")
    print(f"Lower Bound: {lower_bound}")
    print(f"Upper Bound: {upper_bound}")
    print(f"Mean Difference: {mean_diff}")
    print("Double check reorg agg", sum(samps_by_func[0].values())/sum(samps_by_func[1].values()))
    print("Double check reorg agg by mean", np.mean(list(samps_by_func[0].values()))/np.mean(list(samps_by_func[1].values())))


    print("Max size: ", np.max(size_1))
    print("Min size: ", np.min(size_1))
    print("Median size: ", np.median(size_1))
    print("Mean size: ", np.mean(size_1))
    

if __name__ == "__main__":
    main()
