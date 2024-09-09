import argparse
import os

import angr
import tqdm
import json
import pickle
import func_timeout
prsr = argparse.ArgumentParser("Binary function lister")
prsr.add_argument("dir")
prsr.add_argument("out")
args = prsr.parse_args()
target_dir: str = args.dir
working = {}

def get_num_funcs(pth):
        proj = angr.Project(pth)
        proj = angr.Project(pth, auto_load_libs=False,
                                load_debug_info=True, main_opts={"base_addr": 0})
        proj.analyses.CFGFast(normalize=True, data_references=True)
        print(len(proj.kb.functions))
        return len(proj.kb.functions)
for elem in tqdm.tqdm(os.listdir(target_dir)):
    if elem.endswith(".bin"):
        pth = os.path.join(target_dir, elem)
        try:
            working[pth] = func_timeout.func_timeout(400, get_num_funcs, [pth])
        except func_timeout.FunctionTimedOut as e:
             pass
        

with open(args.out, "w") as f:
    pickle.dump(working, f,indent=4)