import argparse
import os

import angr
import tqdm
import json
import func_timeout
import pickle
prsr = argparse.ArgumentParser("Binary function lister")
prsr.add_argument("dir")
prsr.add_argument("out")
args = prsr.parse_args()
target_dir: str = args.dir
working = {}

def get_num_bytes_per_function(pth):
        proj = angr.Project(pth)
        proj = angr.Project(pth, auto_load_libs=False,
                                load_debug_info=True, main_opts={"base_addr": 0})
        symbols = [f for f in proj.loader.main_object.symbols if f.is_function and (not f.is_import) and f.size > 0]
        return [((pth, symb.name, symb.linked_addr, symb.relative_addr), symb.size) for symb in symbols]

for elem in tqdm.tqdm(os.listdir(target_dir)):
    if elem.endswith(".bin"):
        pth = os.path.join(target_dir, elem)
        try:
            working.update(func_timeout.func_timeout(400, get_num_bytes_per_function, [pth]))
        except func_timeout.FunctionTimedOut as e:
             pass
        

with open(args.out, "wb") as f:
    pickle.dump(working, f)