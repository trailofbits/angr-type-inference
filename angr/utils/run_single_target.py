
import argparse
import os
import angr
import pathlib
from angr.knowledge_base import KnowledgeBase
from angr.analyses.typehoon.simple_solver import SimpleSolver, BASE_LATTICES
from angr.analyses.typehoon.algebraic_solver import ConstraintGenerator


def main():
    prsr = argparse.ArgumentParser()
    prsr.add_argument("--target_bin", required=True)
    prsr.add_argument("--addr", required=True, type=int)
    prsr.add_argument("--algebraic", default=False, action="store_true")
    args = prsr.parse_args()
    target_bin = args.target_bin
    binname = os.path.basename(target_bin)
    path = pathlib.Path(target_bin).resolve().absolute()
    proj = angr.Project(path, auto_load_libs=False, load_debug_info=True)
    # hack if it's relocatable we load it at 0 so dwarf offsets line up
    if proj.loader.main_object.is_relocatable:
        proj = angr.Project(path, auto_load_libs=False,
                            load_debug_info=True, main_opts={"base_addr": 0})
    print(proj.loader.main_object)
    proj.analyses.CFGFast(normalize=True, data_references=True)
    proj.analyses.CompleteCallingConventions(
        recover_variables=True, analyze_callsites=True)

    tmp_kb = KnowledgeBase(proj)
    func = proj.kb.functions[args.addr]

    def bldr(bits, constraints, typevars):
        subbldr = (lambda bits, constraints, typevars: ConstraintGenerator(
            constraints, bits)) if args.algebraic else SimpleSolver
        return subbldr(bits, constraints, typevars)
    cres = proj.analyses.Clinic(
        func, solver_builder=bldr, variable_kb=tmp_kb)
    print(cres.ns_time_spent_in_type_inference)


if __name__ == "__main__":
    main()
