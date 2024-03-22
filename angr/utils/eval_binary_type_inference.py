import pathlib
import angr
from dataclasses import dataclass
from angr.knowledge_plugins.functions import Function
from angr.sim_type import SimType
from angr.sim_variable import SimVariable
from cle.backends.elf.variable import VariableType
import argparse
from angr.analyses.typehoon.simple_solver import SimpleSolver
from angr.analyses.typehoon.algebraic_solver import ConstraintGenerator


@dataclass
class VTypesForFunction:
    func: Function
    ftys: dict[SimVariable, SimType]
    ns_time_spent_during_type_inference: int


@dataclass
class TyComparison:
    applied_to_var: SimVariable
    distance: float


@dataclass
class CompResult:
    func: Function
    ns_time_spent_during_inference: int
    comparisons: list[TyComparison]


def collect_variable_types_for_function(func: Function, project: angr.Project) -> None | VTypesForFunction:
    print(
        "old", [v.name for v in project.kb.variables[func.addr].get_variables()])
    try:
        cres = project.analyses.Clinic(
            func, solver_builder=lambda bits, constraints, typevars: ConstraintGenerator(constraints, bits))
    except:
        return None
    # print(cres.ns_time_spent_in_type_inference)
    if cres.ns_time_spent_in_type_inference == 0:
        return None

    vtyf = VTypesForFunction(func, {}, cres.ns_time_spent_in_type_inference)
    # variables should now be recovered and type inference run on decomp
    var_manager = cres.variable_kb.variables[func.addr]
    print("new: ", [v.name for v in var_manager.get_variables()])
    for v in var_manager.get_variables():
        ty = var_manager.get_variable_type(v)
        if ty is not None:
            vtyf.ftys[v] = ty
    return vtyf


def main():
    typeval = argparse.ArgumentParser("DWARF based type inference evaluation")
    typeval.add_argument("target_bin")
    args = typeval.parse_args()
    path = pathlib.Path(args.target_bin).resolve().absolute()
    proj = angr.Project(path, auto_load_libs=False, load_debug_info=True)
    proj.analyses.CFGFast(normalize=True, data_references=True)
    proj.analyses.CompleteCallingConventions(
        recover_variables=True, analyze_callsites=True)

    # so we ensure that we have the same variables as dwarf here
    # angr doesnt populate types from dwarf so this doesnt affect type inference
    proj.kb.variables.load_from_dwarf()

    vtypes_for_functions: list[VTypesForFunction] = []
    for (_, func) in proj.kb.functions.items():
        r = collect_variable_types_for_function(func, proj)
        if r is not None:
            vtypes_for_functions.append(r)

    dwarf_variables: dict[int, dict[str, VariableType]] = {}
    for cu in proj.loader.main_object.compilation_units:
        for (low_pc, f) in cu.functions.items():
            d = {}
            for v in f.local_variables:
                if v.name is not None and v.type is not None:
                    d[v.name] = v.type
            dwarf_variables[low_pc] = d
    print(list(dwarf_variables.items()))
    for vtype in vtypes_for_functions:
        if vtype is not None:
            if vtype.func.addr in dwarf_variables:
                vdict = dwarf_variables[vtype.func.addr]
                for (k, v) in vtype.ftys.items():
                    # print(k.name)
                    if k.name in vdict:
                        print(v)
                        print(vdict[k.name])
                        print(k)


if __name__ == "__main__":
    main()
