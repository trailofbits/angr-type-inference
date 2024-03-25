from typing import Iterable
import pathlib
from typing import Any
import angr
from dataclasses import dataclass
from angr.knowledge_plugins.functions import Function
from angr.sim_type import SimType, SimTypeFunction
from angr.sim_variable import SimVariable
from cle.backends.elf.variable import VariableType
from cle.backends.elf.variable_type import TypedefType, UnionType, PointerType, StructType, ArrayType, BaseType, StructMember
import argparse
from angr.analyses.typehoon.simple_solver import SimpleSolver, BASE_LATTICES
from angr.analyses.typehoon.algebraic_solver import ConstraintGenerator
from angr.analyses.typehoon.typeconsts import TypeConstant, Pointer as TypehoonPointer, Struct as TypehoonStruct, Array as TypehoonArray, BottomType as TypehoonBot, TopType as TypehoonTop
from angr.analyses.typehoon.typeconsts import Int8 as TypehoonInt8, Int16 as TypehoonInt16, Int32 as TypehoonInt32, Int64 as TypehoonInt64, Int as TypehoonInt, Function as TypehoonFunction
from angr.analyses.typehoon.translator import TypeTranslator
from multiprocessing import Pool
import os
import tqdm
from multiprocessing import Process, Pipe
from threading import Thread
import time
from angr.knowledge_base import KnowledgeBase
import networkx as nx
import typing
import itertools
from archinfo import Arch
from sortedcontainers import SortedDict


def run_with_timeout(timeout_secs: int, f, args) -> Any:
    res = None

    def runner_with_return(*args):
        nonlocal res
        res = f(*args)

    proc = Thread(target=runner_with_return, args=args)
    proc.start()
    start = time.perf_counter()
    while True:
        if not proc.is_alive():
            return res
        diff = time.perf_counter() - start
        if diff > timeout_secs:
            return None


@dataclass
class VTypesForFunction:
    func: Function
    fty: SimTypeFunction
    ns_time_spent_during_type_inference: int


@dataclass
class CompResult:
    func: Function
    ns_time_spent_during_inference: int
    recoverd_fty: SimTypeFunction
    ground_truth_type: SimTypeFunction
    arch: Arch


def collect_variable_types_for_function(func: Function, project: angr.Project) -> None | VTypesForFunction:
    tmp_kb = KnowledgeBase(project)
    tmp_kb.variables.load_from_dwarf()
    print("old", func.prototype)
    try:
        cres = project.analyses.Clinic(
            func, solver_builder=lambda bits, constraints, typevars: ConstraintGenerator(constraints, bits), variable_kb=tmp_kb)
        # func, solver_builder=SimpleSolver)
    except:
        return None
    # print(cres.ns_time_spent_in_type_inference)
    if cres.ns_time_spent_in_type_inference == 0:
        return None

    print("new", func.prototype)
    vtyf = VTypesForFunction(func, func.prototype,
                             cres.ns_time_spent_in_type_inference)
    # Clinic should pick a prototype

    return vtyf


@dataclass
class BottomGroundType:
    pass


INT_SIZE = [(8, TypehoonInt8()), (16, TypehoonInt16()),
            (32, TypehoonInt32()), (64, TypehoonInt64())]

TYPE_ENCODINGS_WITH_SIZE = {
    # typehoon base lattice doesnt have floats... should add this at some point
}
for int_names in ["int", "unsigned", "signed"]:
    for (sz, rty) in INT_SIZE:
        TYPE_ENCODINGS_WITH_SIZE[("int", sz)] = rty

UNSIZED_TYPE_ENCODINGS = {
    "int": TypehoonInt(),
    "unsigned": TypehoonInt(),
    "signed": TypehoonInt(),
    "char": TypehoonInt8(),
    "unsigned char": TypehoonInt8(),
    "signed char": TypehoonInt8()
}


class StructOffsets:
    def __init__(self, it: Iterable[StructMember]) -> None:
        self._d = SortedDict(
            [(mem.addr_offset, mem.type.byte_size) for mem in it if mem.addr_offset is not None and mem.type.byte_size is not None])

    def starts_at_end(self, off: int) -> bool:
        leqkey = self._d.bisect_right(off) - 1
        if leqkey > 0:
            (st, end) = self._d.peekitem(leqkey)
            return st + end == off

        return False

    def overlaps_covered(self, off: int, size: int):
        leqkey = self._d.bisect_right(off) - 1
        gt = leqkey + 1

        does_overlap = False

        if leqkey >= 0:
            (ltelem_start, lt_elem_size) = self._d.peekitem(leqkey)
            does_overlap |= not (
                off >= ltelem_start + lt_elem_size)

        if gt < len(self._d):
            (gtelem_start, _) = self._d.peekitem(gt)
            does_overlap |= not (
                off + size <= gtelem_start)

        return does_overlap


class TypeComparison:
    """
    Environment for comparison of two types, requires the type map for the binary for typedefs
    and the lattice def to compute distances of primitive types.
    Also a type translator  
    """

    def __init__(self, base_lattice: nx.DiGraph) -> None:
        self.base_lattice = base_lattice
        self.max_dist = self.compute_max_dist()

    def compute_max_dist(self):
        return nx.shortest_path_length(self.base_lattice, TypehoonTop(), TypehoonBot())

    def base_type_distance(self, t1: TypeConstant, t2: VariableType) -> float:
        bty = self.get_base_type(t2)
        if t1 not in self.base_lattice and bty not in self.base_lattice:
            return 0

        if t1 not in self.base_lattice or bty not in self.base_lattice:
            return self.max_dist

        # the distance for a primitive type is the average of the distance to the join point
        join_point = nx.lowest_common_ancestor(self.base_lattice, t1, bty)

        try:
            t1len = nx.shortest_path_length(self.base_lattice, join_point, t1)
            btylen = nx.shortest_path_length(
                self.base_lattice, join_point, bty)
            return (float(t1len)+float(btylen))/2.0
        except:
            pass

        raise RuntimeError(f"Could not find path between {t1} and {bty}")

    def type_of_tdef(self, tdef: TypedefType) -> VariableType:
        t = tdef.type
        if t is not None:
            return t

        return BottomGroundType()

    def get_base_type(self, t: BaseType):
        if (t.name, t.byte_size) in TYPE_ENCODINGS_WITH_SIZE:
            return TYPE_ENCODINGS_WITH_SIZE[(t.name, t.byte_size)]

        if t.name in UNSIZED_TYPE_ENCODINGS:
            return UNSIZED_TYPE_ENCODINGS[t.name]

        return TypehoonBot()

    def type_distance(self, t1: TypeConstant, t2: VariableType) -> float:
        """
        Compute the distance between types 

        we need a default for unrecovered type defs for whatever reason (hopefully dont see this in practice)
        We just select a void type that compares at 0 for it.

        We do the same for unions since they arent supported.

        - BaseType
        - PointerType
        - StructType
        - ArrayType
        - UnionType
        - BottomGroundType

        """

        def comp_list(lst1: list[TypeConstant], lst2: list[VariableType]):
            total_dist = 0.0
            num = 0
            for (x, y) in zip(lst1, lst2):
                total_dist += self.type_distance(x, y)
                num += 1

            diff = abs(len(lst1) - len(lst2))
            num += diff
            total_dist += diff * self.max_dist

            if num == 0:
                return 0.0
            else:
                return total_dist/num

        match (t1, t2):
            # TODO(Ian) we are going to need to handle functions

            case (_, None):
                return 0
            case (TypehoonFunction(), SimTypeFunction()):
                t1 = typing.cast(TypehoonFunction, t1)
                t2 = typing.cast(SimTypeFunction, t2)

                args = comp_list(t1.params, t2.args)
                outputs = comp_list(
                    t1.outputs, [t2.returnty] if t2.returnty is not None else [])

                return (args + outputs)/2.0
            case (_, BottomGroundType()) | (_, UnionType()):
                # if we say we know nothing about the true type,
                # then we assume 0, we also do this for union since we dont support
                # unions
                return 0
            case (_, TypedefType()):
                return self.type_distance(t1, self.type_of_tdef(t2))
            case (TypehoonPointer(), PointerType()):
                return self.type_distance(t1.basetype,  t2.referenced_type)
            case (TypehoonStruct(), StructType()):
                # we just take the average distance on fields assuming unmatched fields have max dist

                # there's a caveat here where this is asymmetric, we allow for padding by not counting distance for members that dont overlap some member
                # in the ground type
                covered_by_ground = StructOffsets(t2.members)
                total_fld_dist = 0.0
                total_compare = 0
                members = dict([(x.addr_offset, x) for x in t2.members])
                for off in set(list(members.keys()) + list(t1.fields.keys())):
                    compare = True
                    if off in t1.fields and not (off in members):
                        fld = t1.fields[off]
                        try:
                            sz = fld.size
                            if not covered_by_ground.overlaps_covered(off, sz) and covered_by_ground.starts_at_end(off):
                                compare = False
                        except NotImplementedError:
                            pass
                    if compare:
                        total_compare += 1
                        if off in t1.fields and off in members:
                            total_fld_dist += self.type_distance(
                                t1.fields[off], members[off].type)
                if total_compare == 0:
                    return 0.0
                return total_fld_dist/total_compare
            case (TypehoonArray(), ArrayType()):
                return self.type_distance(t1.element, t2.element_type)
            case (_, BaseType()):
                if t1 in self.base_lattice:
                    return self.base_type_distance(t1, t2)
                else:
                    return self.max_dist
            case (_, _):
                print(f"returning max dist for: {t1} {t2}")
                return self.max_dist


def eval_bin(target_bin):
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

    # so we ensure that we have the same variables as dwarf here
    # angr doesnt populate types from dwarf so this doesnt affect type inference
    proj.kb.variables.load_from_dwarf()

    vtypes_for_functions: list[VTypesForFunction] = []
    for (_, func) in proj.kb.functions.items():
        r = collect_variable_types_for_function(func, proj)
        if r is not None:
            vtypes_for_functions.append(r)

    assert func.project is not None
    sigs: dict[int, SimTypeFunction] = {}
    for cu in proj.loader.main_object.compilation_units:
        for (low_pc, f) in cu.functions.items():
            dwarf_sig_args = []
            for v in f.local_variables:
                if v.is_parameter:
                    dwarf_sig_args.append(v.type)
            retty = None
            if f.type_offset is not None and f.type_offset in proj.loader.main_object.type_list:
                retty = proj.loader.main_object.type_list[f.type_offset]
            sigs[low_pc] = SimTypeFunction(dwarf_sig_args, retty)
    print(sigs)
    rectypes = []
    for vtype in vtypes_for_functions:
        if vtype is not None:
            if vtype.func.addr in sigs:
                groundsig = sigs[vtype.func.addr]
                rectypes.append(CompResult(
                    func, vtype.ns_time_spent_during_type_inference, vtype.fty, groundsig, func.project.arch))
    return rectypes


def eval_bin_withtimeout(target_dir):
    return run_with_timeout(360, eval_bin, [target_dir])


def main():
    prser = argparse.ArgumentParser()
    prser.add_argument("target_dir")
    prser.add_argument("-n", default=0, type=int)
    args = prser.parse_args()

    tgts = []
    for x in os.listdir(args.target_dir):
        if x.endswith(".bin"):
            tgts.append(os.path.join(args.target_dir, x))

    max_len = len(tgts) if args.n == 0 else min(args.n, len(tgts))
    with Pool() as p:
        lst: list[CompResult] = list(
            tqdm.tqdm(p.imap(eval_bin_withtimeout, tgts[0:max_len]),  total=len(tgts)))

        total_tdist = 0.0
        total_comps = 0

        for comp in itertools.chain(*list(filter(lambda x: x is not None, lst))):
            print(comp.func)
            print(comp.arch)
            bl = BASE_LATTICES[comp.arch.bits]
            comparer = TypeComparison(bl)
            translator = TypeTranslator(comp.arch)
            print(comp.ground_truth_type)
            total_tdist += comparer.type_distance(
                translator.simtype2tc(comp.recoverd_fty), comp.ground_truth_type)
            total_comps += 1

        print(total_tdist)
        print(total_comps)


if __name__ == "__main__":
    main()
