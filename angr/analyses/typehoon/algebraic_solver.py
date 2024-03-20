

from typing import TypeVar
from abc import abstractmethod, abstractstaticmethod
from abc import ABC
from dataclasses import dataclass
from typing import Set, Iterator, Optional, Any
from .typevars import Existence, Subtype, TypeVariable, DerivedTypeVariable, TypeConstraint
from .typeconsts import TypeConstant
from .simple_solver import BaseSolver
from enum import Enum
from functools import partial, reduce
import copy
import itertools
from pyrsistent import m, pmap, PMap, pset, PSet
from collections import defaultdict
from .typeconsts import TopType as TypehoonTop, BottomType as TypehoonBot, Int as TypehoonInt, FloatBase as TypehoonFloat, Pointer as TypehoonPointer, Struct as TypehoonStruct, Function as TypehoonFunc, Pointer32 as TypehoonPointer32, Pointer64 as TypehoonPointer64
import networkx as nx
# Import labels
from .typevars import FuncIn, FuncOut, Load, Store, ConvertTo, HasField, BaseLabel
from typing import TypeVar, Callable, Optional, Generator
from collections import deque
# A type variable is a unique holder of constraints


class DisjointSet:
    """
    Copyright (c) 2001-2002 Enthought, Inc. 2003-2024, SciPy Developers.
    All rights reserved.
    """

    def __init__(self, elements=None):
        self.n_subsets = 0
        self._sizes = {}
        self._parents = {}
        # _nbrs is a circular linked list which links connected elements.
        self._nbrs = {}
        # _indices tracks the element insertion order in `__iter__`.
        self._indices = {}
        if elements is not None:
            for x in elements:
                self.add(x)

    def __iter__(self):
        return iter(self._indices)

    def __len__(self):
        return len(self._indices)

    def __contains__(self, x):
        return x in self._indices

    def __getitem__(self, x):
        if x not in self._indices:
            raise KeyError(x)

        # find by "path halving"
        parents = self._parents
        while self._indices[x] != self._indices[parents[x]]:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x

    def add(self, x):
        if x in self._indices:
            return

        self._sizes[x] = 1
        self._parents[x] = x
        self._nbrs[x] = x
        self._indices[x] = len(self._indices)
        self.n_subsets += 1

    def merge(self, x, y, can_swap=True):
        xr = self[x]
        yr = self[y]
        if self._indices[xr] == self._indices[yr]:
            return False

        sizes = self._sizes
        if ((sizes[xr], self._indices[yr]) < (sizes[yr], self._indices[xr])) and can_swap:
            xr, yr = yr, xr
        self._parents[yr] = xr
        self._sizes[xr] += self._sizes[yr]
        self._nbrs[xr], self._nbrs[yr] = self._nbrs[yr], self._nbrs[xr]
        self.n_subsets -= 1
        return True

    def connected(self, x, y):
        return self._indices[self[x]] == self._indices[self[y]]

    def subset(self, x):
        if x not in self._indices:
            raise KeyError(x)

        result = [x]
        nxt = self._nbrs[x]
        while self._indices[nxt] != self._indices[x]:
            result.append(nxt)
            nxt = self._nbrs[nxt]
        return set(result)

    def subset_size(self, x):
        return self._sizes[self[x]]

    def subsets(self):
        result = []
        visited = set()
        for x in self:
            if x not in visited:
                xset = self.subset(x)
                visited.update(xset)
                result.append(xset)
        return result


# we give vstorage identity based
class VariableStorage:
    all_mems = []
    tot_ids = 0

    def __init__(self) -> None:
        self.lower_bounds = []
        self.upper_bounds = []
        self.id = VariableStorage.tot_ids
        VariableStorage.tot_ids += 1
        VariableStorage.all_mems.append(self)

    def add_ub(self, c):
        # if isinstance(c, VariableStorage):
        #    assert c.id != self.id
        self.upper_bounds.append(c)

    def add_lb(self, c):
        # if isinstance(c, VariableStorage):
        #    assert c.id != self.id
        self.lower_bounds.append(c)

    def __repr__(self) -> str:
        return f"vstr{self.id}"

    def __hash__(self) -> int:
        return self.id

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, VariableStorage) and self.id == __value.id

    # we are careful to preserve eq and hash accross mutability here

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self

# an atom wraps a base type from angr and provides lattice operations


class Atom:
    name: TypeConstant
    lat_fwd: nx.DiGraph
    lat_bkwd: nx.DiGraph

    def __init__(self, name: TypeConstant, lat_fwd: nx.DiGraph, lat_bkwd: nx.DiGraph) -> None:
        self.name = name
        self.lat_fwd = lat_fwd
        self.lat_bkwd = lat_bkwd

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, Atom) and self.name == __value.name

    def __hash__(self) -> int:
        return hash(self.name)

    def __repr__(self) -> str:
        return f"Atom({self.name})"

    def translate(self, o: TypeConstant):
        match o:
            case TypehoonTop():
                return Top()
            case TypehoonBot():
                return Bottom()
            case _:
                return Atom(o, self.lat_fwd, self.lat_bkwd)

    def join(self, o: "Atom") -> "Atom":
        res = nx.lowest_common_ancestor(self.lat_bkwd, self.name, o.name)
        return self.translate(res)

    def meet(self, o: "Atom") -> "Atom":
        res = nx.lowest_common_ancestor(self.lat_fwd, self.name, o.name)
        return self.translate(res)


"""
pointers are a function in the sense of "store tv" -> "load tv"
"""


@dataclass(frozen=True)
class Pointer:
    store_tv: "ConsTy"
    load_tv: "ConsTy"

    def __repr__(self) -> str:
        return f"ptr(str: {self.store_tv}, ld: {self.load_tv})"


class HashDict:
    def __init__(self, d) -> None:
        self.d = copy.deepcopy(d)
        assert self.d is not None

    def __eq__(self, v: object) -> bool:
        return isinstance(v, HashDict) and tuple(sorted(self.d.items())) == tuple(sorted(v.items()))

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.d.items())))

    def __repr__(self) -> str:
        return f"HashDict(d={self.d})"

    def __len__(self):
        return len(self.d)

    def __contains__(self, k):
        return k in self.d

    def items(self):
        return self.d.items()

    def get(self, k) -> Optional[any]:
        return self.d.get(k)

    def keys(self):
        return self.d.keys()

    def __getitem__(self, key):
        return self.d[key]


def string_of_d_as_args(d: dict[int, "ConsTy"]) -> str:
    std = sorted(d.items(), key=lambda xy: xy[0])
    bs = ""
    for (k, v) in std:
        bs += f"{k}:{v}, "
    return bs


@dataclass(frozen=False, init=False, unsafe_hash=True, eq=True)
class Record:
    fields: PMap[int, "ConsTy"]

    def __init__(self, d) -> None:
        self.fields = pmap(d)
        # (self.fields) > 0

    def __repr__(self) -> str:
        return f"rec({string_of_d_as_args(self.fields)})"


@dataclass(frozen=False, init=False, unsafe_hash=True, eq=True)
class Func:
    params: PMap[int, "ConsTy"]
    return_val: PMap[int, "ConsTy"]

    def __init__(self, p, r) -> None:
        self.params = pmap(p)
        self.return_val = pmap(r)

    def __repr__(self) -> str:
        return f"func({string_of_d_as_args(self.params)})->({string_of_d_as_args(self.return_val)})"


ConsTy = VariableStorage | Pointer | Record | Atom | Func


@dataclass(frozen=True)
class FinalVar:
    ident: int

    def __repr__(self) -> str:
        return f"fv{self.ident}"


@dataclass(frozen=True)
class RecType:
    bound: FinalVar
    body: "ReprTy"

    def __repr__(self) -> str:
        return f"μ{self.bound}.{self.body}"


@dataclass(frozen=True)
class Union:
    lhs: "ReprTy"
    rhs: "ReprTy"

    def __repr__(self) -> str:
        return f"{self.lhs} ⊔ {self.rhs}"


@dataclass(frozen=True)
class Intersection:
    lhs: "ReprTy"
    rhs: "ReprTy"

    def __repr__(self) -> str:
        return f"{self.lhs} ⊓ {self.rhs}"


@dataclass(frozen=True)
class Bottom:
    pass


@dataclass(frozen=True)
class Top:
    pass


ReprTy = Pointer | Record | Atom | FinalVar | Func | Union | Intersection | Bottom | Top


K = TypeVar("K")
V = TypeVar("V")
V2 = TypeVar("V2")


"""
Translates Retypd types into constrained type variables by collecting labels as
type constructors
"""


class Polarity(Enum):
    POSITIVE = 1
    NEGATIVE = 2

    @staticmethod
    def from_bool(b: bool) -> "Polarity":
        return (Polarity.POSITIVE if b else Polarity.NEGATIVE)

    def is_pos(self):
        return self.value == Polarity.POSITIVE


@dataclass(frozen=True)
class PolarVariable:
    var: VariableStorage
    polar: Polarity


class VariableHandler:
    def __init__(self) -> None:
        self.allocated_real_vars = 0

    def fresh_final(self) -> FinalVar:
        res = FinalVar(self.allocated_real_vars)
        self.allocated_real_vars += 1
        return res


class UnificationPass:
    """
    The unifier takes subtyping constraints and produces a unified set of type variables + constraints
    that represent the subtyping relation
    """

    def __init__(self, lat, lat_inverted) -> None:
        super().__init__()
        self.constraints: list[tuple[ReprTy, ReprTy]] = []
        self.base_var_map: dict[TypeVariable, ConsTy] = {}
        self.type_classes = DisjointSet()
        self._lat = lat
        self._lat_inverted = lat_inverted

    def constrain(self, x, y):
        self.constraints.append((x, y))

    def build_base_vars(self) -> dict[TypeVariable, ConsTy]:
        return dict([(k, self.render(v)) for k, v in self.base_var_map.items()])

    def build_constraints(self) -> list[tuple[ReprTy, ReprTy]]:
        return [(self.render(x), self.render(y)) for x, y in self.constraints]

    def render(self, r: ReprTy) -> ConsTy:
        """
        Produces a base var map and constraints in terms of vstore variables. For each type both in constraints
        and base vars, if it's a proper type, build the constructor, if the type is not a proper type, get  a vstore.

        There is a single vstore per.
        """
        rep = self.safe_get(r)
        if isinstance(rep, VariableStorage):
            return rep

        def get_repr_list(mp: HashDict) -> HashDict:
            d = {}
            for k, v in mp.items():
                d[k] = self.render(v)
            return HashDict(d)

        match rep:
            case Atom():
                return r
            case Top():
                return r
            case Bottom():
                return r
            case Func(params=xps, return_val=xrs):
                return Func(get_repr_list(xps), get_repr_list(xrs))
            case Record(fields=xf):
                return Record(get_repr_list(xf))
            # covariant on the load and contravariant on the store
            case Pointer(store_tv=ystv, load_tv=yltv):
                return Pointer(self.render(ystv), self.render(yltv))
        print(rep)
        assert False

    def safe_get(self, ty1: ReprTy):
        self.type_classes.add(ty1)
        return self.type_classes[ty1]

    def unify(self, ty1: ReprTy, ty2: ReprTy, can_swap=True):
        self.type_classes.add(ty1)
        self.type_classes.add(ty2)

        x = self.type_classes[ty1]
        y = self.type_classes[ty2]
        if isinstance(x, VariableStorage):
            self.type_classes.merge(
                y, x, can_swap=isinstance(y, VariableStorage) and can_swap)
            return

        if isinstance(y, VariableStorage):
            self.type_classes.merge(
                x, y, can_swap=isinstance(x, VariableStorage) and can_swap)
            return

        self.type_classes.merge(x, y, can_swap=can_swap)

        def unify_dict_list(xit, yit):
            dlist_new = {}
            for k in itertools.chain(xit.keys(), yit.keys()):
                if k in xit and k in yit:
                    self.unify(xit[k], yit[k])

                if k in xit:
                    dlist_new[k] = xit[k]
                else:
                    dlist_new[k] = yit[k]
            return HashDict(dlist_new)

        match (x, y):
            case (Atom(), Atom()):
                # shouldnt happen but fine
                return
            case (Func(params=xps, return_val=xrs), Func(params=yps, return_val=yrs)):
                ins = unify_dict_list(xps, yps)
                outs = unify_dict_list(xrs, yrs)
                self.type_classes.merge(Func(ins, outs), x, can_swap=False)
            case (Record(fields=xf), Record(fields=yf)):
                nf = unify_dict_list(xf, yf)
                self.type_classes.merge(Record(nf), x, can_swap=False)
            # covariant on the load and contravariant on the store
            case (Pointer(store_tv=xstv, load_tv=xltv), Pointer(store_tv=ystv, load_tv=yltv)):
                self.unify(xstv, ystv)
                self.unify(xltv, yltv)

    def type_of_labels(self, rst: Iterator[BaseLabel]) -> tuple[ConsTy, VariableStorage]:
        elem = next(rst, None)
        if elem:
            (pty, storage) = self.handle_label(elem, rst)
            self.type_classes.add(pty)
            return (pty, storage)
        else:
            nty = self.fresh()
            return (nty, nty)

    def fresh(self) -> VariableStorage:
        vstr = VariableStorage()
        self.type_classes.add(vstr)
        return vstr

    def handle_label(self, label: BaseLabel, rst: Iterator[BaseLabel]) -> tuple[Optional[ConsTy], VariableStorage]:
        (prev_ty, storage) = self.type_of_labels(rst)
        match label:
            case Load():
                store = self.fresh()
                self.constrain(store, prev_ty)
                return (Pointer(store, prev_ty), storage)
            case Store():
                load = self.fresh()
                self.constrain(prev_ty, load)
                return Pointer(prev_ty, load)
            case HasField(bits=sz, offset=off):
                # TODO(Ian): we should allow for refining an atom by a sz or something
                return (Record({off: prev_ty}), storage)
            case FuncIn(loc=loc) | FuncOut(loc=loc):
                nondef = {loc: prev_ty}
                return (Func(nondef if isinstance(
                    label, FuncIn) else {}, nondef if isinstance(label, FuncOut) else {}), storage)
            case _:
                print(label)
                assert False

    def type_of(self, ty: TypeVariable) -> ConsTy:

        if isinstance(ty, Atom):
            return ty

        def get_ty_var(bv: TypeVariable) -> VariableStorage:
            if not (bv in self.base_var_map):
                print("Injecting ", bv)
                self.base_var_map[bv] = self.fresh()
            return self.base_var_map[bv]

        match ty:
            case DerivedTypeVariable(type_var=base_var, labels=label):
                v = get_ty_var(base_var)
                (lb_ty, storage) = self.type_of_labels(iter(label))
                self.unify(lb_ty, v)
                assert storage is not None
                return storage
            case TypeVariable():
                return get_ty_var(ty)
            case TypehoonBot():
                return Bottom()
            case TypehoonTop():
                return Top()
            case TypehoonPointer():
                return Atom(ty, self._lat, self._lat_inverted)
            case TypehoonFloat():
                return Atom(ty, self._lat, self._lat_inverted)
            case TypehoonInt():
                return Atom(ty, self._lat, self._lat_inverted)
            case _:
                print(ty)
                assert False


class ConstraintGenerator(BaseSolver, VariableHandler):
    def __init__(self, ty_cons: Set["TypeConstraint"], bit_size: int) -> None:
        super().__init__(ty_cons, bit_size)
        self.pointer_builder = TypehoonPointer64 if bit_size == 64 else TypehoonPointer32
        self.bit_size = bit_size
        self.base_var_map: dict[TypeVariable, ConsTy] = {}
        self.ordered_vars: list[ConsTy] = []
        self.orig_cons = {}
        self.constrained_closed_list: Set[tuple[ConsTy, ConsTy]] = set()
        self.allocated_real_vars = 0
        # it's safe to keep recursive type variables global. if it was made recursive once it's always recursive
        # the tricky bit is processing has to pick it up immutably
        self.recursive_polar_types: dict[PolarVariable, FinalVar] = dict()
        self.vstor_to_final_var: dict[VariableStorage, FinalVar] = dict()
        self.solved_types = {}
        self.solution = {}
        self.saved_structs: dict[int, TypehoonStruct] = {}
        self.solve_subtyping_constraints(self._constraints)

    def dump_state(self) -> str:
        base = str(self.base_var_map) + "\n"
        # lst = sorted(self.base_var_map.values(), key=lambda x: id(x))
        for v in VariableStorage.all_mems:
            if isinstance(v, VariableStorage):
                base += str(v.id) + " :"
                base += f"{v}: "
                base += f"{{lbs : {v.lower_bounds}, ubs: {v.upper_bounds}}}\n"
        return base

    def clinic_solve(self, constraints: Set["TypeConstraint"]):
        self.orig_cons = constraints
        self.infer_types()

    def find_internal_edges(self, G: nx.MultiDiGraph, scc: set[int]) -> Generator[tuple[int, int, "AlphabetSymbol"], None, None]:
        print(scc)
        for nd in scc:
            for (src, dst, symb) in G.out_edges(nd, data=TypeAutomata.SYMB_NAME):
                if dst in scc:
                    yield (src, dst, symb)

    def select_named_struct_edge(self, G: nx.MultiDiGraph, scc: set[int]) -> Optional[tuple[int, int, "AlphabetSymbol"]]:
        for (src, dst, symb) in self.find_internal_edges(G, scc):
            st: AutState = G.nodes[dst][TypeAutomata.STATE_NAME]
            if RecCons(pset()).ident in st.head_constructors.map_domain and (symb == LoadLabel() or symb == StoreLabel()):
                return (src, dst, symb)
        return None

    def collect_edges_of(self, nd: int,  G: nx.MultiDiGraph, look_for: "AlphabetSymbol", dict_nodes: dict[int, int], pol: bool) -> Optional[TypeConstant]:
        # TODO(Ian): join and meet
        return next(map(lambda d: self.build_angr_type_for_node(d, G, dict_nodes), [dst for (_, dst, symb) in G.out_edges(nd, data=TypeAutomata.SYMB_NAME) if symb == look_for]), None)

    def build_edges(self, nd: int,  G: nx.MultiDiGraph, look_for: list[tuple["AlphabetSymbol", bool]], dict_nodes: dict[int, int]) -> list[TypeConstant]:
        tot = []
        for (x, pol) in [(self.collect_edges_of(nd, G, sym, dict_nodes, pol), pol)
                         for (sym, pol) in look_for]:
            if x is not None:
                tot.append(x)
            else:
                tot.append(TypehoonTop() if pol else TypehoonBot())
        return tot

    def build_record(self, nd: int,  G: nx.MultiDiGraph, cons: "RecCons", dict_nodes, pol: bool) -> TypehoonStruct:
        s = self.get_or_replace_struct(nd)
        es = dict(zip(cons.fields, self.build_edges(nd, G, [(RecordLabel(v), pol)
                                                            for v in cons.fields], dict_nodes)))
        s.fields = es
        return s

    def build_pointer(self, nd: int,  G: nx.MultiDiGraph, dict_nodes, pol: bool) -> TypehoonPointer:
        es = self.build_edges(nd, G, [(LoadLabel(), pol),
                                      (StoreLabel(), not pol)], dict_nodes)
        return self.pointer_builder(es[0])

    def build_function(self, nd: int,  G: nx.MultiDiGraph, func: "FuncCons", dict_nodes, pol: bool) -> TypehoonFunc:
        params = [(Parameter(x), not pol) for x in range(0, max(func.params))]
        rets = [(Return(x), pol) for x in range(0, max(func.rets))]
        ps = self.build_edges(nd, G, params, dict_nodes)
        rs = self.build_edges(nd, G, rets, dict_nodes)

        return TypehoonFunc(ps, rs)

    def get_or_replace_struct(self, nd: int):
        return self.saved_structs.setdefault(nd, TypehoonStruct({}))

    def build_angr_type_for_node(self, nd: int,  G: nx.MultiDiGraph, dict_nodes: dict[int, int]) -> TypeConstant:
        st: AutState = G.nodes[nd][TypeAutomata.STATE_NAME]
        if nd in dict_nodes:
            return self.get_or_replace_struct(dict_nodes[nd])

        if RecCons(pset()).ident in st.head_constructors.map_domain:
            return self.build_record(nd, G, st.head_constructors.map_domain[RecCons(pset()).ident], dict_nodes, st.polarity)

        if PointerCons().ident in st.head_constructors.map_domain:
            return self.build_pointer(nd, G, dict_nodes, st.polarity)

        if FuncCons(dict(), dict()).ident in st.head_constructors.map_domain:
            return self.build_function(nd, G, st.head_constructors.map_domain[FuncCons(dict(), dict()).ident], dict_nodes, st.polarity)

        if AtomicType(Top()).ident in st.head_constructors.map_domain:
            at: AtomicType = st.head_constructors.map_domain[AtomicType(
                Top()).ident]
            match at.atom:
                case Atom(name=nm):
                    return nm
                case Top():
                    return TypehoonTop()
                case Bottom():
                    return TypehoonBot()

        return TypehoonTop() if st.polarity else TypehoonBot()

    def to_angr_type(self, ty: "TypeAutomata") -> TypeConstant:
        # first we break loops
        # iirc doing this optimally is np-hard
        # so for now something sensible... select
        assert ty.entry in ty.G.nodes
        while True:
            comps = list(nx.strongly_connected_components(ty.G))
            cycles = False
            for scc in comps:
                if len(scc) > 1:
                    cycles = True
                    maybe_struct_edge = self.select_named_struct_edge(
                        ty.G, scc)
                    print("Sty edge: ", maybe_struct_edge)
                    maybe_ptr_edge = next(filter(
                        lambda x: x[2] == PointerCons(), self.find_internal_edges(ty.G, scc)), None)
                    backup_edge = maybe_ptr_edge if maybe_ptr_edge is not None else next(
                        self.find_internal_edges(ty.G, scc))
                    if maybe_struct_edge:
                        ty.G.remove_edge(
                            maybe_struct_edge[0], maybe_struct_edge[1])
                        rec = ty.add_named_struct_node(maybe_struct_edge[1])
                        ty.add_edge(
                            maybe_struct_edge[0], rec, maybe_struct_edge[2])
                    else:
                        ty.G.remove_edge(backup_edge[0], backup_edge[1])
                        dst = ty.add_singleton_node(
                            Bottom(), False, AtomicType(Bottom()))
                        ty.add_edge(backup_edge[0], dst, backup_edge[2])
            if not cycles:
                break
        print(ty.entry)
        return self.build_angr_type_for_node(ty.entry, ty.G, ty.named_struct_nodes)

    def determine_type(self, r: ReprTy):
        aut = TypeAutomata()
        aut.build_ty_go(r, False)
        assert aut.entry in aut.G.nodes
        det_aut = aut.detereminise()
        assert det_aut.entry in det_aut.G.nodes
        min_aut = det_aut.minimise()
        assert min_aut.entry in min_aut.G.nodes
        res = self.to_angr_type(min_aut)
        return res

    def build_solution(self):
        tot = dict()
        for k in self.base_var_map:
            ctype = self.coalesce_acc(
                self.base_var_map[k], pmap(), False)
            tot[k] = self.determine_type(ctype)
        return tot

    def solve_subtyping_constraints(self, constraints: Set["TypeConstraint"]):
        self.orig_cons = constraints
        self.infer_types()
        # print(self.dump_state())
        # self.solved_types = self.coalesce_types()
        # self.solution = self.build_solution()

    def infer_types(self):
        uf = UnificationPass(self._base_lattice, self._base_lattice_inverted)
        for (f, cons_set) in self.orig_cons.items():
            for cons in cons_set:
                match cons:
                    case Subtype(sub_type=subty, super_type=sty):
                        uf.constrain(uf.type_of(subty), uf.type_of(sty))
                    case Existence(type_=ty):
                        uf.type_of(ty)
                    case _:
                        assert False

        self.base_var_map = uf.build_base_vars()
        for (eq, to) in self._equivalence.items():
            self.base_var_map[eq] = self.base_var_map[to]

        for (lhs, rhs) in uf.build_constraints():
            self.constrain(lhs, rhs)

    def fresh(self) -> VariableStorage:
        x = VariableStorage(list(), list())
        self.ordered_vars.append(x)
        return x

    # equality

    def constrain_dict_list(self, x: dict, y: dict):
        for k in itertools.chain(x.keys(), y.keys()):
            if k in x and k in y:
                self.constrain(x[k], y[k])

    def constrain(self, lhs: ConsTy, rhs: ConsTy):
        tup = (lhs, rhs)
        if tup in self.constrained_closed_list:
            return

        self.constrained_closed_list.add((lhs, rhs))

        match (lhs, rhs):
            case (Atom(), Atom()):
                # shouldnt happen but fine
                return
            case (Func(params=xps, return_val=xrs), Func(params=yps, return_val=yrs)):
                self.constrain_dict_list(yps, xps)
                self.constrain_dict_list(xrs, yrs)
            case (Record(fields=xf), Record(fields=yf)):
                self.constrain_dict_list(xf, yf)
            # covariant on the load and contravariant on the store
            case (Pointer(store_tv=xstv, load_tv=xltv), Pointer(store_tv=ystv, load_tv=yltv)):
                self.constrain(xltv, yltv)
                self.constrain(ystv, xstv)
            # actual subtyping
#             case (VariableStorage(lower_bounds=lbs, upper_bounds=ubs), VariableStorage(lower_bounds=lb2, upper_bounds=ub2)):
#                 ubs.append(rhs)
#                 for x in lbs:
#                     self.constrain(x, rhs)
# #
#                 lb2.append(lhs)
#                 for x in ub2:
#                     self.constrain(lhs, x)
            case (VariableStorage(lower_bounds=lbs, upper_bounds=ubs), u):
                lhs.add_ub(u)
                for x in lbs:
                    self.constrain(x, u)
            case (l, VariableStorage(lower_bounds=lbs, upper_bounds=ubs)):
                rhs.add_lb(l)
                for x in ubs:
                    self.constrain(l, x)

    @staticmethod
    def map_value(f: Callable[[V], V2], d: dict[K, V]) -> dict[K, V2]:
        return dict(map(lambda kv: (kv[0], f(kv[1])), d.items()))

    def get_or_insert(k: K, f: Callable[[], V], d: dict[K, V]) -> V:
        if k in d:
            return d[k]
        else:
            d[k] = f()
            return d[k]

    def final_var_for_variable(self, vstor: VariableStorage) -> FinalVar:
        return ConstraintGenerator.get_or_insert(vstor, lambda: self.fresh_final(), self.vstor_to_final_var)

    def coalesce_acc(self, ty: ConsTy, processing: PMap[(ConsTy, Polarity), Callable[[], FinalVar]],  is_pos: bool) -> ReprTy:

        if ty in processing:
            return processing[ty]()

        is_recursive = False
        vcache = None

        def variable_for_type():
            nonlocal is_recursive
            nonlocal vcache

            if vcache is not None:
                return vcache
            is_recursive = True
            if isinstance(ty, VariableStorage):
                vcache = self.final_var_for_variable(ty)
            else:
                vcache = self.fresh_final()
            return vcache

        next_processing = processing.set(ty, variable_for_type)

        rec_pos = partial(self.coalesce_acc,
                          processing=next_processing, is_pos=is_pos)
        rec_neg = partial(self.coalesce_acc,
                          processing=next_processing, is_pos=(not is_pos))

        def go():
            match ty:
                case Top():
                    return ty
                case Bottom():
                    return ty
                case Atom():
                    return ty
                case Func(params=prs, return_val=rets):
                    return Func(ConstraintGenerator.map_value(rec_neg, prs), ConstraintGenerator.map_value(rec_pos, rets))
                case Record(fields=fs):
                    return Record(ConstraintGenerator.map_value(rec_pos, fs))
                case Pointer(store_tv=stv, load_tv=lv):
                    return Pointer(rec_neg(stv), rec_pos(lv))
                case VariableStorage(lower_bounds=lbs, upper_bounds=ubs):
                    vs = self.final_var_for_variable(ty)
                    curr_bounds = map(partial(
                        self.coalesce_acc, processing=next_processing, is_pos=is_pos), (lbs if is_pos else ubs))
                    mrg = Union if is_pos else Intersection
                    res_ty = reduce(mrg, curr_bounds, vs)
                    return res_ty
            assert False
        res_ty = go()
        if is_recursive:
            return RecType(variable_for_type(), res_ty)
        else:
            return res_ty

    def coalesce(self, ty: ConsTy) -> ReprTy:
        return self.coalesce_acc(ty, pmap(), True)

    def coalesce_types(self) -> dict[TypeVariable, ReprTy]:
        tot = dict()
        for k in self.orig_cons.keys():
            if isinstance(k, TypeVariable):
                if k in self.base_var_map:
                    tot[k] = self.coalesce(self.base_var_map[k])
        return tot


@dataclass(frozen=True)
class ConstructorID:
    ind: int


class Constructor(ABC):
    @property
    @abstractmethod
    def ident(self) -> ConstructorID:
        pass

    @abstractmethod
    def join(self, o: "Constructor") -> "Constructor":
        pass

    @abstractmethod
    def meet(self, o: "Constructor") -> "Constructor":
        pass

    @abstractmethod
    def geq(self, o: "Constructor") -> "Constructor":
        pass


@dataclass(frozen=True)
class FVCons(Constructor):
    representing: PSet[FinalVar]

    @property
    def ident(self) -> ConstructorID:
        return 1

    def join(self, o: "FVCons") -> "FVCons":
        return FVCons(self.representing.intersection(o.representing))

    def meet(self, o: "FVCons") -> "FVCons":
        return FVCons(self.representing.union(o.representing))

    def geq(self, o: "FVCons") -> bool:
        return self.representing.issubset(o.representing)


@dataclass(frozen=True)
class RecCons(Constructor):
    fields: PSet[int]

    @property
    def ident(self) -> ConstructorID:
        return 2

    def join(self, o: "RecCons") -> "RecCons":
        # contra on params
        return RecCons(self.fields.intersection(o.fields))

    def meet(self, o: "RecCons") -> "RecCons":
        return RecCons(self.fields.union(o.fields))

    def geq(self, o: "FVCons") -> bool:
        return self.fields.issubset(o)


@dataclass(frozen=True)
class PointerCons(Constructor):
    @property
    def ident(self) -> ConstructorID:
        return 3

    def join(self, o: "PointerCons") -> "PointerCons":
        return self

    def meet(self, o: "PointerCons") -> "PointerCons":
        return self

    def geq(self, o: "PointerCons") -> bool:
        return True


@dataclass(frozen=True)
class AtomicType(Constructor):
    atom: Atom | Top | Bottom

    @property
    def ident(self) -> ConstructorID:
        return 4

    def _join(self, o: "AtomicType") -> "AtomicType":
        match (self.atom, o.atom):
            case (Top(), _) | (_, Top()):
                return Top()
            case (x, Bottom()):
                return x
            case (Bottom(), x):
                return x
            case (Atom(), Atom()):
                return self.atom.join(o.atom)

    def join(self, o: "AtomicType") -> "AtomicType":
        return AtomicType(self._join(o))

    def meet(self, o: "AtomicType") -> "AtomicType":
        return AtomicType(self._meet(o))

    def _meet(self, o: "AtomicType") -> "AtomicType":
        match (self.atom, o.atom):
            case (Bottom(), _) | (_, Bottom()):
                return Bottom()
            case (x, Top()):
                return x
            case (Top(), x):
                return x
            case (Atom(), Atom()):
                return self.atom.meet(o.atom)

    def geq(self, o: "AtomicType") -> bool:
        match (self.atom, o.atom):
            case (Top(), _) | (_, Bottom()):
                return True
            case (Bottom(), _) | (_, Top()):
                return False
            case (Atom(), Atom()):
                return self.atom.meet(o.atom)


@dataclass(frozen=True)
class FuncCons(Constructor):
    params: PSet[int]
    rets: PSet[int]

    @property
    def ident(self) -> ConstructorID:
        return 5

    def join(self, o: "FuncCons") -> "FuncCons":
        # contra on params
        return Func(self.params.union(o.params), self.rets.intersection(o.rets))

    def meet(self, o: "FuncCons") -> "FuncCons":
        return FVCons(self.params.intersection(o.params), self.rets.union(o.rets))

    def geq(self, o: "FuncCons") -> bool:
        self.params.issubset(o.params) and self.rets.issubset(o.rets)


@dataclass(frozen=True)
class TypeLattice:
    map_domain: PMap[ConstructorID, Constructor]

    # ub of type
    def join(self, x: "TypeLattice"):
        ks = set(x.map_domain.keys()).intersection(self.map_domain.keys())
        return TypeLattice(pmap([(k, self.map_domain[k].join(x.map_domain[k])) for k in ks]))

    def meet(self, x: "TypeLattice"):
        ks = set(x.map_domain.keys()).union(self.map_domain.keys())
        print(ks)

        def maybe_meet(x: Optional[Constructor], y: Optional[Constructor]) -> Constructor:
            if x is not None and y is not None:
                return x.meet(y)
            elif x:
                return x
            else:
                return y

        return TypeLattice(pmap([(k, maybe_meet(self.map_domain.get(k), x.map_domain.get(k))) for k in ks]))

    def geq(self, o: "TypeLattice") -> bool:
        return all([k in o.map_domain and self.map_domain[k].geq(o.map_domain[k]) for k in self.map_domain])

# We need automata with a lot of extra bookkeeping so we just implement everything custom...


# Edges


class AlphabetSymbol(ABC):
    pass


@dataclass(frozen=True)
class Epsilon(AlphabetSymbol):
    pass


@dataclass(frozen=True)
class RecordLabel(AlphabetSymbol):
    label: int


@dataclass(frozen=True)
class LoadLabel:
    pass


@dataclass(frozen=True)
class StoreLabel:
    pass


@dataclass(frozen=True)
class Parameter(AlphabetSymbol):
    ind: int


@dataclass(frozen=True)
class Return(AlphabetSymbol):
    ind: int


@dataclass(frozen=True)
class AutState:
    polarity: bool
    head_constructors: TypeLattice

    def dfa_equiv(self, o: "AutState") -> bool:
        return self.polarity == o.polarity and self.head_constructors.geq(o) and o.head_constructors.geq(self)


T = TypeVar("T")


class TypeAutomata:
    SYMB_NAME = "label"
    STATE_NAME = "state"

    # adjacency list
    G: nx.MultiDiGraph
    epsilon_subgraph: nx.MultiDiGraph
    type_repr_nodes: dict[ReprTy, int]
    rec_var_nodes: dict[FinalVar, int]
    next_id: int
    entry: Optional[int]
    subnode_map: dict[int, PSet[int]]
    named_struct_nodes: dict[int, int]

    def __init__(self) -> None:
        self.next_id = 0
        self.G = nx.MultiDiGraph()
        self.type_repr_nodes = dict()
        self.rec_var_nodes = dict()
        self.entry = None
        self.subnode_map = dict()
        self.epsilon_subgraph = None
        self.named_struct_nodes = {}

    def singleton(self, pol: bool, cons: Constructor) -> AutState:
        return AutState(pol, TypeLattice(pmap([(cons.ident, cons)])))

    def add_named_struct_node(self, target: int) -> int:
        ndid = self.fresh_node_id()
        self.named_struct_nodes[ndid] = target
        self.G.add_node(ndid, **{TypeAutomata.STATE_NAME: None})
        return ndid

    def fresh_node_id(self) -> int:
        res = self.next_id
        self.next_id += 1
        return res

    def add_subnode(self, parents: PSet[int], st: AutState):
        res_id = self.fresh_node_id()
        self.G.add_node(res_id, **{TypeAutomata.STATE_NAME: st})
        self.subnode_map[res_id] = parents
        return res_id

    def add_node(self, r: ReprTy, st: AutState) -> int:
        res_id = self.fresh_node_id()
        self.G.add_node(res_id,  **{TypeAutomata.STATE_NAME: st})
        self.type_repr_nodes[r] = res_id
        return res_id

    def add_singleton_node(self, r: ReprTy, pol: bool, cons: Constructor) -> int:
        return self.add_node(r, self.singleton(pol, cons))

    def add_edge(self, x: int, y: int, symb: AlphabetSymbol):
        self.G.add_edge(x, y, **{TypeAutomata.SYMB_NAME: symb})

    def build_ty_go(self, r: ReprTy, pol: bool) -> int:
        self.entry = self.build(r, pol)
        return self.entry

    def build(self, r: ReprTy, polarity: bool) -> int:
        def add_dict(d: PMap[T, ReprTy], new_pol: bool, ebuilder: Callable[[T], AlphabetSymbol], parent_node: int):
            for (k, v) in d.items():
                res_nd = self.build(v, new_pol)
                lbl = ebuilder(k)
                self.add_edge(parent_node, res_nd, lbl)

        match r:
            case Top() | Bottom() | Atom():
                return self.add_singleton_node(r, polarity, AtomicType(r))
            case RecType(bound=bnd, body=bdy):
                # hacky way to setup a rec node, add an empty node to capture recursive edges
                self.G.add_node(self.next_id)
                fake_node = self.next_id
                self.next_id += 1
                self.rec_var_nodes[bnd] = fake_node
                bdy_node = self.build(bdy, polarity)

                for (src, _, lbl) in self.G.in_edges(fake_node, data=TypeAutomata.SYMB_NAME):
                    self.add_edge(src, bdy_node, lbl)
                self.G.remove_node(fake_node)
                return bdy_node
            case Pointer(store_tv=stv, load_tv=ltv):
                ptr_nd = self.add_singleton_node(r, polarity, PointerCons())
                stv_nd = self.build(stv, not polarity)
                ltv_nd = self.build(ltv, polarity)
                self.add_edge(ptr_nd, stv_nd, StoreLabel())
                self.add_edge(ptr_nd, ltv_nd, LoadLabel())
                return ptr_nd
            case Union(lhs=l, rhs=rh) | Intersection(lhs=l, rhs=rh):
                lnd = self.build(l, polarity)
                rnd = self.build(rh, polarity)
                pnode = self.add_node(r, AutState(
                    polarity, TypeLattice(pmap())))
                self.add_edge(pnode, lnd, Epsilon())
                self.add_edge(pnode, rnd, Epsilon())
                return pnode
            case Func(params=prs, return_val=rets):
                par = self.add_singleton_node(r, polarity, FuncCons(
                    pset(prs.keys(), pset(rets.keys()))))
                add_dict(prs, not polarity, Parameter, par)
                add_dict(rets, polarity, Return, par)
                return par
            case Record(fields=fs):
                par = self.add_singleton_node(r, polarity, RecCons(
                    pset(fs.keys())))
                print(fs)
                add_dict(fs, polarity, RecordLabel, par)
                return par
            case FinalVar():
                if r in self.rec_var_nodes:
                    return self.rec_var_nodes[r]
                else:
                    return self.add_singleton_node(r, polarity, FVCons(pset([r])))
            case _:
                print(type(r))
                assert False

        assert False

    def reachable_by_epsilon(self, x: int) -> PSet[int]:
        if not self.epsilon_subgraph:
            self.epsilon_subgraph = self.G.edge_subgraph(
                [e for e in self.G.edges if self.G.edges[e][TypeAutomata.SYMB_NAME] == Epsilon()])
            assert Epsilon() == Epsilon()
            print("Epsilon edges", self.epsilon_subgraph.edges())
        if not (x in self.epsilon_subgraph.nodes):
            return pset([x])
        return pset(nx.dfs_preorder_nodes(self.epsilon_subgraph, source=x)).add(x)

    # collect transitions, closed under epsilon
    def collect_transition_table(self, x: PSet[int]) -> dict[AlphabetSymbol, PSet[int]]:
        ttable = dict()

        for (_, dst, symb) in self.G.out_edges(nbunch=x, data=TypeAutomata.SYMB_NAME):
            if symb != Epsilon():
                curr_set = ttable.get(symb, pset())
                ttable[symb] = curr_set.union(self.reachable_by_epsilon(dst))

        return ttable

    def merge_nodes(self, nds: PSet[int]) -> AutState:
        pol = None
        curr_state = None
        for nd in nds:
            st: AutState = self.G.nodes[nd][TypeAutomata.STATE_NAME]
            if pol is None:
                pol = st.polarity
                curr_state = st
            else:
                assert pol == st.polarity
                ncons = curr_state.head_constructors.join(
                    st.head_constructors) if pol else curr_state.head_constructors.meet(st.head_constructors)
                curr_state = AutState(pol, ncons)
        return curr_state

    def detereminise(self):
        handled_nds: dict[PSet[int], int] = dict()
        new_aut = TypeAutomata()
        # closed_list: set[PSet[int]] = set()
        q: deque[PSet[int]] = deque()

        ent_nodes = self.reachable_by_epsilon(self.entry)
        q.append(ent_nodes)
        print("Ent nodes: ", ent_nodes)
        new_aut.entry = new_aut.add_subnode(
            ent_nodes, self.merge_nodes(ent_nodes))
        handled_nds[ent_nodes] = new_aut.entry

        # algo: initialize a queue to the entry nodes (all nodes reachable from entry by epsilon).
        # at each step take off a node, and follow that node through epsilon edges determining a new transition table for each alphabet symbol
        # for each alphabet symbol S collect all reachable nodes E and add a node {E}. Add an edge from curr node to {E} with weight S. Add {E} to the queue provided we have not visited {E}.
        while len(q) > 0:
            curr = q.popleft()

            target_node = handled_nds[curr]

            for (symb, tset) in self.collect_transition_table(curr).items():
                dst_node = None
                if tset not in handled_nds:
                    dst_node = new_aut.add_subnode(
                        tset, self.merge_nodes(tset))
                    handled_nds[tset] = dst_node
                    q.append(tset)
                else:
                    dst_node = handled_nds[tset]

                new_aut.add_edge(target_node, dst_node, symb)

        return new_aut

    def initial_partitions(self) -> list[set[int]]:
        # TODO(Ian): double check that default eq/hash works
        tot: dict[AutState, set[int]] = dict()
        for (lbl, st) in self.G.nodes.data(TypeAutomata.STATE_NAME):
            tot.setdefault(st, set()).add(lbl)

        return list(map(lambda x: x[1], tot.items()))

    def repartition(self, parts: list[set[int]]) -> list[set[int]]:
        # 1. collect node -> orig_index map
        # 2. for each partition collect a map nd -> (A, index) and add to partitions
        # 3. push partitions to list

        orig_part: dict[int, int] = dict()
        for (idx, part) in enumerate(parts):
            for nod in part:
                orig_part[nod] = idx

        tot = list()
        for part in parts:
            part_trans_to_nodes: dict[frozenset[tuple[AlphabetSymbol, int]], set[int]] = dict(
            )
            for nd in part:
                part_trans_to_nodes.setdefault(frozenset([(A, orig_part[dst])
                                                          for (_, dst, A) in self.G.edges(nd, data=TypeAutomata.SYMB_NAME)]), set()).add(nd)

            for _, np in part_trans_to_nodes.items():
                tot.append(np)

        return tot

    def write(self, pth):
        writeable_G = nx.MultiDiGraph()
        for nd in self.G.nodes:
            writeable_G.add_node(nd, label=str(
                self.G.nodes[nd][TypeAutomata.STATE_NAME]).replace(":", "_"))

        for (src, dst, symb) in self.G.edges(data=TypeAutomata.SYMB_NAME):
            writeable_G.add_edge(src, dst, label=str(symb))

        nx.drawing.nx_pydot.write_dot(writeable_G, pth)

    def minimise(self):
        # so ok the idea here is we have two types of states:
        # those that have constructors and those that dont.
        # those that have constructors are essentially accepting states (they form a type).
        # So ok when are two automata states "indistinguishable"... when forall words of capabilities they lead to the same polar constructor
        # So in theory our first paritions are [unlabeled states of polarity x, unlabeled states of polarity y, labeled with each cons polarity x, labeled with each cons polarity y]
        # so we need the following predicate: AutStatex == AutStatey iff consx == consy && polx == poly

        parts = self.initial_partitions()
        while True:
            np = self.repartition(parts)
            if len(np) == len(parts):
                break
            parts = np
        new_aut = TypeAutomata()

        new_nd_lookup: dict[int, int] = dict()
        for pt in parts:
            nd_pars = pset(pt)
            part_node = new_aut.add_subnode(nd_pars, self.merge_nodes(nd_pars))
            for nd in pt:
                new_nd_lookup[nd] = part_node

        new_aut.entry = new_nd_lookup[self.entry]

        edge_set: set[tuple[int, int, AlphabetSymbol]] = set()
        for (src, dst, symb) in self.G.edges.data(TypeAutomata.SYMB_NAME):
            print(symb)
            edge_set.add((new_nd_lookup[src], new_nd_lookup[dst], symb))

        for (src, dst, symb) in edge_set:
            assert src in new_aut.G.nodes
            assert dst in new_aut.G.nodes
            print("adding edge ", symb)
            new_aut.add_edge(src, dst, symb)

        return new_aut

    def decompile(self):
        pass
