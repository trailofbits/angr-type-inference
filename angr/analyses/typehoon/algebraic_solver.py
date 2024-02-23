

from dataclasses import dataclass
from typing import Set, Iterator
from .typevars import Existence, Subtype, TypeVariable, DerivedTypeVariable, TypeConstraint
from .simple_solver import BaseSolver
from enum import Enum
from functools import partial, reduce
import copy
import itertools
from pyrsistent import m, pmap, PMap
from collections import defaultdict

# Import labels
from .typevars import FuncIn, FuncOut, Load, Store, ConvertTo, HasField, BaseLabel
from typing import TypeVar, Callable, Optional

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
        print(can_swap)
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


@dataclass(frozen=True)
class Atom:
    name: str


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
    fields: dict[int, "ConsTy"]

    def __init__(self, d) -> None:
        self.fields = HashDict(d)
        assert len(self.fields) > 0

    def __repr__(self) -> str:
        return f"rec({string_of_d_as_args(self.fields)})"


@dataclass(frozen=False, init=False, unsafe_hash=True, eq=True)
class Func:
    params: dict[int, "ConsTy"]
    return_val: dict[int, "ConsTy"]

    def __init__(self, p, r) -> None:
        self.params = HashDict(p)
        self.return_val = HashDict(r)

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

    def __init__(self) -> None:
        super().__init__()
        self.constraints: list[tuple[ReprTy, ReprTy]] = []
        self.base_var_map: dict[TypeVariable, ConsTy] = {}
        self.type_classes = DisjointSet()

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
        rep = self.type_classes[r]
        if isinstance(rep, VariableStorage):
            return rep

        def get_repr_list(mp: HashDict) -> HashDict:
            d = {}
            for k, v in mp.items():
                d[k] = self.render(v)
            return HashDict(d)

        match rep:
            case Atom():
                # shouldnt happen but fine
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

    def unify(self, ty1: ReprTy, ty2: ReprTy, can_swap=True):
        print(f"Unify {ty1} {ty2}")
        self.type_classes.add(ty1)
        self.type_classes.add(ty2)

        x = self.type_classes[ty1]
        y = self.type_classes[ty2]
        print(x)
        print(y)
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
                if k in x and k in y:
                    self.unify(x[k], y[k])

                if k in x:
                    dlist_new[k] = x[k]
                else:
                    dlist_new[k] = y[k]
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
                self.base_var_map[bv] = self.fresh()
            return self.base_var_map[bv]

        match ty:
            case DerivedTypeVariable(type_var=base_var, labels=label):
                v = get_ty_var(base_var)
                (lb_ty, storage) = self.type_of_labels(iter(label))
                self.unify(lb_ty, v)
                print(f"Curr value: {self.type_classes[get_ty_var(base_var)]}")
                assert storage is not None
                return storage
            case TypeVariable():
                return get_ty_var(ty)
            case _:
                assert False


class ConstraintGenerator(BaseSolver, VariableHandler):
    def __init__(self, ty_cons: Set["TypeConstraint"]) -> None:
        super().__init__(ty_cons)
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

    def solve_subtyping_constraints(self, constraints: Set["TypeConstraint"]):
        print(constraints)
        self.orig_cons = constraints
        self.infer_types()
        print(self.dump_state())
        self.solved_types = self.coalesce_types()

    def infer_types(self):
        uf = UnificationPass()
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
        print(self.base_var_map)
        for (lhs, rhs) in uf.build_constraints():
            print(f"{lhs} <= {rhs}")
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
        print(tup)
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

            if vcache:
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
                case Atom(name=aty):
                    return Atom(aty)
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
                print(f"Coalescing: {k}")
                tot[k] = self.coalesce(self.base_var_map[k])
        return tot


class Optimizer:
    """
    The optimizer performance an occurence analysis on type variables recording, their appearance, removing redundant type variables

    The first pass determines co-occurences where a variable is always present with another variable 
    """

    def __init__(self) -> None:
        self.occ_map = defaultdict(lambda: set())
        self.polarities = defaultdict(lambda: set())
        self.uf = DisjointSet()
        self.all_tv = set()
        self.rec_vars = set()
        self.removable_vars = set()

    def optimize_ty(self, r: ReprTy):
        self.walk_type(r, True)
        self.collect_indistinguishable()
        return self.rewrite_type(r, True)

    def safe_merge(self, v1, v2):
        self.uf.add(v1)
        self.uf.add(v2)
        self.uf.merge(v1, v2)

    def safe_find(self, v1):
        self.uf.add(v1)
        return self.uf[v1]

    def collect_indistinguishable(self):
        for ((tv, _), values) in self.occ_map.items():
            # first we unify a variable with all its co-accuring variables:
            # we cannot unify recursive variables since a rec var must always be the repr of its set
            # so we always check
            for v in values:
                base_var = self.safe_find(tv)
                if isinstance(v, FinalVar):
                    nv = self.safe_find(v)
                    if not (base_var in self.rec_vars and nv in self.rec_vars):
                        if base_var in self.rec_vars:
                            self.uf.merge(base_var, nv, can_swap=False)
                        elif nv in self.rec_vars:
                            self.uf.merge(nv, base_var, can_swap=False)
                        else:
                            self.uf.merge(base_var, nv, can_swap=True)

        for ((tv, pol), values) in self.occ_map.items():
            if len(self.polarities[tv]) < 2:
                self.removable_vars.add(tv)
            for v in values:
                if not isinstance(v, FinalVar) and v in self.occ_map[(tv, not pol)]:
                    self.removable_vars.add(tv)

    def collect_leaves_acc(self, r: ReprTy, cls, acc: list):
        if not isinstance(r, cls):
            acc.append(r)
            return
        else:
            self.collect_leaves_acc(r.lhs, cls, acc)
            self.collect_leaves_acc(r.rhs, cls, acc)

    def collect_leaves(self, r: ReprTy, cls) -> list:
        lst = []
        self.collect_leaves_acc(r, cls, lst)
        return lst

    def collect_union_intersection_group(self,  r: ReprTy, cls, polar: bool):
        tot = self.collect_leaves(r, cls)
        for v in tot:
            if isinstance(v, FinalVar):
                s = self.occ_map[(v, polar)]
                s.intersection(tot)
        for v in tot:
            self.walk_type(v, polar)

    def rewrite_type(self, r: ReprTy, polar: bool) -> ReprTy:
        rewrite_neg = partial(self.rewrite_type, polar=not polar)
        rewrite_pos = partial(self.rewrite_type, polar=polar)

        def rewrite_group(cls, default):
            all_rewritten = [rewrite_pos(
                x) for x in self.collect_leaves(r, cls)]
            s = set([x for x in all_rewritten if x != default])
            if len(s) <= 0:
                s.add(default)
            return reduce(cls, s)

        match r:
            case RecType(bound=bnd, body=bdy):
                return RecType(bnd, rewrite_pos(bdy))
            case Pointer(store_tv=stv, load_tv=ltv):
                return Pointer(rewrite_neg(stv), rewrite_pos(ltv))
            case Union():
                return rewrite_group(Union, Bottom())
            case Intersection():
                return rewrite_group(Intersection, Top())
            case Func(params=prs, return_val=rets):
                return Func(ConstraintGenerator.map_value(rewrite_neg, prs),
                            ConstraintGenerator.map_value(rewrite_pos, rets))
            case Record(fields=fs):
                return Record(ConstraintGenerator.map_value(rewrite_pos, fs))
            case FinalVar():
                if r in self.removable_vars and r not in self.rec_vars:
                    if polar:
                        # bottom is irrelevant to a positive position
                        return Bottom()
                    else:
                        # top is irrelevant to a negative position
                        return Top()
                else:
                    return self.safe_find(r)
        print(type(r))
        assert False

    def walk_type(self, r: ReprTy, polar: bool):

        walk_neg = partial(self.walk_type, polar=not polar)
        walk_pos = partial(self.walk_type, polar=polar)

        def collect_dict(d: dict, w):
            for (_, v) in d.items():
                w(v)

        match r:
            case RecType(bound=bnd, body=bdy):
                self.rec_vars.add(bnd)
                self.walk_type(bdy, polar)
            case Pointer(store_tv=stv, load_tv=ltv):
                self.walk_type(stv, not polar)
                self.walk_type(ltv, polar)
            case Union():
                self.collect_union_intersection_group(r, Union, polar)
            case Intersection():
                self.collect_union_intersection_group(r, Intersection, polar)
            case Func(params=prs, return_val=rets):
                collect_dict(prs, walk_neg)
                collect_dict(rets, walk_pos)
            case Record(fields=fs):
                collect_dict(fs, walk_pos)
            case FinalVar():
                self.polarities[r].add(polar)
                self.all_tv.add(r)
            case _:
                print(type(r))
                assert False


class Rewriter:
    def __init__(self) -> None:
        pass
