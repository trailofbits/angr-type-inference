

from dataclasses import dataclass
from typing import Set, Iterator
from .typevars import Existence, Subtype, TypeVariable, DerivedTypeVariable, TypeConstraint
from .simple_solver import BaseSolver
from enum import Enum
from functools import partial, reduce
import copy

import itertools

# Import labels
from .typevars import FuncIn, FuncOut, Load, Store, ConvertTo, HasField, BaseLabel
from typing import TypeVar, Callable, Optional

# A type variable is a unique holder of constraints


# we give vstorage identity based
@dataclass(eq=False, init=False)
class VariableStorage:
    lower_bounds: list["ConsTy"]
    upper_bounds: list["ConsTy"]
    id: int

    tot_ids = 0

    def __init__(self, lbs, ubs) -> None:
        self.lower_bounds = lbs
        self.upper_bounds = ubs
        self.id = VariableStorage.tot_ids
        VariableStorage.tot_ids += 1

    def __repr__(self) -> str:
        return f"vstr{self.id}"


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


ReprTy = Pointer | Record | Atom | FinalVar | Func | Union | Intersection


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


class ConstraintGenerator(BaseSolver):
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
        for v in self.ordered_vars:
            if isinstance(v, VariableStorage):
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
        for (f, cons_set) in self.orig_cons.items():
            for cons in cons_set:
                match cons:
                    case Subtype(sub_type=subty, super_type=sty):
                        lhs = self.type_of(subty)
                        rhs = self.type_of(sty)
                        self.base_var_map[subty] = lhs
                        self.base_var_map[sty] = rhs
                        self.constrain(lhs, rhs)
                    case Existence(type_=ty):
                        self.base_var_map[ty] = self.type_of(ty)
                    case _:
                        assert False

    def fresh_final(self) -> FinalVar:
        res = FinalVar(self.allocated_real_vars)
        self.allocated_real_vars += 1
        return res

    def fresh(self) -> VariableStorage:
        x = VariableStorage(list(), list())
        self.ordered_vars.append(x)
        return x

    # equality

    def unify(self, ty: VariableStorage, oty: ConsTy):
        self.constrain(ty, oty)
        self.constrain(oty, ty)

    def type_of_labels(self, rst: Iterator[BaseLabel]) -> tuple[ConsTy, VariableStorage]:
        elem = next(rst, None)
        if elem:
            return self.handle_label(elem, rst)
        else:
            nty = self.fresh()
            return (nty, nty)

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
                self.unify(v, lb_ty)
                return storage
            case TypeVariable():
                return get_ty_var(ty)
            case _:
                assert False

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
                ubs.append(u)
                for x in lbs:
                    self.constrain(x, u)
            case (l, VariableStorage(lower_bounds=lbs, upper_bounds=ubs)):
                lbs.append(l)
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

    def coalesce_acc(self, ty: ConsTy, processing: frozenset[PolarVariable],  is_pos: bool) -> ReprTy:
        print(ty)
        print(processing)
        print(is_pos)
        print("----")
        rec_pos = partial(self.coalesce_acc,
                          processing=processing, is_pos=is_pos)
        rec_neg = partial(self.coalesce_acc,
                          processing=processing, is_pos=(not is_pos))
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
                polar_v = PolarVariable(ty, Polarity.from_bool(is_pos))
                if polar_v in processing:
                    print("Curr processing")
                    return ConstraintGenerator.get_or_insert(polar_v, lambda: self.fresh_final(), self.recursive_polar_types)
                else:
                    vs = self.final_var_for_variable(ty)
                    curr_bounds = map(partial(
                        self.coalesce_acc, processing=processing.union([polar_v]), is_pos=is_pos), (lbs if is_pos else ubs))
                    mrg = Union if is_pos else Intersection
                    res_ty = reduce(mrg, curr_bounds, vs)
                    if polar_v in self.recursive_polar_types:
                        return RecType(self.recursive_polar_types[polar_v], res_ty)
                    else:
                        return res_ty
        print(ty)
        print(type(ty))
        assert False

    def coalesce(self, ty: ConsTy) -> ReprTy:
        return self.coalesce_acc(ty, frozenset(), True)

    def coalesce_types(self) -> dict[TypeVariable, ReprTy]:
        tot = dict()
        for k in self.orig_cons.keys():
            if isinstance(k, TypeVariable):
                print(f"Coalescing: {k}")
                tot[k] = self.coalesce(self.base_var_map[k])
        return tot


class Compactor:
    def __init__(self) -> None:
        pass


class Rewriter:
    def __init__(self) -> None:
        pass
