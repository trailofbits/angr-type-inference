

from dataclasses import dataclass
from typing import Set
from .typevars import Existence, Subtype, TypeVariable, DerivedTypeVariable, TypeConstraint
from .simple_solver import BaseSolver
from enum import Enum
from functools import partial, reduce
import copy

import itertools

# Import labels
from .typevars import FuncIn, FuncOut, Load, Store, ConvertTo, HasField
from typing import TypeVar, Callable

# A type variable is a unique holder of constraints


# we give vstorage identity based
@dataclass(eq=False)
class VariableStorage:
    lower_bounds: list["ConsTy"]
    upper_bounds: list["ConsTy"]


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

    def items(self):
        return self.d.items()


@dataclass(frozen=False, init=False, unsafe_hash=True, eq=True)
class Record:
    fields: dict[int, "ConsTy"]

    def __init__(self, d) -> None:
        self.fields = HashDict(d)
        assert len(self.fields) > 0


@dataclass(frozen=False, init=False, unsafe_hash=True, eq=True)
class Func:
    params: dict[int, "ConsTy"]
    return_val: dict[int, "ConsTy"]

    def __init__(self, p, r) -> None:
        self.params = HashDict(p)
        self.return_val = HashDict(r)


ConsTy = VariableStorage | Pointer | Record | Atom | Func


@dataclass(frozen=True)
class FinalVar:
    ident: int


@dataclass(frozen=True)
class RecType:
    bound: FinalVar
    body: "ReprTy"


@dataclass(frozen=True)
class Union:
    lhs: "ReprTy"
    rhs: "ReprTy"


@dataclass(frozen=True)
class Intersection:
    lhs: "ReprTy"
    rhs: "ReprTy"


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
        self.orig_cons = {}
        self.constrained_closed_list: Set[tuple[ConsTy, ConsTy]] = set()
        self.allocated_real_vars = 0
        # it's safe to keep recursive type variables global. if it was made recursive once it's always recursive
        # the tricky bit is processing has to pick it up immutably
        self.recursive_polar_types: dict[PolarVariable, FinalVar] = dict()
        self.vstor_to_final_var: dict[VariableStorage, FinalVar] = dict()
        self.solved_types = {}

        self.solve()

    def solve_subtyping_constraints(self, constraints: Set["TypeConstraint"]):
        self.orig_cons = constraints
        self.infer_types()
        self.solved_types = self.coalesce_types()

    def infer_types(self):
        for cons in self.orig_cons:
            match cons:
                case Subtype(super_type=sty, subty=subty):
                    lhs = self.type_of(subty)
                    rhs = self.type_of(sty)
                    self.base_var_map[subty] = lhs
                    self.base_var_map[sty] = rhs
                    self.constrain(lhs, rhs)
                case Existence(type_=ty):
                    self.base_var_map[ty] = self.type_of(ty)

    def fresh_final(self) -> FinalVar:
        res = FinalVar(self.allocated_real_vars)
        self.allocated_real_vars += 1
        return res

    def fresh(self) -> VariableStorage:
        return VariableStorage(list(), list())

    def type_of(self, ty: TypeVariable, child_type=None) -> ConsTy:
        if ty in self.base_var_map:
            return self.base_var_map[ty]

        prev_ty = child_type if child_type else self.fresh()
        ty_repr = None
        match ty:
            case DerivedTypeVariable(type_var=base_var, label=label):
                ty_repr = prev_ty
                match label:
                    case Load():
                        ld = ty_repr
                        store = self.fresh()
                        self.constrain(store, ld)
                        self.type_of(base_var, child_type=Pointer(store, ld))
                    case Store():
                        store = prev_ty
                        load = self.fresh()
                        self.constrain(store, load)
                        self.type_of(base_var, child_type=Pointer(store, ld))
                    case HasField(bits=sz, offset=off):
                        # TODO(Ian): we should allow for refining an atom by a sz or something
                        self.type_of(
                            base_var, child_type=Record({off: prev_ty}))
                    case FuncIn(loc=loc) | FuncOut(loc=loc):
                        nondef = {loc: prev_ty}
                        self.type_of(base_var, Func(nondef if isinstance(
                            label, FuncIn) else {}, nondef if isinstance(label, FuncOut) else {}))
                    case _:
                        self.type_of(base_var, child_type=self.fresh())

            case TypeVariable():
                ty_repr = prev_ty

        self.base_var_map[ty] = ty_repr
        return ty_repr

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
            case (Func(params=xps, return_vals=xrs), Func(params=yps, return_vals=yrs)):
                self.constrain_dict_list(yps, xps)
                self.constrain_dict_list(xrs, yrs)
            case (Record(fields=xf), Record(fields=yf)):
                self.constrain_dict_list(xf, yf)
            # covariant on the load and contravariant on the store
            case (Pointer(store_tv=xstv, load_tv=xltv), Pointer(store_tv=ystv, load_tv=yltv)):
                self.constrain(xltv, yltv)
                self.constrain(ystv, xstv)
            # actual subtyping
            case (l, VariableStorage(lower_bounds=lbs, upper_bounds=ubs)):
                lbs.append(l)
                for x in ubs:
                    self.constrain(l, x)
            case (VariableStorage(lower_bounds=lbs, upper_bounds=ubs), u):
                ubs.append(u)
                for x in lbs:
                    self.constrain(x, u)

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
        rec_pos = partial(self.coalesce_acc,
                          processing=processing, is_pos=is_pos)
        rec_neg = partial(self.coalesce_acc,
                          processing=processing, is_pos=(not is_pos))
        match ty:
            case Atom(name=aty):
                return Atom(aty)
            case Func(params=prs, return_vals=rets):
                return Func(ConstraintGenerator.map_value(rec_neg, prs), ConstraintGenerator.map_value(rec_pos, rets))
            case Record(fields=fs):
                return Record(ConstraintGenerator.map_value(rec_pos, fs))
            case Pointer(store_tv=stv, load_tv=lv):
                return Pointer(rec_neg(stv), rec_pos(lv))
            case VariableStorage(lower_bounds=lbs, upper_bounds=ubs):
                polar_v = PolarVariable(ty, Polarity.from_bool(is_pos))
                if polar_v in processing:
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
        assert False

    def coalesce(self, ty: ConsTy) -> ReprTy:
        return self.coalesce_acc(ty, frozenset(), True)

    def coalesce_types(self) -> dict[TypeVariable, ReprTy]:
        tot = dict()
        for (k, v) in self.base_var_map.items():
            if isinstance(k, TypeVariable):
                tot[k] = self.coalesce(v)
        return tot


class Compactor:
    def __init__(self) -> None:
        pass


class Rewriter:
    def __init__(self) -> None:
        pass
