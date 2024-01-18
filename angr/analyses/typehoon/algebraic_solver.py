

from dataclasses import dataclass
from typing import Set
from typehoon import TypeConstraint
from typevars import Existence, Subtype, TypeVariable, DerivedTypeVariable
from simple_solver import BaseSolver

import itertools

# Import labels
from typevars import FuncIn, FuncOut, Load, Store, ConvertTo, HasField

# A type variable is a unique holder of constraints


@dataclass
class VariableStorage:
    lower_bounds: list["ConsTy"]
    upper_bounds: list["ConsTy"]

@dataclass
class Atom:
    name: str

"""
pointers are a function in the sense of "store tv" -> "load tv"
"""
@dataclass 
class Pointer:
    store_tv: "ConsTy"
    load_tv: "ConsTy"

@dataclass
class Record:
    fields: dict[int,"ConsTy"]

@dataclass
class Func:
    params: dict[int,"ConsTy"]
    return_val: dict[int,"ConsTy"]





ConsTy = VariableStorage | Pointer | Record  | Atom


@dataclass
class FinalVar:
    ident: int

ReprTy = Pointer | Record | Atom | FinalVar



"""
Translates Retypd types into constrained type variables by collecting labels as
type constructors
"""
class ConstraintGenerator(BaseSolver):
    def __init__(self, ty_cons: Set["TypeConstraint"]) -> None:
        super.__init__(ty_cons)
        self.base_var_map: dict[TypeVariable, ConsTy] = {}
        self.orig_cons = {}
        self.solve()
        self.constrained_closed_list: Set[tuple[ConsTy, ConsTy]] = set()


    def solve_subtyping_constraints(self, constraints: Set["TypeConstraint"]):
        self.orig_cons = constraints
        self.infer_types()
        
    
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
                    
    def fresh(self) -> VariableStorage:
        return VariableStorage()
    
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
                            self.constrain(store,ld)
                            self.type_of(base_var, child_type=Pointer(store,ld))
                    case Store():
                            store = prev_ty
                            load = self.fresh()
                            self.constrain(store, load)
                            self.type_of(base_var, child_type=Pointer(store,ld))
                    case HasField(bits=sz, offset=off):        
                            # TODO(Ian): we should allow for refining an atom by a sz or something
                            self.type_of(base_var, child_type=Record({off: prev_ty}))
                    case FuncIn(loc=loc) | FuncOut(loc=loc):
                            nondef = {loc: prev_ty}
                            self.type_of(base_var, Func(nondef if isinstance(label, FuncIn) else {}, nondef if isinstance(label, FuncOut) else {}))
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
                self.constrain_dict_list(xps, yps)
                self.constrain_dict_list(xrs, yrs)
            case (Record(fields=xf), Record(fields=yf)):
                self.constrain_dict_list(xf, yf)
            # xstr <= xl 
            # ystr <= yl
            # so the result is going to be    , xl <= yl
            case (Pointer(store_tv=xstv, load_tv=xltv), Pointer(store_tv=ystv, load_tv=yltv)):
                raise NotImplementedError()
            # actual subtyping
            case (l, VariableStorage(lower_bounds=lbs, upper_bounds=ubs)):
                lbs.append(l)
                for x in ubs:
                    self.constrain(l,x)
            case (VariableStorage(lower_bounds=lbs, upper_bounds=ubs), u):
                ubs.append(u)
                for x in lbs:
                    self.constrain(x, u)


    def coalesce(self, ty: ConsTy) -> ReprTy:
        pass

    def coalesce_types(self) -> dict[TypeVariable, ReprTy]:
        tot = dict()
        for (k,v) in self.base_var_map.items():
            if isinstance(k, TypeVariable):
                tot[k] = self.coalesce(v)
        return tot


class Compactor:
    def __init__(self) -> None:
        pass

class Rewriter:
    def __init__(self) -> None:
        pass