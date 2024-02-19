#!/usr/bin/env python3
# pylint:disable=missing-class-docstring,no-self-use
from angr.angrdb import AngrDB
from angr.analyses.typehoon.algebraic_solver import ConstraintGenerator, Atom
from angr.analyses.typehoon.typevars import TypeConstraint, Subtype, Load, HasField, TypeVariable, DerivedTypeVariable, FuncIn
__package__ = __package__ or "tests.analyses"  # pylint:disable=redefined-builtin

import os
import unittest

import angr

from ..common import bin_location


test_location = os.path.join(bin_location, "tests")


class TestTypehoon(unittest.TestCase):

    def test_rec_type_solver(self):
        tv_func = TypeVariable()

        tv1 = TypeVariable()
        tv2 = TypeVariable()
        tv3 = TypeVariable()

        load_at_40 = DerivedTypeVariable(
            DerivedTypeVariable(tv1, Load()), HasField(64, 40))

        s1 = Subtype(load_at_40, tv2)
        s2 = Subtype(tv2, tv3)
        s3 = Subtype(tv3, tv1)
        s4 = Subtype(DerivedTypeVariable(tv_func, FuncIn(0)), tv1)

        solved = ConstraintGenerator(set([s1, s2, s3, s4]))
        print("tys: ")
        print(solved.base_var_map)
        print(solved.solved_types)
        assert False

    def test_mooosl(self):
        db = AngrDB()
        proj: angr.Project = db.load(os.path.join(
            test_location, "x86_64", "mooosl.adb"))
        vr = proj.analyses.VariableRecoveryFast(proj.kb.functions["lookup"])
        proj.analyses.CompleteCallingConventions(proj.kb.functions["lookup"])
        print(vr.type_constraints)
        print(vr.var_to_typevars)

        solved = ConstraintGenerator(vr.type_constraints)
        print(solved.solved_types)
        for s in [v for (k, v) in vr.var_to_typevars.items() if k.name == "s_10"]:
            for tv in s:
                print(tv)
                if tv in solved.solved_types:
                    print(tv)
                    print(solved.solved_types[tv])
        assert False

    def test_smoketest(self):
        p = angr.Project(os.path.join(test_location, "x86_64",
                         "linked_list"), auto_load_libs=False)
        cfg = p.analyses.CFG(data_references=True, normalize=True)

        main_func = cfg.kb.functions["sum"]

        vr = p.analyses.VariableRecoveryFast(main_func)
        p.analyses.CompleteCallingConventions()

        # import pprint
        tcons = vr.type_constraints
        # pprint.pprint(vr._outstates[0x4005b2].typevars._typevars)
        # pprint.pprint(tcons)

        _ = p.analyses.Typehoon(tcons)
        # pprint.pprint(t.simtypes_solution)

        # convert function blocks to AIL blocks
        # clinic = p.analyses.Clinic(main_func)

        # t = p.analyses.Typehoon(main_func) #, clinic)
        # print(t)

    def test_type_inference_byte_pointer_cast(self):
        proj = angr.Project(os.path.join(
            test_location, "i386", "type_inference_1"), auto_load_libs=False)
        cfg = proj.analyses.CFG(data_references=True, normalize=True)
        main_func = cfg.kb.functions["main"]
        proj.analyses.VariableRecoveryFast(main_func)
        proj.analyses.CompleteCallingConventions()

        dec = proj.analyses.Decompiler(main_func)
        assert "->field_0 = 10;" in dec.codegen.text
        assert "->field_4 = 20;" in dec.codegen.text
        assert "->field_8 = 808464432;" in dec.codegen.text
        assert "->field_c = 0;" in dec.codegen.text


if __name__ == "__main__":
    unittest.main()
