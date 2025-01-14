import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Std

namespace B01_dep

open Std
open Nat
open Std

def myMapping := HashMap Nat String

def getValue (m : myMapping) (key : Nat) : Option String :=
  m.find! key

def setValue (m : myMapping) (key : Nat) (value : String) : myMapping :=
 m.insert key value


def α := ℚ

def mk_sym (xs : List ℚ) :=
  xs ++ xs.reverse

#eval mk_sym [1, 2, 3]

@[simp] theorem reverse_mk {xs : List ℚ} : (mk_sym xs).reverse = mk_sym xs := by
  simp [mk_sym]

theorem tst {xs ys : List ℚ} : (xs ++ mk_sym ys).reverse = mk_sym ys ++ xs.reverse := by
  simp

#print tst




example : ∃ x, x + 2 = 8 := by
 let a : Nat := 3 * 2
 exists a


def loadGlobalVar : IO Nat := do
 let value ← IO.getEnv "GLOBAL_VAR"
 match value with
 | some v => return v.toNat
 | none => return 0

def main : IO Unit := do
 let globalVar ← loadGlobalVar
 IO.println s!"Global variable value: {globalVar}"
