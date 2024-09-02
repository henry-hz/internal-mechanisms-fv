-- simplifier
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Std


open Std
open Nat
open Std

def append (xs ys : List a) : List a :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys



#eval append [1,2] [3,4]

/-
Prove a property about our append function: that the length of the appended lists is the sum of their lengths.

The Theorem introduces a new theorem named append_length.
The statement (append xs ys).length = xs.length + ys.length is what we want to prove. The by ... block contains the proof. In this proof,

induction xs with initiates a proof by induction on xs;
the nil case proves the base case using simp, the Lean simplifier.
The parameter append instructs the simplifier to expand append’s definition; and
the cons x xs ih case proves the inductive step where ih is the inductive hypothesis.
It also uses simp and omega, which complete the proof using arithmetical reasoning.
In this proof, induction, simp, and omega are tactics. Tactics, which transform one state of
the proof into another, are key to interactive theorem proving in Lean. Users can inspect the states
of their proofs using the Lean InfoView, a panel in the IDE. The InfoView is an interactive object that can
be inspected and browsed by the user. In the following picture, we see the state of our proof before
the simp tactic at line 10. Note that the proof state contains all hypotheses and
the goal (append (x :: xs) ys).length = (x :: xs).length + ys.length, which remains to be proved.
-/

theorem append_length (xs ys : List a)
        : (append xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [append]
  | cons x xs ih => simp [append, ih]; omega

#check append_length
