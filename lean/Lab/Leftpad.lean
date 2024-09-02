import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Std

namespace Leftpad

open Std
open Nat
open Std

universe u
variable {α : Type u}

def leftpad (n : ℕ) (a : α) (l : list α) : list α :=
repeat a (n - length l) ++ l

#eval list.as_string (leftpad 5 'b' (string.to_list "ac"))

theorem leftpad_length (n : ℕ) (a : α) (l : list α) :
length (leftpad n a l) = max n (length l) :=
begin
  rw leftpad, simp,
  rw [add_comm, nat.sub_add_eq_max]
end

theorem leftpad_prefix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
(repeat a (n - length l)) <+: (leftpad n a l) := by {rw leftpad, simp}

theorem leftpad_suffix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
l <:+ (leftpad n a l) := by {rw leftpad, simp}
