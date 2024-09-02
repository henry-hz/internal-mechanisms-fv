-- simplifier
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Std

namespace Staking

open Std
open Nat
open Std

-- basis points
def bps (per: ℚ) : ℚ :=
  per * 100

-- a fixed pool of 100000 reward tokens we wish
-- to fairly distribute goal of 1000
-- to stakers from block 1 to 100
def pool : ℕ := 100000
def goal : ℕ := 1000

def stakers := HashMap ℕ ℕ

def get (m: stakers) (key: ℕ) : Option ℕ :=
  m.find! key

def set (m: stakers) (key: ℕ) (value: ℕ) : stakers:=
  m.insert key value




def staked_bob   := 100
def total_staked := 400

-- add 100 for precision
def bob := staked_bob * 100/ total_staked -- 25

def reward_distributed : ℕ := (bob * goal) /100
#eval reward_distributed




