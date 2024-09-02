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


def WAD     : ℕ := 10^18

structure Wad where
  value : ℕ

def Wad.mks (n : ℕ) : Wad :=
 { value := n * 10 }

def Wad.get (w : Wad) : ℕ :=
 w.value

def Wad.scale (w : Wad) : ℕ :=
  w.value

def w1 : Wad := Wad.mks 10
def w2 : ℕ   := Wad.get w1
def w3 : ℕ   := Wad.scale w1

#eval w1.value
#eval w2
#eval w3

def myWad : Wad := { value := 42 }

def scaleWad (w : Wad) : Int := w.value * 10  -- Function to scale by 10

#eval   myWad.value





structure AMM :=
  (total: ℕ)          -- [sec] linux epoch time in sec


def k(x y : ℕ) : ℕ :=
  x * y

def min(a b : ℕ) : ℕ :=
  if a <= b then a else b


-- FIRST DEPOSIT [shimon]
-------------------------
def a0 : ℕ := 5 * WAD
def a1 : ℕ := 10 * WAD
def r0 : ℕ := 5 * WAD
def r1 : ℕ := 10

#eval k a0 a1
#eval sqrt (a0*a1)

def s  : ℕ := 7 -- mint -> total -> state -> shares -> 0 -> 7
def t  : ℕ := 7 -- mint -> total -> state -> shares -> 0 -> 7

-- SECOND DEPPOSIT [reuven]
---------------------------
def a0' : ℕ := 15
def a1' : ℕ := 30

-- reserve0 * amount1 == reserve1 * amount0
#eval (r0 * a1') = (r1 * a0')

def s'  : ℕ := min ((a0' * t) / r0) ((a1' * t) / r1)
def t'  : ℕ := 28

def r0' : ℕ := 20
def r1' : ℕ := 40

#eval s'

-- THIRD DEPPOSIT [levi]
---------------------------

def a0'' : ℕ := 1
def a1'' : ℕ := 2

def s''  : ℕ := min ((a0'' * t') / r0') ((a1'' * t') / r1')
def t''  : ℕ := 29

def r0'' : ℕ := 21 -- USDC
def r1'' : ℕ := 42 -- TURT

#eval s''


-- FIRST SWAP [yaackov] -  5 t0 -> ??? t1
---------------------------

-- tI = token0
-- tO = token1
-- rI = r0
-- rO = r1

def price(aI rI rO : ℕ) : ℕ :=
  (rO * aI)/(rI + aI)


def r0''' : ℕ := 26 -- USDC
def aF    : ℕ := (5 * 997) / 1000
def p     : ℕ := price aF r0'' r1''
def r1''' : ℕ := 36


#eval aF
#eval p








def computeReward (rt dt st : ℕ) : ℕ :=
  (rt * dt * WAD) / st
