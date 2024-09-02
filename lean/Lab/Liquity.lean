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

def now     : ℕ := 1708213740       -- [sec] 10/4/24 10:29UTC [from 1/2/1970 UTC]

def computeEarned (bl rw pd rs : ℕ) : ℕ :=
  ((bl * (rw - pd)) / WAD) + rs


def get_price := 100 * WAD

def open_trove :=
  -- get price from oracle
  -- require max fee %  [0.5% - 100%]
  -- require trove is non-existent or closed by [owner, liq, redemption]

  3

-- STATE
def Address := ℕ

structure S :=
  (now: ℕ)          -- [sec] linux epoch time in sec
  (reward: ℕ)       -- [wad] reward per token stored
  (rate : ℕ)        -- [per] reward rate per second
  (finish : ℕ)      -- [sec] finish reward time
  (updated : ℕ)     -- [sec] last time rate was updated
  (duration : ℕ)    -- [sec] reward duration time
  (staked : ℕ)      -- [wad] total staked in the contract
  (balance : ℕ)
  (balances: Address → ℕ) -- [wad] user staking balance
  (paid:     Address → ℕ) -- [wad] user reward per token paid
  (rewards:  Address → ℕ) -- [wad] pending reward per user


-- if update rate inserts a rate during a staking period, the rate takes in account the
-- leftover remaining amount multipled by the current rate and divides againg by the duration
def updateRate (s : S) (amount : ℕ) : S :=
  let newRate := if s.now >= s.finish then
                    amount / s.duration
                 else
                   let remaining := s.finish - now
                   let leftover  := remaining * s.rate
                   (amount + leftover) / s.duration

  if newRate <= s.balance / s.duration then
    {s with rate := newRate,
            finish := s.now + s.duration,
            updated := s.now}
  else s


-- USAGE

def exampleUsage : IO Unit := do
  let initialState : S := {
    now := 1708213740
    reward := 0
    rate := 1000,
    finish := 1708213740 + 7 * 24 * 60 * 60, -- 7 days from now
    updated := 1708213740,
    duration := 7 * 24 * 60 * 60, -- 7 days
    staked := 0
    balance := 1000000
    balances := λ _ => 0
    paid := λ _ => 0
    rewards := λ _ => 0
  }

  -- Call notifyRewardAmount with the initial state and an amount
  let updatedState := updateRate initialState 2000

  -- Print the updated state
  IO.println "Updated state:"
  IO.println $ "Rate: " ++ toString updatedState.rate
  IO.println $ "Finish: " ++ toString updatedState.finish
  IO.println $ "Updated: " ++ toString updatedState.updated
  IO.println $ "Duration: " ++ toString updatedState.duration
  IO.println $ "Balance: " ++ toString updatedState.balance

-- Run the example
#eval exampleUsage
