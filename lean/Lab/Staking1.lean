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
def amount  : ℕ := 1000000 * WAD

def now     : ℕ := 1708213740       -- [sec] 10/4/24 10:29UTC [from 1/2/1970 UTC]
def updated : ℕ := now - 172800     -- [sec] 2 days
def deltaT  : ℕ := now - updated    -- [sec]
def staked  : ℕ := 1000000 * WAD    -- [WAD] total staked
def duration: ℕ := 7 * 24 * 60 * 60 -- [sec] 7 days
def rate    : ℕ := amount/duration

def stake   : ℕ := 100 * WAD        -- [WAD]

def note (wad: ℕ) : (ℕ × ℕ × ℕ) :=
  (wad,1,1)


#eval 2*24*60*60
#eval duration
#eval rate
#eval note 323
#eval 16532738095238090800/WAD
#eval 8266369047619045400/WAD


-- the premise is that totalSupply is more than zero
-- accumulated reward

#eval WAD
#eval now


-- when we update the reward, we just recalculate the total
-- to be paid in WAD and move ..
-- bl: balance    [wad] user staked balance
-- rw: reward     [idx] accumulated reward index
-- pd: paid       [idx] accumulated last update
def computeEarned (bl rw pd rs : ℕ) : ℕ :=
  ((bl * (rw - pd)) / WAD) + rs

-- the reward is calculated by multiplying the rate we
-- pay by the elapsed time. However, since we are seeking
-- the proportional reward to be paid in relation to
-- the total staked, and the total staked is in WAD,
-- we need to multiply by WAD to maintain precision in WAD.
-- rt: rate       [per] reward rate per second
-- dt: delta      [sec] delta time (now - updated)
-- st: staked     [wad] total staked in the contract
def computeReward (rt dt st : ℕ) : ℕ :=
  (rt * dt * WAD) / st


-- calculate the WAD rate amount we pay per second,
-- so to know how much to pay, we multiply back by
-- the number of seconds and get the amount to pay
-- am: amount     [wad] reward amount to distribute
-- du: duration   [sec] reward duration time
def computeRate (am du : ℕ) : ℕ :=
  am / du

-- the rate is the reward paid per second in WAD.
-- to know how much reward we have left to pay,
-- we multiply the time by the rate.
-- dt: delta      [sec] delta time (finish - now)
-- rt: rate       [wad] reward rate per second
def computeLeftover (dt rt : ℕ) : ℕ :=
  dt * rt


-- we have left 10 seconds and the rate of 1/2 WAD
#eval computeLeftover 1000 (WAD/2)




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
