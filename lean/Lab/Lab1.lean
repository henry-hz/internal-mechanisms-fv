import Mathlib.Data.Nat.Basic

#eval "hello" ++ " " ++ "world"


#check true


def x := 10

#eval x + 2

def double (x: ℤ) := 2 * x

#eval double 3

#check double


example: double 4 = 8 := rfl


def wad : ℕ := 10^18
--              1000000000000000000
#eval wad
--                          10000000000000000000000000000000000
#eval wad *       wad
#eval (10^18)*(10^18)
--                          100000000000000000000000000000000000000
--                          100000000000000000000000000000000000000
-- 100000000000000000000000000000000000000
-- 1000000000000000000000000000000000000


