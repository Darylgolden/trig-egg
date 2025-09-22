import Mathlib


#norm_num Irrational (100^(1/3))

example : Irrational (100^(1/3 : ℝ)) := by norm_num

#norm_num 3 < 4
#conv norm_num 3 < 4
example : 3 < 4 := by
  norm_num

axiom evalIntOfNat : Int

axiom norm_num_evalIntOfNat {n : Nat} : Int.ofNat n = evalIntOfNat