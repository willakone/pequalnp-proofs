import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25478 : let k : Nat := 29
let rot := fun (s x : Nat) =>
  ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k
let chi := fun (x : Nat) =>
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i)
      (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
let roundG := fun (w x t : Nat) =>
  chi (x ^^^ rot 2 x ^^^ rot (k - 2) x) ^^^ rot (3 * t + 1) w ^^^
    (3 ^ (k + 2 + t) % 2 ^ k)
let bitAt := fun (w : Nat) =>
  (roundG w (roundG w (rot 3 w) 1) 2).testBit 14
xor (xor (bitAt 0) (bitAt (2 ^ 8)))
    (xor (bitAt (2 ^ 19)) (bitAt (2 ^ 8 + 2 ^ 19))) = true := by
  set_option maxRecDepth 100000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; nlinarith)
  | (intros; positivity)
  | (intros; aesop)
