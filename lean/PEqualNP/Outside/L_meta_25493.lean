import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25493 : let rot := fun (s word : Nat) =>
  ((word <<< (s % 5)) ||| (word >>> (5 - s % 5))) % 32
let step := fun (x : Nat) =>
  (List.range 5).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i)
      (!(x.testBit ((i + 1) % 5)) && x.testBit ((i + 2) % 5))).toNat <<< i)) 0
let constant := fun (j : Nat) => 3 ^ (5 + j) % 32
let first := fun (fw row : Nat) =>
  (List.range 4).foldl (fun prevF timeF =>
    step (prevF ^^^ rot 1 prevF ^^^ rot 4 prevF) ^^^ rot (2 * timeF) fw ^^^ constant (timeF + 1))
    (rot 1 fw ^^^ row)
let second := fun (gw col : Nat) =>
  (List.range 4).foldl (fun prevG timeG =>
    step (prevG ^^^ rot 2 prevG ^^^ rot 3 prevG) ^^^ rot (3 * (timeG + 1) + 1) gw ^^^
      constant (4 + (timeG + 1))) (rot 3 gw ^^^ col)
let rows : List Nat :=
  [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a,
   0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402,
   0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a,
   0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e,
   0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351,
   0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082,
   0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8,
   0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]
∀ u v : Fin 32,
  (List.range 32).any (fun key => decide (first key u.val < 4) && decide (second key v.val < 4)) =
    (rows.getD u.val 0).testBit v.val := by
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
