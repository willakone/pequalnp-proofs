import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25524 : let step := fun (x : BitVec 13) =>
  x ^^^ ((~~~(x.rotateRight 1)) &&& x.rotateRight 2)
let row := fun (w : BitVec 13) =>
  let x := w.rotateLeft 1
  step (x ^^^ x.rotateLeft 1 ^^^ x.rotateRight 1) ^^^ w ^^^ BitVec.ofNat 13 (3 ^ 14)
let col := fun (w : BitVec 13) =>
  let x := w.rotateLeft 3 ^^^ 1
  step (x ^^^ x.rotateLeft 2 ^^^ x.rotateRight 2) ^^^ w.rotateLeft 4 ^^^ BitVec.ofNat 13 (3 ^ 15)
let freePass := fun (scan : BitVec 14) =>
  let w := (scan.setWidth 13).rotateLeft 1
  let lastKey := if scan.getLsbD 13 then w ||| 2 else w &&& (~~~2)
  (row w &&& 4032) = 0 ∧ row lastKey < 4096 ∧ col w < 64
freePass 3759 ∧
  (∀ w : BitVec 13, row w < 64 → 115 ≤ col w) ∧
  (∃ w : BitVec 13, row w < 64 ∧ col w = 115) := by
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
