import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25619 : let localUpdate := fun (x : BitVec 17) =>
  let m := x ^^^ x.rotateLeft 1 ^^^ x.rotateRight 1
  m ^^^ ((~~~(m.rotateRight 1)) &&& m.rotateRight 2)
let c₁ := BitVec.ofNat 17 (3 ^ 18)
let c₂ := BitVec.ofNat 17 (3 ^ 19)
let base := c₁ ^^^ 512
let row := base.rotateLeft 1
let key := fun (t : BitVec 10) => base ^^^ (t.setWidth 17).rotateLeft 12
let first := fun (w : BitVec 17) => localUpdate (w.rotateLeft 1 ^^^ row) ^^^ w ^^^ c₁
let second := fun (w y : BitVec 17) => localUpdate y ^^^ w.rotateLeft 2 ^^^ c₂
let actual := fun (t : BitVec 10) => second (key t) (first (key t))
let relaxed := (first base) ||| 3072
(∀ t : BitVec 10,
  (first (key t)).getLsbD 10 = t.getLsbD 0 ∧
  (first (key t)).getLsbD 11 = (!(t.getLsbD 0) && t.getLsbD 1) ∧
  (actual t).getLsbD 8 = (actual 0).getLsbD 8) ∧
(second base relaxed).getLsbD 8 ≠ (actual 0).getLsbD 8 ∧
(actual 3).getLsbD 9 ≠ (actual 7).getLsbD 9 := by
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
