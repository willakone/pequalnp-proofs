import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25482 : ∀ (k : Nat) (u v : Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let cutoff := 2 ^ (k - (k + 1) / 2)
  (List.range (2 ^ k)).any (fun key =>
    decide ((rot 1 key ^^^ u.val) < cutoff) &&
    decide ((rot 3 key ^^^ v.val) < cutoff)) = true ↔
    ∃ w < 2 ^ k, (rot 1 w ^^^ u.val) < cutoff ∧ (rot 3 w ^^^ v.val) < cutoff := by
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
