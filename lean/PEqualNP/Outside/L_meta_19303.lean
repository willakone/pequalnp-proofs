import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19303_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def val (u v k : ℕ) : Bool :=
  if k = 0 then decide (u = 0 ∨ v = 0)
  else if k = 1 then decide (u = 1 ∨ v = 1)
  else if k % 4 = 0 then decide (u = k / 4 + 1 ∨ v = k / 4 + 1)
  else if k % 4 = 1 then decide ((u = (k + 3) / 4 ∨ v = (k + 3) / 4) ∧ (u < (k + 3) / 4 ∨ v < (k + 3) / 4))
  else if k % 4 = 2 then decide (u ≠ v ∧ u ≤ (k + 2) / 4 ∧ v ≤ (k + 2) / 4)
  else decide (u ≤ (k + 1) / 4 ∨ v ≤ (k + 1) / 4)

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w) else if w < 2 * n then decide (v + n = w) else val u v (w - 2 * n)

def gate (n k : ℕ) : Gate :=
  if k = 0 then ⟨GateOp.or, [0, n]⟩
  else if k = 1 then ⟨GateOp.or, [1, n + 1]⟩
  else if k = 2 then ⟨GateOp.and, [2 * n + 1, 2 * n]⟩
  else if k = 3 then ⟨GateOp.or, [2 * n, 2 * n + 1]⟩
  else if k % 4 = 0 then ⟨GateOp.or, [k / 4 + 1, n + (k / 4 + 1)]⟩
  else if k % 4 = 1 then ⟨GateOp.and, [2 * n + (k - 1), 2 * n + (k - 2)]⟩
  else if k % 4 = 2 then ⟨GateOp.or, [2 * n + (k - 1), 2 * n + (k - 4)]⟩
  else ⟨GateOp.or, [2 * n + (k - 4), 2 * n + (k - 3)]⟩

theorem fX (n u v w : ℕ) (h : w < n) : f n u v w = decide (u = w) := by simp [f, h]

theorem fY (n u v w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) : f n u v w = decide (v + n = w) := by
  simp [f, h2, show ¬ w < n by omega]

theorem fG (n u v k : ℕ) : f n u v (2 * n + k) = val u v k := by
  simp [f, show ¬ 2 * n + k < n by omega]

theorem fG0 (n u v : ℕ) : f n u v (2 * n) = val u v 0 := fG n u v 0

theorem v0 (u v : ℕ) : val u v 0 = decide (u = 0 ∨ v = 0) := by simp [val]

theorem v1 (u v : ℕ) : val u v 1 = decide (u = 1 ∨ v = 1) := by simp [val]

theorem vW (u v k : ℕ) (h0 : k ≠ 0) (h : k % 4 = 0) :
    val u v k = decide (u = k / 4 + 1 ∨ v = k / 4 + 1) := by
  simp [val, h0, h, show k ≠ 1 by omega]

theorem vT (u v k : ℕ) (h1 : k ≠ 1) (h : k % 4 = 1) :
    val u v k = decide ((u = (k + 3) / 4 ∨ v = (k + 3) / 4) ∧ (u < (k + 3) / 4 ∨ v < (k + 3) / 4)) := by
  simp [val, h1, h, show k ≠ 0 by omega]

theorem vA (u v k : ℕ) (h : k % 4 = 2) :
    val u v k = decide (u ≠ v ∧ u ≤ (k + 2) / 4 ∧ v ≤ (k + 2) / 4) := by
  simp [val, h, show k ≠ 0 by omega, show k ≠ 1 by omega]

theorem vZ (u v k : ℕ) (h : k % 4 = 3) :
    val u v k = decide (u ≤ (k + 1) / 4 ∨ v ≤ (k + 1) / 4) := by
  simp [val, h, show k ≠ 0 by omega, show k ≠ 1 by omega]

theorem gate_ok (n u v k : ℕ) (hn : 2 ≤ n) (hk : k < 4 * n - 5) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u v)) = f n u v (2 * n + k) := by
  unfold gate
  split_ifs with h0 h1 h2 h3 h4 h5 h6 <;> refine ⟨by simp; omega, ?_⟩ <;>
    simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, fG, fG0]
  · subst h0; rw [fX n u v 0 (by omega), fY n u v n le_rfl (by omega), v0]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · subst h1; rw [fX n u v 1 (by omega), fY n u v (n + 1) (by omega) (by omega), v1]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · subst h2; rw [v0, v1, vA u v 2 (by norm_num)]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  · subst h3; rw [v0, v1, vZ u v 3 (by norm_num)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · rw [fX n u v _ (by omega), fY n u v _ (by omega) (by omega), vW u v k h0 h4]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · rw [vW u v (k - 1) (by omega) (by omega), vZ u v (k - 2) (by omega), vT u v k h1 h5]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vT u v (k - 1) (by omega) (by omega), vA u v (k - 4) (by omega), vA u v k h6]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vZ u v (k - 4) (by omega), vW u v (k - 3) (by omega) (by omega), vZ u v k (by omega)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

end PEqualNP.Outside.L_meta_19303_aux

open PEqualNP.Outside.L_meta_19303_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19303 : ∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u v : Fin n) => decide (u ≠ v)) (4 * n - 5) := by
  intro n hn
  refine ⟨⟨(List.range (4 * n - 5)).map (gate n), 2 * n + (4 * n - 6)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
      simp [PEqualNP.Represents.oneEach]; omega
    have hx : ∀ i < (PEqualNP.Represents.oneEach u v).length,
        (PEqualNP.Represents.oneEach u v).getD i false = f n u v i := by
      intro i hi
      rw [hl] at hi
      apply Bool.eq_iff_iff.2
      simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, List.getElem?_ofFn, f, val]
      split_ifs <;> simp [Fin.ext_iff] <;> omega
    show (List.foldl stp (PEqualNP.Represents.oneEach u v) ((List.range (4 * n - 5)).map (gate n))).getD (2 * n + (4 * n - 6)) false = decide (u ≠ v)
    rw [spec (f n u v) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v k hn hk) _ (by simp [hl]; omega), fG]
    have hu := u.isLt
    have hv := v.isLt
    rw [vA u v _ (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [ne_eq, Fin.ext_iff, Bool.and_eq_true, decide_eq_true_eq]
    omega
