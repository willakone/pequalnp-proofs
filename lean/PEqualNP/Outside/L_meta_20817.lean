import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20817_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem snoc {α : Type} (l : List α) (b d : α) (w : ℕ) :
    (l ++ [b]).getD w d = if w < l.length then l.getD w d else if w = l.length then b else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem pre (x : List Bool) (gs : List Gate) :
    ∀ w < x.length, (gs.foldl stp x).getD w false = x.getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ _ => rfl
  | append_singleton gs g ih =>
    intro w hw
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [snoc, len, ite_cond_eq_true _ _ (eq_true (by omega))]
    exact ih w hw

theorem agree (B : ℕ → Prop) (x y : List Bool) (hxy : x.length = y.length)
    (he : ∀ w, ¬ B w → x.getD w false = y.getD w false) (gs : List Gate)
    (hg : ∀ g ∈ gs, ∀ w ∈ g.inputs, ¬ B w) :
    ∀ w, ¬ B w → (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact he
  | append_singleton gs g ih =>
    intro w hw
    have ih := ih fun g' hg' => hg g' (by simp [hg'])
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [snoc, snoc, len, len, hxy]
    split_ifs
    · exact ih w hw
    · congr 1
      exact List.map_congr_left fun i hi => ih i (hg g (by simp) i hi)
    · rfl

theorem nr (C : Circuit) (w : ℕ) (h : readsIn C (Finset.range C.size) w = 0) :
    ∀ g ∈ C.gates, w ∉ g.inputs := by
  intro g hg hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  unfold readsIn at h
  have := (Finset.sum_eq_zero_iff.1 h) j (Finset.mem_range.2 hj)
  rw [gateAt, List.getD_eq_getElem _ _ hj] at this
  exact (List.count_pos_iff.2 hw).ne' this

theorem sil (C : Circuit) (a b : ℕ) (ha : readsIn C (Finset.range C.size) a = 0)
    (hb : readsIn C (Finset.range C.size) b = 0) (ho : C.output ≠ a ∧ C.output ≠ b)
    (x y : List Bool) (hxy : x.length = y.length)
    (he : ∀ w, w ≠ a → w ≠ b → x.getD w false = y.getD w false) : C.eval x = C.eval y :=
  agree (fun w => w = a ∨ w = b) x y hxy
    (fun w hw => he w (fun h => hw (Or.inl h)) (fun h => hw (Or.inr h))) C.gates
    (fun g hg _ hw h => h.elim (fun e => nr C a ha g hg (e ▸ hw)) (fun e => nr C b hb g hg (e ▸ hw)))
    C.output (fun h => h.elim ho.1 ho.2)

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end PEqualNP.Outside.L_meta_20817_aux

open PEqualNP.Outside.L_meta_20817_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_20817 : ∀ (n : ℕ), 3 ≤ n → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.Represents.Represents (fun u v : Fin n => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n)) C →
  (∀ u1 u2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u1.val = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u2.val = 0 → u1 = u2) ∧
  (∀ v1 v2 : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v1.val) = 0 →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + v2.val) = 0 → v1 = v2) ∧
  n + n ≤ (@Finset.filter ℕ
      (fun w => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w)
      (fun d1 => Classical.propDecidable _) (Finset.range (n + n))).card + 2 := by
  intro n hn C hR
  have T : ∀ u v : Fin n, C.eval (oneEach u v) = true ↔ (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % n) :=
    fun u v => by rw [hR u v]; exact decide_eq_true_iff
  have hm : ∀ x, x < n → (x + 1) % n = x + 1 ∨ ((x + 1) % n = 0 ∧ x + 1 = n) := by
    intro x hx
    rcases Nat.lt_or_ge (x + 1) n with h | h
    · exact Or.inl (Nat.mod_eq_of_lt h)
    · have e : x + 1 = n := by omega
      rw [e, Nat.mod_self]; exact Or.inr ⟨rfl, rfl⟩
  have hout : n + n ≤ C.output := by
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k : Fin n, C.output = k.val ∨ C.output = n + k.val :=
      if h : C.output < n then ⟨⟨_, h⟩, Or.inl rfl⟩
      else ⟨⟨C.output - n, by omega⟩, Or.inr (by simp only; omega)⟩
    have h2 : C.eval (oneEach k k) = true := by
      show (C.gates.foldl stp (oneEach k k)).getD C.output false = true
      rw [pre _ _ _ (by simp [oneEach]; omega)]; exact (oe k k _).2 hk
    exact ((T k k).1 h2).1 rfl
  have rows : ∀ u1 u2 : Fin n, readsIn C (Finset.range C.size) u1.val = 0 →
      readsIn C (Finset.range C.size) u2.val = 0 → u1 = u2 := by
    intro u1 u2 h1 h2
    have i1 := u1.isLt; have i2 := u2.isLt
    have e : ∀ v : Fin n, C.eval (oneEach u1 v) = C.eval (oneEach u2 v) := fun v =>
      sil C _ _ h1 h2 ⟨by omega, by omega⟩ _ _ (by simp [oneEach]) fun w hw1 hw2 => by
        refine Bool.eq_iff_iff.2 ?_; rw [oe, oe]; constructor <;> intro h <;> omega
    have a := (T u1 u1).symm.trans ((Bool.eq_iff_iff.1 (e u1)).trans (T u2 u1))
    have b := (T u1 u2).symm.trans ((Bool.eq_iff_iff.1 (e u2)).trans (T u2 u2))
    have m1 := hm _ i1; have m2 := hm _ i2
    apply Fin.ext
    by_contra hne
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_and, not_not, false_iff] at a b
    omega
  have cols : ∀ v1 v2 : Fin n, readsIn C (Finset.range C.size) (n + v1.val) = 0 →
      readsIn C (Finset.range C.size) (n + v2.val) = 0 → v1 = v2 := by
    intro v1 v2 h1 h2
    have i1 := v1.isLt; have i2 := v2.isLt
    have e : ∀ u : Fin n, C.eval (oneEach u v1) = C.eval (oneEach u v2) := fun u =>
      sil C _ _ h1 h2 ⟨by omega, by omega⟩ _ _ (by simp [oneEach]) fun w hw1 hw2 => by
        refine Bool.eq_iff_iff.2 ?_; rw [oe, oe]; constructor <;> intro h <;> omega
    have a := (T v1 v1).symm.trans ((Bool.eq_iff_iff.1 (e v1)).trans (T v1 v2))
    have b := (T v2 v1).symm.trans ((Bool.eq_iff_iff.1 (e v2)).trans (T v2 v2))
    have m1 := hm _ i1; have m2 := hm _ i2
    apply Fin.ext
    by_contra hne
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_and, not_not, false_iff] at a b
    omega
  refine ⟨rows, cols, ?_⟩
  have key0 : ∀ S : Finset ℕ, (∀ w ∈ Finset.range (n + n),
      readsIn C (Finset.range C.size) w ≠ 0 → w ∈ S) → n + n ≤ S.card + 2 := by
    intro S hS
    let U := (Finset.range (n + n)).filter (fun w => readsIn C (Finset.range C.size) w = 0)
    have h1 : Finset.range (n + n) ⊆ S ∪ U := by
      intro w hw
      by_cases h : readsIn C (Finset.range C.size) w = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hw, h⟩)
      · exact Finset.mem_union_left _ (hS w hw h)
    have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le S U)
    rw [Finset.card_range] at h2
    have h3 : U ⊆ U.filter (fun w => w < n) ∪ U.filter (fun w => ¬ w < n) := by
      intro w hw
      by_cases h : w < n
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hw, h⟩)
    have h6 := (Finset.card_le_card h3).trans (Finset.card_union_le _ _)
    have h4 : (U.filter (fun w => w < n)).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [U, Finset.mem_filter] at ha hb
      exact congrArg Fin.val (rows ⟨a, ha.2⟩ ⟨b, hb.2⟩ ha.1.2 hb.1.2)
    have h5 : (U.filter (fun w => ¬ w < n)).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [U, Finset.mem_filter, Finset.mem_range] at ha hb
      have := congrArg Fin.val (cols ⟨a - n, by omega⟩ ⟨b - n, by omega⟩
        (by rw [Nat.add_sub_cancel' (by omega)]; exact ha.1.2)
        (by rw [Nat.add_sub_cancel' (by omega)]; exact hb.1.2))
      simp only at this; omega
    omega
  have key : ∀ (P : ℕ → Prop) (_ : DecidablePred P), (∀ w, readsIn C (Finset.range C.size) w ≠ 0 → P w) →
      n + n ≤ ((Finset.range (n + n)).filter P).card + 2 := by
    intro P _ hP
    exact key0 _ fun w hw h => Finset.mem_filter.2 ⟨hw, hP w h⟩
  exact key _ _ fun w h => by omega
