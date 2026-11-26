import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20819_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

theorem len2 (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) (j : ℕ) (hj : j < C.size) :
    (gateAt C j).inputs.length ≤ 2 := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases hg _ hmem with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

theorem pt_gate (r : ℕ) (sp A B : Prop) {_ : Decidable sp} {_ : Decidable A} {_ : Decidable B}
    (hsp : sp → ¬ A → 2 ≤ r) (hl : ¬ B → r = 0) :
    (if sp then r else 0) ≤ 2 * (if B then r - 1 else 0) + 2 * (if A then 1 else 0) ∧
    (if sp then 1 else 0) ≤ (if B then r - 1 else 0) + (if A then 1 else 0) := by
  rcases Classical.em sp with h1 | h1 <;> rcases Classical.em A with h3 | h3 <;>
    rcases Classical.em B with h2 | h2 <;> simp only [h1, h2, h3, ↓reduceIte] <;>
    (try have := hsp h1 h3) <;> (try have := hl h2) <;> omega

theorem sum_count (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < N := h a (by simp)
    rw [List.length_cons, ← ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons, Finset.sum_add_distrib, ha]

theorem cp_sum (l : List ℕ) (N : ℕ) (S : ℕ → Prop) (h : ∀ i ∈ l, i < N) :
    l.countP (fun i => @decide (S i) (Classical.propDecidable _)) =
      ∑ w ∈ range N, @ite _ (S w) (Classical.propDecidable _) (l.count w) 0 := by
  rw [List.countP_eq_length_filter, ← sum_count _ N (fun i hi => h i (List.mem_of_mem_filter hi))]
  refine sum_congr rfl fun w _ => ?_
  by_cases hw : S w
  · rw [if_pos hw]
    exact List.count_filter (by simpa using hw)
  · rw [if_neg hw]
    exact List.count_eq_zero.mpr fun hm => hw (by simpa using (List.mem_filter.mp hm).2)

theorem pt_in (a : ℕ) (sp B : Prop) {_ : Decidable sp} {_ : Decidable B}
    (hsp : sp → 2 ≤ a) (hB : B → 1 ≤ a) :
    (if sp then a else 0) + 2 * (if B then 1 else 0) ≤ 2 * a := by
  rcases Classical.em sp with h1 | h1 <;> rcases Classical.em B with h2 | h2 <;>
    simp only [h1, h2, ↓reduceIte] <;> (try have := hsp h1) <;> (try have := hB h2) <;> omega

end PEqualNP.Outside.L_meta_20819_aux

open PEqualNP.Outside.L_meta_20819_aux in
theorem PEqualNP.Outside.L_meta_20819 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size → C.output + 1 = m + C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
let R : ℕ → ℕ := fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w
let special : ℕ → Prop := fun w => (w < m ∧ 2 ≤ R w) ∨
  (m ≤ w ∧ w < m + C.size ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R w))
let ordinary : ℕ → Prop := fun w => (w < m ∧ R w = 1) ∨
  (m ≤ w ∧ w < m + C.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ R w ≤ 1)
let feeds : ℕ → ℕ → Prop := fun w g => g < C.size ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs
let edge : ℕ → ℕ → Prop := fun w w' => ordinary w ∧ ordinary w' ∧ m ≤ w' ∧ feeds w (w' - m)
let root : ℕ → Prop := fun w => ordinary w ∧ (w = C.output ∨ ∃ g, feeds w g ∧ special (m + g))
let skel : ℕ → Prop := fun w => ordinary w ∧ m ≤ w ∧
  ∃ g w0, ordinary (m + g) ∧ feeds w0 g ∧ special w0 ∧ Relation.ReflTransGen edge (m + g) w
let chainGate : ℕ → Prop := fun w => skel w ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - m)).inputs.countP
    (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) = 1
let chainTop : ℕ → Prop := fun w => chainGate w ∧ (root w ∨ ∃ g, feeds w g ∧ ¬ chainGate (m + g))
let ext : ℕ := ∑ g ∈ @Finset.filter ℕ (fun g1 => ordinary (m + g1)) (fun d1 => Classical.propDecidable _)
    (Finset.range C.size),
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
    (fun i => @decide (special i) (Classical.propDecidable _))
let Fin_ : ℕ := ∑ w ∈ Finset.range m, R w
let X : ℕ := ∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
    (Finset.range C.size), (R (m + j) - 1)
let t : ℕ := (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
    PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _) (Finset.range C.size)).card
let r : ℕ := (@Finset.filter ℕ (fun w => 1 ≤ R w) (fun d4 => Classical.propDecidable _) (Finset.range m)).card
ext + 2 * r ≤ 2 * (Fin_ + X + t) := by
  intro m C hg hrb hpos hout hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  have e1 : ext ≤ ∑ g ∈ Finset.range C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
        (fun i => @decide (special i) (Classical.propDecidable _)) :=
    Finset.sum_le_sum_of_subset
      (@Finset.filter_subset ℕ (fun g1 => ordinary (m + g1)) (fun _ => Classical.propDecidable _) _)
  have e2 : ∑ g ∈ Finset.range C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.countP
        (fun i => @decide (special i) (Classical.propDecidable _)) =
      ∑ w ∈ Finset.range (m + C.size), @ite _ (special w) (Classical.propDecidable _) (R w) 0 := by
    rw [Finset.sum_congr rfl fun g hg => cp_sum _ (m + C.size) special fun i hi => by
      have := hrb g (Finset.mem_range.mp hg) i hi
      have := Finset.mem_range.mp hg
      omega]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rcases Classical.em (special w) with h | h <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]
    all_goals try rfl
  rw [Finset.sum_range_add] at e2
  have hS : ∀ j, special (m + j) → ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.not → 2 ≤ R (m + j) := by
    intro j h hn
    rcases h with ⟨h, _⟩ | ⟨_, _, h | h⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h
      exact absurd h hn
    · exact h
  have hA : ∑ w ∈ Finset.range m, @ite _ (special w) (Classical.propDecidable _) (R w) 0 + 2 * r ≤
      2 * Fin_ := by
    simp only [r, Fin_]
    rw [Finset.card_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => pt_in _ _ _ (fun h => ?_) id
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · have := Finset.mem_range.mp hw
      omega
  have hB : ∑ j ∈ Finset.range C.size,
      @ite _ (special (m + j)) (Classical.propDecidable _) (R (m + j)) 0 ≤ 2 * X + 2 * t := by
    simp only [X, t]
    rw [Finset.card_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => (pt_gate _ _ _ _ (hS j) fun hn =>
      (hlast j (Finset.mem_range.mp hj)).2 (by have := Finset.mem_range.mp hj; omega)).1
  clear_value ext r Fin_ X t
  omega
