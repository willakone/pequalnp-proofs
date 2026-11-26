import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20818_aux
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

theorem rt (N s o : ℕ) (L : ℕ → List ℕ) (Sp root : ℕ → Prop) (hL : ∀ g < s, (L g).length ≤ 2)
    (hr : ∀ w, root w → w = o ∨ ∃ g, (g < s ∧ w ∈ L g) ∧ Sp g) :
    (@Finset.filter ℕ root (fun _ => Classical.propDecidable _) (range N)).card ≤
      2 * (@Finset.filter ℕ Sp (fun _ => Classical.propDecidable _) (range s)).card + 1 := by
  classical
  calc _ ≤ (insert o ((@Finset.filter ℕ Sp (fun _ => Classical.propDecidable _) (range s)).biUnion
        (fun g => (L g).toFinset))).card := by
        refine card_le_card fun w hw => ?_
        rcases hr w (mem_filter.mp hw).2 with h | ⟨g, ⟨hg, hw⟩, hs⟩
        · simp [h]
        · exact mem_insert_of_mem (mem_biUnion.mpr ⟨g, mem_filter.mpr ⟨mem_range.mpr hg, hs⟩,
            List.mem_toFinset.mpr hw⟩)
    _ ≤ _ + 1 := card_insert_le _ _
    _ ≤ _ := by
      refine Nat.add_le_add_right (card_biUnion_le.trans ?_) 1
      calc _ ≤ ∑ g ∈ @Finset.filter ℕ Sp (fun _ => Classical.propDecidable _) (range s), 2 :=
            sum_le_sum fun g hg => (List.toFinset_card_le _).trans
              (hL g (mem_range.mp (mem_filter.mp hg).1))
        _ = _ := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

end PEqualNP.Outside.L_meta_20818_aux

open PEqualNP.Outside.L_meta_20818_aux in
theorem PEqualNP.Outside.L_meta_20818 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
(@Finset.filter ℕ root (fun d5 => Classical.propDecidable _) (Finset.range (m + C.size))).card ≤
    2 * (@Finset.filter ℕ (fun g2 => special (m + g2)) (fun d6 => Classical.propDecidable _)
      (Finset.range C.size)).card + 1 ∧
  (@Finset.filter ℕ (fun g3 => special (m + g3)) (fun d7 => Classical.propDecidable _)
      (Finset.range C.size)).card ≤ X + t := by
  intro m C hg hrb hpos hout hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  refine ⟨rt (m + C.size) C.size C.output
    (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs) (fun g => special (m + g))
    root (fun g hg' => len2 C hg g hg') (fun w h => h.2), ?_⟩
  have hS : ∀ j, special (m + j) → ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.not → 2 ≤ R (m + j) := by
    intro j h hn
    rcases h with ⟨h, _⟩ | ⟨_, _, h | h⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h
      exact absurd h hn
    · exact h
  simp only [X, t]
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => (pt_gate _ _ _ _ (hS j) fun hn =>
    (hlast j (Finset.mem_range.mp hj)).2 (by have := Finset.mem_range.mp hj; omega)).2
