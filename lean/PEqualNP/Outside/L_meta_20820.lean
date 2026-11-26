import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20820_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

theorem len2 (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) (j : ℕ) (hj : j < C.size) :
    (gateAt C j).inputs.length ≤ 2 := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases hg _ hmem with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

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

theorem cp_or (l : List ℕ) (P Q : ℕ → Prop) (h : ∀ i ∈ l, P i → Q i → False) :
    l.countP (fun i => @decide (P i ∨ Q i) (Classical.propDecidable _)) =
      l.countP (fun i => @decide (P i) (Classical.propDecidable _)) +
        l.countP (fun i => @decide (Q i) (Classical.propDecidable _)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    rw [ih fun i hi => h i (List.mem_cons_of_mem a hi)]
    have ha := h a (by simp)
    rcases Classical.em (P a) with hp | hp <;> rcases Classical.em (Q a) with hq | hq <;>
      simp [hp, hq] <;> first | omega | exact (ha hp hq).elim

end PEqualNP.Outside.L_meta_20820_aux

open PEqualNP.Outside.L_meta_20820_aux in
theorem PEqualNP.Outside.L_meta_20820 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
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
(@Finset.filter ℕ chainTop (fun d5 => Classical.propDecidable _) (Finset.range (m + C.size))).card ≤ 2 * ext := by
  intro m C hg hrb hpos hout hlast R special ordinary feeds edge root skel chainGate chainTop ext Fin_ X t r
  classical
  have hdis : ∀ w, ordinary w → special w → False := by
    rintro w (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩) (⟨h5, h6⟩ | ⟨h5, h6, h7 | h7⟩)
    all_goals first | omega | exact h3 h7
  have hR1 : ∀ i, skel (m + i) → R (m + i) ≤ 1 := by
    intro i h
    rcases h.1 with ⟨h1, _⟩ | ⟨_, _, _, h4⟩
    · omega
    · exact h4
  have hlen := len2 C hg
  have hcnt : ∀ j < C.size, ∀ v,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count v ≤ R v := fun j hj v =>
    Finset.single_le_sum (f := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count v)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  have huniq : ∀ i g j, skel (m + i) → g < C.size → j < C.size →
      m + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs →
      m + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs → g = j := by
    intro i g j hs hg' hj hg1 hj1
    by_contra hne
    have h2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.count (m + i) +
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) ≤ R (m + i) := by
      have := Finset.sum_le_sum_of_subset
        (f := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.count (m + i))
        (show ({g, j} : Finset ℕ) ⊆ Finset.range C.size by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hx ⊢
          omega)
      rw [Finset.sum_pair hne] at this
      exact this
    have := List.count_pos_iff.mpr hg1
    have := List.count_pos_iff.mpr hj1
    have := hR1 i hs
    omega
  obtain ⟨c, hc⟩ : ∃ f : ℕ → ℕ, f = fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.countP
      (fun i => @decide (special i ∨ skel i) (Classical.propDecidable _)) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ f : ℕ → ℕ, f = fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.countP
      (fun i => @decide (special i) (Classical.propDecidable _)) := ⟨_, rfl⟩
  obtain ⟨sk, hsk⟩ : ∃ f : ℕ → ℕ, f = fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.countP
      (fun i => @decide (skel i) (Classical.propDecidable _)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Finset ℕ, K = (Finset.range C.size).filter (fun j => skel (m + j)) :=
    ⟨_, rfl⟩
  have hKm : ∀ j, j ∈ K ↔ j < C.size ∧ skel (m + j) := by
    intro j
    rw [hK, Finset.mem_filter, Finset.mem_range]
  have hbd : ∀ j < C.size, ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      i < m + C.size := fun j hj i hi => by
    have := hrb j hj i hi
    omega
  -- each skeleton gate has one or two special-or-skeleton operands
  have hc1 : ∀ j ∈ K, 1 ≤ c j ∧ c j ≤ 2 := by
    intro j hj
    obtain ⟨hjs, hsj⟩ := (hKm j).1 hj
    refine ⟨?_, ?_⟩
    · rw [hc]
      beta_reduce
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, List.countP_pos_iff]
      obtain ⟨_, _, g, w0, hog, hf, hw0, hpath⟩ := hsj
      rcases hpath.cases_tail with h | ⟨v, hv, he⟩
      · have : j = g := by omega
        subst this
        exact ⟨w0, hf.2, by simp [hw0]⟩
      · obtain ⟨hov, _, _, hfv⟩ := he
        have hmv : m ≤ v := by
          rcases hv.cases_tail with h | ⟨u, _, hu⟩
          · omega
          · exact hu.2.2.1
        refine ⟨v, ?_, ?_⟩
        · have := hfv.2
          rwa [Nat.add_sub_cancel_left] at this
        · simp only [decide_eq_true_eq]
          exact Or.inr ⟨hov, hmv, g, w0, hog, hf, hw0, hv⟩
    · rw [hc]
      exact List.countP_le_length.trans (hlen j hjs)
  have hcs : ∀ j ∈ K, c j = sp j + sk j := by
    intro j hj
    rw [hc, hsp, hsk]
    exact cp_or _ _ _ fun i _ h1 h2 => hdis i h2.1 h1
  have hsk2 : ∀ j ∈ K, sk j ≤ 2 := by
    intro j hj
    rw [hsk]
    exact List.countP_le_length.trans (hlen j ((hKm j).1 hj).1)
  have skw : ∀ j < C.size, sk j = ∑ i ∈ K,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) := by
    intro j hj
    rw [hsk]
    beta_reduce
    rw [cp_sum _ (m + C.size) skel (hbd j hj), Finset.sum_range_add, hK, Finset.sum_filter]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v hv => if_neg fun h => ?_)
      (Finset.sum_congr rfl fun i _ => ?_)).trans (zero_add _)
    · have := h.2.1
      have := Finset.mem_range.mp hv
      omega
    · split_ifs <;> rfl
  obtain ⟨a, ha⟩ : ∃ f : ℕ → ℕ, f = fun v => ∑ j ∈ K,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count v := ⟨_, rfl⟩
  obtain ⟨ab, hab⟩ : ∃ f : ℕ → ℕ, f = fun v => ∑ j ∈ K,
      (if c j = 2 then (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count v else 0) :=
    ⟨_, rfl⟩
  have fC : ∑ i ∈ K, a (m + i) = ∑ j ∈ K, sk j := by
    rw [ha]
    beta_reduce
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j hj => (skw j ((hKm j).1 hj).1).symm
  have fB : ∑ i ∈ K, ab (m + i) = ∑ j ∈ K, (if c j = 2 then sk j else 0) := by
    rw [hab]
    beta_reduce
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases h2 : c j = 2 <;> simp only [h2, ↓reduceIte, Finset.sum_const_zero]
    exact (skw j ((hKm j).1 hj).1).symm
  have fE : ∑ i ∈ K, (if a (m + i) = 0 then 1 else 0) + ∑ i ∈ K, a (m + i) ≤ ∑ i ∈ K, 1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hai : a (m + i) ≤ R (m + i) := by
      rw [ha]
      show ∑ j ∈ K, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) ≤
        ∑ j ∈ Finset.range C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i)
      exact Finset.sum_le_sum_of_subset (by rw [hK]; exact Finset.filter_subset _ _)
    have := hR1 i ((hKm i).1 hi).2
    split_ifs <;> omega
  have fF : ∑ j ∈ K, (if c j = 2 then sk j else 0) ≤ 2 * ∑ j ∈ K, (if c j = 2 then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have := hsk2 j hj
    split_ifs <;> omega
  have fG : ∑ j ∈ K, 1 + ∑ j ∈ K, (if c j = 2 then 1 else 0) = ∑ j ∈ K, sp j + ∑ j ∈ K, sk j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hc1 j hj
    have := hcs j hj
    split_ifs <;> omega
  have fH : ∑ j ∈ K, sp j ≤ ext := by
    rw [hsp]
    refine Finset.sum_le_sum_of_subset ?_
    intro j hj
    exact (@Finset.mem_filter ℕ _ (fun _ => Classical.propDecidable _) _ _).mpr ⟨Finset.mem_range.mpr ((hKm j).1 hj).1, ((hKm j).1 hj).2.1⟩
  have hA : (@Finset.filter ℕ chainTop (fun _ => Classical.propDecidable _)
      (Finset.range (m + C.size))).card ≤
      ∑ i ∈ K, ((if a (m + i) = 0 then 1 else 0) + ab (m + i)) := by
    rw [Finset.card_filter, Finset.sum_range_add]
    refine (Nat.add_le_add (Nat.le_zero.mpr (Finset.sum_eq_zero fun v hv => if_neg fun h => ?_))
      (le_refl _)).trans ?_
    · have := h.1.1.2.1
      have := Finset.mem_range.mp hv
      omega
    rw [zero_add, hK, Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi => ?_
    have his := Finset.mem_range.mp hi
    by_cases hct : chainTop (m + i)
    · rw [if_pos hct, if_pos hct.1.1]
      have hsi := hct.1.1
      by_cases hz : a (m + i) = 0
      · rw [if_pos hz]
        omega
      · rw [if_neg hz]
        have hex : ∃ j ∈ K, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) ≠ 0 := by
          by_contra hne
          push_neg at hne
          apply hz
          rw [ha]
          exact Finset.sum_eq_zero hne
        obtain ⟨j, hjK, hjc⟩ := hex
        obtain ⟨hjs, hsj⟩ := (hKm j).1 hjK
        have hjin : m + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs :=
          List.count_pos_iff.mp (Nat.pos_of_ne_zero hjc)
        have hc2 : c j = 2 := by
          rcases hct.2 with ⟨_, hout' | ⟨g, hfg, hspg⟩⟩ | ⟨g, hfg, hng⟩
          · exfalso
            have h0 : R (m + i) = 0 := (hlast i his).2 (by omega)
            have := hcnt j hjs (m + i)
            omega
          · exfalso
            have := huniq i g j hsi hfg.1 hjs hfg.2 hjin
            subst this
            exact hdis _ hsj.1 hspg
          · have := huniq i g j hsi hfg.1 hjs hfg.2 hjin
            subst this
            have h12 := hc1 g hjK
            have : c g ≠ 1 := fun h1 => hng ⟨hsj, by
              rw [Nat.add_sub_cancel_left]
              rw [hc] at h1
              exact h1⟩
            omega
        have : 1 ≤ ab (m + i) := by
          rw [hab]
          beta_reduce
          calc 1 ≤ (if c j = 2 then
                (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) else 0) := by
                rw [if_pos hc2]
                omega
            _ ≤ _ := Finset.single_le_sum (f := fun j => if c j = 2 then
                (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count (m + i) else 0)
                (fun _ _ => Nat.zero_le _) hjK
        omega
    · rw [if_neg hct]
      exact Nat.zero_le _
  refine le_trans hA ?_
  rw [Finset.sum_add_distrib, fB]
  clear_value ext
  omega
