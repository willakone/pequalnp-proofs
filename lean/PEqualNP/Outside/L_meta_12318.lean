import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12318_aux

theorem poly_le (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [one_pow, mul_one]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem exp_beats (M d K : ℕ) : ∃ k, K ≤ k ∧ 1 ≤ k ∧ M * (2 * k) ^ d ≤ 2 ^ k := by
  have hT := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) one_lt_two
  have hB : (0 : ℝ) < 1 / ((M : ℝ) * 2 ^ d + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hB))
  refine ⟨max K (max N 1), le_max_left _ _, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  set k := max K (max N 1)
  have hk := hN k (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hpos : (0 : ℝ) < (M : ℝ) * 2 ^ d + 1 := by positivity
  rw [div_lt_div_iff₀ h2 hpos, one_mul] at hk
  have hR : ((M * (2 * k) ^ d : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast hR

theorem len_eq (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (x : List Bool) (k : ℕ) :
    ∀ m, m = k → PEqualNP.Represents.adjFun (k := m) (l := m) (A m) (fun i => x.getD i false) =
      PEqualNP.Represents.adjFun (k := k) (l := k) (A k) (fun i => x.getD i false) := by
  intro m hm
  subst hm
  rfl


theorem exp_ev (M d : ℕ) : ∃ N, ∀ k, N ≤ k → M * (2 * k) ^ d ≤ 2 ^ k := by
  have hT := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) one_lt_two
  have hB : (0 : ℝ) < 1 / ((M : ℝ) * 2 ^ d + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hB))
  refine ⟨N, fun k hk0 => ?_⟩
  have hk := hN k hk0
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hpos : (0 : ℝ) < (M : ℝ) * 2 ^ d + 1 := by positivity
  rw [div_lt_div_iff₀ h2 hpos, one_mul] at hk
  have hR : ((M * (2 * k) ^ d : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast hR

theorem main18 (hBr : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2)))
    (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ) (hd : 0 < d)
    (hA : ∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d))
    (hNP : {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP) :
    ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hsub
  obtain ⟨p, hp⟩ := hsub hNP
  obtain ⟨N1, hN1⟩ := exp_ev (4 * d * p.eval 1 * 2 ^ p.natDegree) p.natDegree
  obtain ⟨N2, hN2⟩ := exp_ev (4 * d) 1
  obtain ⟨m, hm⟩ : ∃ m, m = K + 1 + N1 + N2 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m + m := ⟨_, rfl⟩
  have hKk : K ≤ k := by omega
  obtain ⟨C, hg, hs, hdec⟩ := hp (k + k)
  have hfun : PEqualNP.MetaComplexity.HasCircuitSize (k + k) (PEqualNP.Represents.adjFun (A k)) (p.eval ((k + k : ℕ) : ℕ)) := by
    refine ⟨C, hg, hs, fun y => ?_⟩
    have hlen : (List.ofFn y).length = k + k := List.length_ofFn
    have hd := hdec (List.ofFn y) hlen
    have hm : (List.ofFn y).length / 2 = k := by rw [hlen]; omega
    have hy : (fun i : Fin (k + k) => (List.ofFn y).getD i false) = y := by
      funext i
      simp [List.getD_eq_getElem?_getD]
    apply Bool.eq_iff_iff.mpr
    rw [hd]
    change (Even (List.ofFn y).length ∧ _) ↔ _
    rw [len_eq A (List.ofFn y) k _ hm, hy, hlen]
    exact ⟨fun h => h.2, fun h => ⟨⟨k, rfl⟩, h⟩⟩
  obtain ⟨D, hDm, hDs, hDr⟩ := hBr k k _ (A k) hfun
  apply hA k hKk
  refine ⟨D, hDm, le_trans hDs ?_, hDr⟩
  have hpe := poly_le p (k + k) (by omega)
  have hh : (k + 1) / 2 = m := by omega
  have hP : 2 ^ k = 2 ^ m * 2 ^ m := by rw [hk, pow_add]
  have hpow : (k + k) ^ p.natDegree = 2 ^ p.natDegree * (2 * m) ^ p.natDegree := by
    rw [← mul_pow]; congr 1; omega
  have h1 := hN1 m (by omega)
  have h2 := hN2 m (by omega)
  rw [pow_one] at h2
  rw [hh]
  generalize p.eval ((k + k : ℕ) : ℕ) = s at hpe ⊢
  have hP1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hs4 : 4 * d * s ≤ 2 ^ m := by
    calc 4 * d * s ≤ 4 * d * (p.eval 1 * (k + k) ^ p.natDegree) := Nat.mul_le_mul_left _ hpe
      _ = 4 * d * p.eval 1 * 2 ^ p.natDegree * (2 * m) ^ p.natDegree := by rw [hpow]; ring
      _ ≤ 2 ^ m := h1
  have ha : 4 * d * (2 * m) * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ h2
  have hb : 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.le_mul_of_pos_left _ hP1
  have key : (2 * s + 2 * k * 2 ^ m) * d ≤ 2 ^ k := by
    rw [hP, hk]
    nlinarith
  have hdiv : 2 * s + 2 * k * 2 ^ m ≤ 2 ^ k / d := (Nat.le_div_iff_mul_le hd).2 key
  nlinarith

end PEqualNP.Outside.L_meta_12318_aux

theorem PEqualNP.Outside.L_meta_12318 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  exact PEqualNP.Outside.L_meta_12318_aux.main18
