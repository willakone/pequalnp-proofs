import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19359_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_19359_aux

open PEqualNP.Outside.L_meta_19359_aux in
theorem PEqualNP.Outside.L_meta_19359 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (u.val = 1 ∧ ¬ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (2 ≤ u.val ∧ v.val + 1 ≠ n))) C := by
  intro n hn
  refine ⟨⟨[⟨.and, [1, n + (n - 2)]⟩, ⟨.or, [0, n + n]⟩, ⟨.or, [n + (n - 1), n + n + 1]⟩,
    ⟨.or, [n + (n - 2), n + (n - 1)]⟩, ⟨.not, [n + n + 2]⟩, ⟨.and, [0, n + n + 3]⟩,
    ⟨.or, [n + n + 4, n + n + 5]⟩], n + n + 6⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using gL u ⟨0, by omega⟩ v
    have h1 : (PEqualNP.Represents.oneEach u v).getD 1 false = decide (u.val = 1) := by
      simpa [Fin.ext_iff] using gL u ⟨1, by omega⟩ v
    have h2 : (PEqualNP.Represents.oneEach u v).getD (n + (n - 2)) false = decide (v.val + 2 = n) := by
      have := gR u v ⟨n - 2, by omega⟩
      simp only [Fin.ext_iff] at this
      rw [this]; congr 1; apply propext; omega
    have h3 : (PEqualNP.Represents.oneEach u v).getD (n + (n - 1)) false = decide (v.val + 1 = n) := by
      have := gR u v ⟨n - 1, by omega⟩
      simp only [Fin.ext_iff] at this
      rw [this]; congr 1; apply propext; omega
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 h1 h2 h3
    have i0 : 0 < l.length := by omega
    have i2 : n + (n - 2) < l.length := by omega
    have i3 : n + (n - 1) < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append,
      List.nil_append, List.getElem?_append_left i0,
      List.getElem?_append_left i2, List.getElem?_append_left i3, h0, h1, h2, h3,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    by_cases a : u.val = 0 <;> by_cases b : u.val = 1 <;> by_cases c : v.val + 2 = n <;>
      by_cases d : v.val + 1 = n <;> simp [a, b, c, d] <;> omega
