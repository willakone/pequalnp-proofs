import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29908_aux

open PEqualNP.CircuitLowerBounds

def step (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun j => wires.getD j false)]

def fixed : List Bool := [true, false, false, true, false, false]

theorem head_preserved (gates : List Gate) (bit : Bool) (rest : List Bool) :
    (gates.foldl step (bit :: rest)).getD 0 false = bit := by
  induction gates generalizing rest with
  | nil => rfl
  | cons gate gates ih =>
    exact ih (rest ++ [gate.op.eval (gate.inputs.map fun j => (bit :: rest).getD j false)])

theorem same_tail (gates : List Gate)
    (hread : ∀ gate ∈ gates, 0 ∉ gate.inputs ∨ (gate.op = GateOp.or ∧ 4 ∈ gate.inputs)) (extra : List Bool) :
    ∃ result, gates.foldl step (false :: (fixed ++ extra)) = false :: result ∧
      gates.foldl step (true :: (fixed ++ extra)) = true :: result := by
  induction gates generalizing extra with
  | nil => exact ⟨fixed ++ extra, rfl, rfl⟩
  | cons gate gates ih =>
    have hval : gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false) =
        gate.op.eval (gate.inputs.map fun j => (true :: (fixed ++ extra)).getD j false) := by
      rcases hread gate (by simp) with h0 | ⟨hop, hw⟩
      · congr 1
        apply List.map_congr_left
        intro j hj
        cases j with
        | zero => exact (h0 hj).elim
        | succ j => rfl
      · rw [hop]
        have h1 : ∀ bit : Bool, GateOp.or.eval (gate.inputs.map fun j => (bit :: (fixed ++ extra)).getD j false) = true :=
          fun bit => List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨4, hw, rfl⟩, rfl⟩
        rw [h1 false, h1 true]
    obtain ⟨result, hlo, hhi⟩ := ih (fun g hg => hread g (by simp [hg]))
      (extra ++ [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])
    refine ⟨result, ?_, ?_⟩
    · rw [List.foldl_cons]
      have hstep : step (false :: (fixed ++ extra)) gate = false :: (fixed ++ (extra ++
          [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])) := by
        simp only [step, List.cons_append, List.append_assoc]
      rw [hstep]
      exact hlo
    · rw [List.foldl_cons]
      have hstep : step (true :: (fixed ++ extra)) gate = true :: (fixed ++ (extra ++
          [gate.op.eval (gate.inputs.map fun j => (false :: (fixed ++ extra)).getD j false)])) := by
        simp only [step, List.cons_append, List.append_assoc, hval]
      rw [hstep]
      exact hhi

def input (bit : Bool) (j : Fin 7) : Bool := (bit :: fixed).getD j.val false

end PEqualNP.Outside.L_meta_29908_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29908_aux in
theorem PEqualNP.Outside.L_meta_29908 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true) := by
  rintro ⟨⟨gates, out⟩, i, _, _, _, _, correct, _, hUnique, hOp, _, _, _, hReadW, _, _, _⟩
  have hread : ∀ gate ∈ gates, 0 ∉ gate.inputs ∨ (gate.op = GateOp.or ∧ 4 ∈ gate.inputs) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    by_cases h0 : 0 ∈ gates[j].inputs
    · have e : (⟨j, hj⟩ : Fin gates.length) = i := hUnique ⟨j, hj⟩ h0
      subst e
      exact Or.inr ⟨hOp, hReadW⟩
    · exact Or.inl h0
  cases out with
  | zero =>
    have h := correct (fun j => decide (j = 0))
    change (gates.foldl step [true, false, false, false, false, false, false]).getD 0 false = false at h
    rw [head_preserved] at h
    contradiction
  | succ out =>
    obtain ⟨result, hfalse, htrue⟩ := same_tail gates hread []
    have hlo := correct (input false)
    have hhi := correct (input true)
    change (gates.foldl step (false :: (fixed ++ []))).getD (out + 1) false = false at hlo
    change (gates.foldl step (true :: (fixed ++ []))).getD (out + 1) false = true at hhi
    rw [hfalse] at hlo
    rw [htrue] at hhi
    change result.getD out false = false at hlo
    change result.getD out false = true at hhi
    rw [hlo] at hhi
    contradiction
