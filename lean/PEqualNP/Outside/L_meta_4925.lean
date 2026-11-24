import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4925 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 6 C ∧ C.size = 12 ∧
  (∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = decide (∃ e ∈ ([(0, 3), (1, 4), (0, 5), (1, 5), (2, 3), (2, 4)] : List (Fin 6 × Fin 6)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 3), (1, 4), (0, 5), (1, 5), (2, 3), (2, 4)] : List (Fin 6 × Fin 6)), PEqualNP.Core.ReadTwiceAt 6 C (C.output - 6) e.1 e.2 ↔ e ∈ ([] : List (Fin 6 × Fin 6))) := by
  intro C hC
  subst hC
  refine ⟨by decide, rfl, ?_, ?_⟩
  · intro x
    revert x
    set_option maxRecDepth 100000 in decide
  · set_option maxRecDepth 100000 in decide
