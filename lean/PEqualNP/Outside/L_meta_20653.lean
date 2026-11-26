import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20653 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7406592 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 14] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
