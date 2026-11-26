import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20709 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31917056 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 15] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit), by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩
