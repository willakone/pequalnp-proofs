import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5641 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit).size = 9 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (4699 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 100000 in
  (intros
   try subst_vars
   repeat' apply And.intro
   all_goals first
     | decide +kernel
     | simp [PEqualNP.MetaComplexity.Monotone2]
     | (simp [PEqualNP.MetaComplexity.Monotone2]; decide))
