import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5789 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).size = 8 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (990 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 100000 in
  (intros
   try subst_vars
   repeat' apply And.intro
   all_goals first
     | decide +kernel
     | simp [PEqualNP.MetaComplexity.Monotone2]
     | (simp [PEqualNP.MetaComplexity.Monotone2]; decide))
