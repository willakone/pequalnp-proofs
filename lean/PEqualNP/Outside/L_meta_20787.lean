import Mathlib
import PEqualNP.Defs

-- L-meta-20787: written by our generic row engine (fparse + row_engine). Lower half: a certified frontier search
-- (k-sandhu merged L-meta-927 Run machinery, as packaged in our lb kit); upper half: an explicit circuit.
namespace PEqualNP.Outside.L_meta_20787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


set_option maxRecDepth 100000 in
def W_ : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [4, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [3, 9]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [2, 13]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [1, 17]⟩, ⟨.and, [1, 17]⟩, ⟨.not, [19]⟩, ⟨.and, [18, 20]⟩, ⟨.or, [0, 21]⟩, ⟨.and, [0, 21]⟩, ⟨.not, [23]⟩, ⟨.and, [22, 24]⟩], 25⟩

end PEqualNP.Outside.L_meta_20787_aux

set_option maxRecDepth 100000 in
open PEqualNP.Outside.L_meta_20787_aux in
theorem PEqualNP.Outside.L_meta_20787 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (7608434000728254870 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 20 :=
  ⟨W_, by simp [PEqualNP.MetaComplexity.FanInTwo, W_], by decide, by decide +kernel⟩
