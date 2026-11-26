import Mathlib
import PEqualNP.Defs

-- L-meta-20786: written by our generic row engine (fparse + row_engine). Lower half: a certified frontier search
-- (k-sandhu merged L-meta-927 Run machinery, as packaged in our lb kit); upper half: an explicit circuit.
namespace PEqualNP.Outside.L_meta_20786_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


set_option maxRecDepth 100000 in
def W_ : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [2, 8]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [1, 12]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [0, 16]⟩, ⟨.not, [18]⟩, ⟨.and, [17, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_20786_aux

set_option maxRecDepth 100000 in
open PEqualNP.Outside.L_meta_20786_aux in
theorem PEqualNP.Outside.L_meta_20786 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 16 :=
  ⟨W_, by simp [PEqualNP.MetaComplexity.FanInTwo, W_], by decide, by decide +kernel⟩
