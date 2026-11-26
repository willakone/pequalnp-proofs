import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19059 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 22 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16, (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val := by
  refine ⟨⟨[⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [27, 28]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [29, 32]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [29, 36]⟩], 0⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro v
    fin_cases v
    · exact ⟨37, by decide⟩
    · exact ⟨33, by decide⟩
    · exact ⟨26, by decide⟩
    · exact ⟨22, by decide⟩
