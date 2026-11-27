import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_868 : let V := Fin 3 × Fin 3
let pairs : Finset (V × V) :=
  {((0,1),(0,2)), ((1,1),(1,2)), ((2,1),(2,2)), ((0,0),(1,0))}
let hits := fun (e : Finset V) => ∃ ab ∈ pairs, ab.1 ∈ e ∧ ab.2 ∈ e
let triple := fun (i : Fin 3) => (Finset.univ : Finset (Fin 3)).image (fun t => (i,t))
let clauseEdge := fun (s : Fin 3 → Bool) =>
  (Finset.univ : Finset V).filter (fun v => v.2 = 0 ∨ v.2 = (if s v.1 then 1 else 2))
(∀ a ∈ pairs, a.1 ≠ a.2) ∧
  (∀ a ∈ pairs, ∀ b ∈ pairs, a ≠ b →
    a.1 ≠ b.1 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2) ∧
  (∀ i, hits (triple i)) ∧ (∀ s, hits (clauseEdge s)) ∧
  ¬ ∃ x : Fin 3 → Bool, ∀ s : Fin 3 → Bool, ∃ i, x i = s i := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 100000 in
  (intros
   try subst_vars
   repeat' apply And.intro
   all_goals first
     | decide +kernel
     | simp [PEqualNP.MetaComplexity.Monotone2]
     | (simp [PEqualNP.MetaComplexity.Monotone2]; decide))
