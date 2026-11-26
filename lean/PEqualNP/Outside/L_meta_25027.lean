import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25027_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp


theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem lb {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hM : Monotone2 C)
    (hR : Represents A C) (K : Finset ℕ)
    (hK : ∀ k ∈ K, ∃ (u : Fin n) (v : Fin m) (u' : Fin n) (v' : Fin m), A u v = true ∧
      A u' v' = false ∧ (u.val = k ∨ u = u') ∧ (n + v.val = k ∨ v = v')) :
    K.card ≤ C.size + 1 := by
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hM g hg).2) {C.output}
  have hsub : K ⊆ R' := by
    intro k hk
    by_contra hk'
    obtain ⟨u, v, u', v', h1, h2, h3, h4⟩ := hK k hk
    have e1 := hR u v
    have e2 := hR u' v'
    have hx : (oneEach u v).length = n + m := by simp [oneEach]
    have hyD : ∀ i, ((oneEach u v).set k false).getD i false =
        if i = k then false else (oneEach u v).getD i false := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
      by_cases h : k = i
      · subst h; simp only [ite_true]; split_ifs <;> rfl
      · simp [h, Ne.symm h]
    have eq := hR' (oneEach u v) ((oneEach u v).set k false) hx (by simp [hx])
      (fun i hi => by
        rw [hyD]; split_ifs with h
        · exact absurd (h ▸ hi) hk'
        · rfl) _ (Finset.mem_singleton_self _)
    have := mono C.gates (fun g hg => by simpa using (hM g hg).1) ((oneEach u v).set k false)
      (oneEach u' v') (by simp [oneEach]) (fun i hi => by
        rw [hyD] at hi
        split_ifs at hi with h
        rw [oe] at hi ⊢
        rcases hi with rfl | rfl
        · rcases h3 with h3 | rfl
          · exact absurd h3 h
          · exact Or.inl rfl
        · rcases h4 with h4 | rfl
          · exact absurd h4 h
          · exact Or.inr rfl) C.output
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [e1, h1] at eq
    rw [e2, h2] at this
    exact absurd (this eq.symm) (by simp)
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hc
  simp only [Circuit.size]
  omega

theorem rc : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool), PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun u : Fin n => ∃ u' : Fin n, ∃ v : Fin m, A u v = true ∧ A u' v = false)).card + (Finset.univ.filter (fun v : Fin m => ∃ v' : Fin m, ∃ u : Fin n, A u v = true ∧ A u v' = false)).card ≤ s + 1 := by
  rintro n m s A ⟨C, hM, hs, hR⟩
  have key := lb A C hM hR
    ((Finset.univ.filter (fun u : Fin n => ∃ u' : Fin n, ∃ v : Fin m, A u v = true ∧ A u' v = false)).map
      Fin.valEmbedding ∪
    (Finset.univ.filter (fun v : Fin m => ∃ v' : Fin m, ∃ u : Fin n, A u v = true ∧ A u v' = false)).map
      ⟨fun v : Fin m => n + v.val, fun a b h => Fin.ext (by simpa using h)⟩) (by
    intro k hk
    rw [Finset.mem_union, Finset.mem_map, Finset.mem_map] at hk
    rcases hk with ⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩
    · obtain ⟨u', v, h1, h2⟩ := (Finset.mem_filter.1 hu).2
      exact ⟨u, v, u', v, h1, h2, Or.inl rfl, Or.inr rfl⟩
    · obtain ⟨v', u, h1, h2⟩ := (Finset.mem_filter.1 hv).2
      exact ⟨u, v, u, v', h1, h2, Or.inr rfl, Or.inl rfl⟩)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2 (by
    intro a ha hb
    simp only [Finset.mem_map, Fin.valEmbedding_apply] at ha hb
    obtain ⟨u, -, rfl⟩ := ha
    obtain ⟨v, -, h⟩ := hb
    change n + v.val = u.val at h
    have := u.isLt
    omega)), Finset.card_map, Finset.card_map] at key
  omega

end PEqualNP.Outside.L_meta_25027_aux

theorem PEqualNP.Outside.L_meta_25027 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide ((v : ℕ) < ![6, 6, 4, 4, 2, 2] u)) 7 ∧ ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide ((v : ℕ) < ![6, 6, 4, 4, 2, 2] u)) s → 7 ≤ s :=
  ⟨⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩, by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩,
    fun s h => Nat.succ_le_succ_iff.1 (le_trans (by decide) (PEqualNP.Outside.L_meta_25027_aux.rc 6 6 s _ h))⟩
