import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25307

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

def mg (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

theorem sim (s : ℕ → ℕ) (N L : ℕ) (gs : List Gate) : ∀ W Y : List Bool,
    W.length = Y.length + L → N ≤ Y.length → (∀ i, N ≤ i → s i = i + L) →
    (∀ i, i < N → s i < W.length ∨ W.length + gs.length ≤ s i) →
    (∀ i, W.getD (s i) false = Y.getD i false) →
    ∀ i, ((gs.map (mg s)).foldl stp W).getD (s i) false = (gs.foldl stp Y).getD i false := by
  induction gs with
  | nil => intro W Y _ _ _ _ h5; simpa using h5
  | cons g gs ih =>
    intro W Y h1 h2 h3 h4 h5
    simp only [List.map_cons, List.foldl_cons]
    have eW : (stp W (mg s g)).length = W.length + 1 := by simp [stp]
    have eY : (stp Y g).length = Y.length + 1 := by simp [stp]
    apply ih
    · rw [eW, eY]; omega
    · rw [eY]; omega
    · exact h3
    · intro i hi
      have := h4 i hi
      simp only [List.length_cons] at this
      rw [eW]; omega
    · intro i
      simp only [stp]
      rw [getD_snoc, getD_snoc]
      by_cases hi : i < N
      · rcases h4 i hi with h | h
        · rw [if_pos h, if_pos (by omega : i < Y.length)]; exact h5 i
        · simp only [List.length_cons] at h
          have e1 := h5 i
          rw [getD_ge W (s i) (by omega)] at e1
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact e1
      · have hs := h3 i (by omega)
        rcases lt_trichotomy i Y.length with h | h | h
        · rw [if_pos (by omega), if_pos h]; exact h5 i
        · rw [hs, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos h]
          simp only [mg, List.map_map, Function.comp_def]
          congr 1
          apply List.map_congr_left
          intro j _
          exact h5 j
        · rw [hs, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def sh (N a b B : ℕ) (i : ℕ) : ℕ := if i = a then N else if i = b then B else if i < N then i else i + 1

def mc (C : Circuit) (N a b : ℕ) : Circuit :=
  ⟨⟨GateOp.or, [a, b]⟩ :: C.gates.map (mg (sh N a b (N + 1 + C.gates.length))),
    sh N a b (N + 1 + C.gates.length) C.output⟩

theorem mc_size (C : Circuit) (N a b : ℕ) : (mc C N a b).size = C.size + 1 := by
  simp [mc, Circuit.size]

theorem mc_fan (C : Circuit) (N a b : ℕ) (hF : FanInTwo C) : FanInTwo (mc C N a b) := by
  unfold FanInTwo at hF ⊢
  intro g hg
  simp only [mc, List.mem_cons, List.mem_map] at hg
  rcases hg with rfl | ⟨g0, hg0, rfl⟩
  · simp
  · have := hF g0 hg0
    simpa [mg] using this

theorem merge (C : Circuit) (N a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) (X Y : List Bool)
    (hX : X.length = N) (hY : Y.length = N)
    (h1 : Y.getD a false = (X.getD a false || X.getD b false)) (h2 : Y.getD b false = false)
    (h3 : ∀ i, i < N → i ≠ a → i ≠ b → Y.getD i false = X.getD i false) :
    (mc C N a b).eval X = C.eval Y := by
  have hsN : ∀ i, N ≤ i → sh N a b (N + 1 + C.gates.length) i = i + 1 := by
    intro i hi; simp only [sh]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  show ((C.gates.map (mg (sh N a b (N + 1 + C.gates.length)))).foldl stp
      (stp X ⟨GateOp.or, [a, b]⟩)).getD (sh N a b (N + 1 + C.gates.length) C.output) false =
    (C.gates.foldl stp Y).getD C.output false
  have eW : (stp X ⟨GateOp.or, [a, b]⟩).length = N + 1 := by simp [stp, hX]
  apply sim _ N 1 C.gates _ Y
  · rw [eW, hY]
  · omega
  · exact hsN
  · intro i hi
    rw [eW]
    simp only [sh]
    split_ifs <;> omega
  · intro i
    simp only [stp]
    rw [getD_snoc, hX]
    by_cases hia : i = a
    · subst hia
      rw [show sh N i b (N + 1 + C.gates.length) i = N by simp [sh]]
      rw [if_neg (by omega), if_pos rfl, h1]
      simp [GateOp.eval]
    · by_cases hib : i = b
      · subst hib
        rw [show sh N a i (N + 1 + C.gates.length) i = N + 1 + C.gates.length by simp [sh, hia]]
        rw [if_neg (by omega), if_neg (by omega), h2]
      · by_cases hiN : i < N
        · rw [show sh N a b (N + 1 + C.gates.length) i = i by simp [sh, hia, hib, hiN]]
          rw [if_pos hiN]; exact (h3 i hiN hia hib).symm
        · rw [hsN i (by omega), if_neg (by omega), if_neg (by omega)]
          exact (getD_ge Y i (by omega)).symm

theorem lside (n m : ℕ) (A : Fin n → Fin m → Bool) (u0 : Fin n) (Q : Fin m → Prop) :
    ∀ k (U : Finset (Fin n)) (C : Circuit), U.card ≤ k + 1 → u0 ∈ U →
      (∀ u ∈ U, ∀ v, A u v = A u0 v) → FanInTwo C →
      (∀ u v, (u ∉ U ∨ u = u0) → Q v → C.eval (oneEach u v) = A u v) →
      ∃ C2 : Circuit, FanInTwo C2 ∧ C2.size ≤ C.size + (U.card - 1) ∧
        ∀ u v, Q v → C2.eval (oneEach u v) = A u v := by
  intro k
  induction k with
  | zero =>
    intro U C hc hu0 _ hF hC
    refine ⟨C, hF, by omega, fun u v hv => hC u v ?_ hv⟩
    by_cases hu : u ∈ U
    · exact Or.inr (Finset.card_le_one.1 hc u hu u0 hu0)
    · exact Or.inl hu
  | succ k ih =>
    intro U C hc hu0 hrow hF hC
    by_cases h1 : U.card ≤ 1
    · refine ⟨C, hF, by omega, fun u v hv => hC u v ?_ hv⟩
      by_cases hu : u ∈ U
      · exact Or.inr (Finset.card_le_one.1 h1 u hu u0 hu0)
      · exact Or.inl hu
    · obtain ⟨u1, hu1, hne⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) u0
      have hval : u0.val ≠ u1.val := fun h => hne (Fin.ext h).symm
      have hC' : ∀ u v, (u ∉ U.erase u1 ∨ u = u0) → Q v →
          (mc C (n + m) u0.val u1.val).eval (oneEach u v) = A u v := by
        intro u v hu hv
        have := u0.isLt
        have := u1.isLt
        have := u.isLt
        have := v.isLt
        by_cases h : u = u1
        · rw [h]
          rw [merge C (n + m) _ _ (by omega) (by omega) hval (oneEach u1 v) (oneEach u0 v)
            (oe_len _ _) (oe_len _ _) ?_ ?_ ?_]
          · rw [hC u0 v (Or.inr rfl) hv, hrow u1 hu1 v]
          · apply Bool.eq_iff_iff.2
            simp only [Bool.or_eq_true, oe]
            simp
          · rw [← Bool.not_eq_true, oe]; omega
          · intro i _ h1 h2
            apply Bool.eq_iff_iff.2
            rw [oe, oe]
            constructor <;> intro h <;> omega
        · have hv' : u.val ≠ u1.val := fun e => h (Fin.ext e)
          rw [merge C (n + m) _ _ (by omega) (by omega) hval (oneEach u v) (oneEach u v)
            (oe_len _ _) (oe_len _ _) ?_ ?_ ?_]
          · refine hC u v ?_ hv
            rcases hu with hu | hu
            · left; intro hU; exact hu (Finset.mem_erase.2 ⟨h, hU⟩)
            · right; exact hu
          · apply Bool.eq_iff_iff.2
            simp only [Bool.or_eq_true, oe]
            constructor <;> intro h <;> omega
          · rw [← Bool.not_eq_true, oe]; omega
          · intro i _ _ _; rfl
      obtain ⟨C2, hF2, hs2, hR2⟩ := ih (U.erase u1) (mc C (n + m) u0.val u1.val)
        (by rw [Finset.card_erase_of_mem hu1]; omega) (Finset.mem_erase.2 ⟨hne.symm, hu0⟩)
        (fun u hu v => hrow u (Finset.mem_of_mem_erase hu) v) (mc_fan _ _ _ _ hF) hC'
      refine ⟨C2, hF2, ?_, hR2⟩
      rw [Finset.card_erase_of_mem hu1, mc_size] at hs2
      omega

theorem rside (n m : ℕ) (A : Fin n → Fin m → Bool) (v0 : Fin m) :
    ∀ k (W : Finset (Fin m)) (C : Circuit), W.card ≤ k + 1 → v0 ∈ W →
      (∀ v ∈ W, ∀ u, A u v = A u v0) → FanInTwo C →
      (∀ u v, (v ∉ W ∨ v = v0) → C.eval (oneEach u v) = A u v) →
      ∃ C2 : Circuit, FanInTwo C2 ∧ C2.size ≤ C.size + (W.card - 1) ∧ Represents A C2 := by
  intro k
  induction k with
  | zero =>
    intro W C hc hv0 _ hF hC
    refine ⟨C, hF, by omega, ?_⟩
    intro u v
    refine hC u v ?_
    by_cases hv : v ∈ W
    · exact Or.inr (Finset.card_le_one.1 hc v hv v0 hv0)
    · exact Or.inl hv
  | succ k ih =>
    intro W C hc hv0 hcol hF hC
    by_cases h1 : W.card ≤ 1
    · refine ⟨C, hF, by omega, ?_⟩
      intro u v
      refine hC u v ?_
      by_cases hv : v ∈ W
      · exact Or.inr (Finset.card_le_one.1 h1 v hv v0 hv0)
      · exact Or.inl hv
    · obtain ⟨v1, hv1, hne⟩ := Finset.exists_mem_ne (by omega : 1 < W.card) v0
      have hval : v0.val ≠ v1.val := fun h => hne (Fin.ext h).symm
      have hval2 : n + v0.val ≠ n + v1.val := by omega
      have hC' : ∀ u v, (v ∉ W.erase v1 ∨ v = v0) →
          (mc C (n + m) (n + v0.val) (n + v1.val)).eval (oneEach u v) = A u v := by
        intro u v hv
        have := v0.isLt
        have := v1.isLt
        have := u.isLt
        have := v.isLt
        by_cases h : v = v1
        · rw [h]
          rw [merge C (n + m) _ _ (by omega) (by omega) hval2 (oneEach u v1) (oneEach u v0)
            (oe_len _ _) (oe_len _ _) ?_ ?_ ?_]
          · rw [hC u v0 (Or.inr rfl), hcol v1 hv1 u]
          · apply Bool.eq_iff_iff.2
            simp only [Bool.or_eq_true, oe]
            simp
          · rw [← Bool.not_eq_true, oe]; omega
          · intro i _ h1 h2
            apply Bool.eq_iff_iff.2
            rw [oe, oe]
            constructor <;> intro h <;> omega
        · have hv' : v.val ≠ v1.val := fun e => h (Fin.ext e)
          rw [merge C (n + m) _ _ (by omega) (by omega) hval2 (oneEach u v) (oneEach u v)
            (oe_len _ _) (oe_len _ _) ?_ ?_ ?_]
          · refine hC u v ?_
            rcases hv with hv | hv
            · left; intro hW; exact hv (Finset.mem_erase.2 ⟨h, hW⟩)
            · right; exact hv
          · apply Bool.eq_iff_iff.2
            simp only [Bool.or_eq_true, oe]
            constructor <;> intro h <;> omega
          · rw [← Bool.not_eq_true, oe]; omega
          · intro i _ _ _; rfl
      obtain ⟨C2, hF2, hs2, hR2⟩ := ih (W.erase v1) (mc C (n + m) (n + v0.val) (n + v1.val))
        (by rw [Finset.card_erase_of_mem hv1]; omega) (Finset.mem_erase.2 ⟨hne.symm, hv0⟩)
        (fun v hv u => hcol v (Finset.mem_of_mem_erase hv) u) (mc_fan _ _ _ _ hF) hC'
      refine ⟨C2, hF2, ?_, hR2⟩
      rw [Finset.card_erase_of_mem hv1, mc_size] at hs2
      omega

theorem agree (S : ℕ → Prop) (gs : List Gate) : ∀ W Y : List Bool, W.length = Y.length →
    (∀ k (hk : k < gs.length), S (W.length + k) → ∀ i ∈ (gs[k]).inputs, i < W.length + k → S i) →
    (∀ i, S i → W.getD i false = Y.getD i false) →
    ∀ i, S i → (gs.foldl stp W).getD i false = (gs.foldl stp Y).getD i false := by
  induction gs with
  | nil => intro W Y _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro W Y h1 h2 h3
    simp only [List.foldl_cons]
    have eW : (stp W g).length = W.length + 1 := by simp [stp]
    have eY : (stp Y g).length = Y.length + 1 := by simp [stp]
    apply ih
    · rw [eW, eY, h1]
    · intro k hk hS i hi hlt
      rw [eW] at hS hlt
      exact h2 (k + 1) (by simp; omega) (by rwa [show W.length + (k + 1) = W.length + 1 + k by omega])
        i (by simpa using hi) (by omega)
    · intro i hi
      simp only [stp]
      rw [getD_snoc, getD_snoc, ← h1]
      split_ifs with ha hb
      · exact h3 i hi
      · congr 1
        apply List.map_congr_left
        intro j hj
        by_cases hjl : j < W.length
        · exact h3 j (h2 0 (by simp) (by subst hb; simpa using hi) j (by simpa using hj) (by omega))
        · rw [getD_ge W j (by omega), getD_ge Y j (by omega)]
      · rfl

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs ∧ (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

theorem gd (gs : List Gate) {k : ℕ} (hk : k < gs.length) (d : Gate) : gs.getD k d = gs[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

end PEqualNP.Outside.L_meta_25307

open PEqualNP.Outside.L_meta_25307 PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.EdgeOwnership in
theorem PEqualNP.Outside.L_meta_25307 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → PEqualNP.MetaComplexity.FanInTwo C → (∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → (∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size ≤ C.size + (U.card - 1) + (W.card - 1) ∧ PEqualNP.Represents.Represents A C2) ∧ ((∀ w : ℕ, ((∃ u ∈ U, w = u.val) ∨ (∃ v ∈ W, w = n + v.val)) → C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → PEqualNP.Represents.Represents A C) := by
  intro n m A U W u0 v0 C hu0 hv0 hrow hcol hF hC
  refine ⟨?_, ?_⟩
  · obtain ⟨C1, hF1, hs1, hR1⟩ := lside n m A u0 (fun v => v ∉ W ∨ v = v0) U.card U C
      (by omega) hu0 hrow hF (fun u v hu hv => hC u v hu hv)
    obtain ⟨C2, hF2, hs2, hR2⟩ := rside n m A v0 W.card W C1 (by omega) hv0 hcol hF1
      (fun u v hv => hR1 u v hv)
    exact ⟨C2, hF2, by omega, hR2⟩
  · intro H
    intro u v
    obtain ⟨u', hu'1, hu'2, hu'3⟩ : ∃ u' : Fin n, (u' ∉ U ∨ u' = u0) ∧ A u' = A u ∧
        (u' = u ∨ (u ∈ U ∧ u' = u0)) := by
      by_cases hu : u ∈ U
      · exact ⟨u0, Or.inr rfl, funext fun v => (hrow u hu v).symm, Or.inr ⟨hu, rfl⟩⟩
      · exact ⟨u, Or.inl hu, rfl, Or.inl rfl⟩
    obtain ⟨v', hv'1, hv'2, hv'3⟩ : ∃ v' : Fin m, (v' ∉ W ∨ v' = v0) ∧ (∀ u, A u v' = A u v) ∧
        (v' = v ∨ (v ∈ W ∧ v' = v0)) := by
      by_cases hv : v ∈ W
      · exact ⟨v0, Or.inr rfl, fun u => (hcol v hv u).symm, Or.inr ⟨hv, rfl⟩⟩
      · exact ⟨v, Or.inl hv, fun u => rfl, Or.inl rfl⟩
    rw [show A u v = A u' v' by rw [hv'2, hu'2], ← hC u' v' hu'1 hv'1]
    unfold Circuit.eval Circuit.wires
    change (C.gates.foldl stp _).getD _ _ = (C.gates.foldl stp _).getD _ _
    refine agree (fun i => (i < n + m ∧ ¬ ((∃ u ∈ U, i = u.val) ∨ (∃ v ∈ W, i = n + v.val))) ∨
      (n + m ≤ i ∧ (C.output = i ∨ (n + m ≤ C.output ∧
        InCone (n + m) C (i - (n + m)) (C.output - (n + m)))))) C.gates _ _
      (by rw [oe_len, oe_len]) ?_ ?_ C.output ?_
    · intro k hk hS i hi hlt
      rw [oe_len] at hS hlt
      have hcond : C.output = n + m + k ∨
          (n + m ≤ C.output ∧ InCone (n + m) C k (C.output - (n + m))) := by
        rcases hS with ⟨h, _⟩ | ⟨_, h | ⟨h1, h2⟩⟩
        · omega
        · exact Or.inl h
        · rw [show n + m + k - (n + m) = k by omega] at h2
          exact Or.inr ⟨h1, h2⟩
      by_cases hiN : i < n + m
      · left
        refine ⟨hiN, fun hT => (H i hT).2 k hk hcond ?_⟩
        rw [gd C.gates hk]
        exact hi
      · right
        refine ⟨by omega, Or.inr ⟨?_, ?_⟩⟩
        · rcases hcond with h | h
          · omega
          · exact h.1
        · have hik : InCone (n + m) C (i - (n + m)) k := (inCone_iff _ _ _ _).2
            ⟨hk, i - (n + m), by omega, by
              rw [show n + m + (i - (n + m)) = i by omega, gd C.gates hk]; exact hi, Or.inl rfl⟩
          rcases hcond with h | h
          · rw [h, show n + m + k - (n + m) = k by omega]; exact hik
          · exact inCone_trans _ _ _ _ hik _ h.2
    · intro i hS
      rcases hS with ⟨hiN, hT⟩ | ⟨hiN, _⟩
      · apply Bool.eq_iff_iff.2
        rw [oe, oe]
        push Not at hT
        obtain ⟨hT1, hT2⟩ := hT
        have a1 : i = u.val ↔ i = u'.val := by
          rcases hu'3 with h | ⟨h1, h2⟩
          · rw [h]
          · rw [h2]
            have := hT1 u h1
            have := hT1 u0 hu0
            constructor <;> intro h <;> omega
        have a2 : i = n + v.val ↔ i = n + v'.val := by
          rcases hv'3 with h | ⟨h1, h2⟩
          · rw [h]
          · rw [h2]
            have := hT2 v h1
            have := hT2 v0 hv0
            constructor <;> intro h <;> omega
        rw [a1, a2]
      · rw [getD_ge _ i (by rw [oe_len]; omega), getD_ge _ i (by rw [oe_len]; omega)]
    · by_cases ho : C.output < n + m
      · exact Or.inl ⟨ho, fun hT => (H _ hT).1 rfl⟩
      · exact Or.inr ⟨by omega, Or.inl rfl⟩
