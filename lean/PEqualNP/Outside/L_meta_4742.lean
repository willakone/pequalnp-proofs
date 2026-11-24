import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4742

namespace KCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩


open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
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

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

open PEqualNP.FactorSubst

lemma orC_mem {n : ℕ} {C : Circuit} {c h : ℕ} :
    h ∈ orClosure n C c ↔ h < C.gates.length ∧ h ≠ c ∧ OrReaches n C (n + h) c := by
  unfold orClosure
  rw [Finset.mem_filter, Finset.mem_range]

lemma orC_gt {n : ℕ} {C : Circuit} {c h : ℕ} (hh : h ∈ orClosure n C c) : c < h := by
  obtain ⟨_, hne, hr⟩ := orC_mem.mp hh
  have := orStep_le (orReaches_reach c _ hr).1
  omega

lemma orC_or {n : ℕ} {C : Circuit} {c h : ℕ} (hh : h ∈ orClosure n C c) :
    (gateAt C h).op = GateOp.or := by
  obtain ⟨_, hne, hr⟩ := orC_mem.mp hh
  rcases ((orReaches_iff n C h c).mp hr).2 with h1 | ⟨hop, _⟩
  · exact absurd h1.symm hne
  · exact hop

lemma reach_self {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩

lemma reach_val {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w g : ℕ}
    (hr : OrReaches n C w g) (hv : val C x (n + g) = true) : val C x w = true :=
  orStep_up hx (orReaches_reach g w hr).1 hv

lemma ins_reach {n : ℕ} {C : Circuit} {c w : ℕ} (hc : c < C.gates.length)
    (hw : w ∈ insert c (orClosure n C c)) : OrReaches n C (n + w) c := by
  rcases Finset.mem_insert.mp hw with rfl | h
  · exact reach_self hc
  · exact (orC_mem.mp h).2.2

lemma mem_live {n : ℕ} {C : Circuit} {j : ℕ} : j ∈ liveGates n C ↔
    j < C.gates.length ∧ n ≤ C.output ∧ (j = C.output - n ∨ InCone n C j (C.output - n)) := by
  unfold liveGates
  rw [Finset.mem_filter, Finset.mem_range]

/-! ## Cone order and transitivity (3756) -/

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
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

/-- A gate input that is a gate wire puts that gate (and its cone) in the cone. -/
lemma cone_of_input {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (X : ℕ)
    (hX : X < C.gates.length) (q g : ℕ) (hq : q ∈ (gateAt C X).inputs) (hn : n ≤ q)
    (hg : g = q - n ∨ InCone n C g (q - n)) : InCone n C g X := by
  have e : q < n + X := hRB X hX q hq
  rw [inCone_iff]
  refine ⟨hX, q - n, by omega, ?_, hg⟩
  have : n + (q - n) = q := by omega
  rw [this]
  exact hq

/-- OR-reach lands in the cone: if wire `w` OR-reaches gate `g`, then `g` is gate `w - n` or in its
cone. No hypothesis on `C`. -/
lemma orR_cone (n : ℕ) (C : Circuit) :
    ∀ w g, OrReaches n C w g → g = w - n ∨ InCone n C g (w - n) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro g h
  have hnw : n ≤ w := h.1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have e : n + k - n = k := by omega
  rw [e]
  obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
  rcases h3 with rfl | ⟨_, i, hi, hlt, hr⟩
  · exact Or.inl rfl
  · right
    have hni : n ≤ i := hr.1
    rw [inCone_iff]
    refine ⟨hk, i - n, by omega, by rw [show n + (i - n) = i by omega]; exact hi, ?_⟩
    exact ih i hlt g hr

lemma inOut_of_cone {n : ℕ} {C : Circuit} (X Y : ℕ)
    (hX : PEqualNP.Core.InOutputCone n C X)
    (hY : InCone n C Y X) : PEqualNP.Core.InOutputCone n C Y := by
  refine ⟨(inCone_lt n C Y X hY).1.trans hX.1, Or.inr ?_⟩
  rcases hX.2 with he | ⟨hn, hc⟩
  · refine ⟨by omega, ?_⟩
    have : C.output - n = X := by omega
    rw [this]
    exact hY
  · exact ⟨hn, inCone_trans n C Y X hY _ hc⟩

/-! ## Live gates, dead gates, live size -/

/-- The dead gates: gates that are not live (the output does not depend on them). -/
def deadGates (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => j ∉ liveGates n C

lemma mem_dead {n : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ deadGates n C ↔ j < C.gates.length ∧ j ∉ liveGates n C := by
  unfold deadGates
  rw [Finset.mem_filter, Finset.mem_range]

lemma live_sub_range (n : ℕ) (C : Circuit) : liveGates n C ⊆ Finset.range C.gates.length := by
  intro j hj
  exact Finset.mem_range.mpr (mem_live.mp hj).1

lemma liveSize_le (n : ℕ) (C : Circuit) : liveSize n C ≤ C.gates.length := by
  unfold liveSize
  have := Finset.card_le_card (live_sub_range n C)
  simpa using this

lemma live_add_dead (n : ℕ) (C : Circuit) :
    liveSize n C + (deadGates n C).card = C.gates.length := by
  have h1 : (Finset.range C.gates.length).filter (fun j => j ∈ liveGates n C) = liveGates n C := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨(mem_live.mp h).1, h⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range C.gates.length)
    (fun j => j ∈ liveGates n C)
  rw [h1] at h2
  unfold liveSize deadGates
  simpa using h2

/-- Live gates are closed under the cone. -/
lemma live_closed {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j ∈ liveGates n C) (hc : InCone n C i j) :
    i ∈ liveGates n C := by
  obtain ⟨_, hn, h⟩ := mem_live.mp hj
  have hl := inCone_lt n C i j hc
  refine mem_live.mpr ⟨by omega, hn, Or.inr ?_⟩
  rcases h with e | h'
  · rw [← e]; exact hc
  · exact inCone_trans n C i j hc _ h'

/-- The output gate (when the output is a gate wire) is live. -/
lemma out_live {n : ℕ} {C : Circuit} {o : ℕ} (ho : C.output = n + o) (hlt : o < C.gates.length) :
    o ∈ liveGates n C :=
  mem_live.mpr ⟨hlt, by omega, Or.inl (by omega)⟩

/-- A gate OR-reached from the output wire is live. -/
lemma orR_out_live {n : ℕ} {C : Circuit} {g : ℕ} (hr : OrReaches n C C.output g) :
    g ∈ liveGates n C := by
  have hn : n ≤ C.output := hr.1
  have hg := (orReaches_reach (n := n) (C := C) g C.output hr).2
  rcases orR_cone n C C.output g hr with e | h
  · exact mem_live.mpr ⟨hg, hn, Or.inl e⟩
  · exact mem_live.mpr ⟨hg, hn, Or.inr h⟩

end KCone

end PEqualNP.Outside.L_meta_4742

namespace PEqualNP.Outside.L_meta_4742

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo
lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hw : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        rw [hwn] at hx ⊢
        have h0 : opnd C (w - n) 0 < w := by
          have := opnd_lt hAO hj 0
          omega
        have h1 : opnd C (w - n) 1 < w := by
          have := opnd_lt hAO hj 1
          omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
        · rw [wval_gate_and hAO x hj hop, Bool.and_eq_true] at hx
          rw [wval_gate_and hAO y hj hop, Bool.and_eq_true]
          exact ⟨ih _ h0 hx.1, ih _ h1 hx.2⟩
        · rw [wval_gate_or hAO x hj hop, Bool.or_eq_true] at hx
          rw [wval_gate_or hAO y hj hop, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ h0 h)) (fun h => Or.inr (ih _ h1 h))
      · rw [wval_ge_len C x (by omega)] at hx
        cases hx


lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]


def delMap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def delGateMap (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma delMap_gate (n g r k : ℕ) (hkg : k ≠ g) :
    delMap n g r (n + k) = n + delGateMap g k := by
  unfold delMap delGateMap
  split_ifs <;> omega

def delCircuit (n : ℕ) (C : Circuit) (g r : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin (C.gates.length - 1) =>
      let src := if i.val < g then i.val else i.val + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩
    output := delMap n g r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).gates.length = C.gates.length - 1 := by
  simp [delCircuit]

lemma delCircuit_size (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).size ≤ C.size := by
  simp [Circuit.size, delCircuit]

lemma delCircuit_gateAt {n : ℕ} {C : Circuit} {g r i : ℕ} (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C g r) i =
      let src := if i < g then i else i + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩ := by
  have hlt : i < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [delCircuit]

lemma delCircuit_gateAt_src {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) :
    gateAt (delCircuit n C g r) (delGateMap g k) =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (delMap n g r)⟩ := by
  have hi : delGateMap g k < C.gates.length - 1 := by
    unfold delGateMap; split_ifs <;> omega
  rw [delCircuit_gateAt hi]
  have hsrc : (if delGateMap g k < g then delGateMap g k else delGateMap g k + 1) = k := by
    unfold delGateMap; split_ifs <;> omega
  simp [hsrc]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delCircuit n C g r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    exact hAO.1 (gateAt C (if i.val < g then i.val else i.val + 1)) (gateAt_mem hsrc)
  · intro i hi w hw
    rw [delCircuit_len] at hi
    rw [delCircuit_gateAt hi] at hw
    simp only [List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩
    by_cases hig : i < g
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delMap
      split_ifs <;> omega
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delMap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    simp [hAO.2.2 _ (gateAt_mem hsrc)]

lemma delCircuit_opnd {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) (b : Fin 2) :
    opnd (delCircuit n C g r) (delGateMap g k) b = delMap n g r (opnd C k b) := by
  unfold opnd
  rw [delCircuit_gateAt_src hg hk hkg, gate_inputs_eq hAO hk]
  fin_cases b <;> simp [opnd]

lemma delCircuit_wval_lt {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool) :
    ∀ w < n + g, wval (delCircuit n C g r) x w = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hdgm : delGateMap g (w - n) = w - n := by simp [delGateMap, hk]
      have hk' : w - n < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have hop0 : opnd (delCircuit n C g r) (w - n) 0 = opnd C (w - n) 0 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 0]
        unfold delMap; split_ifs <;> omega
      have hop1 : opnd (delCircuit n C g r) (w - n) 1 = opnd C (w - n) 1 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 1]
        unfold delMap; split_ifs <;> omega
      have hgate : (gateAt (delCircuit n C g r) (w - n)).op = (gateAt C (w - n)).op := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_gateAt_src hg hklt hkg]
      rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hk' (hgate.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]
      · rw [wval_gate_or hAO' x hk' (hgate.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]

lemma delCircuit_wval_le {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hle : wval C x r = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, wval (delCircuit n C g r) x (delMap n g r w) = true → wval C x w = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hD
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr] at hD
        exact hle hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) hD.1, ih _ h1lt (by omega) hD.2⟩
        · rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hge : gateVal n C g x = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C g r) x (delMap n g r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hC
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt]
      exact hC
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr]
        exact hge hC
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm]
        rw [hwn] at hC
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO x hk hop, Bool.and_eq_true] at hC
          rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact ⟨ih _ h0lt (by omega) hC.1, ih _ h1lt (by omega) hC.2⟩
        · rw [wval_gate_or hAO x hk hop, Bool.or_eq_true] at hC
          rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact hC.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))


lemma oR_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) :=
  PEqualNP.Outside.L_meta_4742.KCone.orReaches_iff n C k g

lemma reach_le {n : ℕ} {C : Circuit} {g : ℕ} :
    ∀ w, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨_, h3⟩ := (oR_iff n C k g).mp h
    rcases h3 with rfl | ⟨_, i, _, hlt, hr⟩
    · exact le_refl _
    · have := ih i hlt hr
      omega

lemma reach_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {g : ℕ} (x : Fin n → Bool)
    (hgx : wval C x (n + g) = true) :
    ∀ w, PEqualNP.CleanedNonEdge.OrReaches n C w g → wval C x w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (oR_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact hgx
    · rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hk] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Or.inl (ih _ hlt hr)
      · exact Or.inr (ih _ hlt hr)

lemma descent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) {g : ℕ}
    (hoth : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ∀ w, wval C x w = true → (∃ y : Fin n, x y = true ∧ wval C (unitInput y) w = true) ∨
      (PEqualNP.CleanedNonEdge.OrReaches n C w g ∧ wval C x (n + g) = true) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · left
      refine ⟨⟨w, hlt⟩, ?_, ?_⟩
      · rw [wval_input C x w hlt] at hw; exact hw
      · rw [wval_input C _ w hlt]; simp [unitInput]
    · by_cases hlen : w < n + C.gates.length
      · have hk : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hk) with hop | hop
        · by_cases hkg : w - n = g
          · right
            refine ⟨?_, ?_⟩
            · rw [hwn, hkg]
              exact (oR_iff n C g g).mpr ⟨by omega, Or.inl rfl⟩
            · rw [← hkg, ← hwn]; exact hw
          · exfalso
            have hb := hoth (w - n) hk hop hkg x (by rw [hwn] at hw; exact hw)
            rw [hb] at hx
            exact Bool.noConfusion hx
        · rw [hwn, wval_gate_or hAO x hk hop, Bool.or_eq_true] at hw
          have step : ∀ b : Fin 2, wval C x (opnd C (w - n) b) = true →
              (∃ y : Fin n, x y = true ∧ wval C (unitInput y) w = true) ∨
              (PEqualNP.CleanedNonEdge.OrReaches n C w g ∧ wval C x (n + g) = true) := by
            intro b hb
            have hblt : opnd C (w - n) b < w := by have := opnd_lt hAO hk b; omega
            rcases ih _ hblt hb with ⟨y, hy, hyv⟩ | ⟨hr, hg⟩
            · left
              refine ⟨y, hy, ?_⟩
              rw [hwn, wval_gate_or hAO _ hk hop, Bool.or_eq_true]
              fin_cases b
              · exact Or.inl hyv
              · exact Or.inr hyv
            · right
              refine ⟨?_, hg⟩
              rw [hwn]
              exact (oR_iff n C (w - n) g).mpr ⟨hk, Or.inr ⟨hop, _, opnd_mem hAO hk b,
                opnd_lt hAO hk b, hr⟩⟩
          rcases hw with hw | hw
          · exact step 0 hw
          · exact step 1 hw
      · rw [wval_ge_len C x (by omega)] at hw
        exact Bool.noConfusion hw

lemma core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g a : ℕ) (m : Fin n)
    (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length)
    (ha : a < n + g)
    (hge : ∀ x : Fin n → Bool, wval C x (n + g) = true → wval C x a = true)
    (hA : ∀ y : Fin n, wval C (unitInput y) a = true → G.Adj y m)
    (hoth : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (hpart : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n,
      (PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 0) g ∧ wval C (unitInput z) (opnd C k 1) = true) ∨
      (PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 1) g ∧ wval C (unitInput z) (opnd C k 0) = true) → z = m)
    (hnoboth : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 0) g → PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 1) g → False)
    (hnoout : ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hAO' := delCircuit_isAO2 hAO hg ha
  -- a partner true at an independent input, with `a` true, is impossible
  have hkill : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ p : ℕ,
      (∀ z : Fin n, wval C (unitInput z) p = true → z = m) →
      ¬ PEqualNP.CleanedNonEdge.OrReaches n C p g → wval C x p = true → wval C x a = true → False := by
    intro x hx p hpz hpr hp hav
    rcases descent G hAO hoth x hx p hp with ⟨y, hy, hyv⟩ | ⟨hr, _⟩
    · have hym := hpz y hyv
      subst hym
      rcases descent G hAO hoth x hx a hav with ⟨y', hy', hy'v⟩ | ⟨hr', _⟩
      · have hadj := hA y' hy'v
        have : graphFun G ∅ x = true := (graphFun_iff x).mpr ⟨y', y, hadj, hy', hy⟩
        rw [this] at hx; exact Bool.noConfusion hx
      · have := reach_le a hr'; omega
    · exact hpr hr
  have F3 : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ w < n + C.gates.length,
      wval (delCircuit n C g a) x (delMap n g a w) = true →
      wval C x w = true ∨ (PEqualNP.CleanedNonEdge.OrReaches n C w g ∧ wval C x a = true) := by
    intro x hx w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hD
      by_cases hlt : w < n + g
      · have hm : delMap n g a w = w := by simp [delMap, hlt]
        rw [hm, delCircuit_wval_lt hAO hg ha x w hlt] at hD
        exact Or.inl hD
      · by_cases hwg : w = n + g
        · subst hwg
          have hm : delMap n g a (n + g) = a := by simp [delMap]
          rw [hm, delCircuit_wval_lt hAO hg ha x a ha] at hD
          exact Or.inr ⟨(oR_iff n C g g).mpr ⟨hg, Or.inl rfl⟩, hD⟩
        · have hk : w - n < C.gates.length := by omega
          have hkg : w - n ≠ g := by omega
          have hwn : w = n + (w - n) := by omega
          have hdm : delMap n g a w = n + delGateMap g (w - n) := by
            conv_lhs => rw [hwn]
            exact delMap_gate n g a (w - n) hkg
          have hk' : delGateMap g (w - n) < (delCircuit n C g a).gates.length := by
            rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
          have hgate : (gateAt (delCircuit n C g a) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
            rw [delCircuit_gateAt_src hg hk hkg]
          rw [hdm] at hD
          rcases hAO.1 _ (gateAt_mem hk) with hop | hop
          · rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
              delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
            have i0 := ih _ h0lt (by omega) hD.1
            have i1 := ih _ h1lt (by omega) hD.2
            rcases i0 with c0 | ⟨r0, ha0⟩
            · rcases i1 with c1 | ⟨r1, ha1⟩
              · left
                rw [hwn, wval_gate_and hAO x hk hop, c0, c1]; rfl
              · exfalso
                refine hkill x hx (opnd C (w - n) 0) (fun z hz => hpart _ hk hop z (Or.inr ⟨r1, hz⟩))
                  (fun r0 => hnoboth _ hk hop r0 r1) c0 ha1
            · exfalso
              rcases i1 with c1 | ⟨r1, _⟩
              · exact hkill x hx (opnd C (w - n) 1) (fun z hz => hpart _ hk hop z (Or.inl ⟨r0, hz⟩))
                  (fun r1 => hnoboth _ hk hop r0 r1) c1 ha0
              · exact hnoboth _ hk hop r0 r1
          · rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
              delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
            have step : ∀ b : Fin 2, wval (delCircuit n C g a) x (delMap n g a (opnd C (w - n) b)) = true →
                wval C x w = true ∨ (PEqualNP.CleanedNonEdge.OrReaches n C w g ∧ wval C x a = true) := by
              intro b hb
              have hblt : opnd C (w - n) b < w := by have := opnd_lt hAO hk b; omega
              rcases ih _ hblt (by omega) hb with c | ⟨r, hav⟩
              · left
                rw [hwn, wval_gate_or hAO x hk hop, Bool.or_eq_true]
                fin_cases b
                · exact Or.inl c
                · exact Or.inr c
              · right
                refine ⟨?_, hav⟩
                rw [hwn]
                exact (oR_iff n C (w - n) g).mpr ⟨hk, Or.inr ⟨hop, _, opnd_mem hAO hk b,
                  opnd_lt hAO hk b, r⟩⟩
            rcases hD with hD | hD
            · exact step 0 hD
            · exact step 1 hD
  refine ⟨delCircuit n C g a, hAO', ?_, ?_⟩
  · simp only [Circuit.size, delCircuit_len]; omega
  · funext x
    have hCx : circuitFun n C x = wval C x C.output := rfl
    have hDx : circuitFun n (delCircuit n C g a) x = wval (delCircuit n C g a) x (delMap n g a C.output) := rfl
    cases hFx : graphFun G ∅ x with
    | false =>
      rw [hDx]
      by_contra hne
      have hD : wval (delCircuit n C g a) x (delMap n g a C.output) = true := by
        simpa using hne
      by_cases ho : C.output < n + C.gates.length
      · rcases F3 x hFx C.output ho hD with c | ⟨r, _⟩
        · rw [← hCx, hF, hFx] at c; exact Bool.noConfusion c
        · exact hnoout r
      · have hm : delMap n g a C.output = C.output - 1 := by
          unfold delMap; split_ifs <;> omega
        rw [hm, wval_ge_len _ x (by rw [delCircuit_len]; omega)] at hD
        exact Bool.noConfusion hD
    | true =>
      have hc : wval C x C.output = true := by rw [← hCx, hF, hFx]
      have ho : C.output < n + C.gates.length := by
        by_contra ho
        rw [wval_ge_len C x (by omega)] at hc
        exact Bool.noConfusion hc
      rw [hDx]
      exact delCircuit_wval_ge hAO hg ha x (fun h => hge x h) C.output ho hc

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (m : Fin n)
    (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hgdirty : ¬ BelowF G C g)
    (hoth : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (hpart : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n,
      (PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 0) g ∧ wval C (unitInput z) (opnd C k 1) = true) ∨
      (PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 1) g ∧ wval C (unitInput z) (opnd C k 0) = true) → z = m)
    (hside : (∀ y : Fin n, wval C (unitInput y) (opnd C g 0) = true → G.Adj y m) ∨
      (∀ y : Fin n, wval C (unitInput y) (opnd C g 1) = true → G.Adj y m)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  obtain ⟨x0, hx0g, hx0F⟩ : ∃ x0, wval C x0 (n + g) = true ∧ graphFun G ∅ x0 = false := by
    unfold BelowF at hgdirty
    push_neg at hgdirty
    obtain ⟨x0, h1, h2⟩ := hgdirty
    exact ⟨x0, h1, by simpa using h2⟩
  have hnoboth : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 0) g →
      PEqualNP.CleanedNonEdge.OrReaches n C (opnd C k 1) g → False := by
    intro k hk hop r0 r1
    have hkg : k ≠ g := by
      rintro rfl
      have := reach_le _ r0
      have := opnd_lt hAO hk 0
      omega
    have hv : wval C x0 (n + k) = true := by
      rw [wval_gate_and hAO x0 hk hop, reach_true hAO x0 hx0g _ r0, reach_true hAO x0 hx0g _ r1]; rfl
    have := hoth k hk hop hkg x0 hv
    rw [this] at hx0F; exact Bool.noConfusion hx0F
  have hnoout : ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
    intro r
    have hv : circuitFun n C x0 = true := reach_true hAO x0 hx0g _ r
    rw [hF, hx0F] at hv; exact Bool.noConfusion hv
  rcases hside with hs | hs
  · refine core G C g (opnd C g 0) m hAO hF hg (opnd_lt hAO hg 0) ?_ hs hoth hpart hnoboth hnoout
    intro x h
    rw [wval_gate_and hAO x hg hgand, Bool.and_eq_true] at h
    exact h.1
  · refine core G C g (opnd C g 1) m hAO hF hg (opnd_lt hAO hg 1) ?_ hs hoth hpart hnoboth hnoout
    intro x h
    rw [wval_gate_and hAO x hg hgand, Bool.and_eq_true] at h
    exact h.2

end PEqualNP.Outside.L_meta_4742


theorem PEqualNP.Outside.L_meta_4742 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ((∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m) ∨ (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g m _ _ hAO hF _ _ _ hg hgand hgdirty hoth hpart hside
  exact PEqualNP.Outside.L_meta_4742.main n G C g m hAO hF hg hgand hgdirty hoth hpart hside
