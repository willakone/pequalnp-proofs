import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4748

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

def fsub (n c : ℕ) (sigma : ℕ → ℕ) (r i : ℕ) : ℕ := if i = n + c then sigma r else i

lemma sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma sub_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (r : ℕ) :
    gateAt (substReads C n c sigma) r =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map (fsub n c sigma r)⟩ := by
  unfold gateAt substReads fsub
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases h : C.gates[r]? <;> simp

lemma mem_readers {n : ℕ} {C : Circuit} {c k : ℕ} (hk : k < C.gates.length)
    (h : n + c ∈ (gateAt C k).inputs) : k ∈ PEqualNP.TopForm.readers n C c := by
  unfold PEqualNP.TopForm.readers
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, h⟩

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

lemma sub_mono {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ} {x : List Bool}
    (hx : x.length = n) (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ w, val C x w = true → val (substReads C n c sigma) x w = true := by
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · rw [val_input hx hw] at hv; rw [val_input hx hw]; exact hv
    by_cases hlen : n + C.gates.length ≤ w
    · rw [val_ge hx hlen] at hv; cases hv
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
    rw [val_gate hx hk] at hv
    rw [val_gate hx hk', sub_gateAt]
    simp only [List.map_map]
    have hop := hAO.1 _ (gateAt_mem hk)
    have key := opMono_imp _ hop (gateAt C k).inputs
      (fun i => if i < n + k then val C x i else false)
      ((fun i => if i < n + k then val (substReads C n c sigma) x i else false) ∘
        fsub n c sigma k) ?_ hv
    · exact key
    intro i hi
    have hilt : i < n + k := hAO.2.1 k hk i hi
    simp only [Function.comp_apply, if_pos hilt]
    intro hvi
    unfold fsub
    by_cases hic : i = n + c
    · subst hic
      rw [if_pos rfl]
      have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk hi
      rw [val_and hx hc hcop, hcin] at hvi
      have hva := (hvi a (by simp)).2
      have hvb := (hvi b (by simp)).2
      have hsl : sigma k < n + k := by rcases hsig k hrd with h | h <;> omega
      rw [if_pos hsl]
      rcases hsig k hrd with h | h
      · rw [h]; exact ih a (by omega) hva
      · rw [h]; exact ih b (by omega) hvb
    · rw [if_neg hic, if_pos hilt]; exact ih i hilt hvi

lemma sub_eq {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ} (z : Fin n → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hH2 : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧
        ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ OrReaches n C u r) →
          (sigma r = b → val C (List.ofFn z) y = true → val C (List.ofFn z) a = true) ∧
          (sigma r = a → val C (List.ofFn z) y = true → val C (List.ofFn z) b = true)) :
    ∀ w, ((¬ ∃ h ∈ orClosure n C c, w = n + h) →
        val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w) ∧
      (val (substReads C n c sigma) (List.ofFn z) w = true →
        val C (List.ofFn z) w = true ∨ ∃ r ∈ PEqualNP.TopForm.readers n C c,
          OrReaches n C w r ∧ val C (List.ofFn z) (sigma r) = true) := by
  have hx : (List.ofFn z).length = n := by simp
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  have hvc : val C (List.ofFn z) a = true → val C (List.ofFn z) b = true →
      val C (List.ofFn z) (n + c) = true := by
    intro h1 h2
    rw [val_and hx hc hcop, hcin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hab.1, h1⟩
    · exact ⟨hab.2, h2⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hw : w < n
  · have e : val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w := by
      rw [val_input hx hw, val_input hx hw]
    exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
  by_cases hlen : n + C.gates.length ≤ w
  · have e : val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w := by
      rw [val_ge hx hlen, val_ge hx (by rw [sub_len]; exact hlen)]
    exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
  have hEab : ∀ s, (s = a ∨ s = b) → s < n + k →
      val (substReads C n c sigma) (List.ofFn z) s = val C (List.ofFn z) s := by
    intro s hs hsk
    apply (ih s hsk).1
    rintro ⟨h, hh, rfl⟩
    have := orC_gt hh
    rcases hs with hs | hs <;> omega
  by_cases hO : k ∈ orClosure n C c
  · refine ⟨fun hn => absurd ⟨k, hO, rfl⟩ hn, ?_⟩
    intro hv'
    have hop := orC_or hO
    have hop' : (gateAt (substReads C n c sigma) k).op = GateOp.or := by
      rw [sub_gateAt]; exact hop
    obtain ⟨i', hi', hlt', hvi'⟩ := (val_or hx hk' hop').mp hv'
    rw [sub_gateAt] at hi'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
    have hilt : i < n + k := hAO.2.1 k hk i hi
    unfold fsub at hlt' hvi'
    by_cases hic : i = n + c
    · rw [if_pos hic] at hlt' hvi'
      subst hic
      have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk hi
      right
      refine ⟨k, hrd, reach_self hk, ?_⟩
      rw [← hEab (sigma k) (hsig k hrd) hlt']; exact hvi'
    · rw [if_neg hic] at hlt' hvi'
      rcases (ih i hilt).2 hvi' with h1 | ⟨r, hr, hreach, hvr⟩
      · left; exact (val_or hx hk hop).mpr ⟨i, hi, hilt, h1⟩
      · right
        exact ⟨r, hr, (orReaches_iff n C k r).mpr ⟨hk, Or.inr ⟨hop, i, hi, hilt, hreach⟩⟩, hvr⟩
  · suffices e : val (substReads C n c sigma) (List.ofFn z) (n + k) = val C (List.ofFn z) (n + k) by
      exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
    have hop := hAO.1 _ (gateAt_mem hk)
    have hlen2 := hAO.2.2 _ (gateAt_mem hk)
    by_cases hfr : k ∈ frontier n C c
    · obtain ⟨_, hne, _, w0, hw0, hin0⟩ := Finset.mem_filter.mp hfr
      have hand : (gateAt C k).op = GateOp.and := by
        rcases hop with h | h
        · exact h
        · exfalso
          have hlt0 := hAO.2.1 k hk _ hin0
          have hr : OrReaches n C (n + k) c :=
            (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨h, n + w0, hin0, hlt0, ins_reach hc hw0⟩⟩
          exact hO (orC_mem.mpr ⟨hk, hne, hr⟩)
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
      obtain ⟨u, y, hord, hu⟩ : ∃ u y, ((gateAt C k).inputs = [u, y] ∨
          (gateAt C k).inputs = [y, u]) ∧ ∃ w ∈ insert c (orClosure n C c), u = n + w := by
        rw [hpq] at hin0
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin0
        rcases hin0 with h | h
        · exact ⟨p, q, Or.inl hpq, w0, hw0, h.symm⟩
        · exact ⟨q, p, Or.inr hpq, w0, hw0, h.symm⟩
      obtain ⟨hy, hrr⟩ := hH2 k hfr hand u y hord hu
      have hmem : ∀ i, i ∈ (gateAt C k).inputs ↔ i = u ∨ i = y := by
        intro i
        rcases hord with h | h <;> rw [h] <;> simp <;> tauto
      have huin : u ∈ (gateAt C k).inputs := (hmem u).mpr (Or.inl rfl)
      have hyin : y ∈ (gateAt C k).inputs := (hmem y).mpr (Or.inr rfl)
      have hult := hAO.2.1 k hk u huin
      have hylt := hAO.2.1 k hk y hyin
      have hyc : y ≠ n + c := hy c (Finset.mem_insert_self _ _)
      have hyO : ¬ ∃ h ∈ orClosure n C c, y = n + h := by
        rintro ⟨h, hh, e⟩; exact hy h (Finset.mem_insert_of_mem hh) e
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hv'
        have hall := (val_and hx hk' (by rw [sub_gateAt]; exact hand)).mp hv'
        rw [sub_gateAt] at hall
        have hy' := (hall (fsub n c sigma k y) (List.mem_map_of_mem hyin)).2
        unfold fsub at hy'
        rw [if_neg hyc, (ih y hylt).1 hyO] at hy'
        have hu' := (hall (fsub n c sigma k u) (List.mem_map_of_mem huin))
        have hU : val C (List.ofFn z) u = true ∨ ∃ r ∈ PEqualNP.TopForm.readers n C c,
            (r = k ∨ OrReaches n C u r) ∧ val C (List.ofFn z) (sigma r) = true := by
          unfold fsub at hu'
          by_cases huc : u = n + c
          · rw [if_pos huc] at hu'
            have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk (huc ▸ huin)
            right
            refine ⟨k, hrd, Or.inl rfl, ?_⟩
            rw [← hEab (sigma k) (hsig k hrd) hu'.1]; exact hu'.2
          · rw [if_neg huc] at hu'
            rcases (ih u hult).2 hu'.2 with h1 | ⟨r, hr, hreach, hvr⟩
            · exact Or.inl h1
            · exact Or.inr ⟨r, hr, Or.inr hreach, hvr⟩
        have hvu : val C (List.ofFn z) u = true := by
          rcases hU with h1 | ⟨r, hr, hr', hvr⟩
          · exact h1
          · obtain ⟨w1, hw1, rfl⟩ := hu
            apply reach_val hx (ins_reach hc hw1)
            obtain ⟨hb, ha⟩ := hrr r hr hr'
            rcases hsig r hr with e | e
            · rw [e] at hvr; exact hvc hvr (ha e hy')
            · rw [e] at hvr; exact hvc (hb e hy') hvr
        rw [val_and hx hk hand]
        intro i hi
        rcases (hmem i).mp hi with rfl | rfl
        · exact ⟨hult, hvu⟩
        · exact ⟨hylt, hy'⟩
      · exact sub_mono hx hAO hc hcop hcin hsig _
    · have hgood : ∀ i ∈ (gateAt C k).inputs, i ≠ n + c ∧ ¬ ∃ h ∈ orClosure n C c, i = n + h := by
        intro i hi
        have hilt := hAO.2.1 k hk i hi
        by_cases hkc : k = c
        · constructor
          · omega
          · rintro ⟨h, hh, rfl⟩; have := orC_gt hh; omega
        · constructor
          · rintro rfl
            exact hfr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkc, hO, c,
              Finset.mem_insert_self _ _, hi⟩)
          · rintro ⟨h, hh, rfl⟩
            exact hfr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkc, hO, h,
              Finset.mem_insert_of_mem hh, hi⟩)
      rw [val_gate hx hk', val_gate hx hk, sub_gateAt]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨h1, h2⟩ := hgood i hi
      have hilt := hAO.2.1 k hk i hi
      simp only [Function.comp_apply, fsub, if_neg h1, if_pos hilt]
      exact (ih i hilt).1 h2

lemma fsub_ne {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    {j : ℕ} (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) :
    fsub n c sigma j i ≠ n + c := by
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  unfold fsub
  by_cases hic : i = n + c
  · rw [if_pos hic]
    subst hic
    rcases hsig j (mem_readers hj hi) with h | h <;> omega
  · rw [if_neg hic]; exact hic

lemma no_cone_c {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j, ¬ InCone n (substReads C n c sigma) c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro h
  obtain ⟨hjl, k, hkj, hin, hrest⟩ := (inCone_iff n _ c j).mp h
  rw [sub_len] at hjl
  rw [sub_gateAt] at hin
  obtain ⟨i0, hi0, he⟩ := List.mem_map.mp hin
  rcases hrest with rfl | hrest
  · exact fsub_ne hAO hc hcin hsig hjl hi0 he
  · exact ih k hkj hrest

lemma cone_sub {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j i, InCone n (substReads C n c sigma) i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro i h
  obtain ⟨hjl, k, hkj, hin, hrest⟩ := (inCone_iff n _ i j).mp h
  rw [sub_len] at hjl
  rw [sub_gateAt] at hin
  obtain ⟨i0, hi0, he⟩ := List.mem_map.mp hin
  have hrest' : i = k ∨ InCone n C i k := hrest.imp id (ih k hkj i)
  unfold fsub at he
  by_cases hic : i0 = n + c
  · rw [if_pos hic] at he
    subst hic
    have hrd := mem_readers hjl hi0
    have hkc : n + k ∈ (gateAt C c).inputs := by
      rw [hcin]; rcases hsig j hrd with h | h <;> rw [← he, h] <;> simp
    have hklt : k < c := by have := hAO.2.1 c hc _ hkc; omega
    have hcj : c < j := by have := hAO.2.1 j hjl _ hi0; omega
    rw [inCone_iff]
    refine ⟨hjl, c, hcj, hi0, Or.inr ?_⟩
    rw [inCone_iff]
    exact ⟨hc, k, hklt, hkc, hrest'⟩
  · rw [if_neg hic] at he
    subst he
    rw [inCone_iff]
    exact ⟨hjl, k, hkj, hi0, hrest'⟩

lemma mem_live {n : ℕ} {C : Circuit} {j : ℕ} : j ∈ liveGates n C ↔
    j < C.gates.length ∧ n ≤ C.output ∧ (j = C.output - n ∨ InCone n C j (C.output - n)) := by
  unfold liveGates
  rw [Finset.mem_filter, Finset.mem_range]


/-! ## Generic run comparison (3543): two runs of the gate list of `C`, narrowed reads replaced -/

lemma gen (n u : ℕ) (C : Circuit) (S : ℕ → Prop) (R : Bool → Bool → Prop) (hR : OpMono R)
    (hRf : R false false)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (v1 v2 a1 a2 : ℕ → Bool) (f1 f2 : ℕ → ℕ → Bool)
    (h1 : ∀ r < C.gates.length, v1 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f1 r)))
    (h2 : ∀ r < C.gates.length, v2 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f2 r)))
    (hf1 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f1 r i = a1 r) ∧
      (¬ (S r ∧ i = n + u) → f1 r i = if i < n + r then v1 i else false))
    (hf2 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f2 r i = a2 r) ∧
      (¬ (S r ∧ i = n + u) → f2 r i = if i < n + r then v2 i else false))
    (hin : ∀ i < n, R (v1 i) (v2 i))
    (ha : ∀ r < C.gates.length, S r → (∀ h < r, R (v1 (n + h)) (v2 (n + h))) → R (a1 r) (a2 r)) :
    ∀ r < C.gates.length, R (v1 (n + r)) (v2 (n + r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr
  rw [h1 r hr, h2 r hr]
  refine hR _ (hops r hr) _ _ _ (fun i hi => ?_)
  by_cases hs : S r ∧ i = n + u
  · rw [(hf1 r hr i hi).1 hs, (hf2 r hr i hi).1 hs]
    exact ha r hr hs.1 (fun h hh => ih h hh (by omega))
  · rw [(hf1 r hr i hi).2 hs, (hf2 r hr i hi).2 hs]
    by_cases hlt : i < n + r
    · rw [if_pos hlt, if_pos hlt]
      by_cases hn : i < n
      · exact hin i hn
      · obtain ⟨h, rfl⟩ : ∃ h, i = n + h := ⟨i - n, by omega⟩
        exact ih h (by omega) (by omega)
    · rw [if_neg hlt, if_neg hlt]; exact hRf

lemma all_wires (n len : ℕ) (R : Bool → Bool → Prop) (hRf : R false false) (v1 v2 : ℕ → Bool)
    (hin : ∀ i < n, R (v1 i) (v2 i)) (hg : ∀ r < len, R (v1 (n + r)) (v2 (n + r)))
    (hb1 : ∀ i, n + len ≤ i → v1 i = false) (hb2 : ∀ i, n + len ≤ i → v2 i = false) :
    ∀ i, R (v1 i) (v2 i) := by
  intro i
  by_cases h1 : i < n
  · exact hin i h1
  by_cases h2 : i < n + len
  · obtain ⟨r, rfl⟩ : ∃ r, i = n + r := ⟨i - n, by omega⟩
    exact hg r (by omega)
  · rw [hb1 i (by omega), hb2 i (by omega)]; exact hRf

lemma gen_all (n u : ℕ) (C : Circuit) (S : ℕ → Prop)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (v1 v2 a1 a2 : ℕ → Bool) (f1 f2 : ℕ → ℕ → Bool)
    (h1 : ∀ r < C.gates.length, v1 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f1 r)))
    (h2 : ∀ r < C.gates.length, v2 (n + r) = (gateAt C r).op.eval ((gateAt C r).inputs.map (f2 r)))
    (hf1 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f1 r i = a1 r) ∧
      (¬ (S r ∧ i = n + u) → f1 r i = if i < n + r then v1 i else false))
    (hf2 : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, (S r ∧ i = n + u → f2 r i = a2 r) ∧
      (¬ (S r ∧ i = n + u) → f2 r i = if i < n + r then v2 i else false))
    (hin : ∀ i < n, v1 i = true → v2 i = true)
    (ha : ∀ r < C.gates.length, S r → (∀ h < r, v1 (n + h) = true → v2 (n + h) = true) →
      a1 r = true → a2 r = true)
    (hb1 : ∀ i, n + C.gates.length ≤ i → v1 i = false)
    (hb2 : ∀ i, n + C.gates.length ≤ i → v2 i = false) :
    ∀ i, v1 i = true → v2 i = true :=
  all_wires n C.gates.length (fun a b => a = true → b = true) (fun h => h) v1 v2 hin
    (gen n u C S _ opMono_imp (fun h => h) hops v1 v2 a1 a2 f1 f2 h1 h2 hf1 hf2 hin ha) hb1 hb2

def shf (n L i : ℕ) : ℕ := if i < n then i else i + L

def cv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool := val C (List.ofFn x) i

def ev (n L : ℕ) (D : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool := val D (List.ofFn x) (shf n L i)

def fc (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if i < n + r then cv n C x i else false

def fd (n L : ℕ) (D : Circuit) (rho : ℕ → ℕ → ℕ) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if rho r i < n + L + r then val D (List.ofFn x) (rho r i) else false

lemma c_run (n u : ℕ) (C : Circuit) (hRB : ReadsBack n C) (S : ℕ → Prop) (x : Fin n → Bool) :
    (∀ r < C.gates.length, cv n C x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fc n C x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (S r ∧ i = n + u → fc n C x r i = cv n C x (n + u)) ∧
      (¬ (S r ∧ i = n + u) → fc n C x r i = if i < n + r then cv n C x i else false)) := by
  refine ⟨fun r hr => ?_, fun r hr i hi => ⟨fun h => ?_, fun _ => rfl⟩⟩
  · exact val_gate (n := n) (by simp) hr
  · rw [← h.2]; unfold fc; rw [if_pos (hRB r hr i hi)]

lemma d_run (n u : ℕ) (C D : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (S : ℕ → Prop)
    (hrho : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, ¬ (S r ∧ i = n + u) →
      rho r i = if i < n then i else i + G0.length) (x : Fin n → Bool) :
    (∀ r < C.gates.length, ev n G0.length D x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fd n G0.length D rho x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      (S r ∧ i = n + u → fd n G0.length D rho x r i = fd n G0.length D rho x r (n + u)) ∧
      (¬ (S r ∧ i = n + u) → fd n G0.length D rho x r i =
        if i < n + r then ev n G0.length D x i else false)) := by
  refine ⟨fun r hr => ?_, fun r hr i hi => ⟨fun h => by rw [h.2], fun h => ?_⟩⟩
  · have hj : G0.length + r < D.gates.length := by rw [hDg]; simp; omega
    have hg : gateAt D (G0.length + r) =
        ⟨(gateAt C r).op, (gateAt C r).inputs.map (fun i7 => rho r i7)⟩ := by
      rw [gateAt_eq hj, gateAt_eq hr]
      simp only [hDg]
      rw [List.getElem_append_right (by omega)]
      simp
    have := val_gate (C := D) (n := n) (x := List.ofFn x) (by simp) hj
    rw [hg] at this
    unfold ev shf
    rw [if_neg (by omega)]
    have e : n + r + G0.length = n + (G0.length + r) := by omega
    rw [e, this, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, fd]
    rw [show n + (G0.length + r) = n + G0.length + r by omega]
  · unfold fd ev shf
    rw [hrho r hr i hi h]
    by_cases hn : i < n
    · rw [if_pos hn, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hn]
      by_cases hlt : i < n + r
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]

lemma d_pre (n : ℕ) (C D : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + G0.length) :
    val D (List.ofFn x) w = val (⟨G0, 0⟩ : Circuit) (List.ofFn x) w := by
  unfold val
  rw [wires_eq_foldl, wires_eq_foldl, hDg, List.foldl_append]
  apply foldl_getD_lt
  rw [foldl_length]
  simp
  omega

lemma and_eval_false (l : List ℕ) (f : ℕ → Bool) (z : ℕ) (hz : z ∈ l) (hf : f z = false) :
    GateOp.and.eval (l.map f) = false := by
  simp only [GateOp.eval]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h (f z) (List.mem_map_of_mem hz)
  simp [hf] at this

lemma d_run2 (n : ℕ) (C D : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ)
    (hDg : D.gates = G0 ++ C.gates.mapIdx (fun r7 g7 =>
      ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)))
    (Nn : ℕ → ℕ → Prop)
    (hrho : ∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, Nn r i →
      rho r i = if i < n then i else i + G0.length) (x : Fin n → Bool) :
    (∀ r < C.gates.length, ev n G0.length D x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fd n G0.length D rho x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs, Nn r i → fd n G0.length D rho x r i =
        if i < n + r then ev n G0.length D x i else false) := by
  refine ⟨fun r hr => ?_, fun r hr i hi h => ?_⟩
  · have hj : G0.length + r < D.gates.length := by rw [hDg]; simp; omega
    have hg : gateAt D (G0.length + r) =
        ⟨(gateAt C r).op, (gateAt C r).inputs.map (fun i7 => rho r i7)⟩ := by
      rw [gateAt_eq hj, gateAt_eq hr]
      simp only [hDg]
      rw [List.getElem_append_right (by omega)]
      simp
    have := val_gate (C := D) (n := n) (x := List.ofFn x) (by simp) hj
    rw [hg] at this
    unfold ev shf
    rw [if_neg (by omega)]
    have e : n + r + G0.length = n + (G0.length + r) := by omega
    rw [e, this, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, fd]
    rw [show n + (G0.length + r) = n + G0.length + r by omega]
  · unfold fd ev shf
    rw [hrho r hr i hi h]
    by_cases hn : i < n
    · rw [if_pos hn, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hn]
      by_cases hlt : i < n + r
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]

/-! ## Redirect ALL reads of wire `n + g` to wire `a` (3710 / 3724) -/

def red (n g a : ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : Gate)),
    output := if C.output = n + g then a else C.output }

def fr (n g a : ℕ) (C : Circuit) (x : Fin n → Bool) (r i : ℕ) : Bool :=
  if (if i = n + g then a else i) < n + r then
    cv n (red n g a C) x (if i = n + g then a else i) else false

lemma red_len (n g a : ℕ) (C : Circuit) : (red n g a C).gates.length = C.gates.length := by
  simp [red]

lemma red_gateAt (n g a : ℕ) (C : Circuit) {r : ℕ} (hr : r < C.gates.length) :
    gateAt (red n g a C) r = ⟨(gateAt C r).op,
      (gateAt C r).inputs.map (fun i => if i = n + g then a else i)⟩ := by
  rw [gateAt_eq (by rw [red_len]; exact hr), gateAt_eq hr]
  simp [red]

lemma r_run (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) :
    (∀ r < C.gates.length, cv n (red n g a C) x (n + r) =
      (gateAt C r).op.eval ((gateAt C r).inputs.map (fr n g a C x r))) ∧
    (∀ r < C.gates.length, ∀ i ∈ (gateAt C r).inputs,
      ((g < r) ∧ i = n + g → fr n g a C x r i =
        (fun r => if a < n + r then cv n (red n g a C) x a else false) r) ∧
      (¬ ((g < r) ∧ i = n + g) → fr n g a C x r i =
        if i < n + r then cv n (red n g a C) x i else false)) := by
  refine ⟨fun r hr => ?_, fun r hr i hi => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hr' : r < (red n g a C).gates.length := by rw [red_len]; exact hr
    unfold cv
    rw [val_gate (n := n) (C := red n g a C) (x := List.ofFn x) (by simp) hr', red_gateAt n g a C hr,
      List.map_map]
    rfl
  · unfold fr; rw [if_pos h.2]
  · have hne : i ≠ n + g := by
      intro he; apply h; refine ⟨?_, he⟩; have := hRB r hr i hi; omega
    unfold fr; rw [if_neg hne]

lemma inC (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    cv n C x i = x ⟨i, hi⟩ := by
  unfold cv
  rw [val_input (n := n) (by simp) hi]
  simp [List.getD_eq_getElem?_getD, hi]

lemma beC (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    cv n C x i = false :=
  val_ge (n := n) (by simp) hi

lemma Cmono (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (x1 x2 : Fin n → Bool) (hle : ∀ j, x1 j = true → x2 j = true) :
    ∀ i, cv n C x1 i = true → cv n C x2 i = true := by
  have A1 := c_run n 0 C hRB (fun _ => False) x1
  have A2 := c_run n 0 C hRB (fun _ => False) x2
  refine gen_all n 0 C (fun _ => False) hops (cv n C x1) (cv n C x2)
    (fun _ => cv n C x1 (n + 0)) (fun _ => cv n C x2 (n + 0)) (fc n C x1) (fc n C x2)
    A1.1 A2.1 A1.2 A2.2 ?_ ?_ (beC n C x1) (beC n C x2)
  · intro i hi h
    rw [inC n C x2 i hi]; rw [inC n C x1 i hi] at h; exact hle _ h
  · intro r _ hs; exact hs.elim

lemma Rmono (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (x1 x2 : Fin n → Bool) (hle : ∀ j, x1 j = true → x2 j = true) :
    ∀ i, cv n (red n g a C) x1 i = true → cv n (red n g a C) x2 i = true := by
  have A1 := r_run n g a C hRB x1
  have A2 := r_run n g a C hRB x2
  refine gen_all n g C (fun r => g < r) hops (cv n (red n g a C) x1) (cv n (red n g a C) x2)
    (fun r => if a < n + r then cv n (red n g a C) x1 a else false)
    (fun r => if a < n + r then cv n (red n g a C) x2 a else false)
    (fr n g a C x1) (fr n g a C x2) A1.1 A2.1 A1.2 A2.2 ?_ ?_ ?_ ?_
  · intro i hi h; rw [inC _ _ x2 i hi]; rw [inC _ _ x1 i hi] at h; exact hle _ h
  · intro r _ _ ih
    beta_reduce
    by_cases ha : a < n + r
    · rw [if_pos ha, if_pos ha]
      by_cases han : a < n
      · rw [inC _ _ x2 a han, inC _ _ x1 a han]; exact hle _
      · have := ih (a - n) (by omega); rw [show n + (a - n) = a by omega] at this; exact this
    · rw [if_neg ha, if_neg ha]; intro h; exact h
  · intro i hi; exact beC n _ x1 i (by rw [red_len]; exact hi)
  · intro i hi; exact beC n _ x2 i (by rw [red_len]; exact hi)

lemma cmpG (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (x : Fin n → Bool) (hyp : cv n C x a = true → cv n C x (n + g) = true) :
    ∀ i, cv n (red n g a C) x i = true → cv n C x i = true := by
  have A1 := r_run n g a C hRB x
  have A2 := c_run n g C hRB (fun r => g < r) x
  refine gen_all n g C (fun r => g < r) hops (cv n (red n g a C) x) (cv n C x)
    (fun r => if a < n + r then cv n (red n g a C) x a else false) (fun _ => cv n C x (n + g))
    (fr n g a C x) (fc n C x) A1.1 A2.1 A1.2 A2.2 ?_ ?_ ?_ (beC n C x)
  · intro i hi h; rw [inC _ _ x i hi]; rw [inC _ _ x i hi] at h; exact h
  · intro r _ _ ih
    beta_reduce
    by_cases ha : a < n + r
    · rw [if_pos ha]
      intro h
      have hca : cv n C x a = true := by
        by_cases han : a < n
        · rw [inC _ _ x a han]; rw [inC _ _ x a han] at h; exact h
        · have := ih (a - n) (by omega); rw [show n + (a - n) = a by omega] at this; exact this h
      exact hyp hca
    · rw [if_neg ha]; intro h; cases h
  · intro i hi; exact beC n _ x i (by rw [red_len]; exact hi)

lemma cmp2G (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hga : a < n + g) (x : Fin n → Bool) (hyp : cv n C x (n + g) = true → cv n C x a = true) :
    ∀ i, cv n C x i = true → cv n (red n g a C) x i = true := by
  have A1 := r_run n g a C hRB x
  have A2 := c_run n g C hRB (fun r => g < r) x
  refine gen_all n g C (fun r => g < r) hops (cv n C x) (cv n (red n g a C) x)
    (fun _ => cv n C x (n + g)) (fun r => if a < n + r then cv n (red n g a C) x a else false)
    (fc n C x) (fr n g a C x) A2.1 A1.1 A2.2 A1.2 ?_ ?_ (beC n C x) ?_
  · intro i hi h; rw [inC _ _ x i hi]; rw [inC _ _ x i hi] at h; exact h
  · intro r _ hs ih
    beta_reduce
    rw [if_pos (by omega)]
    intro h
    have h1 := hyp h
    by_cases han : a < n
    · rw [inC _ _ x a han]; rw [inC _ _ x a han] at h1; exact h1
    · have := ih (a - n) (by omega); rw [show n + (a - n) = a by omega] at this; exact this h1
  · intro i hi; exact beC n _ x i (by rw [red_len]; exact hi)

lemma upO (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hga : a < n + g) (x : Fin n → Bool) (hyp : cv n C x (n + g) = true → cv n C x a = true)
    (h : cv n C x C.output = true) :
    cv n (red n g a C) x (if C.output = n + g then a else C.output) = true := by
  by_cases ho : C.output = n + g
  · rw [if_pos ho]; rw [ho] at h; exact cmp2G n g a C hRB hops hga x hyp a (hyp h)
  · rw [if_neg ho]; exact cmp2G n g a C hRB hops hga x hyp _ h

lemma downO (n g a : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (x : Fin n → Bool) (hyp : cv n C x a = true → cv n C x (n + g) = true)
    (h : cv n (red n g a C) x (if C.output = n + g then a else C.output) = true) :
    cv n C x C.output = true := by
  by_cases ho : C.output = n + g
  · rw [if_pos ho] at h; rw [ho]; exact hyp (cmpG n g a C hRB hops x hyp a h)
  · rw [if_neg ho] at h; exact cmpG n g a C hRB hops x hyp _ h

/-- Gates-only redirect: every read of wire `n + g` becomes a read of `a`; the output is KEPT
(the 3710 shape). Same gate list as `red`, so all wire values agree with `red` (`cv_redK`). -/
def redK (n g a : ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : Gate)),
    output := C.output }

lemma cv_redK (n g a : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    cv n (redK n g a C) x i = cv n (red n g a C) x i := rfl

lemma ops_of_AO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or :=
  fun r hr => h.1 _ (gateAt_mem hr)

lemma rb_of_AO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : ReadsBack n C := h.2.1

/-- Value of an AND gate with inputs `[a, b]` (either order). -/
lemma and_gate_cv (n g a b : ℕ) (C : Circuit) (hRB : ReadsBack n C) (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.and)
    (hin : (gateAt C g).inputs = [a, b] ∨ (gateAt C g).inputs = [b, a]) :
    ∀ x, cv n C x (n + g) = (cv n C x a && cv n C x b) := by
  have hmem : a ∈ (gateAt C g).inputs ∧ b ∈ (gateAt C g).inputs := by
    rcases hin with h | h <;> rw [h] <;> simp
  have hga := hRB g hg a hmem.1
  have hgb := hRB g hg b hmem.2
  intro x
  unfold cv
  rw [val_gate (n := n) (C := C) (x := List.ofFn x) (by simp) hg, hop]
  rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hga, hgb, Bool.and_comm]

/-- Gate `g = a AND b`, redirect reads of `g` to `a`: down direction when `a → b` at `x`. -/
lemma cmpAnd (n g a b : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hgv : ∀ x, cv n C x (n + g) = (cv n C x a && cv n C x b))
    (x : Fin n → Bool) (hab : cv n C x a = true → cv n C x b = true) :
    ∀ i, cv n (red n g a C) x i = true → cv n C x i = true :=
  cmpG n g a C hRB hops x (fun h => by rw [hgv x, h, hab h]; rfl)

/-- Gate `g = a AND b`, redirect reads of `g` to `a`: up direction, always. -/
lemma cmp2And (n g a b : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hga : a < n + g)
    (hgv : ∀ x, cv n C x (n + g) = (cv n C x a && cv n C x b)) (x : Fin n → Bool) :
    ∀ i, cv n C x i = true → cv n (red n g a C) x i = true :=
  cmp2G n g a C hRB hops hga x (fun h => by rw [hgv x, Bool.and_eq_true] at h; exact h.1)

/-! ## Edge functions: monotone + true on edges + false on maximal independent sets -/

lemma graphFun_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n}
    (huv : G.Adj u v) : graphFun G ∅ (fun z => decide (z = u ∨ z = v)) = true := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨u, v, huv, by simp, by simp⟩

lemma graphFun_indep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Finset (Fin n))
    (hM : ∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) : graphFun G ∅ (fun z => decide (z ∈ M)) = false := by
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  exact hM a ha b hb hab

/-- Any monotone Boolean function that is true on every edge and false on every maximal
independent set is the edge function `graphFun G ∅`. -/
theorem fun_eq_graphFun (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ j, x j = true → y j = true) → f x = true → f y = true)
    (hedge : ∀ u v : Fin n, G.Adj u v → f (fun z => decide (z = u ∨ z = v)) = true)
    (hmis : ∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) →
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) → f (fun z => decide (z ∈ M)) = true → False) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    by_contra hFx
    have hno : ∀ u v, G.Adj u v → x u = true → x v = true → False := by
      intro u v huv hu hv; apply hFx
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨u, v, huv, hu, hv⟩
    let S : Finset (Fin n) := Finset.univ.filter (fun j => x j = true)
    let P : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun M : Finset (Fin n) => S ⊆ M ∧ ∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v)
    have hSP : S ∈ P := by
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨subset_rfl, ?_⟩
      intro u hu v hv huv
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact hno u v huv hu hv
    obtain ⟨M, hMP, hMmax⟩ := Finset.exists_max_image P Finset.card ⟨S, hSP⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hMP
    obtain ⟨hSM, hMind⟩ := hMP
    have hMdom : ∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v := by
      intro v hv
      by_contra hc
      push_neg at hc
      have hins : insert v M ∈ P := by
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hSM.trans (Finset.subset_insert _ _), ?_⟩
        intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl hab
        · exact hc b hb hab.symm
        · exact hc a ha hab
        · exact hMind a ha b hb hab
      have h1 := hMmax _ hins
      have h2 := Finset.card_lt_card (Finset.ssubset_insert hv)
      omega
    have hxz : ∀ j, x j = true → (fun z => decide (z ∈ M)) j = true := fun j hj => by
      simp only [decide_eq_true_eq]
      exact hSM (by simp [S, hj])
    exact hmis M hMind hMdom (hmono x _ hxz h)
  · intro h
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨a, ha, _⟩ | ⟨u, v, huv, hu, hv⟩
    · simp at ha
    refine hmono _ x (fun j hj => ?_) (hedge u v huv)
    simp only [decide_eq_true_eq] at hj
    rcases hj with rfl | rfl
    · exact hu
    · exact hv

/-- AND/OR circuits that read back compute monotone functions. -/
lemma circuitFun_mono (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or) :
    ∀ x y : Fin n → Bool, (∀ j, x j = true → y j = true) →
      PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true :=
  fun x y h => Cmono n C hRB hops x y h C.output

/-- Two circuits: if `C` computes the edge function, `D` is AND/OR reading back, `D ≥ C` on edge
inputs and `D ≤ C` on maximal independent sets, then `D` computes the edge function too. -/
theorem mono_circuit_graphFun (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C D : Circuit)
    (hRB : ReadsBack n D)
    (hops : ∀ r < D.gates.length, (gateAt D r).op = GateOp.and ∨ (gateAt D r).op = GateOp.or)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      PEqualNP.MetaComplexity.circuitFun n C (fun z => decide (z = u ∨ z = v)) = true →
      PEqualNP.MetaComplexity.circuitFun n D (fun z => decide (z = u ∨ z = v)) = true)
    (hmis : ∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) →
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
      PEqualNP.MetaComplexity.circuitFun n D (fun z => decide (z ∈ M)) = true →
      PEqualNP.MetaComplexity.circuitFun n C (fun z => decide (z ∈ M)) = true) :
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
  apply fun_eq_graphFun n G _ (circuitFun_mono n D hRB hops)
  · intro u v huv
    exact hedge u v huv (by rw [hF]; exact graphFun_edge G huv)
  · intro M hM hdom h
    have h2 := hmis M hM hdom h
    rw [hF, graphFun_indep G M hM] at h2
    cases h2

/-- The 3724 replacement rule, general: redirect every read of gate `w` (and the output, if it is
`w`) to an earlier wire `w2`. Same edge function if `w → w2` on edge inputs and `w2 → w` on
maximal independent sets. -/
theorem redirect_graphFun (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w w2 : ℕ) (hRB : ReadsBack n C)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (hw2 : w2 < n + w)
    (hK : ∀ u v : Fin n, G.Adj u v → cv n C (fun z => decide (z = u ∨ z = v)) (n + w) = true →
      cv n C (fun z => decide (z = u ∨ z = v)) w2 = true)
    (hZ : ∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) →
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
      cv n C (fun z => decide (z ∈ M)) w2 = true → cv n C (fun z => decide (z ∈ M)) (n + w) = true) :
    PEqualNP.MetaComplexity.circuitFun n (red n w w2 C) = graphFun G ∅ := by
  apply fun_eq_graphFun n G
  · intro x y hxy h
    exact Rmono n w w2 C hRB hops x y hxy (red n w w2 C).output h
  · intro u v huv
    have he : PEqualNP.MetaComplexity.circuitFun n C (fun z => decide (z = u ∨ z = v)) = true := by
      rw [hF]; exact graphFun_edge G huv
    exact upO n w w2 C hRB hops hw2 _ (hK u v huv) he
  · intro M hM hdom h
    have h1 := downO n w w2 C hRB hops _ (hZ M hM hdom) h
    have h2 : PEqualNP.MetaComplexity.circuitFun n C (fun z => decide (z ∈ M)) = true := h1
    rw [hF, graphFun_indep G M hM] at h2
    cases h2


lemma sub_eq_redK (n j y : ℕ) (C : Circuit) :
    PEqualNP.FactorSubst.substReads C n j (fun _ => y) = redK n j y C := by
  unfold PEqualNP.FactorSubst.substReads redK
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem main4748 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j y : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true))
    (hy : y < n + j)
    (hY : ∀ x : Fin n → Bool, cv n C x y =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true ∧
        cv n C (fun i => decide (i = a ∨ i = b)) (n + j) = true)) :
    ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n
        (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  have hRB := hAO.2.1
  have hops := ops_of_AO2 hAO
  have hF' : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅ := by
    funext x; rw [hF x]; simp [graphFun]
  have key : (fun x => cv n (red n j y C) x C.output) = graphFun G ∅ := by
    apply fun_eq_graphFun n G
    · intro x1 x2 hle h; exact Rmono n j y C hRB hops x1 x2 hle _ h
    · intro u v huv
      have he : cv n C (fun z => decide (z = u ∨ z = v)) C.output = true := by
        have := congrFun hF' (fun z => decide (z = u ∨ z = v))
        rw [graphFun_edge G huv] at this; exact this
      refine cmp2G n j y C hRB hops hy _ ?_ _ he
      intro hj; rw [hY]; simp only [decide_eq_true_eq]
      exact ⟨u, v, huv, by simp, by simp, hj⟩
    · intro M hM _ h
      have hyp : cv n C (fun z => decide (z ∈ M)) y = true →
          cv n C (fun z => decide (z ∈ M)) (n + j) = true := by
        intro hc; rw [hY] at hc; simp only [decide_eq_true_eq] at hc
        obtain ⟨a, b, hab, ha, hb, _⟩ := hc
        exact absurd hab (hM a ha b hb)
      have h1 := cmpG n j y C hRB hops _ hyp _ h
      have h2 : PEqualNP.MetaComplexity.circuitFun n C (fun z => decide (z ∈ M)) = true := h1
      rw [hF', graphFun_indep G M hM] at h2
      cases h2
  intro x
  rw [sub_eq_redK]
  show cv n (red n j y C) x C.output = _
  rw [congrFun key x]; simp [graphFun]

end PEqualNP.Outside.L_meta_4748

theorem PEqualNP.Outside.L_meta_4748 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j y : ℕ),
  PEqualNP.TopForm.IsAO2 n C → j < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
  y < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD y false =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true ∧
        (C.wires (List.ofFn (fun i => decide (i = a ∨ i = b)))).getD (n + j) false = true)) →
  ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro n G _ C j y hAO _ _ hF hy hY
  exact PEqualNP.Outside.L_meta_4748.main4748 n G C j y hAO hF hy hY
