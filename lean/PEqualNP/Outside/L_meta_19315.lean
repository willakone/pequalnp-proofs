import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19315_aux

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

-- FRAGMENT restrict    DEPENDS: fold mono
-- Dropping a set S of gates that no kept gate reads (S read-closed), with renumbering of the kept wires
-- (rows 2774, 3312). Reading back with an offset (RBo) for gate lists built piece by piece.
-- Abbreviation: hcl = for all k < C.gates.length, k not in S -> for all i in (gateAt C k).inputs, i < n or i - n not in S.
-- Exports:
--   def RBo b gs : for all p < gs.length, every input i of gs.getD p (OR of nothing) has i < b + p
--       (RBo n C.gates is ReadsBack n C by unfolding; RBo n D.gates proves the ReadsBack part of IsAO2 n D)
--   RBo_nil b ;  RBo_cons (all inputs of g below b) (RBo (b + 1) gs) : RBo b (g :: gs)
--   RBo_append (RBo b g1) (RBo (b + g1.length) g2) : RBo b (g1 ++ g2)
--   def keepL S m := (List.range m).filter (not in S) ;  def rk S m := (keepL S m).length (new index of old gate m)
--   def rn n S w := if w < n then w else n + rk S (w - n)  (new wire of old wire w)
--   def mkG n C S j := gate j with inputs mapped by rn n S ;  def Dg n C S m := (keepL S m).map (mkG n C S)
--   keepL_succ_in / keepL_succ_out, Dg_succ_in (m in S) : Dg (m+1) = Dg m ;  Dg_succ_out : Dg (m+1) = Dg m ++ [mkG m]
--   rk_mono (a <= b) : rk S a <= rk S b ;  rk_lt (j < m) (j not in S) : rk S j < rk S m ;  rk_succ_out (m not in S) : rk S (m+1) = rk S m + 1
--   rn_lt (i < n + m) (i < n or i - n not in S) : rn n S i < n + rk S m ;  rn_gate : rn n S (n + o) = n + rk S o
--   Dg_len : (Dg n C S m).length = rk S m ;  keep_gate : j in keepL S C.gates.length -> gateAt C j in C.gates
--   restrict_val (ReadsBack n C) hcl (x.length = n) : for m <= len, (W (Dg n C S m) x).length = n + rk S m and
--       for every w < n + m with (w < n or w - n not in S), (W (Dg n C S m) x).getD (rn n S w) false = val C x w
--   restrict_rb (ReadsBack n C) hcl : m <= len -> RBo n (Dg n C S m)
--   restrict_size (all j in S below len) : (Dg n C S C.gates.length).length + S.card <= C.gates.length
--   restrict_circ (IsAO2 n C) hcl (S below len) (o < len, o not in S, C.output = n + o) :
--       exists D, IsAO2 n D and circuitFun n D = circuitFun n C and D.size + S.card <= C.size
--       (D = the circuit with gates Dg n C S C.gates.length and output n + rk S o)
-- Use: pick the dead set S, prove hcl, then restrict_circ; for other gate shapes use restrict_val / restrict_rb directly
-- (keep_gate transports per-gate properties such as op or fan-in). For S = gates outside the output cone see frag live.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : rk S (m + 1) = rk S m + 1 := by
  unfold rk
  rw [keepL_succ_out S m h, List.length_append, List.length_singleton]

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 := rk_succ_out S j hS
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem rn_gate (n : ℕ) (S : Finset ℕ) (o : ℕ) : rn n S (n + o) = n + rk S o := by
  unfold rn
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  exact gateAt_mem hjl

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : List Bool) (hx : x.length = n) :
    ∀ m, m ≤ C.gates.length →
      (W (Dg n C S m) x).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (W (Dg n C S m) x).getD (rn n S w) false = val C x w := by
  have hsn : ∀ (l : List Bool) (b : Bool) (k : ℕ), l.length = k → (l ++ [b]).getD k false = b := by
    intro l b k hk
    subst hk
    exact getD_app_len l b
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [W_length, Dg_len, hx]
    · intro w hw _
      have hw' : w < n := by omega
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e, W_prefix (Dg n C S 0) x w (by omega), val_input hx hw']
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · rw [Dg_succ_out n C S m hS, rk_succ_out S m hS, W_append]
      have hsingle : ∀ v : List Bool, W [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          rw [rn_gate, hsn _ _ _ hlen, val_gate_rb hx (by omega) (hRB m (by omega)), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_app_lt _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem restrict_size (n : ℕ) (C : Circuit) (S : Finset ℕ) (hS : ∀ j ∈ S, j < C.gates.length) :
    (Dg n C S C.gates.length).length + S.card ≤ C.gates.length := by
  have h3 : (List.range C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length +
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length :=
    List.length_eq_length_filter_add _
  have h4 : S.card ≤ ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length := by
    refine le_trans (Finset.card_le_card ?_)
      (List.toFinset_card_le (l := (List.range C.gates.length).filter (fun j => decide (j ∈ S))))
    intro j hj
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr (hS j hj), by simpa using hj⟩
  have h5 : (Dg n C S C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length := Dg_len n C S _
  rw [List.length_range] at h3
  omega

theorem restrict_circ (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ S) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  refine ⟨⟨Dg n C S C.gates.length, n + rk S o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact hao (gateAt C j) (keep_gate C S j hj)
  · exact restrict_rb n C S hRB hcl _ le_rfl
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    have := h2 _ (keep_gate C S j hj)
    show ((gateAt C j).inputs.map (rn n S)).length = 2
    rw [List.length_map]
    exact this
  · funext x
    have h := (restrict_val n C S hRB hcl (List.ofFn x) (by simp) C.gates.length le_rfl).2 (n + o)
      (by omega) (Or.inr (by rw [Nat.add_sub_cancel_left]; exact hoS))
    rw [rn_gate] at h
    show (W (Dg n C S C.gates.length) (List.ofFn x)).getD (n + rk S o) false =
      val C (List.ofFn x) C.output
    rw [hout]
    exact h
  · exact restrict_size n C S hS

-- FRAGMENT orchain    DEPENDS: fold mono restrict
-- OR chains over a list of existing wires placed at an offset b (the first chain gate is wire b), stars
-- x_c AND (OR of a list) and blocks of several stars, with their values, lengths, ReadsBack (RBo) and gate shapes.
-- Exports (w : List Bool is the wire list before the block, w.length = b):
--   def ocg t L b : OR chain: gates OR(t, L0) at wire b, OR(b, L1) at wire b + 1, ... (L.length gates)
--   def octop t L b : its top wire (t if L = [], else b + L.length - 1) ;  octop_nil, octop_cons (L ne []) ;  octop_lt (t < b) : octop t L b < b + L.length
--   ocg_len : (ocg t L b).length = L.length ;  ocg_gate : g in ocg t L b -> g.op = or and g.inputs.length = 2
--   ocg_val (w.length = b) (t < b) (all of L < b) :
--       (W (ocg t L b) w).getD (octop t L b) false = true iff (w.getD t false = true or exists i in L, w.getD i false = true)
--   ocg_rb (t < b) (all of L < b) : RBo b (ocg t L b)
--   def ostar c L b : the star x_c AND OR(L): [] if L = [], else ocg L0 (tail) b ++ [AND(c, top)] (L.length gates, star wire b + L.length - 1)
--   ostar_len : (ostar c L b).length = L.length ;  ostar_gate : g in ostar c L b -> (op and or or) and 2 inputs
--   ostar_val (L ne []) (w.length = b) (c < b) (all of L < b) :
--       (W (ostar c L b) w).getD (b + L.length - 1) false = true iff (w.getD c false = true and exists i in L, w.getD i false = true)
--   ostar_rb (c < b) (all of L < b) : RBo b (ostar c L b)
--   def ostars Lf cs b : stars of the centres cs (list of wires, block of centre c uses the list Lf c), one after the other
--   def ostarW Lf cs b d : the star wire of the first occurrence of centre d in cs
--   ostars_len : (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum ;  ostars_gate : shapes as ostar_gate
--   ostars_val (w.length = b) (all c in cs, c < b) (all c in cs, all i in Lf c, i < b) (d in cs) (Lf d ne []) :
--       ostarW Lf cs b d < b + (ostars Lf cs b).length and ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true
--       iff (w.getD d false = true and exists i in Lf d, w.getD i false = true))
--   ostars_rb (same bounds) : RBo b (ostars Lf cs b)
--   def ochain L b := chain OR over L at b (L.length - 1 gates, [] for L = [] or one wire) ;  def ochainTop L b : its top wire
--   ochain_len ;  ochain_gate (OR, 2 inputs) ;  ochain_rb (all of L < b) : RBo b (ochain L b)
--   ochain_val (L ne []) (w.length = b) (all of L < b) : ochainTop L b < b + (ochain L b).length and
--       ((W (ochain L b) w).getD (ochainTop L b) false = true iff exists i in L, w.getD i false = true)
--   def ochains Lf Xs b / ochainsW Lf Xs b d : one chain per key X (over the wire list Lf X), one after the other, and the top of key d
--   ochains_len : length = (Xs.map fun X => (Lf X).length - 1).sum ;  ochains_gate ;  ochains_rb (all wires < b)
--   ochains_val (w.length = b) (all wires < b) (d in Xs) (Lf d ne []) : ochainsW < b + length and
--       (value at ochainsW iff exists i in Lf d, w.getD i false = true)
--   oc_ex (all i in L, w1.getD i false = w.getD i false) : (exists i in L, w1 true) iff (exists i in L, w true)
-- Use: as the middle block of frag reorder (block placed after the kept head part, b = n + head part length); the star
-- wire values then come from ostars_val with w = the run of the head part, and frag reorder transports them.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ocg : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | t, i :: L, b => ⟨GateOp.or, [t, i]⟩ :: ocg b L (b + 1)

def octop : ℕ → List ℕ → ℕ → ℕ
  | t, [], _ => t
  | _, _ :: L, b => octop b L (b + 1)

theorem oc_ex (L : List ℕ) (w1 w : List Bool) (h : ∀ i ∈ L, w1.getD i false = w.getD i false) :
    (∃ i ∈ L, w1.getD i false = true) ↔ (∃ i ∈ L, w.getD i false = true) := by
  constructor
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [← h i hi]; exact h1⟩
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [h i hi]; exact h1⟩

theorem ocg_len (L : List ℕ) : ∀ (t b : ℕ), (ocg t L b).length = L.length := by
  induction L with
  | nil => intro t b; rfl
  | cons i L ih =>
    intro t b
    show (ocg b L (b + 1)).length + 1 = L.length + 1
    rw [ih]

theorem octop_nil (t b : ℕ) : octop t [] b = t := rfl

theorem octop_cons (L : List ℕ) : ∀ (t b : ℕ), L ≠ [] → octop t L b = b + L.length - 1 := by
  induction L with
  | nil => intro t b h; exact absurd rfl h
  | cons i L ih =>
    intro t b _
    show octop b L (b + 1) = b + (L.length + 1) - 1
    by_cases h : L = []
    · subst h
      rfl
    · rw [ih b (b + 1) h]
      omega

theorem octop_lt (L : List ℕ) (t b : ℕ) (ht : t < b) : octop t L b < b + L.length := by
  by_cases h : L = []
  · subst h
    rw [octop_nil]
    simp
    exact ht
  · rw [octop_cons L t b h]
    have : L.length ≠ 0 := by
      intro h0
      exact h (List.length_eq_zero_iff.mp h0)
    omega

theorem ocg_gate (L : List ℕ) : ∀ (t b : ℕ) (g : Gate), g ∈ ocg t L b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction L with
  | nil => intro t b g hg; simp [ocg] at hg
  | cons i L ih =>
    intro t b g hg
    have hg' : g ∈ (⟨GateOp.or, [t, i]⟩ : Gate) :: ocg b L (b + 1) := hg
    rcases List.mem_cons.mp hg' with h1 | h1
    · subst h1
      exact ⟨rfl, rfl⟩
    · exact ih b (b + 1) g h1

theorem ocg_val (L : List ℕ) : ∀ (t b : ℕ) (w : List Bool), w.length = b → t < b → (∀ i ∈ L, i < b) →
    ((W (ocg t L b) w).getD (octop t L b) false = true ↔
      (w.getD t false = true ∨ ∃ i ∈ L, w.getD i false = true)) := by
  induction L with
  | nil =>
    intro t b w _ _ _
    simp [ocg, octop, W_nil]
  | cons i L ih =>
    intro t b w hw ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    have hs : ∀ a, a < b → (step w ⟨GateOp.or, [t, i]⟩).getD a false = w.getD a false :=
      fun a ha => step_lt w _ a (by omega)
    have hb : (step w ⟨GateOp.or, [t, i]⟩).getD b false = (w.getD t false || w.getD i false) := by
      rw [step_last w _ b hw.symm]
      simp [GateOp.eval]
    show (W (ocg b L (b + 1)) (step w ⟨GateOp.or, [t, i]⟩)).getD (octop b L (b + 1)) false = true ↔ _
    rw [ih b (b + 1) _ (by rw [step_len, hw]) (by omega) (fun a ha => by have := hL2 a ha; omega)]
    rw [hb, oc_ex L _ w (fun a ha => hs a (hL2 a ha))]
    constructor
    · rintro (h | ⟨a, ha, h⟩)
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro (h | ⟨a, ha, h⟩)
      · exact Or.inl (by rw [h]; rfl)
      · rcases List.mem_cons.mp ha with h2 | ha2
        · subst h2
          exact Or.inl (by rw [h, Bool.or_true])
        · exact Or.inr ⟨a, ha2, h⟩

theorem ocg_rb (L : List ℕ) : ∀ (t b : ℕ), t < b → (∀ i ∈ L, i < b) → RBo b (ocg t L b) := by
  induction L with
  | nil => intro t b _ _; exact RBo_nil b
  | cons i L ih =>
    intro t b ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    apply RBo_cons
    · intro a ha
      have ha' : a ∈ [t, i] := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with h | h <;> omega
    · exact ih b (b + 1) (by omega)
        (fun a ha => by have := hL a (List.mem_cons.mpr (Or.inr ha)); omega)

def ostar : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | c, i :: L, b => ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]

theorem ostar_len (c : ℕ) (L : List ℕ) (b : ℕ) : (ostar c L b).length = L.length := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b ++ [_]).length = L.length + 1
    rw [List.length_append, ocg_len]
    rfl

theorem ostar_gate (c : ℕ) (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ostar c L b) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ostar] at hg
  | cons i L =>
    have hg' : g ∈ ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩] := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · have := ocg_gate L i b g h1
      exact ⟨Or.inr this.1, this.2⟩
    · rw [List.mem_singleton] at h1
      subst h1
      exact ⟨Or.inl rfl, rfl⟩

theorem ostar_val (c : ℕ) (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    ((W (ostar c L b) w).getD (b + L.length - 1) false = true ↔
      (w.getD c false = true ∧ ∃ i ∈ L, w.getD i false = true)) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show (W (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]) w).getD (b + (L.length + 1) - 1) false = true ↔ _
    have hlen : (W (ocg i L b) w).length = b + L.length := by rw [W_length, ocg_len, hw]
    rw [W_snoc, step_last _ _ _ (by rw [hlen]; omega)]
    have h1 : (W (ocg i L b) w).getD c false = w.getD c false := W_prefix _ w c (by omega)
    have h2 := ocg_val L i b w hw hi hL2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [h1, h2]
    constructor
    · rintro ⟨hc1, h | ⟨a, ha, h⟩⟩
      · exact ⟨hc1, i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨hc1, a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro ⟨hc1, a, ha, h⟩
      refine ⟨hc1, ?_⟩
      rcases List.mem_cons.mp ha with h3 | h3
      · subst h3
        exact Or.inl h
      · exact Or.inr ⟨a, h3, h⟩

theorem ostar_rb (c : ℕ) (L : List ℕ) (b : ℕ) (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    RBo b (ostar c L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show RBo b (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩])
    apply RBo_append _ _ _ (ocg_rb L i b hi hL2)
    apply RBo_cons _ _ _ _ (RBo_nil _)
    intro a ha
    have ha' : a ∈ [c, octop i L b] := ha
    have htop := octop_lt L i b hi
    rw [ocg_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with h | h <;> omega

def ostars (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | c :: cs, b => ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)

def ostarW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, b, d => if c = d then b + (Lf c).length - 1 else ostarW Lf cs (b + (Lf c).length) d

theorem ostars_len (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b,
    (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum := by
  induction cs with
  | nil => intro b; rfl
  | cons c cs ih =>
    intro b
    show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
    rw [List.length_append, ostar_len, ih, List.map_cons, List.sum_cons]

theorem ostars_gate (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b (g : Gate), g ∈ ostars Lf cs b →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction cs with
  | nil => intro b g hg; simp [ostars] at hg
  | cons c cs ih =>
    intro b g hg
    have hg' : g ∈ ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ostar_gate c (Lf c) b g h1
    · exact ih _ g h1

theorem ostars_rb (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b, (∀ c ∈ cs, c < b) →
    (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → RBo b (ostars Lf cs b) := by
  induction cs with
  | nil => intro b _ _; exact RBo_nil b
  | cons c cs ih =>
    intro b hc hi
    show RBo b (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length))
    apply RBo_append _ _ _ (ostar_rb c (Lf c) b (hc c (List.mem_cons.mpr (Or.inl rfl)))
      (hi c (List.mem_cons.mpr (Or.inl rfl))))
    rw [ostar_len]
    apply ih
    · intro d hd
      have := hc d (List.mem_cons.mpr (Or.inr hd))
      omega
    · intro d hd i hi2
      have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
      omega

theorem ostars_val (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ c ∈ cs, c < b) → (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → ∀ d ∈ cs, Lf d ≠ [] →
    ostarW Lf cs b d < b + (ostars Lf cs b).length ∧
    ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true ↔
      (w.getD d false = true ∧ ∃ i ∈ Lf d, w.getD i false = true)) := by
  induction cs with
  | nil => intro b w _ _ _ d hd; simp at hd
  | cons c cs ih =>
    intro b w hw hc hi d hd hLd
    have hc0 : c < b := hc c (List.mem_cons.mpr (Or.inl rfl))
    have hi0 : ∀ i ∈ Lf c, i < b := hi c (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ostar c (Lf c) b) w).length = b + (Lf c).length := by
      rw [W_length, ostar_len, hw]
    have hpre : ∀ a, a < b → (W (ostar c (Lf c) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ostars Lf (c :: cs) b) w = W (ostars Lf cs (b + (Lf c).length)) (W (ostar c (Lf c) b) w) :=
      W_append _ _ w
    have eL : (ostars Lf (c :: cs) b).length = (Lf c).length + (ostars Lf cs (b + (Lf c).length)).length := by
      show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
      rw [List.length_append, ostar_len]
    rw [eW, eL]
    by_cases hcd : c = d
    · subst hcd
      have ew : ostarW Lf (c :: cs) b c = b + (Lf c).length - 1 := by
        show (if c = c then b + (Lf c).length - 1 else _) = _
        rw [if_pos rfl]
      have hpos : (Lf c).length ≠ 0 := by
        intro h0
        exact hLd (List.length_eq_zero_iff.mp h0)
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact ostar_val c (Lf c) b w hLd hw hc0 hi0
    · have ew : ostarW Lf (c :: cs) b d = ostarW Lf cs (b + (Lf c).length) d := by
        show (if c = d then b + (Lf c).length - 1 else _) = _
        rw [if_neg hcd]
      have hd2 : d ∈ cs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hcd
        · exact h
      have hcs : ∀ e ∈ cs, e < b := fun e he => hc e (List.mem_cons.mpr (Or.inr he))
      have his : ∀ e ∈ cs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (Lf c).length) _ hlen1
        (fun e he => by have := hcs e he; omega)
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, hpre d (hcs d hd2), oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def ochain : List ℕ → ℕ → List Gate
  | [], _ => []
  | i :: L, b => ocg i L b

def ochainTop : List ℕ → ℕ → ℕ
  | [], _ => 0
  | i :: L, b => octop i L b

theorem ochain_len (L : List ℕ) (b : ℕ) : (ochain L b).length = L.length - 1 := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b).length = L.length + 1 - 1
    rw [ocg_len]
    omega

theorem ochain_gate (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ochain L b) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ochain] at hg
  | cons i L => exact ocg_gate L i b g hg

theorem ochain_rb (L : List ℕ) (b : ℕ) (hL : ∀ i ∈ L, i < b) : RBo b (ochain L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    exact ocg_rb L i b (hL i (List.mem_cons.mpr (Or.inl rfl)))
      (fun a ha => hL a (List.mem_cons.mpr (Or.inr ha)))

theorem ochain_val (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hL : ∀ i ∈ L, i < b) :
    ochainTop L b < b + (ochain L b).length ∧
    ((W (ochain L b) w).getD (ochainTop L b) false = true ↔ ∃ i ∈ L, w.getD i false = true) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    refine ⟨?_, ?_⟩
    · show octop i L b < b + (ocg i L b).length
      rw [ocg_len]
      exact octop_lt L i b hi
    · show (W (ocg i L b) w).getD (octop i L b) false = true ↔ _
      rw [ocg_val L i b w hw hi hL2]
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
      · rintro ⟨a, ha, h⟩
        rcases List.mem_cons.mp ha with h2 | h2
        · subst h2
          exact Or.inl h
        · exact Or.inr ⟨a, h2, h⟩

def ochains (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | X :: Xs, b => ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)

def ochainsW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | X :: Xs, b, d => if X = d then ochainTop (Lf X) b else ochainsW Lf Xs (b + (ochain (Lf X) b).length) d

theorem ochains_len (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b,
    (ochains Lf Xs b).length = (Xs.map fun X => (Lf X).length - 1).sum := by
  induction Xs with
  | nil => intro b; rfl
  | cons X Xs ih =>
    intro b
    show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
    rw [List.length_append, ochain_len, ih, List.map_cons, List.sum_cons]

theorem ochains_gate (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b (g : Gate), g ∈ ochains Lf Xs b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction Xs with
  | nil => intro b g hg; simp [ochains] at hg
  | cons X Xs ih =>
    intro b g hg
    have hg' : g ∈ ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ochain_gate (Lf X) b g h1
    · exact ih _ g h1

theorem ochains_rb (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b, (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) →
    RBo b (ochains Lf Xs b) := by
  induction Xs with
  | nil => intro b _; exact RBo_nil b
  | cons X Xs ih =>
    intro b hi
    show RBo b (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length))
    apply RBo_append _ _ _ (ochain_rb (Lf X) b (hi X (List.mem_cons.mpr (Or.inl rfl))))
    apply ih
    intro d hd i hi2
    have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
    omega

theorem ochains_val (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) → ∀ d ∈ Xs, Lf d ≠ [] →
    ochainsW Lf Xs b d < b + (ochains Lf Xs b).length ∧
    ((W (ochains Lf Xs b) w).getD (ochainsW Lf Xs b d) false = true ↔
      ∃ i ∈ Lf d, w.getD i false = true) := by
  induction Xs with
  | nil => intro b w _ _ d hd; simp at hd
  | cons X Xs ih =>
    intro b w hw hi d hd hLd
    have hi0 : ∀ i ∈ Lf X, i < b := hi X (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ochain (Lf X) b) w).length = b + (ochain (Lf X) b).length := by
      rw [W_length, hw]
    have hpre : ∀ a, a < b → (W (ochain (Lf X) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ochains Lf (X :: Xs) b) w =
        W (ochains Lf Xs (b + (ochain (Lf X) b).length)) (W (ochain (Lf X) b) w) := W_append _ _ w
    have eL : (ochains Lf (X :: Xs) b).length =
        (ochain (Lf X) b).length + (ochains Lf Xs (b + (ochain (Lf X) b).length)).length := by
      show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
      rw [List.length_append]
    rw [eW, eL]
    by_cases hXd : X = d
    · subst hXd
      have ew : ochainsW Lf (X :: Xs) b X = ochainTop (Lf X) b := by
        show (if X = X then ochainTop (Lf X) b else _) = _
        rw [if_pos rfl]
      obtain ⟨hlt, hv⟩ := ochain_val (Lf X) b w hLd hw hi0
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact hv
    · have ew : ochainsW Lf (X :: Xs) b d = ochainsW Lf Xs (b + (ochain (Lf X) b).length) d := by
        show (if X = d then ochainTop (Lf X) b else _) = _
        rw [if_neg hXd]
      have hd2 : d ∈ Xs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hXd
        · exact h
      have his : ∀ e ∈ Xs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (ochain (Lf X) b).length) _ hlen1
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

-- FRAGMENT agree    DEPENDS: fold mono
-- Two runs (two gate lists, two inputs) agree on every wire outside a set P of changed wires, provided each
-- unchanged gate computes the same value whenever its earlier wires agree outside P; cone versions.
-- Exports:
--   def ag_gat gs k := gs.getD k (OR of nothing)   (gateAt C k = ag_gat C.gates k by rfl)
--   def ag_val g w := g.op.eval (g.inputs.map fun q => w.getD q false)   (step w g = w ++ [ag_val g w] by rfl)
--   ag_gat_eq (k < gs.length) : ag_gat gs k = gs[k] ;  ag_gat_of (gs[k]? = some g) : ag_gat gs k = g
--   ag_gat_set_eq (i < gs.length) : ag_gat (gs.set i g) i = g ;  ag_gat_set_ne (k ne i) : ag_gat (gs.set i g) k = ag_gat gs k
--   ag_W_take (k <= gs.length) (q < x.length + k) : (W (gs.take k) x) at q = (W gs x) at q
--   ag_W_fix (k < gs.length) (inputs of gate k below x.length + k) : (W gs x) at (x.length + k) = ag_val (ag_gat gs k) (W gs x)
--   agree_stepP : one step keeps agreement outside P if the new wire is in P or the two new values agree
--   agreeP2 x x2 gs gs2 P (x2.length = x.length) (gs2.length = gs.length) (x2, x agree outside P)
--       (hstep: for k < gs.length with not P (x.length + k), agreement outside P of the runs of gs2.take k, gs.take k
--        implies ag_val (ag_gat gs2 k) on run2 = ag_val (ag_gat gs k) on run1) :
--       for all k <= gs.length, q not in P : (W (gs2.take k) x2) at q = (W (gs.take k) x) at q
--   agreeP2_full : same, conclusion for the full runs: (W gs2 x2) at q = (W gs x) at q for q not in P
--   agreeP_full x gs gs2 P (same input x) : as agreeP2_full (the 2920 form)
--   agree_full x gs gs2 i m p (p = x.length + i) (gates equal except i, m) (only gate m reads p)
--       (gate m values agree when runs agree off p) : for all q ne p, (W gs2 x) at q = (W gs x) at q
--   agree_closed x x2 gs gs2 B (lengths) (inputs agree off B) (gate k with wire not in B is unchanged)
--       (gate k with wire not in B reads only wires not in B) : (W gs2 x2) at q = (W gs x) at q for q not in B
--   def ag_rd L gs z w : exists k < gs.length, w = L + k and z is an input of ag_gat gs k   (z is read by wire w)
--   agree_cone x x2 gs y (x2.length = x.length) (x2, x agree on every input q < x.length that reaches y
--       by Relation.ReflTransGen (ag_rd x.length gs)) : (W gs x2) at y = (W gs x) at y
--   agree_cone_val n C x x2 y (x2 t = x t for every t : Fin n reaching y) : val C (ofFn x2) y = val C (ofFn x) y
--   agree_except_one n C x x2 u y (x2 t = x t for t ne u) (u does not reach y) : val C (ofFn x2) y = val C (ofFn x) y
--   agree_ofFn x y k (agree off k) (i ne k) : (List.ofFn x) at i = (List.ofFn y) at i
--   ag_rb_core : read-back bound of a gate list survives changing gates i and m if the new gates i, m read back
-- Use: for a local rewrite (gs2 = gs with a few gates set), apply agreeP_full or agree_closed with P = the changed
-- wires, prove the changed gate values by hand (ag_W_take / ag_W_fix), and evaluate the output (not in P).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ag_gat (gs : List Gate) (k : ℕ) : Gate := gs.getD k ⟨GateOp.or, []⟩

def ag_val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun q => w.getD q false)

theorem ag_gat_eq (gs : List Gate) (k : ℕ) (hk : k < gs.length) : ag_gat gs k = gs[k] :=
  List.getD_eq_getElem _ _ hk

theorem ag_gat_set_eq (gs : List Gate) (i : ℕ) (g : Gate) (hi : i < gs.length) :
    ag_gat (gs.set i g) i = g := by
  unfold ag_gat
  rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hi)]
  simp

theorem ag_gat_set_ne (gs : List Gate) (i k : ℕ) (g : Gate) (h : k ≠ i) :
    ag_gat (gs.set i g) k = ag_gat gs k := by
  unfold ag_gat
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem ag_gat_of (gs : List Gate) (k : ℕ) (g : Gate) (h : gs[k]? = some g) : ag_gat gs k = g := by
  unfold ag_gat
  rw [List.getD_eq_getElem?_getD, h]
  rfl

theorem ag_W_take (gs : List Gate) (x : List Bool) (k q : ℕ) (hk : k ≤ gs.length)
    (hq : q < x.length + k) :
    (W (gs.take k) x).getD q false = (W gs x).getD q false := by
  have e : W gs x = W (gs.drop k) (W (gs.take k) x) := by
    rw [← W_append, List.take_append_drop]
  rw [e, W_prefix (gs.drop k) (W (gs.take k) x) q
    (by rw [W_length, List.length_take]; omega)]

theorem ag_W_fix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ q ∈ (ag_gat gs k).inputs, q < x.length + k) :
    (W gs x).getD (x.length + k) false = ag_val (ag_gat gs k) (W gs x) := by
  have e : W gs x = W (gs.drop (k + 1)) (step (W (gs.take k) x) (ag_gat gs k)) := by
    rw [ag_gat_eq gs k hk, ← W_cons, ← List.drop_eq_getElem_cons hk, ← W_append,
      List.take_append_drop]
  have hl : (W (gs.take k) x).length = x.length + k := by
    rw [W_length, List.length_take]; omega
  have h2 : (step (W (gs.take k) x) (ag_gat gs k)).getD (x.length + k) false
      = ag_val (ag_gat gs k) (W (gs.take k) x) := by
    show ((W (gs.take k) x) ++ [ag_val (ag_gat gs k) (W (gs.take k) x)]).getD (x.length + k) false = _
    rw [← hl]
    exact getD_app_len _ _
  conv_lhs => rw [e]
  rw [W_prefix _ _ _ (by rw [step_len]; omega), h2]
  unfold ag_val
  congr 1
  apply List.map_congr_left
  intro q hq
  exact ag_W_take gs x k q (le_of_lt hk) (hr q hq)

theorem agree_stepP (w w' : List Bool) (g g' : Gate) (P : ℕ → Prop) (hl : w'.length = w.length)
    (h : ∀ q, ¬ P q → w'.getD q false = w.getD q false)
    (hv : P w.length ∨ ag_val g' w' = ag_val g w) :
    ∀ q, ¬ P q → (step w' g').getD q false = (step w g).getD q false := by
  intro q hq
  show (w' ++ [ag_val g' w']).getD q false = (w ++ [ag_val g w]).getD q false
  by_cases h1 : q < w.length
  · rw [getD_app_lt w' _ q (by omega), getD_app_lt w _ q h1]
    exact h q hq
  · by_cases h2 : q = w.length
    · have e1 : (w ++ [ag_val g w]).getD q false = ag_val g w := by
        rw [h2]; exact getD_app_len w _
      have e2 : (w' ++ [ag_val g' w']).getD q false = ag_val g' w' := by
        rw [h2, ← hl]; exact getD_app_len w' _
      rw [e1, e2]
      rcases hv with hv | hv
      · rw [h2] at hq
        exact absurd hv hq
      · exact hv
    · have e1 : (w ++ [ag_val g w]).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      have e2 : (w' ++ [ag_val g' w']).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none e1, List.getElem?_eq_none e2]

theorem agreeP2 (x x' : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ P q → x'.getD q false = x.getD q false)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x') = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ k, k ≤ gs.length → ∀ q, ¬ P q →
      (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false := by
  intro k
  induction k with
  | zero =>
    intro _ q hq
    simp only [List.take_zero]
    exact hin q hq
  | succ k ih =>
    intro hk
    have hk1 : k < gs.length := by omega
    have hk2 : k < gs'.length := by omega
    have IH := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk2,
      W_append, W_append, W_single, W_single, ← ag_gat_eq gs k hk1, ← ag_gat_eq gs' k hk2]
    have l1 : (W (gs.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    have l2 : (W (gs'.take k) x').length = x.length + k := by
      rw [W_length, List.length_take, hx]; omega
    refine agree_stepP _ _ _ _ P (by omega) IH ?_
    by_cases hP : P (x.length + k)
    · left
      rw [l1]
      exact hP
    · right
      exact hstep k hk1 hP IH

theorem agreeP2_full (x x' : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ P q → x'.getD q false = x.getD q false)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x') = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ q, ¬ P q → (W gs' x').getD q false = (W gs x).getD q false := by
  intro q hq
  have h := agreeP2 x x' gs gs' P hx hlen hin hstep gs.length le_rfl q hq
  rwa [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h

theorem agreeP_full (x : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hlen : gs'.length = gs.length)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x) = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ q, ¬ P q → (W gs' x).getD q false = (W gs x).getD q false :=
  agreeP2_full x x gs gs' P rfl hlen (fun _ _ => rfl) hstep

theorem agree_full (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → ag_gat gs' k = ag_gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (ag_gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      ag_val (ag_gat gs' m) (W (gs'.take m) x) = ag_val (ag_gat gs m) (W (gs.take m) x)) :
    ∀ q, q ≠ p → (W gs' x).getD q false = (W gs x).getD q false := by
  refine agreeP_full x gs gs' (fun q => q = p) hlen ?_
  intro k hk hP IH
  have hP' : x.length + k ≠ p := hP
  have hki : k ≠ i := fun h => hP' (by omega)
  by_cases hkm : k = m
  · subst hkm
    exact hval IH
  · rw [hsame k hki hkm]
    unfold ag_val
    congr 1
    apply List.map_congr_left
    intro r hr
    apply IH
    intro hre
    have hre' : r = p := hre
    rw [hre'] at hr
    exact hread k hk hkm hr

theorem agree_closed (x x' : List Bool) (gs gs' : List Gate) (B : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ B q → x'.getD q false = x.getD q false)
    (hch : ∀ k < gs.length, ¬ B (x.length + k) → ag_gat gs' k = ag_gat gs k)
    (hrd : ∀ k < gs.length, ¬ B (x.length + k) → ∀ i ∈ (ag_gat gs k).inputs, ¬ B i) :
    ∀ q, ¬ B q → (W gs' x').getD q false = (W gs x).getD q false := by
  refine agreeP2_full x x' gs gs' B hx hlen hin ?_
  intro k hk hB IH
  rw [hch k hk hB]
  unfold ag_val
  congr 1
  apply List.map_congr_left
  intro i hi
  exact IH i (hrd k hk hB i hi)

def ag_rd (L : ℕ) (gs : List Gate) (z w : ℕ) : Prop :=
  ∃ k < gs.length, w = L + k ∧ z ∈ (ag_gat gs k).inputs

theorem agree_cone (x x' : List Bool) (gs : List Gate) (y : ℕ) (hx : x'.length = x.length)
    (h : ∀ q < x.length, Relation.ReflTransGen (ag_rd x.length gs) q y →
      x'.getD q false = x.getD q false) :
    (W gs x').getD y false = (W gs x).getD y false := by
  refine agree_closed x x' gs gs (fun q => ¬ Relation.ReflTransGen (ag_rd x.length gs) q y) hx rfl
    ?_ (fun _ _ _ => rfl) ?_ y (fun hn => hn Relation.ReflTransGen.refl)
  · intro q hq
    by_cases hql : q < x.length
    · exact h q hql (by by_contra hc; exact hq hc)
    · rw [getD_ge x' q (by omega), getD_ge x q (by omega)]
  · intro k hk hB i hi hn
    exact hB (fun hr => hn (Relation.ReflTransGen.head ⟨k, hk, rfl, hi⟩ hr))

theorem agree_cone_val (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (y : ℕ)
    (h : ∀ t : Fin n, Relation.ReflTransGen (ag_rd n C.gates) t.val y → x' t = x t) :
    val C (List.ofFn x') y = val C (List.ofFn x) y := by
  have hl : (List.ofFn x).length = n := List.length_ofFn
  have e := agree_cone (List.ofFn x) (List.ofFn x') C.gates y (by simp) (by
    intro q hq hr
    rw [hl] at hq hr
    rw [ofFn_getD x' q hq, ofFn_getD x q hq]
    exact h ⟨q, hq⟩ hr)
  exact e

theorem agree_except_one (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (u : Fin n)
    (hxu : ∀ t, t ≠ u → x' t = x t) (y : ℕ)
    (hu : ¬ Relation.ReflTransGen (ag_rd n C.gates) u.val y) :
    val C (List.ofFn x') y = val C (List.ofFn x) y :=
  agree_cone_val n C x x' y (fun t ht => hxu t (fun e => hu (by rw [← e]; exact ht)))

theorem agree_ofFn {m : ℕ} (x y : Fin m → Bool) (k : Fin m)
    (h : ∀ k1 : Fin m, k1 ≠ k → x k1 = y k1) (i : ℕ) (hi : i ≠ k.val) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hlt : i < m
  · rw [ofFn_getD x i hlt, ofFn_getD y i hlt]
    exact h ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
  · rw [ofFn_getD_ge x i (by omega), ofFn_getD_ge y i (by omega)]

theorem ag_rb_core (n : ℕ) (gs G : List Gate) (i m : ℕ) (hlen : G.length = gs.length)
    (hRB : ∀ k < gs.length, ∀ q ∈ (ag_gat gs k).inputs, q < n + k)
    (hsame : ∀ k, k ≠ i → k ≠ m → ag_gat G k = ag_gat gs k)
    (hi : ∀ q ∈ (ag_gat G i).inputs, q < n + i)
    (hm : ∀ q ∈ (ag_gat G m).inputs, q < n + m) :
    ∀ k < G.length, ∀ q ∈ (ag_gat G k).inputs, q < n + k := by
  intro k hk q hq
  by_cases h1 : k = i
  · subst h1; exact hi q hq
  · by_cases h2 : k = m
    · subst h2; exact hm q hq
    · rw [hsame k h1 h2] at hq
      exact hRB k (by omega) q hq

-- FRAGMENT depcount    DEPENDS: fold mono agree
-- Dependency count: a circuit whose gates have fan-in at most k + 1 and whose output depends on m inputs
-- has at least (m - 1) / k gates (fan-in 2: m <= size + 1). Plus castAdd / natAdd facts for two input blocks.
-- Exports:
--   dc_dep_k n pre k (all g in pre, g.inputs.length <= k + 1) S : exists T, T.card <= k * pre.length + S.card and
--       for x y of length n agreeing on T, (W pre x).getD w false = (W pre y).getD w false for every w in S
--   dc_dep n pre (fan-in <= 2) S : same with T.card <= pre.length + S.card
--   dc_ne_of (a = true) (b = false) : a ne b
--   dc_sens_card (fan-in <= k + 1) (K : Finset (Fin n)) (each i in K sensitive: exists x y, circuitFun n C x ne
--       circuitFun n C y and x j = y j for all j ne i) : K.card <= k * C.size + 1
--   dc_sens_univ (fan-in <= k + 1) (every i : Fin n sensitive) : n <= k * C.size + 1
--   dc_sens2 (fan-in <= 2) K (sensitive) : K.card <= C.size + 1 ;  dc_sens2_univ : n <= C.size + 1
--   dc_sens_mono2 (Monotone2 C) (every i sensitive) : n <= C.size + 1 ;  dc_sens_ao2 (IsAO2 n C) : same
--   dc_cast_inj : Fin.castAdd L a = Fin.castAdd L b -> a = b ;  dc_nat_inj : Fin.natAdd P a = Fin.natAdd P b -> a = b
--   dc_nat_ne_cast a b : Fin.natAdd N a ne Fin.castAdd M b  (as Fin (N + M) with a : Fin M, b : Fin N)
--   dc_cast_ne_nat : Fin.castAdd M b ne Fin.natAdd N a
-- Use: for each input i build two inputs differing only at i with different circuitFun values (one accepted,
-- one rejected; dc_ne_of), then dc_sens2_univ / dc_sens_mono2 gives n <= C.size + 1.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem dc_dep_k (n : ℕ) (pre : List Gate) (k : ℕ) : (∀ g ∈ pre, g.inputs.length ≤ k + 1) →
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card ≤ k * pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ k + 1 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ k + 1 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ g.inputs, i ∈ S1) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        have hmap : (g.inputs.map fun i => (W pre x).getD i false)
            = (g.inputs.map fun i => (W pre y).getD i false) :=
          List.map_congr_left (fun i hi => hI2 i (hin (heq ▸ hw) i hi))
        rw [hmap]
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    by_cases hm : (n + pre.length) ∈ S
    · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
      · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_of_mem hm
        have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
        rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
        omega
      · intro w hw hne
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
      · intro _ i hi
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
      omega

theorem dc_dep (n : ℕ) (pre : List Gate) (h2 : ∀ g ∈ pre, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  obtain ⟨T, hT, hv⟩ := dc_dep_k n pre 1 h2 S
  exact ⟨T, by rw [Nat.one_mul] at hT; exact hT, hv⟩

theorem dc_ne_of {a b : Bool} (ha : a = true) (hb : b = false) : a ≠ b := by
  rw [ha, hb]; decide

theorem dc_sens_card {n : ℕ} (C : Circuit) (k : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ k + 1)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ k * C.size + 1 := by
  obtain ⟨T, hT, hTv⟩ := dc_dep_k n C.gates k hfan {C.output}
  have hall : ∀ i ∈ K, i.val ∈ T := by
    intro i hi
    by_contra hk
    obtain ⟨x, y, hne, hxy⟩ := hK i hi
    have he := hTv (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun j hj => agree_ofFn x y i hxy j (fun h => hk (h ▸ hj))) C.output
      (Finset.mem_singleton_self _)
    exact hne he
  have hcard : K.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => hall i hi)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_singleton] at hT
  show K.card ≤ k * C.gates.length + 1
  omega

theorem dc_sens_univ {n : ℕ} (C : Circuit) (k : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ k + 1)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ k * C.size + 1 := by
  have h := dc_sens_card C k hfan Finset.univ (fun i _ => hK i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem dc_sens2 {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ C.size + 1 := by
  have h := dc_sens_card C 1 hfan K hK
  rw [Nat.one_mul] at h
  exact h

theorem dc_sens2_univ {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 := by
  have h := dc_sens_univ C 1 hfan hK
  rw [Nat.one_mul] at h
  exact h

theorem dc_sens_mono2 {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 :=
  dc_sens2_univ C (fun _ hg => monotone2_len hC hg) hK

theorem dc_sens_ao2 {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 :=
  dc_sens2_univ C (fun _ hg => le_of_eq (isAO2_len hC hg)) hK

theorem dc_cast_inj {P L : ℕ} {a b : Fin P} (h : Fin.castAdd L a = Fin.castAdd L b) : a = b := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem dc_nat_inj {P L : ℕ} {a b : Fin L} (h : Fin.natAdd P a = Fin.natAdd P b) : a = b := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem dc_nat_ne_cast {N M : ℕ} (a : Fin M) (b : Fin N) : Fin.natAdd N a ≠ Fin.castAdd M b := by
  intro h
  have h1 : N + a.val = b.val := congrArg Fin.val h
  have h2 := b.isLt
  omega

theorem dc_cast_ne_nat {N M : ℕ} (a : Fin M) (b : Fin N) : Fin.castAdd M b ≠ Fin.natAdd N a :=
  fun h => dc_nat_ne_cast a b h.symm

def skp (c a : ℕ) : ℕ := if a < c then a else a + 1

def sk (c n : ℕ) : List ℕ := (List.range (n - 1)).map (skp c)

theorem sk_len (c n : ℕ) : (sk c n).length = n - 1 := by simp [sk]

theorem sk_mem (c n k : ℕ) (hc : c < n) : k ∈ sk c n ↔ (k < n ∧ k ≠ c) := by
  unfold sk
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [List.mem_range] at ha
    unfold skp
    split_ifs <;> omega
  · rintro ⟨h1, h2⟩
    by_cases h : k < c
    · exact ⟨k, List.mem_range.2 (by omega), by simp [skp, h]⟩
    · refine ⟨k - 1, List.mem_range.2 (by omega), ?_⟩
      unfold skp
      split_ifs <;> omega

def pt (n a b : ℕ) : Fin (n + n) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n : ℕ) (u v : Fin n) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem oe_len (n : ℕ) (u v : Fin n) : (PEqualNP.Represents.oneEach u v).length = n + n := by
  rw [oneEach_pt, List.length_ofFn]

theorem oe_getD (n : ℕ) (u v : Fin n) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + n
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem rep_pt {n : ℕ} {A : Fin n → Fin n → Bool} {C : Circuit}
    (h : PEqualNP.Represents.Represents A C) (u v : Fin n) :
    circuitFun (n + n) C (pt n u.val (n + v.val)) = A u v := by
  rw [← h u v, oneEach_pt]
  rfl

theorem sens_off {N : ℕ} (C : Circuit) (hC : Monotone2 C) (x z : Fin N → Bool) (k : Fin N)
    (hx : circuitFun N C x = true) (hz : circuitFun N C z = false)
    (hle : ∀ m : Fin N, m ≠ k → x m = true → z m = true) :
    ∃ x y : Fin N → Bool, circuitFun N C x ≠ circuitFun N C y ∧ ∀ m : Fin N, m ≠ k → x m = y m := by
  refine ⟨x, fun m => x m && decide (m ≠ k), ?_, ?_⟩
  · have hy : circuitFun N C (fun m => x m && decide (m ≠ k)) = false := by
      cases hc : circuitFun N C (fun m => x m && decide (m ≠ k)) with
      | false => rfl
      | true =>
        have h2 := circuitFun_mono N C (andOrOnly_of_monotone2 hC) _ z (fun m hm => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
          exact hle m hm.2 hm.1) hc
        rw [hz] at h2
        exact absurd h2 (by simp)
    rw [hx, hy]
    simp
  · intro m hm
    simp [hm]

def lf (n i j : ℕ) (c : ℕ) : List ℕ := if c < n then (sk j n).map (fun a => n + a) else sk i n

theorem Ly_mem (n : ℕ) (j : Fin n) (k : ℕ) :
    k ∈ (sk j.val n).map (fun a => n + a) ↔ (n ≤ k ∧ k < n + n ∧ k ≠ n + j.val) := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [sk_mem _ _ _ j.isLt] at ha
    omega
  · intro h
    exact ⟨k - n, (sk_mem _ _ _ j.isLt).2 (by omega), by omega⟩

theorem other (n : ℕ) (hn : 2 ≤ n) (c : Fin n) : ∃ d : Fin n, d.val ≠ c.val := by
  by_cases h : c.val = 0
  · exact ⟨⟨1, by omega⟩, by show 1 ≠ c.val; omega⟩
  · exact ⟨⟨0, by omega⟩, by show 0 ≠ c.val; omega⟩

theorem upper3 (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j))
      (2 * n - 3) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  have hi := i.isLt
  have hj := j.isLt
  have hl0 : lf n i.val j.val 0 = (sk j.val n).map (fun a => n + a) := by
    unfold lf
    rw [if_pos (by omega)]
  have hln : lf n i.val j.val n = sk i.val n := by
    unfold lf
    rw [if_neg (by omega)]
  have hLf : ∀ c ∈ [0, n], ∀ k ∈ lf n i.val j.val c, k < n + n := by
    intro c hc k hk
    simp at hc
    rcases hc with h | h <;> rw [h] at hk
    · rw [hl0, Ly_mem] at hk
      omega
    · rw [hln, sk_mem _ _ _ hi] at hk
      omega
  have hne0 : lf n i.val j.val 0 ≠ [] := by
    rw [hl0]
    intro h
    have h2 := congrArg List.length h
    rw [List.length_map, sk_len, List.length_nil] at h2
    omega
  have hnen : lf n i.val j.val n ≠ [] := by
    rw [hln]
    intro h
    have h2 := congrArg List.length h
    rw [sk_len, List.length_nil] at h2
    omega
  have hGlen : (ochains (lf n i.val j.val) [0, n] (n + n)).length = (n - 1 - 1) + (n - 1 - 1) := by
    rw [ochains_len]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hl0, hln, List.length_map, sk_len, sk_len]
    omega
  refine ⟨⟨ochains (lf n i.val j.val) [0, n] (n + n) ++
      [⟨GateOp.and, [ochainsW (lf n i.val j.val) [0, n] (n + n) n,
        ochainsW (lf n i.val j.val) [0, n] (n + n) 0]⟩],
      n + n + (ochains (lf n i.val j.val) [0, n] (n + n)).length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · have h2 := ochains_gate _ _ _ g h
      exact ⟨by rw [h2.1]; simp, by rw [h2.2]⟩
    · simp at h
      subst h
      exact ⟨by simp, by simp⟩
  · show (ochains (lf n i.val j.val) [0, n] (n + n) ++ [_]).length ≤ 2 * n - 3
    rw [List.length_append, hGlen, List.length_singleton]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hw := oe_len n u v
    obtain ⟨_, hA⟩ := ochains_val (lf n i.val j.val) [0, n] (n + n) _ hw hLf n (by simp) hnen
    obtain ⟨_, hB⟩ := ochains_val (lf n i.val j.val) [0, n] (n + n) _ hw hLf 0 (by simp) hne0
    have keyA : (∃ k ∈ (sk j.val n).map (fun a => n + a),
        (PEqualNP.Represents.oneEach u v).getD k false = true) ↔ v.val ≠ j.val := by
      simp only [oe_getD]
      constructor
      · rintro ⟨k, hk, hk2⟩
        rw [Ly_mem] at hk
        omega
      · intro h
        exact ⟨n + v.val, (Ly_mem n j _).2 ⟨by omega, by omega, by omega⟩, Or.inr rfl⟩
    have keyB : (∃ k ∈ sk i.val n,
        (PEqualNP.Represents.oneEach u v).getD k false = true) ↔ u.val ≠ i.val := by
      simp only [oe_getD]
      constructor
      · rintro ⟨k, hk, hk2⟩
        rw [sk_mem _ _ _ hi] at hk
        omega
      · intro h
        exact ⟨u.val, (sk_mem _ _ _ hi).2 ⟨hu, h⟩, Or.inl rfl⟩
    show (W (ochains (lf n i.val j.val) [0, n] (n + n) ++ [_])
      (PEqualNP.Represents.oneEach u v)).getD
      (n + n + (ochains (lf n i.val j.val) [0, n] (n + n)).length) false = _
    rw [W_snoc_getD, if_pos (by rw [hw])]
    simp only [List.map_cons, List.map_nil, eval_and2]
    rw [Bool.eq_iff_iff, Bool.and_eq_true, hA, hB, hl0, hln, keyA, keyB]
    by_cases h1 : u.val = i.val <;> by_cases h2 : v.val = j.val <;> simp [Fin.ext_iff, h1, h2]

theorem lower3 (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j))
      (2 * n - 4) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  rintro ⟨C, hC, hs, hrep⟩
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨a, ha⟩ := other n hn i
  obtain ⟨b, hb⟩ := other n hn j
  have hab : Fin.castAdd n i ≠ Fin.natAdd n j := by
    intro h
    have h2 := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
    omega
  have hK : ∀ k ∈ ({Fin.castAdd n i, Fin.natAdd n j} : Finset (Fin (n + n)))ᶜ,
      ∃ x y : Fin (n + n) → Bool, circuitFun (n + n) C x ≠ circuitFun (n + n) C y ∧
        ∀ m : Fin (n + n), m ≠ k → x m = y m := by
    intro k hk
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hk1 : k.val ≠ i.val := fun e => hk.1 (Fin.ext (by simp [e]))
    have hk2 : k.val ≠ n + j.val := fun e => hk.2 (Fin.ext (by simp only [Fin.val_natAdd]; omega))
    have hkl := k.isLt
    by_cases hkn : k.val < n
    · refine sens_off C hC _ _ k ((rep_pt hrep ⟨k.val, hkn⟩ b).trans ?_)
        ((rep_pt hrep i b).trans ?_) ?_
      · simp [Fin.ext_iff, hk1, hb]
      · simp
      · intro m hm hxm
        have hm' : m.val ≠ k.val := fun e => hm (Fin.ext e)
        simp only [pt, Bool.or_eq_true, decide_eq_true_eq] at hxm ⊢
        omega
    · have hk3 : k.val - n ≠ j.val := by omega
      refine sens_off C hC _ _ k ((rep_pt hrep a ⟨k.val - n, by omega⟩).trans ?_)
        ((rep_pt hrep a j).trans ?_) ?_
      · simp [Fin.ext_iff, ha, hk3]
      · simp
      · intro m hm hxm
        have hm' : m.val ≠ k.val := fun e => hm (Fin.ext e)
        simp only [pt, Bool.or_eq_true, decide_eq_true_eq] at hxm ⊢
        omega
  have hc := dc_sens2 C (fun _ hg => monotone2_len hC hg) _ hK
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab] at hc
  have hsz : C.size ≤ 2 * n - 4 := hs
  omega

theorem notRep (n : ℕ) (i j : Fin n) :
    PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j))
      ⟨[⟨GateOp.or, [i.val, n + j.val]⟩, ⟨GateOp.not, [n + n]⟩], n + n + 1⟩ := by
  intro u v
  have hl := oe_len n u v
  have h0 : (PEqualNP.Represents.oneEach u v).getD i.val false = decide (u = i) := by
    rw [Bool.eq_iff_iff, oe_getD, decide_eq_true_iff, Fin.ext_iff]
    have := v.isLt
    omega
  have h1 : (PEqualNP.Represents.oneEach u v).getD (n + j.val) false = decide (v = j) := by
    rw [Bool.eq_iff_iff, oe_getD, decide_eq_true_iff, Fin.ext_iff]
    have := u.isLt
    omega
  rw [eval_W, W_cons, W_cons, W_nil, step_last _ _ _ (by rw [step_len, hl]),
    List.map_cons, List.map_nil, step_last _ _ _ hl.symm, List.map_cons, List.map_cons,
    List.map_nil, h0, h1]
  by_cases hu : u = i <;> by_cases hv : v = j <;> simp [hu, hv, GateOp.eval]

end PEqualNP.Outside.L_meta_19315_aux

theorem PEqualNP.Outside.L_meta_19315 : ¬ ∃ a b : ℕ, ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (s : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (a * s + b) := by
  rintro ⟨a, b, h⟩
  have hn : 2 ≤ a * 2 + b + 2 := by omega
  obtain ⟨C, hC, hs, hr⟩ := h (a * 2 + b + 2) _ 2 _ (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp)
    le_rfl (PEqualNP.Outside.L_meta_19315_aux.notRep _ ⟨0, by omega⟩ ⟨0, by omega⟩)
  exact PEqualNP.Outside.L_meta_19315_aux.lower3 _ _ _ hn ⟨C, hC, by omega, hr⟩
