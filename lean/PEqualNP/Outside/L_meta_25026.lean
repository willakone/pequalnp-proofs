import Mathlib
import PEqualNP.Defs

-- Lower half: the chain-graph bound of merged L-meta-21919 (2n + k - 4 - a - b), copied into this
-- step namespace with credit to its authors. Upper half: an explicit 8-gate AND/OR circuit.

namespace PEqualNP.Outside.L_meta_25026

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem getD_app_lt {α : Type*} (l l2 : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {α : Type*} (l l2 : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i d = l2.getD (i - l.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_snoc {α : Type*} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i < l.length then l.getD i d else if i = l.length then v else d := by
  by_cases h1 : i < l.length
  · simp only [h1, ↓reduceIte, getD_app_lt l [v] d i h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i = l.length
    · subst h2; simp [List.getD]
    · simp only [h2, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show (l ++ [v]).length ≤ i by simp; omega), Option.getD_none]

theorem getD_ge {α : Type*} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

inductive WVal where
  | c0
  | c1
  | ref (i : ℕ)
deriving DecidableEq

def wvalLt (B : ℕ) : WVal → Prop
  | .c0 => True
  | .c1 => True
  | .ref i => i < B

theorem wvalLt_mono {B B' : ℕ} (h : B ≤ B') {v : WVal} (hv : wvalLt B v) : wvalLt B' v := by
  cases v with
  | c0 => trivial
  | c1 => trivial
  | ref i => exact lt_of_lt_of_le hv h

def evalWVal (v : WVal) (w : List Bool) : Bool :=
  match v with
  | .c0 => false
  | .c1 => true
  | .ref i => w.getD i false

structure BGate where
  isOr : Bool
  a : ℕ
  b : ℕ
deriving DecidableEq

def dGate : BGate := ⟨false, 0, 0⟩

def evalBGate (g : BGate) (w : List Bool) : Bool :=
  let va := w.getD g.a false
  let vb := w.getD g.b false
  if g.isOr then (va || vb) else (va && vb)

def bstep (w : List Bool) (g : BGate) : List Bool :=
  w ++ [evalBGate g w]

def BW (gs : List BGate) (w : List Bool) : List Bool :=
  gs.foldl bstep w

theorem bstep_len (w : List Bool) (g : BGate) : (bstep w g).length = w.length + 1 := by
  simp [bstep]

theorem BW_nil (w : List Bool) : BW [] w = w := rfl

theorem BW_append (a b : List BGate) (w : List Bool) : BW (a ++ b) w = BW b (BW a w) := by
  simp [BW, List.foldl_append]

theorem BW_snoc (gs : List BGate) (g : BGate) (w : List Bool) :
    BW (gs ++ [g]) w = bstep (BW gs w) g := by
  rw [BW_append]; rfl

theorem BW_len (gs : List BGate) (w : List Bool) : (BW gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [BW]
  | append_singleton gs g ih =>
    rw [BW_snoc, bstep_len, ih, List.length_append, List.length_singleton]
    omega

theorem BW_prefix (gs : List BGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (BW gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [BW_snoc, bstep, getD_app_lt _ _ _ _ (by rw [BW_len]; omega), ih]

theorem BW_take_getD (gs : List BGate) (w : List Bool) (k i : ℕ)
    (hi : i < w.length + (gs.take k).length) :
    (BW gs w).getD i false = (BW (gs.take k) w).getD i false := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsp, BW_append]
  rw [BW_prefix _ _ _ (by rw [BW_len]; exact hi)]

theorem BW_gate (gs : List BGate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (ha : (gs.getD j dGate).a < w.length + j) (hb : (gs.getD j dGate).b < w.length + j) :
    (BW gs w).getD (w.length + j) false = evalBGate (gs.getD j dGate) (BW gs w) := by
  have htk : gs.take (j + 1) = gs.take j ++ [gs.getD j dGate] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hlenj : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hlenj1 : (gs.take (j + 1)).length = j + 1 := List.length_take_of_le hj
  rw [BW_take_getD gs w (j + 1) (w.length + j) (by omega), htk, BW_snoc, bstep,
    getD_snoc, BW_len, hlenj]
  simp only [lt_irrefl, ↓reduceIte, evalBGate]
  rw [← BW_take_getD gs w j (gs.getD j dGate).a (by omega),
      ← BW_take_getD gs w j (gs.getD j dGate).b (by omega)]

structure BCirc (N : ℕ) where
  gates : List BGate
  out : WVal
  wf : ∀ j < gates.length,
    let g := gates.getD j dGate
    g.a < N + j ∧ g.b < N + j ∧ g.a ≠ g.b
  out_wf : wvalLt (N + gates.length) out

def BCirc.val {N : ℕ} (C : BCirc N) (x : List Bool) (w : ℕ) : Bool :=
  (BW C.gates x).getD w false

def BCirc.eval {N : ℕ} (C : BCirc N) (x : List Bool) : Bool :=
  evalWVal C.out (BW C.gates x)

theorem BCirc.val_input {N : ℕ} (C : BCirc N) {x : List Bool} (hx : x.length = N)
    {w : ℕ} (hw : w < N) : C.val x w = x.getD w false :=
  BW_prefix C.gates x w (by omega)

theorem BCirc.val_gate {N : ℕ} (C : BCirc N) {x : List Bool} (hx : x.length = N)
    {j : ℕ} (hj : j < C.gates.length) :
    C.val x (N + j) = evalBGate (C.gates.getD j dGate) (BW C.gates x) := by
  have hwf := C.wf j hj
  have h := BW_gate C.gates x j hj (by rw [hx]; exact hwf.1) (by rw [hx]; exact hwf.2.1)
  rwa [hx] at h

theorem evalBGate_mono (g : BGate) (w1 w2 : List Bool)
    (ha : w1.getD g.a false = true → w2.getD g.a false = true)
    (hb : w1.getD g.b false = true → w2.getD g.b false = true) :
    evalBGate g w1 = true → evalBGate g w2 = true := by
  unfold evalBGate
  cases g.isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true]
  · rintro ⟨h1, h2⟩; exact ⟨ha h1, hb h2⟩
  · rintro (h1 | h2); exact Or.inl (ha h1); exact Or.inr (hb h2)

theorem BCirc.val_mono {N : ℕ} (C : BCirc N) {x y : List Bool}
    (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i < N, x.getD i false = true → y.getD i false = true) :
    ∀ w < N + C.gates.length, C.val x w = true → C.val y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hxw
    by_cases hlt : w < N
    · rw [C.val_input hx hlt] at hxw
      rw [C.val_input hy hlt]
      exact hxy w hlt hxw
    · have hj : w - N < C.gates.length := by omega
      have hw_eq : w = N + (w - N) := by omega
      rw [hw_eq] at hxw ⊢
      rw [C.val_gate hx hj] at hxw
      rw [C.val_gate hy hj]
      have hwf := C.wf (w - N) hj
      exact evalBGate_mono _ _ _
        (ih _ (by omega) (by omega))
        (ih _ (by omega) (by omega)) hxw

theorem BCirc.eval_mono {N : ℕ} (C : BCirc N) {x y : List Bool}
    (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i < N, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  cases h : C.out with
  | c0 => simp [BCirc.eval, evalWVal, h]
  | c1 => simp [BCirc.eval, evalWVal, h]
  | ref w =>
    have hw : w < N + C.gates.length := by
      have := C.out_wf; rw [h] at this; exact this
    simp only [BCirc.eval, evalWVal, h]
    exact C.val_mono hx hy hxy w hw

theorem BCirc.val_le_except {N : ℕ} (C : BCirc N) {x y : List Bool}
    (hx : x.length = N) (hy : y.length = N) (E : ℕ → Prop)
    (hIn : ∀ i < N, ¬ E i → x.getD i false = true → y.getD i false = true)
    (hGate : ∀ j < C.gates.length,
      C.val x (N + j) = false ∨ C.val y (N + j) = true ∨
      (¬ E (C.gates.getD j dGate).a ∧ ¬ E (C.gates.getD j dGate).b)) :
    ∀ w < N + C.gates.length, ¬ E w → C.val x w = true → C.val y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hEw hxw
    by_cases hlt : w < N
    · rw [C.val_input hx hlt] at hxw
      rw [C.val_input hy hlt]
      exact hIn w hlt hEw hxw
    · have hj : w - N < C.gates.length := by omega
      have hw_eq : w = N + (w - N) := by omega
      rw [hw_eq] at hxw ⊢
      rcases hGate (w - N) hj with hxf | hyt | ⟨hEa, hEb⟩
      · rw [hxf] at hxw; cases hxw
      · exact hyt
      · rw [C.val_gate hx hj] at hxw
        rw [C.val_gate hy hj]
        have hwf := C.wf (w - N) hj
        exact evalBGate_mono _ _ _
          (ih _ (by omega) (by omega) hEa)
          (ih _ (by omega) (by omega) hEb) hxw

def simpBin (isOr : Bool) (va vb : WVal) (nextIdx : ℕ) : Option BGate × WVal :=
  match isOr, va, vb with
  | false, .c0, _ => (none, .c0)
  | false, _, .c0 => (none, .c0)
  | false, .c1, v => (none, v)
  | false, v, .c1 => (none, v)
  | true, .c1, _ => (none, .c1)
  | true, _, .c1 => (none, .c1)
  | true, .c0, v => (none, v)
  | true, v, .c0 => (none, v)
  | _, .ref a, .ref b =>
    if a = b then (none, .ref a)
    else (some ⟨isOr, a, b⟩, .ref nextIdx)

theorem simpBin_wf (isOr : Bool) (va vb : WVal) (B : ℕ)
    (ha : wvalLt B va) (hb : wvalLt B vb) :
    let r := simpBin isOr va vb B
    (match r.1 with
     | none => wvalLt B r.2
     | some g => g.a < B ∧ g.b < B ∧ g.a ≠ g.b ∧ r.2 = .ref B) := by
  cases isOr <;> cases va <;> cases vb <;> dsimp only [simpBin]
  all_goals try exact ha
  all_goals try exact hb
  all_goals try trivial
  all_goals
    rename_i a b
    by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [hab]; exact ⟨ha, hb⟩

theorem simpBin_eval (isOr : Bool) (va vb : WVal) (w : List Bool) :
    let r := simpBin isOr va vb w.length
    let w' := match r.1 with | none => w | some g => bstep w g
    evalWVal r.2 w' = if isOr then (evalWVal va w || evalWVal vb w) else (evalWVal va w && evalWVal vb w) := by
  cases isOr <;> cases va <;> cases vb <;> dsimp only [simpBin, evalWVal]
  all_goals try (simp; done)
  all_goals
    rename_i a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, bstep, evalBGate]

theorem simpBin_none_of_c0_left (isOr : Bool) (vb : WVal) (B : ℕ) :
    (simpBin isOr .c0 vb B).1 = none := by
  cases isOr <;> cases vb <;> rfl

theorem simpBin_none_of_c0_right (isOr : Bool) (va : WVal) (B : ℕ) :
    (simpBin isOr va .c0 B).1 = none := by
  cases isOr <;> cases va <;> rfl

theorem simpBin_c0_of_both_c0 (isOr : Bool) (B : ℕ) :
    (simpBin isOr .c0 .c0 B).2 = .c0 := by
  cases isOr <;> rfl

theorem simpBin_c0_of_and_left (vb : WVal) (B : ℕ) :
    (simpBin false .c0 vb B).2 = .c0 := by
  cases vb <;> rfl

theorem simpBin_c0_of_and_right (va : WVal) (B : ℕ) :
    (simpBin false va .c0 B).2 = .c0 := by
  cases va <;> rfl

theorem simpBin_ref_of_some (isOr : Bool) (va vb : WVal) (B : ℕ) {g : BGate}
    (h : (simpBin isOr va vb B).1 = some g) : (simpBin isOr va vb B).2 = .ref B := by
  cases isOr <;> cases va <;> cases vb <;> dsimp only [simpBin] at h ⊢
  all_goals try cases h
  all_goals
    rename_i a b
    by_cases hab : a = b
    · simp only [hab, ↓reduceIte] at h; cases h
    · simp only [hab, ↓reduceIte]

def cstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def CW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl cstep w

theorem CW_len (gs : List Gate) (w : List Bool) : (CW gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [CW]
  | append_singleton gs g ih =>
    simp only [CW, List.foldl_append, List.foldl_cons, List.foldl_nil, cstep, List.length_append,
      List.length_singleton]
    rw [show gs.foldl cstep w = CW gs w from rfl, ih]; omega

def normOne (N : ℕ) (st : List BGate × List WVal) (g : Gate) : List BGate × List WVal :=
  match g.op, g.inputs with
  | .and, [] => (st.1, st.2 ++ [.c1])
  | .or, [] => (st.1, st.2 ++ [.c0])
  | _, [i] => (st.1, st.2 ++ [st.2.getD i .c0])
  | .and, [i, j] =>
    let r := simpBin false (st.2.getD i .c0) (st.2.getD j .c0) (N + st.1.length)
    match r.1 with
    | none => (st.1, st.2 ++ [r.2])
    | some g' => (st.1 ++ [g'], st.2 ++ [r.2])
  | .or, [i, j] =>
    let r := simpBin true (st.2.getD i .c0) (st.2.getD j .c0) (N + st.1.length)
    match r.1 with
    | none => (st.1, st.2 ++ [r.2])
    | some g' => (st.1 ++ [g'], st.2 ++ [r.2])
  | _, _ => (st.1, st.2 ++ [.c0])

def initEnv (N : ℕ) : List WVal := List.ofFn (fun i : Fin N => WVal.ref i.val)

theorem initEnv_len (N : ℕ) : (initEnv N).length = N := by simp [initEnv]

theorem initEnv_getD (N i : ℕ) :
    (initEnv N).getD i .c0 = if i < N then .ref i else .c0 := by
  unfold initEnv; rw [getD_ofFn]; split_ifs <;> rfl

def normRun (N : ℕ) (gs : List Gate) : List BGate × List WVal :=
  gs.foldl (normOne N) ([], initEnv N)

theorem normRun_inv (N : ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let st := normRun N gs
    st.1.length ≤ gs.length ∧
    st.2.length = N + gs.length ∧
    (∀ j < st.1.length, let g := st.1.getD j dGate; g.a < N + j ∧ g.b < N + j ∧ g.a ≠ g.b) ∧
    (∀ i < st.2.length, wvalLt (N + st.1.length) (st.2.getD i .c0)) ∧
    (∀ x : List Bool, x.length = N →
      ∀ i < N + gs.length, (CW gs x).getD i false = evalWVal (st.2.getD i .c0) (BW st.1 x)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨le_rfl, by simp [normRun, initEnv_len], fun j hj => by simp [normRun] at hj, ?_, ?_⟩
    · intro i hi
      simp only [normRun, List.foldl_nil, initEnv_getD, List.length_nil, add_zero] at hi ⊢
      rw [initEnv_len] at hi
      simp only [hi, ↓reduceIte, wvalLt]
    · intro x hx i hi
      simp only [normRun, List.foldl_nil, CW, BW, initEnv_getD]
      simp only [List.length_nil, add_zero] at hi
      simp only [hi, ↓reduceIte]; rfl
  | append_singleton gs g ih =>
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_append_left _ hg')
    obtain ⟨hlen1, hlen2, hwf, hewf, heval⟩ := ih hM'
    obtain ⟨hop, hgin⟩ := hM g (List.mem_append_right _ List.mem_cons_self)
    set st := normRun N gs
    have hrun : normRun N (gs ++ [g]) = normOne N st g := by
      simp [normRun, st, List.foldl_append]
    rw [hrun]
    have hEnvLt : ∀ k, wvalLt (N + st.1.length) (st.2.getD k .c0) := by
      intro k
      by_cases hk : k < st.2.length
      · exact hewf k hk
      · rw [getD_ge _ _ _ (by omega)]; trivial
    have hEvalAll : ∀ (x : List Bool) (hx : x.length = N) (k : ℕ),
        (CW gs x).getD k false = evalWVal (st.2.getD k .c0) (BW st.1 x) := by
      intro x hx k
      by_cases hk : k < N + gs.length
      · exact heval x hx k hk
      · rw [getD_ge _ _ _ (by rw [CW_len, hx]; omega), getD_ge _ _ _ (by omega)]; rfl
    have hCWstep : ∀ (x : List Bool) (hx : x.length = N) (i : ℕ),
        (CW (gs ++ [g]) x).getD i false =
        if i < N + gs.length then (CW gs x).getD i false
        else if i = N + gs.length then g.op.eval (g.inputs.map fun a => (CW gs x).getD a false)
        else false := by
      intro x hx i
      simp only [CW, List.foldl_append, List.foldl_cons, List.foldl_nil, cstep]
      rw [getD_snoc, show gs.foldl cstep x = CW gs x from rfl, CW_len, hx]
    have hMonoStep : ∀ (v : WVal) (hv : wvalLt (N + st.1.length) v)
        (hv_eq : ∀ (x : List Bool), x.length = N →
          g.op.eval (g.inputs.map fun a => (CW gs x).getD a false) = evalWVal v (BW st.1 x)),
        let st' := (st.1, st.2 ++ [v])
        st'.1.length ≤ (gs ++ [g]).length ∧
        st'.2.length = N + (gs ++ [g]).length ∧
        (∀ j < st'.1.length, let gg := st'.1.getD j dGate; gg.a < N + j ∧ gg.b < N + j ∧ gg.a ≠ gg.b) ∧
        (∀ i < st'.2.length, wvalLt (N + st'.1.length) (st'.2.getD i .c0)) ∧
        (∀ x : List Bool, x.length = N →
          ∀ i < N + (gs ++ [g]).length,
            (CW (gs ++ [g]) x).getD i false = evalWVal (st'.2.getD i .c0) (BW st'.1 x)) := by
      intro v hv hv_eq
      refine ⟨by simp; omega, by simp [hlen2]; omega, hwf, ?_, ?_⟩
      · intro i hi
        rw [getD_snoc]
        split_ifs with h1 h2
        · exact hewf i h1
        · exact hv
        · trivial
      · intro x hx i hi
        rw [hCWstep x hx i, getD_snoc, hlen2]
        split_ifs with h1 h2
        · exact heval x hx i h1
        · exact hv_eq x hx
        · rfl
    have hBinStep : ∀ (isOr : Bool) (a b : ℕ)
        (hgop : g.op = if isOr then GateOp.or else GateOp.and)
        (hgin2 : g.inputs = [a, b]),
        let r := simpBin isOr (st.2.getD a .c0) (st.2.getD b .c0) (N + st.1.length)
        let st' := match r.1 with | none => (st.1, st.2 ++ [r.2]) | some g' => (st.1 ++ [g'], st.2 ++ [r.2])
        st'.1.length ≤ (gs ++ [g]).length ∧
        st'.2.length = N + (gs ++ [g]).length ∧
        (∀ j < st'.1.length, let gg := st'.1.getD j dGate; gg.a < N + j ∧ gg.b < N + j ∧ gg.a ≠ gg.b) ∧
        (∀ i < st'.2.length, wvalLt (N + st'.1.length) (st'.2.getD i .c0)) ∧
        (∀ x : List Bool, x.length = N →
          ∀ i < N + (gs ++ [g]).length,
            (CW (gs ++ [g]) x).getD i false = evalWVal (st'.2.getD i .c0) (BW st'.1 x)) := by
      intro isOr a b hgop hgin2
      have hwf_r := simpBin_wf isOr (st.2.getD a .c0) (st.2.getD b .c0) (N + st.1.length)
        (hEnvLt a) (hEnvLt b)
      dsimp only at hwf_r ⊢
      cases hr : (simpBin isOr (st.2.getD a .c0) (st.2.getD b .c0) (N + st.1.length)).1 with
      | none =>
        rw [hr] at hwf_r
        apply hMonoStep _ hwf_r
        intro x hx
        have he := simpBin_eval isOr (st.2.getD a .c0) (st.2.getD b .c0) (BW st.1 x)
        dsimp only at he
        rw [BW_len, hx, hr] at he
        rw [he, hgop, hgin2]
        cases isOr
        · simp only [Bool.false_eq_true, ↓reduceIte, GateOp.eval, List.map, List.all, id, Bool.and_true]
          rw [hEvalAll x hx a, hEvalAll x hx b]
        · simp only [↓reduceIte, GateOp.eval, List.map, List.any, id, Bool.or_false]
          rw [hEvalAll x hx a, hEvalAll x hx b]
      | some g' =>
        rw [hr] at hwf_r
        obtain ⟨hga, hgb, hgab, hr2⟩ := hwf_r
        refine ⟨by simp; omega, by simp [hlen2]; omega, ?_, ?_, ?_⟩
        · intro j hj
          rw [getD_snoc]
          split_ifs with h1 h2
          · exact hwf j h1
          · subst h2; exact ⟨hga, hgb, hgab⟩
          · simp at hj; omega
        · intro i hi
          rw [getD_snoc]
          split_ifs with h1 h2
          · exact wvalLt_mono (by simp) (hewf i h1)
          · rw [hr2]; simp [wvalLt]
          · trivial
        · intro x hx i hi
          rw [hCWstep x hx i, getD_snoc, hlen2]
          split_ifs with h1 h2
          · rw [heval x hx i h1, BW_snoc, bstep]
            have hlt_i := hewf i (by omega)
            cases hv : st.2.getD i .c0 with
            | c0 => rfl
            | c1 => rfl
            | ref w =>
              rw [hv] at hlt_i
              simp only [evalWVal]
              rw [getD_app_lt _ _ _ _ (by rw [BW_len, hx]; exact hlt_i)]
          · have he := simpBin_eval isOr (st.2.getD a .c0) (st.2.getD b .c0) (BW st.1 x)
            dsimp only at he
            rw [BW_len, hx, hr] at he
            rw [BW_snoc, he, hgop, hgin2]
            cases isOr
            · simp only [Bool.false_eq_true, ↓reduceIte, GateOp.eval, List.map, List.all, id, Bool.and_true]
              rw [hEvalAll x hx a, hEvalAll x hx b]
            · simp only [↓reduceIte, GateOp.eval, List.map, List.any, id, Bool.or_false]
              rw [hEvalAll x hx a, hEvalAll x hx b]
          · rfl
    rcases Set.mem_insert_iff.mp hop with hopA | hopO
    · match hgi : g.inputs with
      | [] =>
        simp only [normOne, hopA, hgi]
        exact hMonoStep .c1 trivial (fun x _ => by simp [hopA, hgi, GateOp.eval, evalWVal])
      | [a] =>
        simp only [normOne, hopA, hgi]
        exact hMonoStep (st.2.getD a .c0) (hEnvLt a) (fun x hx => by
          simp only [hopA, hgi, GateOp.eval, List.map, List.all, id, Bool.and_true]
          exact hEvalAll x hx a)
      | [a, b] =>
        simp only [normOne, hopA, hgi]
        exact hBinStep false a b (by simp [hopA]) hgi
      | _ :: _ :: _ :: _ => rw [hgi] at hgin; simp at hgin
    · have hopO' : g.op = GateOp.or := Set.mem_singleton_iff.mp hopO
      match hgi : g.inputs with
      | [] =>
        simp only [normOne, hopO', hgi]
        exact hMonoStep .c0 trivial (fun x _ => by simp [hopO', hgi, GateOp.eval, evalWVal])
      | [a] =>
        simp only [normOne, hopO', hgi]
        exact hMonoStep (st.2.getD a .c0) (hEnvLt a) (fun x hx => by
          simp only [hopO', hgi, GateOp.eval, List.map, List.any, id, Bool.or_false]
          exact hEvalAll x hx a)
      | [a, b] =>
        simp only [normOne, hopO', hgi]
        exact hBinStep true a b (by simp [hopO']) hgi
      | _ :: _ :: _ :: _ => rw [hgi] at hgin; simp at hgin

theorem normCircuit_exists (N : ℕ) (C : Circuit) (hM : Monotone2 C) :
    ∃ B : BCirc N, B.gates.length ≤ C.size ∧
      ∀ x : List Bool, x.length = N → B.eval x = C.eval x := by
  obtain ⟨hlen1, hlen2, hwf, hewf, heval⟩ := normRun_inv N C.gates hM
  set st := normRun N C.gates
  have hout_wf : wvalLt (N + st.1.length) (st.2.getD C.output .c0) := by
    by_cases ho : C.output < st.2.length
    · exact hewf C.output ho
    · rw [getD_ge _ _ _ (by omega)]; trivial
  refine ⟨⟨st.1, st.2.getD C.output .c0, hwf, hout_wf⟩, hlen1, fun x hx => ?_⟩
  simp only [BCirc.eval, Circuit.eval, Circuit.wires]
  change evalWVal (st.2.getD C.output .c0) (BW st.1 x) = (CW C.gates x).getD C.output false
  by_cases ho : C.output < N + C.gates.length
  · exact (heval x hx C.output ho).symm
  · rw [getD_ge st.2 .c0 C.output (by omega), getD_ge (CW C.gates x) false C.output (by rw [CW_len, hx]; omega)]
    rfl

structure SubstState where
  acc : List BGate
  env : List WVal
  kept : List Bool

def substOne (N' : ℕ) (forceZero : ℕ → Bool) (st : SubstState) (g : BGate) : SubstState :=
  let j := st.kept.length
  if forceZero j then
    ⟨st.acc, st.env ++ [.c0], st.kept ++ [false]⟩
  else
    let va := st.env.getD g.a .c0
    let vb := st.env.getD g.b .c0
    let r := simpBin g.isOr va vb (N' + st.acc.length)
    match r.1 with
    | none => ⟨st.acc, st.env ++ [r.2], st.kept ++ [false]⟩
    | some g' => ⟨st.acc ++ [g'], st.env ++ [r.2], st.kept ++ [true]⟩

theorem substOne_kept_len (N' : ℕ) (fz : ℕ → Bool) (st : SubstState) (g : BGate) :
    (substOne N' fz st g).kept.length = st.kept.length + 1 := by
  unfold substOne
  by_cases h : fz st.kept.length = true
  · simp [h]
  · simp only [h, ↓reduceIte]
    cases (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 <;> simp

theorem substOne_env_len (N' : ℕ) (fz : ℕ → Bool) (st : SubstState) (g : BGate) :
    (substOne N' fz st g).env.length = st.env.length + 1 := by
  unfold substOne
  by_cases h : fz st.kept.length = true
  · simp [h]
  · simp only [h, ↓reduceIte]
    cases (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 <;> simp

theorem substOne_env_lt (N' : ℕ) (fz : ℕ → Bool) (st : SubstState) (g : BGate)
    (i : ℕ) (hi : i < st.env.length) :
    (substOne N' fz st g).env.getD i .c0 = st.env.getD i .c0 := by
  unfold substOne
  by_cases h : fz st.kept.length = true
  · simp only [h, ↓reduceIte]; exact getD_app_lt _ _ _ _ hi
  · simp only [h, ↓reduceIte]
    cases (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1
    <;> exact getD_app_lt _ _ _ _ hi

theorem substOne_kept_lt (N' : ℕ) (fz : ℕ → Bool) (st : SubstState) (g : BGate)
    (j : ℕ) (hj : j < st.kept.length) :
    (substOne N' fz st g).kept.getD j true = st.kept.getD j true := by
  unfold substOne
  by_cases h : fz st.kept.length = true
  · simp only [h, ↓reduceIte]; exact getD_app_lt _ _ _ _ hj
  · simp only [h, ↓reduceIte]
    cases (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1
    <;> exact getD_app_lt _ _ _ _ hj

theorem substOne_acc_prefix (N' : ℕ) (fz : ℕ → Bool) (st : SubstState) (g : BGate) :
    ∃ tail : List BGate, (substOne N' fz st g).acc = st.acc ++ tail := by
  unfold substOne
  by_cases h : fz st.kept.length = true
  · exact ⟨[], by simp [h]⟩
  · simp only [h, ↓reduceIte]
    cases hr : (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 with
    | none => exact ⟨[], by simp⟩
    | some g' => exact ⟨[g'], rfl⟩

def substRun (N' : ℕ) (forceZero : ℕ → Bool) (env₀ : List WVal) (gs : List BGate) : SubstState :=
  gs.foldl (substOne N' forceZero) ⟨[], env₀, []⟩

theorem substRun_nil (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) :
    substRun N' fz env₀ [] = ⟨[], env₀, []⟩ := rfl

theorem substRun_snoc (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (gs : List BGate) (g : BGate) :
    substRun N' fz env₀ (gs ++ [g]) = substOne N' fz (substRun N' fz env₀ gs) g := by
  simp [substRun, List.foldl_append]

theorem substRun_kept_len (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (gs : List BGate) :
    (substRun N' fz env₀ gs).kept.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [substRun_snoc, substOne_kept_len, ih]; simp

theorem substRun_env_len (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (gs : List BGate) :
    (substRun N' fz env₀ gs).env.length = env₀.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [substRun]
  | append_singleton gs g ih =>
    rw [substRun_snoc, substOne_env_len, ih]; simp; omega

theorem substRun_acc_prefix (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (pre post : List BGate) :
    ∃ tail : List BGate, (substRun N' fz env₀ (pre ++ post)).acc = (substRun N' fz env₀ pre).acc ++ tail := by
  induction post using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton post g ih =>
    obtain ⟨t1, ht1⟩ := ih
    rw [← List.append_assoc, substRun_snoc]
    obtain ⟨t2, ht2⟩ := substOne_acc_prefix N' fz (substRun N' fz env₀ (pre ++ post)) g
    exact ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

theorem substRun_basic (N N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (hlen0 : env₀.length = N)
    (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0)) (gs : List BGate) :
    let st := substRun N' fz env₀ gs
    st.kept.length = gs.length ∧
    st.env.length = N + gs.length ∧
    st.acc.length = st.kept.count true ∧
    (∀ j < st.acc.length, let g := st.acc.getD j dGate; g.a < N' + j ∧ g.b < N' + j ∧ g.a ≠ g.b) ∧
    (∀ i < st.env.length, wvalLt (N' + st.acc.length) (st.env.getD i .c0)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, by simp [substRun, hlen0], rfl, fun j hj => by simp [substRun] at hj, ?_⟩
    intro i hi
    simp only [substRun, List.foldl_nil, List.length_nil, add_zero] at hi ⊢
    exact hwf0 i (by omega)
  | append_singleton gs g ih =>
    obtain ⟨hklen, helen, halen, hwf, hewf⟩ := ih
    rw [substRun_snoc]
    generalize hst : substRun N' fz env₀ gs = st at hklen helen halen hwf hewf ⊢
    have hEnvLt : ∀ k, wvalLt (N' + st.acc.length) (st.env.getD k .c0) := by
      intro k
      by_cases hk : k < st.env.length
      · exact hewf k hk
      · rw [getD_ge _ _ _ (by omega)]; trivial
    dsimp only [substOne]
    by_cases hfz : fz st.kept.length = true
    · simp only [hfz, ↓reduceIte]
      refine ⟨by simp [hklen], by simp [helen]; omega, by simp [halen, List.count_append], hwf, ?_⟩
      intro i hi
      rw [getD_snoc]
      split_ifs with h1 h2
      · exact hewf i h1
      · trivial
      · trivial
    · simp only [hfz, Bool.false_eq_true, ↓reduceIte]
      have hwf_r := simpBin_wf g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0)
        (N' + st.acc.length) (hEnvLt g.a) (hEnvLt g.b)
      dsimp only at hwf_r ⊢
      cases hr : (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 with
      | none =>
        rw [hr] at hwf_r
        dsimp only
        refine ⟨by simp [hklen], by simp [helen]; omega, by simp [halen, List.count_append], hwf, ?_⟩
        intro i hi
        rw [getD_snoc]
        split_ifs with h1 h2
        · exact hewf i h1
        · exact hwf_r
        · trivial
      | some g' =>
        rw [hr] at hwf_r
        obtain ⟨hga, hgb, hgab, hr2⟩ := hwf_r
        dsimp only
        refine ⟨by simp [hklen], by simp [helen]; omega,
          by simp [halen, List.count_append], ?_, ?_⟩
        · intro j hj
          rw [getD_snoc]
          split_ifs with h1 h2
          · exact hwf j h1
          · subst h2; exact ⟨hga, hgb, hgab⟩
          · simp at hj; omega
        · intro i hi
          rw [getD_snoc]
          split_ifs with h1 h2
          · exact wvalLt_mono (by simp) (hewf i h1)
          · rw [hr2]; simp [wvalLt]
          · trivial

theorem substRun_take (N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (gs : List BGate) (k : ℕ) :
    let st := substRun N' fz env₀ gs
    let stk := substRun N' fz env₀ (gs.take k)
    (∀ i < stk.env.length, st.env.getD i .c0 = stk.env.getD i .c0) ∧
    (∀ j < stk.kept.length, st.kept.getD j true = stk.kept.getD j true) := by
  have haux : ∀ (pre post : List BGate),
      let st1 := substRun N' fz env₀ pre
      let st2 := substRun N' fz env₀ (pre ++ post)
      (∀ i < st1.env.length, st2.env.getD i .c0 = st1.env.getD i .c0) ∧
      (∀ j < st1.kept.length, st2.kept.getD j true = st1.kept.getD j true) := by
    intro pre post
    induction post using List.reverseRecOn with
    | nil => simp
    | append_singleton post g ih =>
      obtain ⟨ihe, ihk⟩ := ih
      rw [← List.append_assoc, substRun_snoc]
      have hle_e : (substRun N' fz env₀ pre).env.length ≤ (substRun N' fz env₀ (pre ++ post)).env.length := by
        rw [substRun_env_len, substRun_env_len]; simp
      have hle_k : (substRun N' fz env₀ pre).kept.length ≤ (substRun N' fz env₀ (pre ++ post)).kept.length := by
        rw [substRun_kept_len, substRun_kept_len]; simp
      exact ⟨fun i hi => by rw [substOne_env_lt _ _ _ _ i (lt_of_lt_of_le hi hle_e), ihe i hi],
             fun j hj => by rw [substOne_kept_lt _ _ _ _ j (lt_of_lt_of_le hj hle_k), ihk j hj]⟩
  have := haux (gs.take k) (gs.drop k)
  rwa [List.take_append_drop] at this

theorem substRun_gate_spec (N N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (hlen0 : env₀.length = N)
    (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0)) (gs : List BGate) (j : ℕ) (hj : j < gs.length)
    (ha : (gs.getD j dGate).a < N + j) (hb : (gs.getD j dGate).b < N + j) :
    let st := substRun N' fz env₀ gs
    let g := gs.getD j dGate
    let stj := substRun N' fz env₀ (gs.take j)
    let r := simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + stj.acc.length)
    (fz j = true → st.env.getD (N + j) .c0 = .c0 ∧ st.kept.getD j true = false) ∧
    (fz j = false → st.env.getD (N + j) .c0 = r.2 ∧ st.kept.getD j true = r.1.isSome) := by
  dsimp only
  have htk : gs.take (j + 1) = gs.take j ++ [gs.getD j dGate] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hlenj : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hlenj1 : (gs.take (j + 1)).length = j + 1 := List.length_take_of_le hj
  have htpj := substRun_take N' fz env₀ gs j
  have htpj1 := substRun_take N' fz env₀ gs (j + 1)
  have he_eq : (substRun N' fz env₀ gs).env.getD (N + j) .c0 =
      (substRun N' fz env₀ (gs.take (j + 1))).env.getD (N + j) .c0 :=
    htpj1.1 (N + j) (by rw [substRun_env_len, hlen0, hlenj1]; omega)
  have hk_eq : (substRun N' fz env₀ gs).kept.getD j true =
      (substRun N' fz env₀ (gs.take (j + 1))).kept.getD j true :=
    htpj1.2 j (by rw [substRun_kept_len, hlenj1]; omega)
  have ha_eq : (substRun N' fz env₀ gs).env.getD (gs.getD j dGate).a .c0 =
      (substRun N' fz env₀ (gs.take j)).env.getD (gs.getD j dGate).a .c0 :=
    htpj.1 _ (by rw [substRun_env_len, hlen0, hlenj]; exact ha)
  have hb_eq : (substRun N' fz env₀ gs).env.getD (gs.getD j dGate).b .c0 =
      (substRun N' fz env₀ (gs.take j)).env.getD (gs.getD j dGate).b .c0 :=
    htpj.1 _ (by rw [substRun_env_len, hlen0, hlenj]; exact hb)
  rw [he_eq, hk_eq, ha_eq, hb_eq, htk, substRun_snoc]
  have hkj : (substRun N' fz env₀ (gs.take j)).kept.length = j := by rw [substRun_kept_len, hlenj]
  have hej : (substRun N' fz env₀ (gs.take j)).env.length = N + j := by rw [substRun_env_len, hlen0, hlenj]
  generalize substRun N' fz env₀ (gs.take j) = stj at hkj hej ⊢
  constructor
  · intro hfz
    simp [substOne, hkj, hfz, getD_snoc, hej]
  · intro hfz
    simp only [substOne, hkj, hfz, Bool.false_eq_true, ↓reduceIte]
    cases hr : (simpBin (gs.getD j dGate).isOr (stj.env.getD (gs.getD j dGate).a .c0)
        (stj.env.getD (gs.getD j dGate).b .c0) (N' + stj.acc.length)).1 with
    | none =>
      simp [getD_snoc, hej, hkj]
    | some g' =>
      simp [getD_snoc, hej, hkj]

theorem substRun_eval (N N' : ℕ) (fz : ℕ → Bool) (env₀ : List WVal) (hlen0 : env₀.length = N)
    (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0))
    (gs : List BGate) (hgs_wf : ∀ j < gs.length, (gs.getD j dGate).a < N + j ∧ (gs.getD j dGate).b < N + j)
    (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N') :
    let st := substRun N' fz env₀ gs
    ((∀ i < N, evalWVal (env₀.getD i .c0) x' = true → x.getD i false = true) →
     ∀ w < N + gs.length, evalWVal (st.env.getD w .c0) (BW st.acc x') = true → (BW gs x).getD w false = true) ∧
    ((∀ i < N, x.getD i false = evalWVal (env₀.getD i .c0) x') →
     (∀ j < gs.length, fz j = true → (BW gs x).getD (N + j) false = false) →
     ∀ w < N + gs.length, (BW gs x).getD w false = evalWVal (st.env.getD w .c0) (BW st.acc x')) := by
  induction gs using List.reverseRecOn with
  | nil =>
    constructor
    · intro hle w hw h1
      simp only [substRun, List.foldl_nil, BW_nil] at h1 ⊢
      exact hle w (by simpa using hw) h1
    · intro heq _ w hw
      simp only [substRun, List.foldl_nil, BW_nil]
      exact heq w (by simpa using hw)
  | append_singleton gs g ih =>
    have hgs_wf' : ∀ j < gs.length, (gs.getD j dGate).a < N + j ∧ (gs.getD j dGate).b < N + j := by
      intro j hj
      have h := hgs_wf j (by simp; omega)
      rwa [getD_app_lt gs [g] dGate j hj] at h
    have hg_wf : g.a < N + gs.length ∧ g.b < N + gs.length := by
      have h := hgs_wf gs.length (by simp)
      rwa [getD_snoc, if_neg (lt_irrefl _), if_pos rfl] at h
    obtain ⟨ih_mono, ih_eq⟩ := ih hgs_wf'
    have hbas := substRun_basic N N' fz env₀ hlen0 hwf0 gs
    rw [substRun_snoc]
    generalize hst : substRun N' fz env₀ gs = st at ih_mono ih_eq hbas ⊢
    have hstep_w : ∀ (v : WVal) (hv : wvalLt (N' + st.acc.length) v) (og : Option BGate),
        evalWVal v (BW (match og with | none => st.acc | some g' => st.acc ++ [g']) x') =
        evalWVal v (BW st.acc x') := by
      intro v hv og
      cases og with
      | none => rfl
      | some g' =>
        cases v with
        | c0 => rfl
        | c1 => rfl
        | ref u =>
          simp only [evalWVal, BW_snoc, bstep]
          exact getD_app_lt _ _ _ _ (by rw [BW_len, hx']; exact hv)
    have hEval_r := simpBin_eval g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (BW st.acc x')
    dsimp only at hEval_r
    rw [BW_len, hx'] at hEval_r
    dsimp only [substOne]
    constructor
    · intro hle w hw h1
      rw [BW_snoc, bstep, getD_snoc, BW_len, hx]
      by_cases hfz : fz st.kept.length = true
      · simp only [hfz, ↓reduceIte] at h1
        rw [getD_snoc, hbas.2.1] at h1
        split_ifs at h1 with hlt heq
        · simp only [hlt, ↓reduceIte]; exact ih_mono hle w hlt h1
        · cases h1
        · cases h1
      · simp only [hfz, Bool.false_eq_true, ↓reduceIte] at h1
        cases hr1 : (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 with
        | none =>
          rw [hr1] at h1 hEval_r
          dsimp only at h1 hEval_r
          rw [getD_snoc, hbas.2.1] at h1
          split_ifs at h1 with hlt heq
          · simp only [hlt, ↓reduceIte]; exact ih_mono hle w hlt h1
          · simp only [heq, lt_irrefl, ↓reduceIte]
            rw [hEval_r] at h1
            unfold evalBGate
            cases hio : g.isOr <;> simp only [hio, Bool.false_eq_true, ↓reduceIte,
              Bool.and_eq_true, Bool.or_eq_true] at h1 ⊢
            · exact ⟨ih_mono hle g.a hg_wf.1 h1.1, ih_mono hle g.b hg_wf.2 h1.2⟩
            · rcases h1 with ha | hb
              · exact Or.inl (ih_mono hle g.a hg_wf.1 ha)
              · exact Or.inr (ih_mono hle g.b hg_wf.2 hb)
          · cases h1
        | some g' =>
          rw [hr1] at h1 hEval_r
          dsimp only at h1 hEval_r
          rw [getD_snoc, hbas.2.1] at h1
          split_ifs at h1 with hlt heq
          · simp only [hlt, ↓reduceIte]
            have hst_e := hstep_w (st.env.getD w .c0) (hbas.2.2.2.2 w (by rw [hbas.2.1]; exact hlt)) (some g')
            dsimp only at hst_e
            rw [hst_e] at h1
            exact ih_mono hle w hlt h1
          · simp only [heq, lt_irrefl, ↓reduceIte]
            rw [BW_snoc, hEval_r] at h1
            unfold evalBGate
            cases hio : g.isOr <;> simp only [hio, Bool.false_eq_true, ↓reduceIte,
              Bool.and_eq_true, Bool.or_eq_true] at h1 ⊢
            · exact ⟨ih_mono hle g.a hg_wf.1 h1.1, ih_mono hle g.b hg_wf.2 h1.2⟩
            · rcases h1 with ha | hb
              · exact Or.inl (ih_mono hle g.a hg_wf.1 ha)
              · exact Or.inr (ih_mono hle g.b hg_wf.2 hb)
          · cases h1
    · intro heq hfz0 w hw
      have hfz0' : ∀ j < gs.length, fz j = true → (BW gs x).getD (N + j) false = false := by
        intro j hj hf
        have h := hfz0 j (by simp; omega) hf
        rwa [BW_snoc, bstep, getD_app_lt _ _ _ _ (by rw [BW_len, hx]; omega)] at h
      rw [BW_snoc, bstep, getD_snoc, BW_len, hx]
      by_cases hfz : fz st.kept.length = true
      · simp only [hfz, ↓reduceIte, getD_snoc, hbas.2.1]
        split_ifs with hlt heq_w
        · exact ih_eq heq hfz0' w hlt
        · have h0 := hfz0 gs.length (by simp) (by rwa [hbas.1] at hfz)
          rw [BW_snoc, bstep, getD_snoc, BW_len, hx] at h0
          simpa [evalWVal] using h0
        · rfl
      · simp only [hfz, Bool.false_eq_true, ↓reduceIte]
        cases hr1 : (simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (N' + st.acc.length)).1 with
        | none =>
          rw [hr1] at hEval_r
          dsimp only at hEval_r ⊢
          rw [getD_snoc, hbas.2.1]
          split_ifs with hlt heq_w
          · exact ih_eq heq hfz0' w hlt
          · rw [hEval_r, evalBGate, ih_eq heq hfz0' g.a hg_wf.1, ih_eq heq hfz0' g.b hg_wf.2]
          · rfl
        | some g' =>
          rw [hr1] at hEval_r
          dsimp only at hEval_r ⊢
          rw [getD_snoc, hbas.2.1]
          split_ifs with hlt heq_w
          · have hst_e := hstep_w (st.env.getD w .c0) (hbas.2.2.2.2 w (by rw [hbas.2.1]; exact hlt)) (some g')
            dsimp only at hst_e
            rw [hst_e]
            exact ih_eq heq hfz0' w hlt
          · rw [BW_snoc, hEval_r, evalBGate, ih_eq heq hfz0' g.a hg_wf.1, ih_eq heq hfz0' g.b hg_wf.2]
          · rfl

theorem count_true_eq_card_filter (l : List Bool) :
    l.count true = (Finset.univ.filter (fun j : Fin l.length => l.getD j.val true = true)).card := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    rw [List.count_cons, ih]
    let T := Finset.univ.filter (fun j : Fin (b :: bs).length => (b :: bs).getD j.val true = true)
    let f : Fin bs.length ↪ Fin (b :: bs).length := ⟨Fin.succ, Fin.succ_injective _⟩
    have hmap : T.erase 0 = (Finset.univ.filter (fun j : Fin bs.length => bs.getD j.val true = true)).map f := by
      ext j
      simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, f, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hj0, hjb⟩
        refine ⟨j.pred hj0, ?_, Fin.succ_pred j hj0⟩
        have hv : j.val = (j.pred hj0).val + 1 := by
          have h := congrArg Fin.val (Fin.succ_pred j hj0)
          simp only [Fin.val_succ] at h
          exact h.symm
        rw [hv] at hjb
        exact hjb
      · rintro ⟨i, hib, rfl⟩
        exact ⟨Fin.succ_ne_zero i, hib⟩
    change (Finset.univ.filter (fun j : Fin bs.length => bs.getD j.val true = true)).card +
      (if (b == true) = true then 1 else 0) = T.card
    by_cases hb : b = true
    · have h0 : (0 : Fin (b :: bs).length) ∈ T := by simp [T, hb]
      rw [← Finset.card_erase_add_one h0, hmap, Finset.card_map]; simp [hb]
    · have h0 : (0 : Fin (b :: bs).length) ∉ T := by simp [T, hb]
      rw [← Finset.erase_eq_of_notMem h0, hmap, Finset.card_map]; simp [hb]

theorem count_true_add_false_set (l : List Bool) (S : Finset (Fin l.length))
    (hS : ∀ j ∈ S, l.getD j.val true = false) :
    l.count true + S.card ≤ l.length := by
  rw [count_true_eq_card_filter l]
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin l.length => l.getD j.val true = true)) S := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := hS j hj2
    rw [h1] at h2; cases h2
  have hunion := Finset.card_union_of_disjoint hdisj
  have hle : (Finset.univ.filter (fun j : Fin l.length => l.getD j.val true = true) ∪ S).card ≤
      (Finset.univ : Finset (Fin l.length)).card := Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

def mkSubstBCirc {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0)) : BCirc N' :=
  let st := substRun N' fz env₀ C.gates
  let hbas := substRun_basic N N' fz env₀ hlen0 hwf0 C.gates
  ⟨st.acc,
   match C.out with
   | .c0 => .c0
   | .c1 => .c1
   | .ref w => st.env.getD w .c0,
   hbas.2.2.2.1,
   by
     cases ho : C.out with
     | c0 => trivial
     | c1 => trivial
     | ref w =>
       have hw : w < N + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
       exact hbas.2.2.2.2 w (by rw [hbas.2.1]; exact hw)⟩

theorem mkSubstBCirc_gates {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0)) :
    (mkSubstBCirc C fz env₀ hlen0 hwf0).gates = (substRun N' fz env₀ C.gates).acc := rfl

theorem mkSubstBCirc_out {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0)) :
    (mkSubstBCirc C fz env₀ hlen0 hwf0).out =
      match C.out with
      | .c0 => .c0
      | .c1 => .c1
      | .ref w => (substRun N' fz env₀ C.gates).env.getD w .c0 := rfl

theorem mkSubstBCirc_eval_eq {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0))
    (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N')
    (heq : ∀ i < N, x.getD i false = evalWVal (env₀.getD i .c0) x')
    (hfz0 : ∀ j < C.gates.length, fz j = true → C.val x (N + j) = false) :
    (mkSubstBCirc C fz env₀ hlen0 hwf0).eval x' = C.eval x := by
  have hev := (substRun_eval N N' fz env₀ hlen0 hwf0 C.gates
    (fun j hj => ⟨(C.wf j hj).1, (C.wf j hj).2.1⟩) x x' hx hx').2 heq hfz0
  simp only [BCirc.eval, mkSubstBCirc_out, mkSubstBCirc_gates]
  cases ho : C.out with
  | c0 => rfl
  | c1 => rfl
  | ref w =>
    have hw : w < N + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
    exact (hev w hw).symm

theorem mkSubstBCirc_eval_mono {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0))
    (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N')
    (hle : ∀ i < N, evalWVal (env₀.getD i .c0) x' = true → x.getD i false = true) :
    (mkSubstBCirc C fz env₀ hlen0 hwf0).eval x' = true → C.eval x = true := by
  have hmo := (substRun_eval N N' fz env₀ hlen0 hwf0 C.gates
    (fun j hj => ⟨(C.wf j hj).1, (C.wf j hj).2.1⟩) x x' hx hx').1 hle
  simp only [BCirc.eval, mkSubstBCirc_out, mkSubstBCirc_gates]
  cases ho : C.out with
  | c0 => intro h; cases h
  | c1 => intro _; rfl
  | ref w =>
    have hw : w < N + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
    exact hmo w hw

theorem mkSubstBCirc_size_le {N N' : ℕ} (C : BCirc N) (fz : ℕ → Bool) (env₀ : List WVal)
    (hlen0 : env₀.length = N) (hwf0 : ∀ i < N, wvalLt N' (env₀.getD i .c0))
    (S : Finset (Fin C.gates.length))
    (hS : ∀ j ∈ S, (substRun N' fz env₀ C.gates).kept.getD j.val true = false) :
    (mkSubstBCirc C fz env₀ hlen0 hwf0).gates.length + S.card ≤ C.gates.length := by
  have hbas := substRun_basic N N' fz env₀ hlen0 hwf0 C.gates
  set st := substRun N' fz env₀ C.gates
  change st.acc.length + S.card ≤ C.gates.length
  rw [hbas.2.2.1]
  have hlenk : st.kept.length = C.gates.length := hbas.1
  let e : Fin C.gates.length ≃ Fin st.kept.length := finCongr hlenk.symm
  have hcard : (S.map e.toEmbedding).card = S.card := Finset.card_map _
  have hcnt := count_true_add_false_set st.kept (S.map e.toEmbedding) (by
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨j0, hj0, rfl⟩
    exact hS j0 hj0)
  rw [hcard, hlenk] at hcnt
  exact hcnt

def forceZeroAt {N : ℕ} (C : BCirc N) (j0 : ℕ) : BCirc N :=
  mkSubstBCirc C (fun j => decide (j = j0)) (initEnv N) (initEnv_len N)
    (fun i hi => by rw [initEnv_getD]; simp [hi, wvalLt])

theorem forceZeroAt_size {N : ℕ} (C : BCirc N) {j0 : ℕ} (hj0 : j0 < C.gates.length) :
    (forceZeroAt C j0).gates.length + 1 ≤ C.gates.length := by
  unfold forceZeroAt
  have h := mkSubstBCirc_size_le (N' := N) C (fun j => decide (j = j0)) (initEnv N) (initEnv_len N)
    (fun i hi => by rw [initEnv_getD]; simp [hi, wvalLt])
    {⟨j0, hj0⟩} (by
      intro j hj
      rw [Finset.mem_singleton.mp hj]
      have hsp := substRun_gate_spec N N (fun j => decide (j = j0)) (initEnv N) (initEnv_len N)
        (fun i hi => by rw [initEnv_getD]; simp [hi, wvalLt])
        C.gates j0 hj0 (C.wf j0 hj0).1 (C.wf j0 hj0).2.1
      exact (hsp.1 (by simp)).2)
  simpa using h

theorem forceZeroAt_mono {N : ℕ} (C : BCirc N) (j0 : ℕ) {x : List Bool} (hx : x.length = N) :
    (forceZeroAt C j0).eval x = true → C.eval x = true :=
  mkSubstBCirc_eval_mono C _ _ _ _ x x hx hx (fun i hi => by
    rw [initEnv_getD]; simp only [hi, ↓reduceIte, evalWVal]; exact id)

theorem forceZeroAt_eq_of_val_false {N : ℕ} (C : BCirc N) (j0 : ℕ)
    {x : List Bool} (hx : x.length = N) (h0 : C.val x (N + j0) = false) :
    (forceZeroAt C j0).eval x = C.eval x :=
  mkSubstBCirc_eval_eq C _ _ _ _ x x hx hx
    (fun i hi => by rw [initEnv_getD]; simp only [hi, ↓reduceIte, evalWVal])
    (fun j _ hfz => by
      have : j = j0 := of_decide_eq_true hfz
      subst this; exact h0)

theorem forceZeroAt_eq_of_dead {N : ℕ} (C : BCirc N) {j0 : ℕ} (hj0 : j0 < C.gates.length)
    (hout : C.out ≠ .ref (N + j0))
    (hdead : ∀ k < C.gates.length, j0 < k →
      (C.gates.getD k dGate).a ≠ N + j0 ∧ (C.gates.getD k dGate).b ≠ N + j0)
    {x : List Bool} (hx : x.length = N) :
    (forceZeroAt C j0).eval x = C.eval x := by
  let fz := fun j => decide (j = j0)
  let st := substRun N fz (initEnv N) C.gates
  have hwf0 : ∀ i < N, wvalLt N ((initEnv N).getD i .c0) := fun i hi => by
    rw [initEnv_getD]; simp [hi, wvalLt]
  have hwire : ∀ w < N + C.gates.length, w ≠ N + j0 →
      evalWVal (st.env.getD w .c0) (BW st.acc x) = C.val x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hne
      by_cases hlt : w < N
      · have htp := (substRun_take N fz (initEnv N) C.gates 0).1 w
          (by simp [substRun, initEnv_len, hlt])
        simp only [List.take_zero, substRun_nil] at htp
        change evalWVal ((substRun N fz (initEnv N) C.gates).env.getD w .c0) _ = _
        rw [htp, initEnv_getD]; simp only [hlt, ↓reduceIte, evalWVal, BCirc.val]
        rw [BW_prefix _ _ _ (by omega), BW_prefix _ _ _ (by omega)]
      · have hj : w - N < C.gates.length := by omega
        have hw_eq : w = N + (w - N) := by omega
        have hne_j : w - N ≠ j0 := by omega
        rw [hw_eq]
        have hwf := C.wf (w - N) hj
        have hsp := (substRun_gate_spec N N fz (initEnv N) (initEnv_len N) hwf0 C.gates
          (w - N) hj hwf.1 hwf.2.1).2 (by simp [fz, hne_j])
        have hlenj : (C.gates.take (w - N)).length = w - N := List.length_take_of_le (Nat.le_of_lt hj)
        have hbasj := substRun_basic N N fz (initEnv N) (initEnv_len N) hwf0 (C.gates.take (w - N))
        have hsp_tk : C.gates.take (w - N + 1) = C.gates.take (w - N) ++ [C.gates.getD (w - N) dGate] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hj]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        obtain ⟨tail1, htail1⟩ := substRun_acc_prefix N fz (initEnv N)
          (C.gates.take (w - N + 1)) (C.gates.drop (w - N + 1))
        rw [List.take_append_drop] at htail1
        obtain ⟨tail0, htail0⟩ := substRun_acc_prefix N fz (initEnv N)
          (C.gates.take (w - N)) (C.gates.drop (w - N))
        rw [List.take_append_drop] at htail0
        have ha_t := (substRun_take N fz (initEnv N) C.gates (w - N)).1 (C.gates.getD (w - N) dGate).a
          (by rw [hbasj.2.1, hlenj]; exact hwf.1)
        have hb_t := (substRun_take N fz (initEnv N) C.gates (w - N)).1 (C.gates.getD (w - N) dGate).b
          (by rw [hbasj.2.1, hlenj]; exact hwf.2.1)
        have hst1_eq : (substRun N fz (initEnv N) (C.gates.take (w - N + 1))).acc =
            match (simpBin (C.gates.getD (w - N) dGate).isOr
              (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
              (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
              (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).1 with
            | none => (substRun N fz (initEnv N) (C.gates.take (w - N))).acc
            | some g' => (substRun N fz (initEnv N) (C.gates.take (w - N))).acc ++ [g'] := by
          rw [hsp_tk, substRun_snoc]
          dsimp only [substOne]
          rw [hbasj.1, hlenj]
          simp only [fz, decide_eq_true_eq, hne_j, ↓reduceIte]
          rw [← ha_t, ← hb_t]
          cases (simpBin (C.gates.getD (w - N) dGate).isOr
            (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
            (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
            (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).1 <;> rfl
        have hga_ne : (C.gates.getD (w - N) dGate).a ≠ N + j0 := by
          by_cases hgt : j0 < w - N
          · exact (hdead (w - N) hj hgt).1
          · omega
        have hgb_ne : (C.gates.getD (w - N) dGate).b ≠ N + j0 := by
          by_cases hgt : j0 < w - N
          · exact (hdead (w - N) hj hgt).2
          · omega
        have hval_a := ih (C.gates.getD (w - N) dGate).a (by omega) (by omega) hga_ne
        have hval_b := ih (C.gates.getD (w - N) dGate).b (by omega) (by omega) hgb_ne
        have ha_lt_j : wvalLt (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)
            (st.env.getD (C.gates.getD (w - N) dGate).a .c0) := by
          change wvalLt _ ((substRun N fz (initEnv N) C.gates).env.getD _ .c0)
          rw [ha_t]; exact hbasj.2.2.2.2 _ (by rw [hbasj.2.1, hlenj]; exact hwf.1)
        have hb_lt_j : wvalLt (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)
            (st.env.getD (C.gates.getD (w - N) dGate).b .c0) := by
          change wvalLt _ ((substRun N fz (initEnv N) C.gates).env.getD _ .c0)
          rw [hb_t]; exact hbasj.2.2.2.2 _ (by rw [hbasj.2.1, hlenj]; exact hwf.2.1)
        have hEval_r := simpBin_eval (C.gates.getD (w - N) dGate).isOr
          (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
          (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
          (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x)
        dsimp only at hEval_r
        rw [BW_len, hx] at hEval_r
        have hpref_j : ∀ (v : WVal)
            (hv : wvalLt (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length) v),
            evalWVal v (BW st.acc x) =
            evalWVal v (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x) := by
          intro v hv
          cases v with
          | c0 => rfl
          | c1 => rfl
          | ref u =>
            simp only [evalWVal, show st.acc = _ ++ tail0 from htail0, BW_append]
            exact BW_prefix _ _ _ (by rw [BW_len, hx]; exact hv)
        have hpref_j1 : ∀ (v : WVal)
            (hv : wvalLt (N + (substRun N fz (initEnv N) (C.gates.take (w - N + 1))).acc.length) v),
            evalWVal v (BW st.acc x) =
            evalWVal v (BW (substRun N fz (initEnv N) (C.gates.take (w - N + 1))).acc x) := by
          intro v hv
          cases v with
          | c0 => rfl
          | c1 => rfl
          | ref u =>
            simp only [evalWVal, show st.acc = _ ++ tail1 from htail1, BW_append]
            exact BW_prefix _ _ _ (by rw [BW_len, hx]; exact hv)
        have hwf_r := simpBin_wf (C.gates.getD (w - N) dGate).isOr
          (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
          (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
          (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length) ha_lt_j hb_lt_j
        dsimp only at hwf_r
        change evalWVal ((substRun N fz (initEnv N) C.gates).env.getD (N + (w - N)) .c0) (BW st.acc x) = _
        rw [hsp.1, hpref_j1 _ (by
          rw [hst1_eq]
          cases hr1 : (simpBin (C.gates.getD (w - N) dGate).isOr
            (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
            (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
            (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).1 with
          | none => rw [hr1] at hwf_r; exact hwf_r
          | some g' => rw [hr1] at hwf_r; rw [hwf_r.2.2.2]; simp [wvalLt])]
        rw [hst1_eq]
        have hEval_r' : evalWVal (simpBin (C.gates.getD (w - N) dGate).isOr
            (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
            (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
            (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).2
            (BW (match (simpBin (C.gates.getD (w - N) dGate).isOr
                (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
                (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
                (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).1 with
              | none => (substRun N fz (initEnv N) (C.gates.take (w - N))).acc
              | some g' => (substRun N fz (initEnv N) (C.gates.take (w - N))).acc ++ [g']) x) =
            if (C.gates.getD (w - N) dGate).isOr then
              (evalWVal (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
                (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x) ||
               evalWVal (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
                (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x))
            else
              (evalWVal (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
                (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x) &&
               evalWVal (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
                (BW (substRun N fz (initEnv N) (C.gates.take (w - N))).acc x)) := by
          cases hr1 : (simpBin (C.gates.getD (w - N) dGate).isOr
            (st.env.getD (C.gates.getD (w - N) dGate).a .c0)
            (st.env.getD (C.gates.getD (w - N) dGate).b .c0)
            (N + (substRun N fz (initEnv N) (C.gates.take (w - N))).acc.length)).1
          <;> (rw [hr1] at hEval_r; simpa [BW_snoc] using hEval_r)
        rw [hEval_r', ← hpref_j _ ha_lt_j, ← hpref_j _ hb_lt_j, hval_a, hval_b, C.val_gate hx hj]
        rfl
  simp only [forceZeroAt, BCirc.eval, mkSubstBCirc_out, mkSubstBCirc_gates]
  cases ho : C.out with
  | c0 => rfl
  | c1 => rfl
  | ref w =>
    have hw : w < N + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
    have hne : w ≠ N + j0 := fun h => hout (by rw [ho, h])
    exact hwire w hw hne

def zbsIn (m : ℕ) (ou ov : Option (Fin m)) : List Bool :=
  List.ofFn (fun u : Fin m => decide (ou = some u)) ++
  List.ofFn (fun v : Fin m => decide (ov = some v))

theorem zbsIn_len (m : ℕ) (ou ov : Option (Fin m)) : (zbsIn m ou ov).length = 2 * m := by
  simp [zbsIn]; omega

theorem zbsIn_getD (m : ℕ) (ou ov : Option (Fin m)) (t : ℕ) :
    (zbsIn m ou ov).getD t false =
      if h1 : t < m then decide (ou = some ⟨t, h1⟩)
      else if h2 : t < 2 * m then decide (ov = some ⟨t - m, by omega⟩)
      else false := by
  unfold zbsIn
  by_cases h1 : t < m
  · rw [dif_pos h1, getD_app_lt _ _ _ _ (by simp [h1]), getD_ofFn, dif_pos h1]
  · rw [dif_neg h1, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn, getD_ofFn]
    by_cases h2 : t < 2 * m
    · rw [dif_pos h2, dif_pos (by omega : t - m < m)]
    · rw [dif_neg h2, dif_neg (by omega : ¬ t - m < m)]

theorem zbsIn_getD_L (m : ℕ) (ou ov : Option (Fin m)) (u : Fin m) :
    (zbsIn m ou ov).getD u.val false = decide (ou = some u) := by
  rw [zbsIn_getD, dif_pos u.isLt]

theorem zbsIn_getD_R (m : ℕ) (ou ov : Option (Fin m)) (v : Fin m) :
    (zbsIn m ou ov).getD (m + v.val) false = decide (ov = some v) := by
  rw [zbsIn_getD, dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]

def zbsSpec (m : ℕ) (ou ov : Option (Fin m)) : Bool :=
  match ou, ov with
  | some u, some v => decide (v.val ≤ u.val)
  | _, _ => false

def RepresentsZBS (m : ℕ) (C : BCirc (2 * m)) : Prop :=
  ∀ ou ov : Option (Fin m), C.eval (zbsIn m ou ov) = zbsSpec m ou ov

def IsMinZBS (m : ℕ) (C : BCirc (2 * m)) : Prop :=
  RepresentsZBS m C ∧ ∀ D : BCirc (2 * m), RepresentsZBS m D → C.gates.length ≤ D.gates.length

def IsS1DWire {N : ℕ} (C : BCirc N) (w : ℕ) : Prop :=
  ∃ j : Fin C.gates.length,
    (C.gates.getD j.val dGate).isOr = true ∧
    ((C.gates.getD j.val dGate).a = w ∨ (C.gates.getD j.val dGate).b = w) ∧
    ∀ k : Fin C.gates.length,
      ((C.gates.getD k.val dGate).a = w ∨ (C.gates.getD k.val dGate).b = w) → k = j

theorem zbs_base_one (C : BCirc 2) (hR : RepresentsZBS 1 C) : 1 ≤ C.gates.length := by
  by_contra h0
  have hlen : C.gates.length = 0 := by omega
  have hwf := C.out_wf
  rw [hlen, add_zero] at hwf
  cases ho : C.out with
  | c0 =>
    have h := hR (some ⟨0, by omega⟩) (some ⟨0, by omega⟩)
    simp [BCirc.eval, evalWVal, ho, zbsSpec] at h
  | c1 =>
    have h := hR none none
    simp [BCirc.eval, evalWVal, ho, zbsSpec] at h
  | ref w =>
    rw [ho] at hwf
    simp only [wvalLt] at hwf
    have hgs : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
    have : w = 0 ∨ w = 1 := by omega
    rcases this with rfl | rfl
    · have h := hR (some ⟨0, by omega⟩) none
      rw [BCirc.eval, ho, evalWVal, hgs, BW_nil, zbsIn_getD] at h
      simp [zbsSpec] at h
    · have h := hR none (some ⟨0, by omega⟩)
      rw [BCirc.eval, ho, evalWVal, hgs, BW_nil, zbsIn_getD] at h
      simp [zbsSpec] at h

theorem zbs_out_is_gate {m : ℕ} (hm : 1 ≤ m) {C : BCirc (2 * m)} (hR : RepresentsZBS m C) :
    ∃ outJ : Fin C.gates.length, C.out = .ref (2 * m + outJ.val) := by
  have hwf := C.out_wf
  cases ho : C.out with
  | c0 =>
    have h := hR (some ⟨0, by omega⟩) (some ⟨0, by omega⟩)
    simp [BCirc.eval, evalWVal, ho, zbsSpec] at h
  | c1 =>
    have h := hR none none
    simp [BCirc.eval, evalWVal, ho, zbsSpec] at h
  | ref w =>
    rw [ho] at hwf
    simp only [wvalLt] at hwf
    by_cases hw : w < 2 * m
    · by_cases hwm : w < m
      · have h := hR (some ⟨w, hwm⟩) none
        simp only [BCirc.eval, evalWVal, ho, zbsSpec] at h
        rw [BW_prefix _ _ _ (by rw [zbsIn_len]; exact hw), zbsIn_getD, dif_pos hwm] at h
        simp at h
      · have h := hR none (some ⟨w - m, by omega⟩)
        simp only [BCirc.eval, evalWVal, ho, zbsSpec] at h
        rw [BW_prefix _ _ _ (by rw [zbsIn_len]; exact hw), zbsIn_getD, dif_neg hwm, dif_pos hw] at h
        simp at h
    · exact ⟨⟨w - 2 * m, by omega⟩, by congr 1; dsimp; omega⟩

theorem zbs_live {m : ℕ} {C : BCirc (2 * m)} (hMin : IsMinZBS m C) (j : Fin C.gates.length) :
    C.out = .ref (2 * m + j.val) ∨
    ∃ k : Fin C.gates.length, j.val < k.val ∧
      ((C.gates.getD k.val dGate).a = 2 * m + j.val ∨
       (C.gates.getD k.val dGate).b = 2 * m + j.val) := by
  by_contra h
  push_neg at h
  obtain ⟨hout, hdead⟩ := h
  have hRep' : RepresentsZBS m (forceZeroAt C j.val) := by
    intro ou ov
    rw [forceZeroAt_eq_of_dead C j.isLt hout (fun k hk hjk => hdead ⟨k, hk⟩ hjk) (zbsIn_len m ou ov)]
    exact hMin.1 ou ov
  have hle := hMin.2 _ hRep'
  have hlt := forceZeroAt_size C j.isLt
  omega

theorem zbs_nonzero_on_ones {m : ℕ} {C : BCirc (2 * m)} (hMin : IsMinZBS m C)
    (j : Fin C.gates.length) :
    ∃ u v : Fin m, v.val ≤ u.val ∧ C.val (zbsIn m (some u) (some v)) (2 * m + j.val) = true := by
  by_contra h
  push_neg at h
  have h0 : ∀ u v : Fin m, v.val ≤ u.val → C.val (zbsIn m (some u) (some v)) (2 * m + j.val) = false := by
    intro u v hvu
    cases hv : C.val (zbsIn m (some u) (some v)) (2 * m + j.val)
    · rfl
    · exact absurd hv (h u v hvu)
  have hRep' : RepresentsZBS m (forceZeroAt C j.val) := by
    intro ou ov
    cases hspec : zbsSpec m ou ov
    · cases hev : (forceZeroAt C j.val).eval (zbsIn m ou ov)
      · rfl
      · have := forceZeroAt_mono C j.val (zbsIn_len m ou ov) hev
        rw [hMin.1 ou ov, hspec] at this; cases this
    · cases ou with
      | none => simp [zbsSpec] at hspec
      | some u =>
        cases ov with
        | none => simp [zbsSpec] at hspec
        | some v =>
          simp only [zbsSpec, decide_eq_true_eq] at hspec
          rw [forceZeroAt_eq_of_val_false C j.val (zbsIn_len m _ _) (h0 u v hspec), hMin.1]
          simp [zbsSpec, hspec]
  have hle := hMin.2 _ hRep'
  have hlt := forceZeroAt_size C j.isLt
  omega

theorem zbs_input_read {m : ℕ} (hm : 1 ≤ m) {C : BCirc (2 * m)} (hR : RepresentsZBS m C)
    (w : ℕ) (hw : w < 2 * m) :
    ∃ j : Fin C.gates.length,
      (C.gates.getD j.val dGate).a = w ∨ (C.gates.getD j.val dGate).b = w := by
  by_contra hno
  push_neg at hno
  obtain ⟨outJ, hout⟩ := zbs_out_is_gate hm hR
  by_cases hwm : w < m
  · let u : Fin m := ⟨w, hwm⟩
    have hle := C.val_le_except (zbsIn_len m (some u) (some u)) (zbsIn_len m none (some u))
      (fun t => t = w)
      (fun i hi hne h1 => by
        rw [zbsIn_getD] at h1 ⊢
        by_cases him : i < m
        · rw [dif_pos him] at h1
          simp [Fin.ext_iff, u] at h1; exact absurd h1.symm hne
        · rw [dif_neg him, dif_pos hi] at h1 ⊢; exact h1)
      (fun j hj => Or.inr (Or.inr (hno ⟨j, hj⟩)))
      (2 * m + outJ.val) (by omega) (by omega)
    have h1 : C.val (zbsIn m (some u) (some u)) (2 * m + outJ.val) = true := by
      have := hR (some u) (some u); simp [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
    have h2 : C.val (zbsIn m none (some u)) (2 * m + outJ.val) = false := by
      have := hR none (some u); simp [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
    rw [hle h1] at h2; cases h2
  · let v : Fin m := ⟨w - m, by omega⟩
    have hle := C.val_le_except (zbsIn_len m (some v) (some v)) (zbsIn_len m (some v) none)
      (fun t => t = w)
      (fun i hi hne h1 => by
        rw [zbsIn_getD] at h1 ⊢
        by_cases him : i < m
        · rw [dif_pos him] at h1 ⊢; exact h1
        · rw [dif_neg him, dif_pos hi] at h1
          simp [Fin.ext_iff, v] at h1; omega)
      (fun j hj => Or.inr (Or.inr (hno ⟨j, hj⟩)))
      (2 * m + outJ.val) (by omega) (by omega)
    have h1 : C.val (zbsIn m (some v) (some v)) (2 * m + outJ.val) = true := by
      have := hR (some v) (some v); simp [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
    have h2 : C.val (zbsIn m (some v) none) (2 * m + outJ.val) = false := by
      have := hR (some v) none; simp [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
    rw [hle h1] at h2; cases h2

theorem zbs_not_all_s1d {m : ℕ} (hm : 1 ≤ m) {C : BCirc (2 * m)} (hMin : IsMinZBS m C) :
    ¬ (∀ w < 2 * m, IsS1DWire C w) := by
  classical
  intro hAll
  obtain ⟨outJ, hout⟩ := zbs_out_is_gate hm hMin.1
  let ug : ∀ w, w < 2 * m → Fin C.gates.length := fun w hw => Classical.choose (hAll w hw)
  have hug_spec : ∀ w (hw : w < 2 * m),
      let j := ug w hw
      let g := C.gates.getD j.val dGate
      g.isOr = true ∧ (g.a = w ∨ g.b = w) ∧
      ∀ k : Fin C.gates.length, ((C.gates.getD k.val dGate).a = w ∨ (C.gates.getD k.val dGate).b = w) → k = j :=
    fun w hw => Classical.choose_spec (hAll w hw)
  let sib : ∀ w, w < 2 * m → ℕ := fun w hw =>
    let g := C.gates.getD (ug w hw).val dGate
    if g.a = w then g.b else g.a
  have hsib_props : ∀ w (hw : w < 2 * m),
      sib w hw < 2 * m + (ug w hw).val ∧ sib w hw ≠ w ∧
      ∀ x : List Bool, x.length = 2 * m →
        C.val x (2 * m + (ug w hw).val) = (x.getD w false || C.val x (sib w hw)) := by
    intro w hw
    have hsp := hug_spec w hw
    have hwf := C.wf (ug w hw).val (ug w hw).isLt
    dsimp only [sib]
    split_ifs with ha
    · refine ⟨hwf.2.1, ?_, fun x hx => ?_⟩
      · intro h; exact hwf.2.2 (ha.trans h.symm)
      · rw [C.val_gate hx (ug w hw).isLt, evalBGate, hsp.1]
        simp only [↓reduceIte, ha]
        rw [BW_prefix _ _ _ (by omega)]; rfl
    · have hb : (C.gates.getD (ug w hw).val dGate).b = w := hsp.2.1.resolve_left ha
      refine ⟨hwf.1, ha, fun x hx => ?_⟩
      rw [C.val_gate hx (ug w hw).isLt, evalBGate, hsp.1]
      simp only [↓reduceIte, hb]
      rw [Bool.or_comm, BW_prefix _ _ _ (by omega)]; rfl
  have hval_before_ug_x : ∀ (u : Fin m) (z : ℕ), z < 2 * m + (ug u.val (by omega)).val → z ≠ u.val →
      C.val (zbsIn m (some u) none) z = false := by
    intro u z
    induction z using Nat.strong_induction_on with
    | ind z ih =>
      intro hz hne
      by_cases hlt : z < 2 * m
      · rw [C.val_input (zbsIn_len m (some u) none) hlt, zbsIn_getD]
        by_cases hzm : z < m
        · rw [dif_pos hzm]; simp [Fin.ext_iff]; omega
        · rw [dif_neg hzm, dif_pos hlt]; rfl
      · have hj : z - 2 * m < C.gates.length := by omega
        have hju : z - 2 * m < (ug u.val (by omega)).val := by omega
        rw [show z = 2 * m + (z - 2 * m) from by omega, C.val_gate (zbsIn_len m (some u) none) hj, evalBGate]
        have hwf := C.wf (z - 2 * m) hj
        have hna : (C.gates.getD (z - 2 * m) dGate).a ≠ u.val := fun h => by
          have := congrArg Fin.val ((hug_spec u.val (by omega)).2.2 ⟨z - 2 * m, hj⟩ (Or.inl h))
          dsimp only at this; omega
        have hnb : (C.gates.getD (z - 2 * m) dGate).b ≠ u.val := fun h => by
          have := congrArg Fin.val ((hug_spec u.val (by omega)).2.2 ⟨z - 2 * m, hj⟩ (Or.inr h))
          dsimp only at this; omega
        change (if (C.gates.getD (z - 2 * m) dGate).isOr then
          (C.val _ (C.gates.getD (z - 2 * m) dGate).a || C.val _ (C.gates.getD (z - 2 * m) dGate).b)
          else (C.val _ (C.gates.getD (z - 2 * m) dGate).a && C.val _ (C.gates.getD (z - 2 * m) dGate).b)) = false
        rw [ih _ (by omega) (by omega) hna, ih _ (by omega) (by omega) hnb]
        cases (C.gates.getD (z - 2 * m) dGate).isOr <;> rfl
  have hval_before_ug_y : ∀ (v : Fin m) (z : ℕ), z < 2 * m + (ug (m + v.val) (by omega)).val →
      z ≠ m + v.val → C.val (zbsIn m none (some v)) z = false := by
    intro v z
    induction z using Nat.strong_induction_on with
    | ind z ih =>
      intro hz hne
      by_cases hlt : z < 2 * m
      · rw [C.val_input (zbsIn_len m none (some v)) hlt, zbsIn_getD]
        by_cases hzm : z < m
        · rw [dif_pos hzm]; rfl
        · rw [dif_neg hzm, dif_pos hlt]; simp [Fin.ext_iff]; omega
      · have hj : z - 2 * m < C.gates.length := by omega
        have hju : z - 2 * m < (ug (m + v.val) (by omega)).val := by omega
        rw [show z = 2 * m + (z - 2 * m) from by omega, C.val_gate (zbsIn_len m none (some v)) hj, evalBGate]
        have hwf := C.wf (z - 2 * m) hj
        have hna : (C.gates.getD (z - 2 * m) dGate).a ≠ m + v.val := fun h => by
          have := congrArg Fin.val ((hug_spec (m + v.val) (by omega)).2.2 ⟨z - 2 * m, hj⟩ (Or.inl h))
          dsimp only at this; omega
        have hnb : (C.gates.getD (z - 2 * m) dGate).b ≠ m + v.val := fun h => by
          have := congrArg Fin.val ((hug_spec (m + v.val) (by omega)).2.2 ⟨z - 2 * m, hj⟩ (Or.inr h))
          dsimp only at this; omega
        change (if (C.gates.getD (z - 2 * m) dGate).isOr then
          (C.val _ (C.gates.getD (z - 2 * m) dGate).a || C.val _ (C.gates.getD (z - 2 * m) dGate).b)
          else (C.val _ (C.gates.getD (z - 2 * m) dGate).a && C.val _ (C.gates.getD (z - 2 * m) dGate).b)) = false
        rw [ih _ (by omega) (by omega) hna, ih _ (by omega) (by omega) hnb]
        cases (C.gates.getD (z - 2 * m) dGate).isOr <;> rfl
  have hLemAL : ∀ (i : Fin m) (ou : Option (Fin m)) (v : Fin m),
      (match ou with | none => True | some u => u.val < v.val) → v.val ≤ i.val →
      C.val (zbsIn m ou (some v)) (sib i.val (by omega)) = false := by
    intro i ou v hou hvi
    cases hs : C.val (zbsIn m ou (some v)) (sib i.val (by omega))
    · rfl
    · have hug_t : C.val (zbsIn m ou (some v)) (2 * m + (ug i.val (by omega)).val) = true := by
        rw [(hsib_props i.val (by omega)).2.2 _ (zbsIn_len m _ _), hs, Bool.or_true]
      have hle := C.val_le_except (zbsIn_len m (some i) (some v)) (zbsIn_len m ou (some v))
        (fun t => t = i.val)
        (fun idx hidx hne h1 => by
          rw [zbsIn_getD] at h1 ⊢
          by_cases him : idx < m
          · rw [dif_pos him] at h1; simp [Fin.ext_iff] at h1; exact absurd h1.symm hne
          · rw [dif_neg him, dif_pos hidx] at h1 ⊢; exact h1)
        (fun j hj => by
          by_cases hjeq : j = (ug i.val (by omega)).val
          · rw [hjeq]; exact Or.inr (Or.inl hug_t)
          · right; right
            exact ⟨fun h => hjeq (congrArg Fin.val ((hug_spec i.val (by omega)).2.2 ⟨j, hj⟩ (Or.inl h))),
                   fun h => hjeq (congrArg Fin.val ((hug_spec i.val (by omega)).2.2 ⟨j, hj⟩ (Or.inr h)))⟩)
        (2 * m + outJ.val) (by omega) (by omega)
      have h1 : C.val (zbsIn m (some i) (some v)) (2 * m + outJ.val) = true := by
        have := hMin.1 (some i) (some v)
        simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
        simpa [BCirc.val, hvi] using this
      have h2 : C.val (zbsIn m ou (some v)) (2 * m + outJ.val) = false := by
        have := hMin.1 ou (some v)
        simp only [BCirc.eval, evalWVal, hout] at this
        change (BW C.gates (zbsIn m ou (some v))).getD (2 * m + outJ.val) false = false
        rw [this]; cases ou with
        | none => rfl
        | some u => simp only [zbsSpec, decide_eq_false_iff_not]; omega
      rw [hle h1] at h2; cases h2
  have hLemAR : ∀ (j : Fin m) (u : Fin m) (ov : Option (Fin m)),
      j.val ≤ u.val → (match ov with | none => True | some v => u.val < v.val) →
      C.val (zbsIn m (some u) ov) (sib (m + j.val) (by omega)) = false := by
    intro j u ov hju hov
    cases hs : C.val (zbsIn m (some u) ov) (sib (m + j.val) (by omega))
    · rfl
    · have hug_t : C.val (zbsIn m (some u) ov) (2 * m + (ug (m + j.val) (by omega)).val) = true := by
        rw [(hsib_props (m + j.val) (by omega)).2.2 _ (zbsIn_len m _ _), hs, Bool.or_true]
      have hle := C.val_le_except (zbsIn_len m (some u) (some j)) (zbsIn_len m (some u) ov)
        (fun t => t = m + j.val)
        (fun idx hidx hne h1 => by
          rw [zbsIn_getD] at h1 ⊢
          by_cases him : idx < m
          · rw [dif_pos him] at h1 ⊢; exact h1
          · rw [dif_neg him, dif_pos hidx] at h1; simp [Fin.ext_iff] at h1; omega)
        (fun k hk => by
          by_cases hkeq : k = (ug (m + j.val) (by omega)).val
          · rw [hkeq]; exact Or.inr (Or.inl hug_t)
          · right; right
            exact ⟨fun h => hkeq (congrArg Fin.val ((hug_spec (m + j.val) (by omega)).2.2 ⟨k, hk⟩ (Or.inl h))),
                   fun h => hkeq (congrArg Fin.val ((hug_spec (m + j.val) (by omega)).2.2 ⟨k, hk⟩ (Or.inr h)))⟩)
        (2 * m + outJ.val) (by omega) (by omega)
      have h1 : C.val (zbsIn m (some u) (some j)) (2 * m + outJ.val) = true := by
        have := hMin.1 (some u) (some j)
        simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
        simpa [BCirc.val, hju] using this
      have h2 : C.val (zbsIn m (some u) ov) (2 * m + outJ.val) = false := by
        have := hMin.1 (some u) ov
        simp only [BCirc.eval, evalWVal, hout] at this
        change (BW C.gates (zbsIn m (some u) ov)).getD (2 * m + outJ.val) false = false
        rw [this]; cases ov with
        | none => rfl
        | some v => simp only [zbsSpec, decide_eq_false_iff_not]; omega
      rw [hle h1] at h2; cases h2
  have hInv : ∀ w < 2 * m + C.gates.length, ∀ u v : Fin m, v.val ≤ u.val →
      C.val (zbsIn m (some u) (some v)) w = true →
      C.val (zbsIn m (some u) none) w = true ∨ C.val (zbsIn m none (some v)) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw u v hvu h1
      by_cases hlt : w < 2 * m
      · rw [C.val_input (zbsIn_len m _ _) hlt, zbsIn_getD] at h1
        by_cases hwm : w < m
        · rw [dif_pos hwm] at h1
          left; rw [C.val_input (zbsIn_len m _ _) hlt, zbsIn_getD, dif_pos hwm]; exact h1
        · rw [dif_neg hwm, dif_pos hlt] at h1
          right; rw [C.val_input (zbsIn_len m _ _) hlt, zbsIn_getD, dif_neg hwm, dif_pos hlt]; exact h1
      · have hk : w - 2 * m < C.gates.length := by omega
        have hw_eq : w = 2 * m + (w - 2 * m) := by omega
        rw [hw_eq] at h1 ⊢
        have hwf := C.wf (w - 2 * m) hk
        rw [C.val_gate (zbsIn_len m _ _) hk, evalBGate] at h1
        rw [C.val_gate (zbsIn_len m _ _) hk, C.val_gate (zbsIn_len m _ _) hk]
        cases hio : (C.gates.getD (w - 2 * m) dGate).isOr with
        | true =>
          simp only [hio, ↓reduceIte, Bool.or_eq_true] at h1
          simp only [evalBGate, hio, ↓reduceIte, Bool.or_eq_true]
          rcases h1 with ha | hb
          · rcases ih (C.gates.getD (w - 2 * m) dGate).a (by omega) (by omega) u v hvu ha with hax | hay
            · exact Or.inl (Or.inl hax)
            · exact Or.inr (Or.inl hay)
          · rcases ih (C.gates.getD (w - 2 * m) dGate).b (by omega) (by omega) u v hvu hb with hbx | hby
            · exact Or.inl (Or.inr hbx)
            · exact Or.inr (Or.inr hby)
        | false =>
          simp only [hio, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h1
          simp only [evalBGate, hio, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
          have hCross : (ug u.val (by omega)).val < w - 2 * m →
              (ug (m + v.val) (by omega)).val < w - 2 * m → False := by
            intro hug_u_lt hug_v_lt
            have hFindY : ∀ d : ℕ, ∀ u₀ : Fin m, m - 1 - u₀.val = d →
                (ug u₀.val (by omega)).val < w - 2 * m →
                ∃ b' : Fin m, u₀.val < b'.val ∧
                  C.val (zbsIn m none (some b')) (sib u₀.val (by omega)) = true := by
              intro d
              induction d using Nat.strong_induction_on with
              | ind d ihd =>
                intro u₀ hd hug0
                have hsp0 := hsib_props u₀.val (by omega)
                by_cases hs_in : sib u₀.val (by omega) < 2 * m
                · by_cases hs_m : sib u₀.val (by omega) < m
                  · let a' : Fin m := ⟨sib u₀.val (by omega), hs_m⟩
                    have hne_a : a'.val ≠ u₀.val := hsp0.2.1
                    have hug_eq : ug a'.val (by omega) = ug u₀.val (by omega) := by
                      symm
                      apply (hug_spec a'.val (by omega)).2.2 (ug u₀.val (by omega))
                      dsimp only [a', sib]
                      split_ifs
                      · exact Or.inr rfl
                      · exact Or.inl rfl
                    by_cases hlt_a : a'.val < u₀.val
                    · have hf := hLemAL u₀ (some a') u₀ hlt_a le_rfl
                      rw [C.val_input (zbsIn_len m _ _) hs_in, zbsIn_getD, dif_pos hs_m] at hf
                      simp [a'] at hf
                    · have hlt_u : u₀.val < a'.val := by omega
                      have hsib_a : sib a'.val (by omega) = u₀.val := by
                        dsimp only [sib]; rw [hug_eq]
                        have hwf0 := C.wf (ug u₀.val (by omega)).val (ug u₀.val (by omega)).isLt
                        have hspu := (hug_spec u₀.val (by omega)).2.1
                        split_ifs with ha1
                        · have : a'.val = (C.gates.getD (ug u₀.val (by omega)).val dGate).a := ha1.symm
                          dsimp only [a', sib] at this
                          split_ifs at this with ha2
                          · exact absurd this.symm hwf0.2.2
                          · exact hspu.resolve_left ha2
                        · have hb1 : (C.gates.getD (ug u₀.val (by omega)).val dGate).b = a'.val := by
                            dsimp only [a', sib]
                            split_ifs with ha2
                            · rfl
                            · exfalso; apply ha1; dsimp only [a', sib]; rw [if_neg ha2]
                          rcases hspu with ha2 | hb2
                          · exact ha2
                          · exact absurd (hb2.symm.trans hb1) hne_a.symm
                      have hf := hLemAL a' (some u₀) a' hlt_u le_rfl
                      rw [hsib_a, C.val_input (zbsIn_len m _ _) (by omega), zbsIn_getD, dif_pos u₀.isLt] at hf
                      simp at hf
                  · let b' : Fin m := ⟨sib u₀.val (by omega) - m, by omega⟩
                    have hb_true : C.val (zbsIn m none (some b')) (sib u₀.val (by omega)) = true := by
                      rw [C.val_input (zbsIn_len m _ _) hs_in, zbsIn_getD, dif_neg hs_m, dif_pos hs_in]
                      simp [b']
                    have hlt_b : u₀.val < b'.val := by
                      by_contra hle
                      have hf := hLemAL u₀ none b' trivial (by omega)
                      rw [hb_true] at hf; cases hf
                    exact ⟨b', hlt_b, hb_true⟩
                · let j_s : Fin C.gates.length := ⟨sib u₀.val (by omega) - 2 * m, by omega⟩
                  obtain ⟨u', v', hv'u', hs_t⟩ := zbs_nonzero_on_ones hMin j_s
                  have hs_eq : 2 * m + j_s.val = sib u₀.val (by omega) := by dsimp only [j_s]; omega
                  rw [hs_eq] at hs_t
                  rcases ih (sib u₀.val (by omega)) (by omega) (by omega) u' v' hv'u' hs_t with hx' | hy'
                  · have hu'_ne : u'.val ≠ u₀.val := by
                      intro he
                      have hfa := hval_before_ug_x u₀ (sib u₀.val (by omega)) hsp0.1 hsp0.2.1
                      have : u' = u₀ := Fin.ext he
                      rw [this, hfa] at hx'; cases hx'
                    have hu'_gt : u₀.val < u'.val := by
                      by_contra hle
                      have hmo := C.val_mono (zbsIn_len m (some u') none) (zbsIn_len m (some u') (some u₀))
                        (fun idx hidx hi1 => by
                          rw [zbsIn_getD] at hi1 ⊢
                          by_cases him : idx < m
                          · rw [dif_pos him] at hi1 ⊢; exact hi1
                          · rw [dif_neg him, dif_pos hidx] at hi1; simp at hi1)
                        (sib u₀.val (by omega)) (by omega) hx'
                      have hf := hLemAL u₀ (some u') u₀ (by omega) le_rfl
                      rw [hmo] at hf; cases hf
                    have hug'_lt : (ug u'.val (by omega)).val < w - 2 * m := by
                      by_contra hge
                      have hfa := hval_before_ug_x u' (sib u₀.val (by omega)) (by omega) (by omega)
                      rw [hfa] at hx'; cases hx'
                    obtain ⟨b', hgt_b', hb'_t⟩ := ihd (m - 1 - u'.val) (by omega) u' rfl hug'_lt
                    have hug'_t : C.val (zbsIn m none (some b')) (2 * m + (ug u'.val (by omega)).val) = true := by
                      rw [(hsib_props u'.val (by omega)).2.2 _ (zbsIn_len m _ _), hb'_t, Bool.or_true]
                    have htrans := C.val_le_except (zbsIn_len m (some u') none) (zbsIn_len m none (some b'))
                      (fun t => t = u'.val)
                      (fun idx hidx hne hi1 => by
                        rw [zbsIn_getD] at hi1
                        by_cases him : idx < m
                        · rw [dif_pos him] at hi1; simp [Fin.ext_iff] at hi1; exact absurd hi1.symm hne
                        · rw [dif_neg him, dif_pos hidx] at hi1; simp at hi1)
                      (fun j hj => by
                        by_cases hjeq : j = (ug u'.val (by omega)).val
                        · rw [hjeq]; exact Or.inr (Or.inl hug'_t)
                        · right; right
                          exact ⟨fun h => hjeq (congrArg Fin.val ((hug_spec u'.val (by omega)).2.2 ⟨j, hj⟩ (Or.inl h))),
                                 fun h => hjeq (congrArg Fin.val ((hug_spec u'.val (by omega)).2.2 ⟨j, hj⟩ (Or.inr h)))⟩)
                      (sib u₀.val (by omega)) (by omega) (by omega) hx'
                    exact ⟨b', by omega, htrans⟩
                  · have hlt_v' : u₀.val < v'.val := by
                      by_contra hle
                      have hf := hLemAL u₀ none v' trivial (by omega)
                      rw [hy'] at hf; cases hf
                    exact ⟨v', hlt_v', hy'⟩
            have hFindX : ∀ d : ℕ, ∀ v₀ : Fin m, v₀.val = d →
                (ug (m + v₀.val) (by omega)).val < w - 2 * m →
                ∃ a' : Fin m, a'.val < v₀.val ∧
                  C.val (zbsIn m (some a') none) (sib (m + v₀.val) (by omega)) = true := by
              intro d
              induction d using Nat.strong_induction_on with
              | ind d ihd =>
                intro v₀ hd hug0
                have hsp0 := hsib_props (m + v₀.val) (by omega)
                by_cases hs_in : sib (m + v₀.val) (by omega) < 2 * m
                · by_cases hs_m : sib (m + v₀.val) (by omega) < m
                  · let a' : Fin m := ⟨sib (m + v₀.val) (by omega), hs_m⟩
                    have ha_true : C.val (zbsIn m (some a') none) (sib (m + v₀.val) (by omega)) = true := by
                      rw [C.val_input (zbsIn_len m _ _) hs_in, zbsIn_getD, dif_pos hs_m]
                      simp [a']
                    have hlt_a : a'.val < v₀.val := by
                      by_contra hge
                      have hf := hLemAR v₀ a' none (by omega) trivial
                      rw [ha_true] at hf; cases hf
                    exact ⟨a', hlt_a, ha_true⟩
                  · let b' : Fin m := ⟨sib (m + v₀.val) (by omega) - m, by omega⟩
                    have hne_b : m + b'.val ≠ m + v₀.val := by have := hsp0.2.1; dsimp only [b']; omega
                    have hug_eq : ug (m + b'.val) (by omega) = ug (m + v₀.val) (by omega) := by
                      symm
                      apply (hug_spec (m + b'.val) (by omega)).2.2 (ug (m + v₀.val) (by omega))
                      have hmb : m + b'.val = sib (m + v₀.val) (by omega) := by dsimp only [b']; omega
                      rw [hmb]; dsimp only [sib]
                      split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
                    by_cases hgt_b : v₀.val < b'.val
                    · have hf := hLemAR v₀ v₀ (some b') le_rfl hgt_b
                      rw [C.val_input (zbsIn_len m _ _) hs_in, zbsIn_getD, dif_neg hs_m, dif_pos hs_in] at hf
                      simp [b'] at hf
                    · have hlt_v : b'.val < v₀.val := by omega
                      have hsib_b : sib (m + b'.val) (by omega) = m + v₀.val := by
                        dsimp only [sib]; rw [hug_eq]
                        have hwf0 := C.wf (ug (m + v₀.val) (by omega)).val (ug (m + v₀.val) (by omega)).isLt
                        have hspv := (hug_spec (m + v₀.val) (by omega)).2.1
                        have hmb : m + b'.val = sib (m + v₀.val) (by omega) := by dsimp only [b']; omega
                        split_ifs with ha1
                        · have : m + b'.val = (C.gates.getD (ug (m + v₀.val) (by omega)).val dGate).a := ha1.symm
                          rw [hmb] at this; dsimp only [sib] at this
                          split_ifs at this with ha2
                          · exact absurd this.symm hwf0.2.2
                          · exact hspv.resolve_left ha2
                        · have hb1 : (C.gates.getD (ug (m + v₀.val) (by omega)).val dGate).b = m + b'.val := by
                            rw [hmb]; dsimp only [sib]
                            split_ifs with ha2
                            · rfl
                            · exfalso; apply ha1; rw [hmb]; dsimp only [sib]; rw [if_neg ha2]
                          rcases hspv with ha2 | hb2
                          · exact ha2
                          · exact absurd (hb2.symm.trans hb1) hne_b.symm
                      have hf := hLemAR b' b' (some v₀) le_rfl hlt_v
                      rw [hsib_b, C.val_input (zbsIn_len m _ _) (by omega), zbsIn_getD,
                        dif_neg (by omega), dif_pos (by omega)] at hf
                      simp at hf
                · let j_s : Fin C.gates.length := ⟨sib (m + v₀.val) (by omega) - 2 * m, by omega⟩
                  obtain ⟨u', v', hv'u', hs_t⟩ := zbs_nonzero_on_ones hMin j_s
                  have hs_eq : 2 * m + j_s.val = sib (m + v₀.val) (by omega) := by dsimp only [j_s]; omega
                  rw [hs_eq] at hs_t
                  rcases ih (sib (m + v₀.val) (by omega)) (by omega) (by omega) u' v' hv'u' hs_t with hx' | hy'
                  · have hlt_u' : u'.val < v₀.val := by
                      by_contra hge
                      have hf := hLemAR v₀ u' none (by omega) trivial
                      rw [hx'] at hf; cases hf
                    exact ⟨u', hlt_u', hx'⟩
                  · have hv'_ne : v'.val ≠ v₀.val := by
                      intro he
                      have hfb := hval_before_ug_y v₀ (sib (m + v₀.val) (by omega)) hsp0.1 hsp0.2.1
                      have : v' = v₀ := Fin.ext he
                      rw [this, hfb] at hy'; cases hy'
                    have hv'_lt : v'.val < v₀.val := by
                      by_contra hge
                      have hmo := C.val_mono (zbsIn_len m none (some v')) (zbsIn_len m (some v₀) (some v'))
                        (fun idx hidx hi1 => by
                          rw [zbsIn_getD] at hi1 ⊢
                          by_cases him : idx < m
                          · rw [dif_pos him] at hi1; simp at hi1
                          · rw [dif_neg him, dif_pos hidx] at hi1 ⊢; exact hi1)
                        (sib (m + v₀.val) (by omega)) (by omega) hy'
                      have hf := hLemAR v₀ v₀ (some v') le_rfl (by omega)
                      rw [hmo] at hf; cases hf
                    have hug'_lt : (ug (m + v'.val) (by omega)).val < w - 2 * m := by
                      by_contra hge
                      have hfb := hval_before_ug_y v' (sib (m + v₀.val) (by omega)) (by omega) (by omega)
                      rw [hfb] at hy'; cases hy'
                    obtain ⟨a', hlt_a', ha'_t⟩ := ihd v'.val (by omega) v' rfl hug'_lt
                    have hug'_t : C.val (zbsIn m (some a') none) (2 * m + (ug (m + v'.val) (by omega)).val) = true := by
                      rw [(hsib_props (m + v'.val) (by omega)).2.2 _ (zbsIn_len m _ _), ha'_t, Bool.or_true]
                    have htrans := C.val_le_except (zbsIn_len m none (some v')) (zbsIn_len m (some a') none)
                      (fun t => t = m + v'.val)
                      (fun idx hidx hne hi1 => by
                        rw [zbsIn_getD] at hi1
                        by_cases him : idx < m
                        · rw [dif_pos him] at hi1; simp at hi1
                        · rw [dif_neg him, dif_pos hidx] at hi1; simp [Fin.ext_iff] at hi1; omega)
                      (fun j hj => by
                        by_cases hjeq : j = (ug (m + v'.val) (by omega)).val
                        · rw [hjeq]; exact Or.inr (Or.inl hug'_t)
                        · right; right
                          exact ⟨fun h => hjeq (congrArg Fin.val ((hug_spec (m + v'.val) (by omega)).2.2 ⟨j, hj⟩ (Or.inl h))),
                                 fun h => hjeq (congrArg Fin.val ((hug_spec (m + v'.val) (by omega)).2.2 ⟨j, hj⟩ (Or.inr h)))⟩)
                      (sib (m + v₀.val) (by omega)) (by omega) (by omega) hy'
                    exact ⟨a', by omega, htrans⟩
            obtain ⟨b', hlt_b', hb'_t⟩ := hFindY (m - 1 - u.val) u rfl hug_u_lt
            obtain ⟨a', hlt_a', ha'_t⟩ := hFindX v.val v rfl hug_v_lt
            have hgu_t : C.val (zbsIn m (some a') (some b')) (2 * m + (ug u.val (by omega)).val) = true := by
              rw [(hsib_props u.val (by omega)).2.2 _ (zbsIn_len m _ _)]
              have hm1 := C.val_mono (zbsIn_len m none (some b')) (zbsIn_len m (some a') (some b'))
                (fun idx hidx hi1 => by
                  rw [zbsIn_getD] at hi1 ⊢
                  by_cases him : idx < m
                  · rw [dif_pos him] at hi1; simp at hi1
                  · rw [dif_neg him, dif_pos hidx] at hi1 ⊢; exact hi1)
                (sib u.val (by omega))
                (by have := (hsib_props u.val (by omega)).1; have := (ug u.val (by omega)).isLt; omega) hb'_t
              rw [hm1, Bool.or_true]
            have hgv_t : C.val (zbsIn m (some a') (some b')) (2 * m + (ug (m + v.val) (by omega)).val) = true := by
              rw [(hsib_props (m + v.val) (by omega)).2.2 _ (zbsIn_len m _ _)]
              have hm2 := C.val_mono (zbsIn_len m (some a') none) (zbsIn_len m (some a') (some b'))
                (fun idx hidx hi1 => by
                  rw [zbsIn_getD] at hi1 ⊢
                  by_cases him : idx < m
                  · rw [dif_pos him] at hi1 ⊢; exact hi1
                  · rw [dif_neg him, dif_pos hidx] at hi1; simp at hi1)
                (sib (m + v.val) (by omega))
                (by have := (hsib_props (m + v.val) (by omega)).1; have := (ug (m + v.val) (by omega)).isLt; omega) ha'_t
              rw [hm2, Bool.or_true]
            have hfin := C.val_le_except (zbsIn_len m (some u) (some v)) (zbsIn_len m (some a') (some b'))
              (fun t => t = u.val ∨ t = m + v.val)
              (fun idx hidx hE hi1 => by
                rw [zbsIn_getD] at hi1
                by_cases him : idx < m
                · rw [dif_pos him] at hi1; simp [Fin.ext_iff] at hi1; exact absurd (Or.inl hi1.symm) hE
                · rw [dif_neg him, dif_pos hidx] at hi1; simp [Fin.ext_iff] at hi1; exact absurd (Or.inr (by omega)) hE)
              (fun j hj => by
                by_cases hj1 : j = (ug u.val (by omega)).val
                · rw [hj1]; exact Or.inr (Or.inl hgu_t)
                · by_cases hj2 : j = (ug (m + v.val) (by omega)).val
                  · rw [hj2]; exact Or.inr (Or.inl hgv_t)
                  · right; right
                    refine ⟨?_, ?_⟩
                    · rintro (h | h)
                      · exact hj1 (congrArg Fin.val ((hug_spec u.val (by omega)).2.2 ⟨j, hj⟩ (Or.inl h)))
                      · exact hj2 (congrArg Fin.val ((hug_spec (m + v.val) (by omega)).2.2 ⟨j, hj⟩ (Or.inl h)))
                    · rintro (h | h)
                      · exact hj1 (congrArg Fin.val ((hug_spec u.val (by omega)).2.2 ⟨j, hj⟩ (Or.inr h)))
                      · exact hj2 (congrArg Fin.val ((hug_spec (m + v.val) (by omega)).2.2 ⟨j, hj⟩ (Or.inr h))))
              (2 * m + outJ.val) (by omega) (by omega)
            have h1out : C.val (zbsIn m (some u) (some v)) (2 * m + outJ.val) = true := by
              have := hMin.1 (some u) (some v)
              simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
              simpa [BCirc.val, hvu] using this
            have h2out : C.val (zbsIn m (some a') (some b')) (2 * m + outJ.val) = false := by
              have := hMin.1 (some a') (some b')
              simp only [BCirc.eval, evalWVal, hout] at this
              change (BW C.gates (zbsIn m (some a') (some b'))).getD (2 * m + outJ.val) false = false
              rw [this]; simp only [zbsSpec, decide_eq_false_iff_not]; omega
            rw [hfin h1out] at h2out; cases h2out
          rcases ih (C.gates.getD (w - 2 * m) dGate).a (by omega) (by omega) u v hvu h1.1 with hax | hay
          · rcases ih (C.gates.getD (w - 2 * m) dGate).b (by omega) (by omega) u v hvu h1.2 with hbx | hby
            · exact Or.inl ⟨hax, hbx⟩
            · exfalso
              have hga_ne : (C.gates.getD (w - 2 * m) dGate).a ≠ u.val := fun he => by
                have := (hug_spec u.val (by omega)).2.2 ⟨w - 2 * m, hk⟩ (Or.inl he)
                have hO := (hug_spec u.val (by omega)).1
                rw [← this] at hO; rw [hO] at hio; cases hio
              have hgb_ne : (C.gates.getD (w - 2 * m) dGate).b ≠ m + v.val := fun he => by
                have := (hug_spec (m + v.val) (by omega)).2.2 ⟨w - 2 * m, hk⟩ (Or.inr he)
                have hO := (hug_spec (m + v.val) (by omega)).1
                rw [← this] at hO; rw [hO] at hio; cases hio
              exact hCross
                (by by_contra hge; have hfa := hval_before_ug_x u _ (by omega) hga_ne; rw [hfa] at hax; cases hax)
                (by by_contra hge; have hfb := hval_before_ug_y v _ (by omega) hgb_ne; rw [hfb] at hby; cases hby)
          · rcases ih (C.gates.getD (w - 2 * m) dGate).b (by omega) (by omega) u v hvu h1.2 with hbx | hby
            · exfalso
              have hgb_ne : (C.gates.getD (w - 2 * m) dGate).b ≠ u.val := fun he => by
                have := (hug_spec u.val (by omega)).2.2 ⟨w - 2 * m, hk⟩ (Or.inr he)
                have hO := (hug_spec u.val (by omega)).1
                rw [← this] at hO; rw [hO] at hio; cases hio
              have hga_ne : (C.gates.getD (w - 2 * m) dGate).a ≠ m + v.val := fun he => by
                have := (hug_spec (m + v.val) (by omega)).2.2 ⟨w - 2 * m, hk⟩ (Or.inl he)
                have hO := (hug_spec (m + v.val) (by omega)).1
                rw [← this] at hO; rw [hO] at hio; cases hio
              exact hCross
                (by by_contra hge; have hfb := hval_before_ug_x u _ (by omega) hgb_ne; rw [hfb] at hbx; cases hbx)
                (by by_contra hge; have hfa := hval_before_ug_y v _ (by omega) hga_ne; rw [hfa] at hay; cases hay)
            · exact Or.inr ⟨hay, hby⟩
  let z0 : Fin m := ⟨0, by omega⟩
  have h1 : C.val (zbsIn m (some z0) (some z0)) (2 * m + outJ.val) = true := by
    have := hMin.1 (some z0) (some z0)
    simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
    simpa [BCirc.val] using this
  rcases hInv (2 * m + outJ.val) (by omega) z0 z0 le_rfl h1 with hx0 | hy0
  · have := hMin.1 (some z0) none
    simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
    change (BW C.gates (zbsIn m (some z0) none)).getD (2 * m + outJ.val) false = true at hx0
    rw [hx0] at this; cases this
  · have := hMin.1 none (some z0)
    simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this
    change (BW C.gates (zbsIn m none (some z0))).getD (2 * m + outJ.val) false = true at hy0
    rw [hy0] at this; cases this

theorem zbs_not_single_shared_gate {m : ℕ} (hm : 2 ≤ m) {C : BCirc (2 * m)}
    (hR : RepresentsZBS m C) (i : Fin m) (j : Fin C.gates.length) :
    ¬ (∀ k : Fin C.gates.length,
        ((C.gates.getD k.val dGate).a = i.val ∨ (C.gates.getD k.val dGate).b = i.val ∨
         (C.gates.getD k.val dGate).a = m + i.val ∨ (C.gates.getD k.val dGate).b = m + i.val) → k = j) := by
  intro hOnly
  obtain ⟨outJ, hout⟩ := zbs_out_is_gate (by omega : 1 ≤ m) hR
  have hri : (C.gates.getD j.val dGate).a = i.val ∨ (C.gates.getD j.val dGate).b = i.val := by
    obtain ⟨k, hk⟩ := zbs_input_read (by omega : 1 ≤ m) hR i.val (by omega)
    have hkj : k = j := hOnly k (by rcases hk with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)])
    subst hkj; exact hk
  have hrm : (C.gates.getD j.val dGate).a = m + i.val ∨ (C.gates.getD j.val dGate).b = m + i.val := by
    obtain ⟨k, hk⟩ := zbs_input_read (by omega : 1 ≤ m) hR (m + i.val) (by omega)
    have hkj : k = j := hOnly k (by rcases hk with h | h <;> [exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))])
    subst hkj; exact hk
  have hpair : ((C.gates.getD j.val dGate).a = i.val ∧ (C.gates.getD j.val dGate).b = m + i.val) ∨
      ((C.gates.getD j.val dGate).a = m + i.val ∧ (C.gates.getD j.val dGate).b = i.val) := by
    rcases hri with ha | hb <;> rcases hrm with ha' | hb'
    · omega
    · exact Or.inl ⟨ha, hb'⟩
    · exact Or.inr ⟨ha', hb⟩
    · omega
  cases hio : (C.gates.getD j.val dGate).isOr with
  | true =>
    have hj_t : C.val (zbsIn m (some i) none) (2 * m + j.val) = true := by
      rw [C.val_gate (zbsIn_len m _ _) j.isLt, evalBGate, hio]
      simp only [↓reduceIte]
      rcases hpair with ⟨ha, _⟩ | ⟨_, hb⟩
      · rw [ha, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_L]; simp
      · rw [hb, Bool.or_comm, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_L]; simp
    have hle := C.val_le_except (zbsIn_len m (some i) (some i)) (zbsIn_len m (some i) none)
      (fun t => t = m + i.val)
      (fun idx hidx hne hi1 => by
        rw [zbsIn_getD] at hi1 ⊢
        by_cases him : idx < m
        · rw [dif_pos him] at hi1 ⊢; exact hi1
        · rw [dif_neg him, dif_pos hidx] at hi1; simp [Fin.ext_iff] at hi1; omega)
      (fun k hk => by
        by_cases hkj : k = j.val
        · rw [hkj]; exact Or.inr (Or.inl hj_t)
        · right; right
          exact ⟨fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inr (Or.inr (Or.inl h))))),
                 fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inr (Or.inr (Or.inr h)))))⟩)
      (2 * m + outJ.val) (by omega) (by omega)
    have h1 : C.val (zbsIn m (some i) (some i)) (2 * m + outJ.val) = true := by
      have := hR (some i) (some i); simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this; simpa [BCirc.val] using this
    have h2 : C.val (zbsIn m (some i) none) (2 * m + outJ.val) = false := by
      have := hR (some i) none; simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
    rw [hle h1] at h2; cases h2
  | false =>
    by_cases hi0 : 0 < i.val
    · let i' : Fin m := ⟨0, by omega⟩
      have hj_f : C.val (zbsIn m (some i) (some i')) (2 * m + j.val) = false := by
        rw [C.val_gate (zbsIn_len m _ _) j.isLt, evalBGate, hio]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hpair with ⟨_, hb⟩ | ⟨ha, _⟩
        · rw [hb, Bool.and_comm, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_R]
          simp [Fin.ext_iff, i']; omega
        · rw [ha, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_R]
          simp [Fin.ext_iff, i']; omega
      have hle := C.val_le_except (zbsIn_len m (some i) (some i')) (zbsIn_len m none (some i'))
        (fun t => t = i.val)
        (fun idx hidx hne hi1 => by
          rw [zbsIn_getD] at hi1 ⊢
          by_cases him : idx < m
          · rw [dif_pos him] at hi1; simp [Fin.ext_iff] at hi1; exact absurd hi1.symm hne
          · rw [dif_neg him, dif_pos hidx] at hi1 ⊢; exact hi1)
        (fun k hk => by
          by_cases hkj : k = j.val
          · rw [hkj]; exact Or.inl hj_f
          · right; right
            exact ⟨fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inl h))),
                   fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inr (Or.inl h))))⟩)
        (2 * m + outJ.val) (by omega) (by omega)
      have h1 : C.val (zbsIn m (some i) (some i')) (2 * m + outJ.val) = true := by
        have := hR (some i) (some i'); simp only [BCirc.eval, evalWVal, hout, zbsSpec, i'] at this
        simpa [BCirc.val] using this
      have h2 : C.val (zbsIn m none (some i')) (2 * m + outJ.val) = false := by
        have := hR none (some i'); simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
      rw [hle h1] at h2; cases h2
    · let i' : Fin m := ⟨1, by omega⟩
      have hi_eq : i.val = 0 := by omega
      have hj_f : C.val (zbsIn m (some i') (some i)) (2 * m + j.val) = false := by
        rw [C.val_gate (zbsIn_len m _ _) j.isLt, evalBGate, hio]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hpair with ⟨ha, _⟩ | ⟨_, hb⟩
        · rw [ha, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_L]
          simp [Fin.ext_iff, i', hi_eq]
        · rw [hb, Bool.and_comm, BW_prefix _ _ _ (by rw [zbsIn_len]; omega), zbsIn_getD_L]
          simp [Fin.ext_iff, i', hi_eq]
      have hle := C.val_le_except (zbsIn_len m (some i') (some i)) (zbsIn_len m (some i') none)
        (fun t => t = m + i.val)
        (fun idx hidx hne hi1 => by
          rw [zbsIn_getD] at hi1 ⊢
          by_cases him : idx < m
          · rw [dif_pos him] at hi1 ⊢; exact hi1
          · rw [dif_neg him, dif_pos hidx] at hi1; simp [Fin.ext_iff] at hi1; omega)
        (fun k hk => by
          by_cases hkj : k = j.val
          · rw [hkj]; exact Or.inl hj_f
          · right; right
            exact ⟨fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inr (Or.inr (Or.inl h))))),
                   fun h => hkj (congrArg Fin.val (hOnly ⟨k, hk⟩ (Or.inr (Or.inr (Or.inr h)))))⟩)
        (2 * m + outJ.val) (by omega) (by omega)
      have h1 : C.val (zbsIn m (some i') (some i)) (2 * m + outJ.val) = true := by
        have := hR (some i') (some i); simp only [BCirc.eval, evalWVal, hout, zbsSpec, i', hi_eq] at this
        simpa [BCirc.val] using this
      have h2 : C.val (zbsIn m (some i') none) (2 * m + outJ.val) = false := by
        have := hR (some i') none; simp only [BCirc.eval, evalWVal, hout, zbsSpec] at this; exact this
      rw [hle h1] at h2; cases h2

def skipFin {m : ℕ} (i : Fin (m + 1)) (x : Fin m) : Fin (m + 1) :=
  if h : x.val < i.val then ⟨x.val, by omega⟩ else ⟨x.val + 1, by omega⟩

theorem skipFin_ne {m : ℕ} (i : Fin (m + 1)) (x : Fin m) : skipFin i x ≠ i := by
  unfold skipFin; split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem skipFin_inj {m : ℕ} (i : Fin (m + 1)) {x y : Fin m} (h : skipFin i x = skipFin i y) :
    x = y := by
  unfold skipFin at h; split_ifs at h <;> simp [Fin.ext_iff] at h ⊢ <;> omega

theorem skipFin_le_iff {m : ℕ} (i : Fin (m + 1)) (x y : Fin m) :
    (skipFin i x).val ≤ (skipFin i y).val ↔ x.val ≤ y.val := by
  unfold skipFin; split_ifs <;> dsimp <;> omega

theorem skipFin_surj {m : ℕ} (i y : Fin (m + 1)) (h : y ≠ i) :
    ∃ x : Fin m, skipFin i x = y := by
  have hv : y.val ≠ i.val := fun e => h (Fin.ext e)
  by_cases hlt : y.val < i.val
  · refine ⟨⟨y.val, by omega⟩, ?_⟩
    unfold skipFin; rw [dif_pos hlt]
  · refine ⟨⟨y.val - 1, by omega⟩, ?_⟩
    unfold skipFin; dsimp only; rw [dif_neg (by omega)]; ext; dsimp; omega

def unskipWVal {m : ℕ} (i : Fin (m + 1)) (off : ℕ) (t : ℕ) : WVal :=
  if t < i.val then .ref (off + t)
  else if t = i.val then .c0
  else .ref (off + (t - 1))

theorem unskipWVal_lt {m : ℕ} (i : Fin (m + 1)) (off B t : ℕ) (ht : t < m + 1)
    (hB : off + m ≤ B) : wvalLt B (unskipWVal i off t) := by
  unfold unskipWVal
  split_ifs <;> simp only [wvalLt] <;> omega

theorem unskipWVal_self {m : ℕ} (i : Fin (m + 1)) (off : ℕ) :
    unskipWVal i off i.val = .c0 := by
  unfold unskipWVal; simp

theorem eval_unskipWVal_opt {m : ℕ} (i : Fin (m + 1)) (off t : ℕ) (ht : t < m + 1)
    (ox : Option (Fin m)) (x' : List Bool)
    (hx' : ∀ y : Fin m, x'.getD (off + y.val) false = decide (ox = some y)) :
    decide (ox.map (skipFin i) = some ⟨t, ht⟩) = evalWVal (unskipWVal i off t) x' := by
  unfold unskipWVal
  split_ifs with h1 h2
  · simp only [evalWVal, hx' ⟨t, by omega⟩]
    cases ox with
    | none => rfl
    | some y =>
      simp only [Option.map_some, Option.some.injEq, decide_eq_decide]
      constructor
      · intro h; ext; unfold skipFin at h; split_ifs at h <;> simp [Fin.ext_iff] at h <;> omega
      · intro h; have hy : y.val = t := congrArg Fin.val h
        unfold skipFin; rw [dif_pos (by omega)]; ext; exact hy
  · simp only [evalWVal]
    cases ox with
    | none => rfl
    | some y =>
      simp only [Option.map_some, Option.some.injEq, decide_eq_false_iff_not]
      intro h; exact skipFin_ne i y (h.trans (Fin.ext h2))
  · simp only [evalWVal, hx' ⟨t - 1, by omega⟩]
    cases ox with
    | none => rfl
    | some y =>
      simp only [Option.map_some, Option.some.injEq, decide_eq_decide]
      constructor
      · intro h; ext; dsimp only; unfold skipFin at h; split_ifs at h <;> simp [Fin.ext_iff] at h <;> omega
      · intro h; have hy : y.val = t - 1 := congrArg Fin.val h
        unfold skipFin; rw [dif_neg (by omega)]; ext; dsimp; omega

theorem zbs_lb : ∀ m : ℕ, 1 ≤ m → ∀ C : BCirc (2 * m), RepresentsZBS m C →
    3 * m - 2 ≤ C.gates.length := by
  classical
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ C_in hR_in
    by_cases hm0 : m = 0
    · subst hm0; exact zbs_base_one C_in hR_in
    · have hm1 : 1 ≤ m := by omega
      have hEx : ∃ s : ℕ, ∃ C : BCirc (2 * (m + 1)), RepresentsZBS (m + 1) C ∧ C.gates.length = s :=
        ⟨C_in.gates.length, C_in, hR_in, rfl⟩
      have hle_in : Nat.find hEx ≤ C_in.gates.length := Nat.find_min' hEx ⟨C_in, hR_in, rfl⟩
      obtain ⟨C, hRep, hSz⟩ := Nat.find_spec hEx
      have hMin : IsMinZBS (m + 1) C := ⟨hRep, fun D hD => by
        rw [hSz]; exact Nat.find_min' hEx ⟨D, hD, rfl⟩⟩
      suffices hgoal : 3 * (m + 1) - 2 ≤ C.gates.length by omega
      have hNotAll := zbs_not_all_s1d (by omega : 1 ≤ m + 1) hMin
      have hExistsBad : ∃ w < 2 * (m + 1), ¬ IsS1DWire C w := by
        by_contra h; push_neg at h; exact hNotAll h
      obtain ⟨wBad, hwBad, hNotS1D⟩ := hExistsBad
      let i : Fin (m + 1) := if h : wBad < m + 1 then ⟨wBad, h⟩ else ⟨wBad - (m + 1), by omega⟩
      have hwBad_eq : wBad = i.val ∨ wBad = (m + 1) + i.val := by
        dsimp only [i]; split_ifs <;> [exact Or.inl rfl; exact Or.inr (by dsimp; omega)]
      let env₀ : List WVal :=
        List.ofFn (fun u : Fin (m + 1) => unskipWVal i 0 u.val) ++
        List.ofFn (fun v : Fin (m + 1) => unskipWVal i m v.val)
      have hlen0 : env₀.length = 2 * (m + 1) := by simp [env₀]; omega
      have hwf0 : ∀ t < 2 * (m + 1), wvalLt (2 * m) (env₀.getD t .c0) := by
        intro t ht
        unfold env₀
        by_cases htm : t < m + 1
        · rw [getD_app_lt _ _ _ _ (by simp [htm]), getD_ofFn, dif_pos htm]
          exact unskipWVal_lt i 0 (2 * m) t htm (by omega)
        · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
            getD_ofFn, dif_pos (by omega : t - (m + 1) < m + 1)]
          exact unskipWVal_lt i m (2 * m) (t - (m + 1)) (by omega) (by omega)
      have henv_iL : env₀.getD i.val .c0 = .c0 := by
        unfold env₀
        rw [getD_app_lt _ _ _ _ (by simp [i.isLt]), getD_ofFn, dif_pos i.isLt]
        exact unskipWVal_self i 0
      have henv_iR : env₀.getD ((m + 1) + i.val) .c0 = .c0 := by
        unfold env₀
        rw [getD_app_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
          getD_ofFn, dif_pos i.isLt]
        exact unskipWVal_self i m
      let C' : BCirc (2 * m) := mkSubstBCirc C (fun _ => false) env₀ hlen0 hwf0
      have hRep' : RepresentsZBS m C' := by
        intro ou ov
        have heq := mkSubstBCirc_eval_eq C (fun _ => false) env₀ hlen0 hwf0
          (zbsIn (m + 1) (ou.map (skipFin i)) (ov.map (skipFin i))) (zbsIn m ou ov)
          (zbsIn_len (m + 1) _ _) (zbsIn_len m _ _)
          (fun t ht => by
            rw [zbsIn_getD]
            unfold env₀
            by_cases htm : t < m + 1
            · rw [dif_pos htm, getD_app_lt _ _ _ _ (by simp [htm]), getD_ofFn, dif_pos htm]
              exact eval_unskipWVal_opt i 0 t htm ou (zbsIn m ou ov)
                (fun y => by simpa using zbsIn_getD_L m ou ov y)
            · rw [dif_neg htm, dif_pos ht, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
                getD_ofFn, dif_pos (by omega : t - (m + 1) < m + 1)]
              exact eval_unskipWVal_opt i m (t - (m + 1)) (by omega) ov (zbsIn m ou ov)
                (fun y => zbsIn_getD_R m ou ov y))
          (fun _ _ hf => by cases hf)
        change C'.eval (zbsIn m ou ov) = zbsSpec m ou ov
        rw [heq, hRep]
        cases ou <;> cases ov <;> simp only [zbsSpec, Option.map_none, Option.map_some, skipFin_le_iff]
      have hIH : 3 * m - 2 ≤ C'.gates.length := ih hm1 C' hRep'
      set st := substRun (2 * m) (fun _ => false) env₀ C.gates
      have hst_in : ∀ t < 2 * (m + 1), st.env.getD t .c0 = env₀.getD t .c0 := by
        intro t ht
        have htp := (substRun_take (2 * m) (fun _ => false) env₀ C.gates 0).1 t
          (by simp [substRun, hlen0, ht])
        rw [List.take_zero, substRun_nil] at htp
        exact htp
      have hst_iL : st.env.getD i.val .c0 = .c0 := by rw [hst_in i.val (by omega), henv_iL]
      have hst_iR : st.env.getD ((m + 1) + i.val) .c0 = .c0 := by rw [hst_in ((m + 1) + i.val) (by omega), henv_iR]
      have hgate_sp : ∀ j : Fin C.gates.length,
          let g := C.gates.getD j.val dGate
          let stj := substRun (2 * m) (fun _ => false) env₀ (C.gates.take j.val)
          let r := simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (2 * m + stj.acc.length)
          st.env.getD (2 * (m + 1) + j.val) .c0 = r.2 ∧ st.kept.getD j.val true = r.1.isSome := by
        intro j
        exact (substRun_gate_spec (2 * (m + 1)) (2 * m) (fun _ => false) env₀ hlen0 hwf0 C.gates
          j.val j.isLt (C.wf j.val j.isLt).1 (C.wf j.val j.isLt).2.1).2 rfl
      have hkept_of_c0 : ∀ j : Fin C.gates.length,
          (st.env.getD (C.gates.getD j.val dGate).a .c0 = .c0 ∨
           st.env.getD (C.gates.getD j.val dGate).b .c0 = .c0) →
          st.kept.getD j.val true = false := by
        intro j h0
        have hsp := (hgate_sp j).2
        rw [hsp]
        rcases h0 with ha | hb
        · rw [ha, simpBin_none_of_c0_left]; rfl
        · rw [hb, simpBin_none_of_c0_right]; rfl
      let D : Finset (Fin C.gates.length) := Finset.univ.filter (fun j =>
        (C.gates.getD j.val dGate).a = i.val ∨ (C.gates.getD j.val dGate).b = i.val ∨
        (C.gates.getD j.val dGate).a = (m + 1) + i.val ∨ (C.gates.getD j.val dGate).b = (m + 1) + i.val)
      let S₀ : Finset (Fin C.gates.length) := Finset.univ.filter (fun j =>
        st.env.getD (2 * (m + 1) + j.val) .c0 = .c0)
      let S_w : Finset (Fin C.gates.length) := Finset.univ.filter (fun j =>
        st.env.getD (2 * (m + 1) + j.val) .c0 ≠ .c0 ∧ st.kept.getD j.val true = false)
      have hS₀_kept : ∀ j ∈ S₀, st.kept.getD j.val true = false := by
        intro j hj
        have h0 : st.env.getD (2 * (m + 1) + j.val) .c0 = .c0 := (Finset.mem_filter.mp hj).2
        have hsp := hgate_sp j
        dsimp only at hsp
        cases h1 : (simpBin (C.gates.getD j.val dGate).isOr
          (st.env.getD (C.gates.getD j.val dGate).a .c0)
          (st.env.getD (C.gates.getD j.val dGate).b .c0)
          (2 * m + (substRun (2 * m) (fun _ => false) env₀ (C.gates.take j.val)).acc.length)).1 with
        | none => rw [hsp.2, h1]; rfl
        | some g' =>
          have href := simpBin_ref_of_some _ _ _ _ h1
          rw [href] at hsp
          rw [h0] at hsp; cases hsp.1
      have hDisj : Disjoint S₀ S_w := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2
      have hAllFalse : ∀ j ∈ S₀ ∪ S_w, st.kept.getD j.val true = false := by
        intro j hj
        rcases Finset.mem_union.mp hj with h1 | h2
        · exact hS₀_kept j h1
        · exact (Finset.mem_filter.mp h2).2.2
      have hDrop := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 (S₀ ∪ S_w) hAllFalse
      rw [Finset.card_union_of_disjoint hDisj] at hDrop
      have hD_sub : D ⊆ S₀ ∪ S_w := by
        intro j hj
        have hmem := (Finset.mem_filter.mp hj).2
        have hkf : st.kept.getD j.val true = false := hkept_of_c0 j (by
          rcases hmem with h | h | h | h
          · exact Or.inl (by rw [h, hst_iL])
          · exact Or.inr (by rw [h, hst_iL])
          · exact Or.inl (by rw [h, hst_iR])
          · exact Or.inr (by rw [h, hst_iR]))
        by_cases h0 : st.env.getD (2 * (m + 1) + j.val) .c0 = .c0
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, hkf⟩)
      have hD_ge2 : 2 ≤ D.card := by
        obtain ⟨j1, hj1⟩ := zbs_input_read (by omega : 1 ≤ m + 1) hRep i.val (by omega)
        have hj1D : j1 ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by rcases hj1 with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]⟩
        have hnot1 := zbs_not_single_shared_gate (by omega : 2 ≤ m + 1) hRep i j1
        push_neg at hnot1
        obtain ⟨j2, hj2m, hj2ne⟩ := hnot1
        have hj2D : j2 ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2m⟩
        have hpair : ({j1, j2} : Finset (Fin C.gates.length)) ⊆ D := by
          intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hj1D
          · rw [Finset.mem_singleton.mp hx']; exact hj2D
        have hc := Finset.card_le_card hpair
        rw [Finset.card_pair hj2ne.symm] at hc; exact hc
      suffices h3 : 3 ≤ S₀.card + S_w.card by
        change C'.gates.length + (S₀.card + S_w.card) ≤ C.gates.length at hDrop
        omega
      by_cases hD3 : 3 ≤ D.card
      · have hle := Finset.card_le_card hD_sub
        rw [Finset.card_union_of_disjoint hDisj] at hle; omega
      · have hD2 : D.card = 2 := by omega
        have hS₀_ne : S₀.Nonempty := by
          by_contra hEmp
          rw [Finset.not_nonempty_iff_eq_empty] at hEmp
          have hno0 : ∀ j : Fin C.gates.length, st.env.getD (2 * (m + 1) + j.val) .c0 ≠ .c0 := by
            intro j h0
            have : j ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
            rw [hEmp] at this; exact Finset.notMem_empty j this
          obtain ⟨jL, hjL⟩ := zbs_input_read (by omega : 1 ≤ m + 1) hRep i.val (by omega)
          obtain ⟨jR, hjR⟩ := zbs_input_read (by omega : 1 ≤ m + 1) hRep ((m + 1) + i.val) (by omega)
          have hjLD : jL ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by rcases hjL with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]⟩
          have hjRD : jR ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by rcases hjR with h | h <;> [exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]⟩
          have hLR_ne : jL ≠ jR := by
            intro heq; subst heq
            have hboth : st.env.getD (C.gates.getD jL.val dGate).a .c0 = .c0 ∧
                st.env.getD (C.gates.getD jL.val dGate).b .c0 = .c0 := by
              rcases hjL with h1 | h1 <;> rcases hjR with h2 | h2
              · omega
              · exact ⟨by rw [h1, hst_iL], by rw [h2, hst_iR]⟩
              · exact ⟨by rw [h2, hst_iR], by rw [h1, hst_iL]⟩
              · omega
            have hsp := (hgate_sp jL).1
            rw [hboth.1, hboth.2, simpBin_c0_of_both_c0] at hsp
            exact hno0 jL hsp
          have hD_eq : D = {jL, jR} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact hjLD
              · rw [Finset.mem_singleton.mp hx']; exact hjRD
            · rw [hD2, Finset.card_pair hLR_ne]
          have hAllOr : ∀ j ∈ D, (C.gates.getD j.val dGate).isOr = true := by
            intro j hj
            cases hio : (C.gates.getD j.val dGate).isOr
            · exfalso
              have hmem := (Finset.mem_filter.mp hj).2
              have hsp := (hgate_sp j).1
              rw [hio] at hsp
              rcases hmem with h | h | h | h
              · rw [h, hst_iL, simpBin_c0_of_and_left] at hsp; exact hno0 j hsp
              · rw [h, hst_iL, simpBin_c0_of_and_right] at hsp; exact hno0 j hsp
              · rw [h, hst_iR, simpBin_c0_of_and_left] at hsp; exact hno0 j hsp
              · rw [h, hst_iR, simpBin_c0_of_and_right] at hsp; exact hno0 j hsp
            · rfl
          have hNoBoth : ∀ j : Fin C.gates.length,
              ¬ (((C.gates.getD j.val dGate).a = i.val ∨ (C.gates.getD j.val dGate).b = i.val) ∧
                 ((C.gates.getD j.val dGate).a = (m + 1) + i.val ∨ (C.gates.getD j.val dGate).b = (m + 1) + i.val)) := by
            rintro j ⟨h1, h2⟩
            have hboth : st.env.getD (C.gates.getD j.val dGate).a .c0 = .c0 ∧
                st.env.getD (C.gates.getD j.val dGate).b .c0 = .c0 := by
              rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
              · omega
              · exact ⟨by rw [h1, hst_iL], by rw [h2, hst_iR]⟩
              · exact ⟨by rw [h2, hst_iR], by rw [h1, hst_iL]⟩
              · omega
            have hsp := (hgate_sp j).1
            rw [hboth.1, hboth.2, simpBin_c0_of_both_c0] at hsp
            exact hno0 j hsp
          rcases hwBad_eq with hEq | hEq
          · apply hNotS1D; rw [hEq]
            refine ⟨jL, hAllOr jL hjLD, hjL, fun k hk => ?_⟩
            have hkD : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by rcases hk with h | h <;> [exact Or.inl h; exact Or.inr (Or.inl h)]⟩
            rw [hD_eq] at hkD
            rcases Finset.mem_insert.mp hkD with rfl | hk'
            · rfl
            · rw [Finset.mem_singleton.mp hk'] at hk
              exact absurd ⟨hk, hjR⟩ (hNoBoth jR)
          · apply hNotS1D; rw [hEq]
            refine ⟨jR, hAllOr jR hjRD, hjR, fun k hk => ?_⟩
            have hkD : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by rcases hk with h | h <;> [exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]⟩
            rw [hD_eq] at hkD
            rcases Finset.mem_insert.mp hkD with hk' | hk'
            · rw [hk'] at hk
              exact absurd ⟨hjL, hk⟩ (hNoBoth jL)
            · exact Finset.mem_singleton.mp hk'
        let jMax : Fin C.gates.length := S₀.max' hS₀_ne
        have hjMax_mem : jMax ∈ S₀ := Finset.max'_mem S₀ hS₀_ne
        have hjMax_c0 : st.env.getD (2 * (m + 1) + jMax.val) .c0 = .c0 := (Finset.mem_filter.mp hjMax_mem).2
        have hjMax_ne_out : C.out ≠ .ref (2 * (m + 1) + jMax.val) := by
          intro ho
          have h1 := hRep' (some ⟨0, by omega⟩) (some ⟨0, by omega⟩)
          simp only [C', mkSubstBCirc, BCirc.eval, ho, zbsSpec] at h1
          change evalWVal (st.env.getD (2 * (m + 1) + jMax.val) .c0) _ = true at h1
          rw [hjMax_c0] at h1; cases h1
        have hlive := (zbs_live hMin jMax).resolve_left hjMax_ne_out
        obtain ⟨h, hjh_lt, hh_reads⟩ := hlive
        have hh_notS₀ : h ∉ S₀ := by
          intro hh0
          have hle := Finset.le_max' S₀ h hh0
          change h.val ≤ jMax.val at hle; omega
        have hh_kept : st.kept.getD h.val true = false := hkept_of_c0 h (by
          rcases hh_reads with ha | hb
          · exact Or.inl (by rw [ha, hjMax_c0])
          · exact Or.inr (by rw [hb, hjMax_c0]))
        have hh_Sw : h ∈ S_w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h0 => hh_notS₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩), hh_kept⟩
        have hSw_ge1 : 1 ≤ S_w.card := Finset.card_pos.mpr ⟨h, hh_Sw⟩
        by_cases hS₀_2 : 2 ≤ S₀.card
        · omega
        · have hS₀_1 : S₀.card = 1 := by
            have := Finset.card_pos.mpr hS₀_ne; omega
          obtain ⟨x0, hx0⟩ := Finset.card_eq_one.mp hS₀_1
          have hjMax_eq_x0 : jMax = x0 := Finset.mem_singleton.mp (hx0 ▸ hjMax_mem)
          have hS₀_eq : S₀ = {jMax} := by rw [hjMax_eq_x0, hx0]
          have hD_diff : (D.erase jMax).Nonempty := by
            apply Finset.card_pos.mp
            by_cases hmem : jMax ∈ D
            · rw [Finset.card_erase_of_mem hmem, hD2]; omega
            · rw [Finset.erase_eq_of_notMem hmem, hD2]; omega
          obtain ⟨d2, hd2_er⟩ := hD_diff
          have hd2_ne : d2 ≠ jMax := (Finset.mem_erase.mp hd2_er).1
          have hd2_D : d2 ∈ D := (Finset.mem_erase.mp hd2_er).2
          have hd2_notS₀ : d2 ∉ S₀ := by rw [hS₀_eq, Finset.mem_singleton]; exact hd2_ne
          have hd2_Sw : d2 ∈ S_w := by
            rcases Finset.mem_union.mp (hD_sub hd2_D) with h0 | hw
            · exact absurd h0 hd2_notS₀
            · exact hw
          have hh_ne_d2 : h ≠ d2 := by
            intro heq; subst heq
            have hd2m := (Finset.mem_filter.mp hd2_D).2
            have hboth : st.env.getD (C.gates.getD h.val dGate).a .c0 = .c0 ∧
                st.env.getD (C.gates.getD h.val dGate).b .c0 = .c0 := by
              rcases hh_reads with ha | hb
              · rcases hd2m with h1 | h1 | h1 | h1
                · omega
                · exact ⟨by rw [ha, hjMax_c0], by rw [h1, hst_iL]⟩
                · omega
                · exact ⟨by rw [ha, hjMax_c0], by rw [h1, hst_iR]⟩
              · rcases hd2m with h1 | h1 | h1 | h1
                · exact ⟨by rw [h1, hst_iL], by rw [hb, hjMax_c0]⟩
                · omega
                · exact ⟨by rw [h1, hst_iR], by rw [hb, hjMax_c0]⟩
                · omega
            have hsp := (hgate_sp h).1
            rw [hboth.1, hboth.2, simpBin_c0_of_both_c0] at hsp
            exact hh_notS₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsp⟩)
          have hpair_Sw : ({h, d2} : Finset (Fin C.gates.length)) ⊆ S_w := by
            intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hh_Sw
            · rw [Finset.mem_singleton.mp hx']; exact hd2_Sw
          have hSw2 := Finset.card_le_card hpair_Sw
          rw [Finset.card_pair hh_ne_d2] at hSw2
          omega

def RepresentsBip {r c : ℕ} (A : Fin r → Fin c → Bool) (C : BCirc (r + c)) : Prop :=
  ∀ (u : Fin r) (v : Fin c), C.eval (oneEach u v) = A u v

theorem oneEach_len {r c : ℕ} (u : Fin r) (v : Fin c) : (oneEach u v).length = r + c := by
  simp [oneEach]

theorem oneEach_getD {r c : ℕ} (u : Fin r) (v : Fin c) (t : ℕ) :
    (oneEach u v).getD t false =
      if t < r then decide (t = u.val)
      else if t < r + c then decide (t = r + v.val)
      else false := by
  unfold oneEach
  by_cases h1 : t < r
  · rw [if_pos h1, getD_app_lt _ _ _ _ (by simp [h1]), getD_ofFn, dif_pos h1]
    simp [Fin.ext_iff]
  · rw [if_neg h1, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn, getD_ofFn]
    by_cases h2 : t < r + c
    · rw [if_pos h2, dif_pos (by omega : t - r < c)]
      simp only [Fin.ext_iff, decide_eq_decide]; omega
    · rw [if_neg h2, dif_neg (by omega : ¬ t - r < c)]

theorem oneEach_getD_L {r c : ℕ} (u : Fin r) (v : Fin c) (i : Fin r) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  rw [oneEach_getD, if_pos i.isLt]; simp [Fin.ext_iff]

theorem oneEach_getD_R {r c : ℕ} (u : Fin r) (v : Fin c) (j : Fin c) :
    (oneEach u v).getD (r + j.val) false = decide (j = v) := by
  rw [oneEach_getD, if_neg (by omega), if_pos (by omega)]; simp [Fin.ext_iff]

theorem bip_read_L {r c : ℕ} {A : Fin r → Fin c → Bool} {C : BCirc (r + c)}
    (hR : RepresentsBip A C) (u u₀ u' : Fin r) (v v' : Fin c)
    (h1 : A u v = true) (h0 : A u₀ v = false) (hne : u' ≠ u) (h1' : A u' v' = true) :
    ∃ j : Fin C.gates.length,
      (C.gates.getD j.val dGate).a = u.val ∨ (C.gates.getD j.val dGate).b = u.val := by
  by_contra hno; push_neg at hno
  cases ho : C.out with
  | c0 => have := hR u v; simp [BCirc.eval, evalWVal, ho, h1] at this
  | c1 => have := hR u₀ v; simp [BCirc.eval, evalWVal, ho, h0] at this
  | ref w =>
    have hw : w < r + c + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
    have hwu : w ≠ u.val := by
      intro he; subst he
      have := hR u' v'
      simp only [BCirc.eval, evalWVal, ho, h1'] at this
      rw [BW_prefix _ _ _ (by rw [oneEach_len]; omega), oneEach_getD_L] at this
      simp [hne.symm] at this
    have hle := C.val_le_except (oneEach_len u v) (oneEach_len u₀ v) (fun t => t = u.val)
      (fun i hi hne_i hi1 => by
        rw [oneEach_getD] at hi1 ⊢
        by_cases hir : i < r
        · rw [if_pos hir] at hi1; simp at hi1; exact absurd hi1 hne_i
        · rw [if_neg hir, if_pos hi] at hi1 ⊢; exact hi1)
      (fun j hj => Or.inr (Or.inr (hno ⟨j, hj⟩)))
      w hw hwu
    have e1 : C.val (oneEach u v) w = true := by
      have := hR u v; simp only [BCirc.eval, evalWVal, ho, h1] at this; exact this
    have e2 : C.val (oneEach u₀ v) w = false := by
      have := hR u₀ v; simp only [BCirc.eval, evalWVal, ho, h0] at this; exact this
    rw [hle e1] at e2; cases e2

theorem bip_read_R {r c : ℕ} {A : Fin r → Fin c → Bool} {C : BCirc (r + c)}
    (hR : RepresentsBip A C) (u u' : Fin r) (v v₀ v' : Fin c)
    (h1 : A u v = true) (h0 : A u v₀ = false) (hne : v' ≠ v) (h1' : A u' v' = true) :
    ∃ j : Fin C.gates.length,
      (C.gates.getD j.val dGate).a = r + v.val ∨ (C.gates.getD j.val dGate).b = r + v.val := by
  by_contra hno; push_neg at hno
  cases ho : C.out with
  | c0 => have := hR u v; simp [BCirc.eval, evalWVal, ho, h1] at this
  | c1 => have := hR u v₀; simp [BCirc.eval, evalWVal, ho, h0] at this
  | ref w =>
    have hw : w < r + c + C.gates.length := by have := C.out_wf; rw [ho] at this; exact this
    have hwv : w ≠ r + v.val := by
      intro he; subst he
      have := hR u' v'
      simp only [BCirc.eval, evalWVal, ho, h1'] at this
      rw [BW_prefix _ _ _ (by rw [oneEach_len]; omega), oneEach_getD_R] at this
      simp [hne.symm] at this
    have hle := C.val_le_except (oneEach_len u v) (oneEach_len u v₀) (fun t => t = r + v.val)
      (fun i hi hne_i hi1 => by
        rw [oneEach_getD] at hi1 ⊢
        by_cases hir : i < r
        · rw [if_pos hir] at hi1 ⊢; exact hi1
        · rw [if_neg hir, if_pos hi] at hi1; simp at hi1; exact absurd hi1 hne_i)
      (fun j hj => Or.inr (Or.inr (hno ⟨j, hj⟩)))
      w hw hwv
    have e1 : C.val (oneEach u v) w = true := by
      have := hR u v; simp only [BCirc.eval, evalWVal, ho, h1] at this; exact this
    have e2 : C.val (oneEach u v₀) w = false := by
      have := hR u v₀; simp only [BCirc.eval, evalWVal, ho, h0] at this; exact this
    rw [hle e1] at e2; cases e2

theorem staircase_lb_add2 (m : ℕ) (hm : 1 ≤ m) (C_in : BCirc ((m + 2) + (m + 2)))
    (hR_in : RepresentsBip (fun u v : Fin (m + 2) => decide (v.val ≤ u.val)) C_in) :
    3 * m ≤ C_in.gates.length := by
  classical
  let A : Fin (m + 2) → Fin (m + 2) → Bool := fun u v => decide (v.val ≤ u.val)
  have hEx : ∃ s : ℕ, ∃ C : BCirc ((m + 2) + (m + 2)), RepresentsBip A C ∧ C.gates.length = s :=
    ⟨C_in.gates.length, C_in, hR_in, rfl⟩
  have hle_in : Nat.find hEx ≤ C_in.gates.length := Nat.find_min' hEx ⟨C_in, hR_in, rfl⟩
  obtain ⟨C, hRep, hSz⟩ := Nat.find_spec hEx
  have hMin : ∀ D : BCirc ((m + 2) + (m + 2)), RepresentsBip A D → C.gates.length ≤ D.gates.length :=
    fun D hD => by rw [hSz]; exact Nat.find_min' hEx ⟨D, hD, rfl⟩
  suffices hgoal : 3 * m ≤ C.gates.length by omega
  have hLive : ∀ j : Fin C.gates.length, C.out = .ref ((m + 2) + (m + 2) + j.val) ∨
      ∃ q : Fin C.gates.length, j.val < q.val ∧
        ((C.gates.getD q.val dGate).a = (m + 2) + (m + 2) + j.val ∨
         (C.gates.getD q.val dGate).b = (m + 2) + (m + 2) + j.val) := by
    intro j
    by_contra h; push_neg at h
    have hRep' : RepresentsBip A (forceZeroAt C j.val) := fun u v => by
      rw [forceZeroAt_eq_of_dead C j.isLt h.1 (fun q hq hjq => h.2 ⟨q, hq⟩ hjq) (oneEach_len u v)]
      exact hRep u v
    have := hMin _ hRep'
    have := forceZeroAt_size C j.isLt
    omega
  obtain ⟨jX, hjX⟩ := bip_read_L hRep ⟨m + 1, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
    ⟨m + 1, by omega⟩ ⟨0, by omega⟩ (by simp [A]) (by simp [A]) (by simp [Fin.ext_iff]) (by simp [A])
  obtain ⟨jY, hjY⟩ := bip_read_R hRep ⟨0, by omega⟩ ⟨m + 1, by omega⟩
    ⟨0, by omega⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩
    (by simp [A]) (by simp [A]) (by simp [Fin.ext_iff]) (by simp [A])
  dsimp only at hjX hjY
  rw [add_zero] at hjY
  let env₀ : List WVal :=
    List.ofFn (fun u : Fin (m + 2) =>
      if u.val = 0 then .c0 else if u.val = m + 1 then .c0 else .ref (u.val - 1)) ++
    List.ofFn (fun v : Fin (m + 2) =>
      if v.val = 0 then .c0 else if v.val = m + 1 then .c0 else .ref (m + (v.val - 1)))
  have hlen0 : env₀.length = (m + 2) + (m + 2) := by simp [env₀]; omega
  have hwf0 : ∀ t < (m + 2) + (m + 2), wvalLt (2 * m) (env₀.getD t .c0) := by
    intro t ht; unfold env₀
    by_cases htl : t < m + 2
    · rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
      dsimp only; split_ifs <;> simp only [wvalLt] <;> omega
    · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
        getD_ofFn, dif_pos (by omega : t - (m + 2) < m + 2)]
      dsimp only; split_ifs <;> simp only [wvalLt] <;> omega
  let C' : BCirc (2 * m) := mkSubstBCirc C (fun _ => false) env₀ hlen0 hwf0
  let embL : Option (Fin m) → Fin (m + 2) := fun ou =>
    match ou with | none => ⟨0, by omega⟩ | some u => ⟨u.val + 1, by omega⟩
  let embR : Option (Fin m) → Fin (m + 2) := fun ov =>
    match ov with | none => ⟨m + 1, by omega⟩ | some v => ⟨v.val + 1, by omega⟩
  have hRep' : RepresentsZBS m C' := by
    intro ou ov
    cases ou with
    | some u =>
      cases ov with
      | some v =>
        have heq := mkSubstBCirc_eval_eq C (fun _ => false) env₀ hlen0 hwf0
          (oneEach (embL (some u)) (embR (some v))) (zbsIn m (some u) (some v))
          (oneEach_len _ _) (zbsIn_len m _ _)
          (fun t ht => by
            rw [oneEach_getD]
            unfold env₀
            by_cases htl : t < m + 2
            · rw [if_pos htl, getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
              dsimp only [embL]
              split_ifs with h1 h2
              · simp [evalWVal]; omega
              · simp [evalWVal]; omega
              · simp only [evalWVal, zbsIn_getD, dif_pos (by omega : t - 1 < m)]
                simp only [Option.some.injEq, Fin.ext_iff, decide_eq_decide]; omega
            · rw [if_neg htl, if_pos ht, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
                getD_ofFn, dif_pos (by omega : t - (m + 2) < m + 2)]
              dsimp only [embR]
              split_ifs with h1 h2
              · simp [evalWVal]; omega
              · simp [evalWVal]; omega
              · simp only [evalWVal, zbsIn_getD, dif_neg (by omega : ¬ m + (t - (m + 2) - 1) < m),
                  dif_pos (by omega : m + (t - (m + 2) - 1) < 2 * m)]
                simp only [Option.some.injEq, Fin.ext_iff, decide_eq_decide]; omega)
          (fun _ _ hf => by cases hf)
        change C'.eval (zbsIn m (some u) (some v)) = zbsSpec m (some u) (some v)
        rw [heq, hRep]
        simp [A, embL, embR, zbsSpec]
      | none =>
        cases hv : C'.eval (zbsIn m (some u) none)
        · rfl
        · have hmo := mkSubstBCirc_eval_mono C (fun _ => false) env₀ hlen0 hwf0
            (oneEach (embL (some u)) (embR none)) (zbsIn m (some u) none)
            (oneEach_len _ _) (zbsIn_len m _ _)
            (fun t ht ht1 => by
              rw [oneEach_getD]
              unfold env₀ at ht1
              by_cases htl : t < m + 2
              · rw [if_pos htl]
                rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl] at ht1
                dsimp only at ht1
                split_ifs at ht1 with h1 h2
                · cases ht1
                · cases ht1
                · simp only [evalWVal, zbsIn_getD, dif_pos (by omega : t - 1 < m)] at ht1
                  simp [Fin.ext_iff] at ht1; simp [embL]; omega
              · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
                  getD_ofFn, dif_pos (by omega : t - (m + 2) < m + 2)] at ht1
                dsimp only at ht1
                split_ifs at ht1 with h1 h2
                · cases ht1
                · cases ht1
                · simp only [evalWVal, zbsIn_getD, dif_neg (by omega : ¬ m + (t - (m + 2) - 1) < m),
                    dif_pos (by omega : m + (t - (m + 2) - 1) < 2 * m)] at ht1
                  simp at ht1) hv
          rw [hRep] at hmo; simp [A, embL, embR] at hmo; omega
    | none =>
      cases hv : C'.eval (zbsIn m none ov)
      · rfl
      · have hmo := mkSubstBCirc_eval_mono C (fun _ => false) env₀ hlen0 hwf0
          (oneEach (embL none) (embR ov)) (zbsIn m none ov)
          (oneEach_len _ _) (zbsIn_len m _ _)
          (fun t ht ht1 => by
            rw [oneEach_getD]
            unfold env₀ at ht1
            by_cases htl : t < m + 2
            · rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl] at ht1
              dsimp only at ht1
              split_ifs at ht1 with h1 h2
              · cases ht1
              · cases ht1
              · simp only [evalWVal, zbsIn_getD, dif_pos (by omega : t - 1 < m)] at ht1
                simp at ht1
            · rw [if_neg htl, if_pos ht]
              rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
                getD_ofFn, dif_pos (by omega : t - (m + 2) < m + 2)] at ht1
              dsimp only at ht1
              split_ifs at ht1 with h1 h2
              · cases ht1
              · cases ht1
              · simp only [evalWVal, zbsIn_getD, dif_neg (by omega : ¬ m + (t - (m + 2) - 1) < m),
                  dif_pos (by omega : m + (t - (m + 2) - 1) < 2 * m)] at ht1
                cases ov with
                | none => simp at ht1
                | some v =>
                  simp [Fin.ext_iff] at ht1; simp [embR]; omega) hv
        rw [hRep] at hmo
        cases ov with
        | none => simp [A, embL, embR] at hmo
        | some v => simp [A, embL, embR] at hmo
  have hZBS : 3 * m - 2 ≤ C'.gates.length := zbs_lb m hm C' hRep'
  set st := substRun (2 * m) (fun _ => false) env₀ C.gates
  have hst_in : ∀ t < (m + 2) + (m + 2), st.env.getD t .c0 = env₀.getD t .c0 := by
    intro t ht
    have htp := (substRun_take (2 * m) (fun _ => false) env₀ C.gates 0).1 t (by simp [substRun, hlen0, ht])
    rw [List.take_zero, substRun_nil] at htp
    exact htp
  have hst_X : st.env.getD (m + 1) .c0 = .c0 := by
    rw [hst_in (m + 1) (by omega)]; unfold env₀
    rw [getD_app_lt _ _ _ _ (by simp), getD_ofFn, dif_pos (by omega)]; simp
  have hst_Y : st.env.getD (m + 2) .c0 = .c0 := by
    rw [hst_in (m + 2) (by omega)]; unfold env₀
    rw [getD_app_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, getD_ofFn, dif_pos (by omega)]; simp
  have hgate_sp : ∀ j : Fin C.gates.length,
      let g := C.gates.getD j.val dGate
      let stj := substRun (2 * m) (fun _ => false) env₀ (C.gates.take j.val)
      let r := simpBin g.isOr (st.env.getD g.a .c0) (st.env.getD g.b .c0) (2 * m + stj.acc.length)
      st.env.getD ((m + 2) + (m + 2) + j.val) .c0 = r.2 ∧ st.kept.getD j.val true = r.1.isSome := fun j =>
    (substRun_gate_spec ((m + 2) + (m + 2)) (2 * m) (fun _ => false) env₀ hlen0 hwf0 C.gates j.val j.isLt
      (C.wf j.val j.isLt).1 (C.wf j.val j.isLt).2.1).2 rfl
  have hkept_c0 : ∀ j : Fin C.gates.length,
      (st.env.getD (C.gates.getD j.val dGate).a .c0 = .c0 ∨
       st.env.getD (C.gates.getD j.val dGate).b .c0 = .c0) →
      st.kept.getD j.val true = false := by
    intro j h0; rw [(hgate_sp j).2]
    rcases h0 with ha | hb
    · rw [ha, simpBin_none_of_c0_left]; rfl
    · rw [hb, simpBin_none_of_c0_right]; rfl
  have hkX : st.kept.getD jX.val true = false := hkept_c0 jX (by
    rcases hjX with h | h <;> [exact Or.inl (by rw [h, hst_X]); exact Or.inr (by rw [h, hst_X])])
  have hkY : st.kept.getD jY.val true = false := hkept_c0 jY (by
    rcases hjY with h | h <;> [exact Or.inl (by rw [h, hst_Y]); exact Or.inr (by rw [h, hst_Y])])
  by_cases hne : jX ≠ jY
  · have hDrop := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 {jX, jY} (by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hkX
      · rw [Finset.mem_singleton.mp hx']; exact hkY)
    rw [Finset.card_pair hne] at hDrop; change C'.gates.length + 2 ≤ C.gates.length at hDrop; omega
  · push_neg at hne; subst hne
    have hboth : st.env.getD (C.gates.getD jX.val dGate).a .c0 = .c0 ∧
        st.env.getD (C.gates.getD jX.val dGate).b .c0 = .c0 := by
      rcases hjX with h1 | h1 <;> rcases hjY with h2 | h2
      · omega
      · exact ⟨by rw [h1, hst_X], by rw [h2, hst_Y]⟩
      · exact ⟨by rw [h2, hst_Y], by rw [h1, hst_X]⟩
      · omega
    have hX0 : st.env.getD ((m + 2) + (m + 2) + jX.val) .c0 = .c0 := by
      have hsp := (hgate_sp jX).1; rw [hboth.1, hboth.2, simpBin_c0_of_both_c0] at hsp; exact hsp
    have hX_ne_out : C.out ≠ .ref ((m + 2) + (m + 2) + jX.val) := by
      intro ho
      have h1 := hRep' (some ⟨0, by omega⟩) (some ⟨0, by omega⟩)
      simp only [C', mkSubstBCirc, BCirc.eval, ho, zbsSpec] at h1
      change evalWVal (st.env.getD ((m + 2) + (m + 2) + jX.val) .c0) _ = true at h1
      rw [hX0] at h1; cases h1
    obtain ⟨q, hjq_lt, hq_reads⟩ := (hLive jX).resolve_left hX_ne_out
    have hkQ : st.kept.getD q.val true = false := hkept_c0 q (by
      rcases hq_reads with ha | hb <;> [exact Or.inl (by rw [ha, hX0]); exact Or.inr (by rw [hb, hX0])])
    have hq_ne : jX ≠ q := fun he => by rw [he] at hjq_lt; omega
    have hDrop := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 {jX, q} (by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hkX
      · rw [Finset.mem_singleton.mp hx']; exact hkQ)
    rw [Finset.card_pair hq_ne] at hDrop; change C'.gates.length + 2 ≤ C.gates.length at hDrop; omega

theorem staircase_lb (k : ℕ) (hk : 3 ≤ k) (C_in : BCirc (k + k))
    (hR_in : RepresentsBip (fun u v : Fin k => decide (v.val ≤ u.val)) C_in) :
    3 * k - 6 ≤ C_in.gates.length := by
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      have h := staircase_lb_add2 m (by omega) C_in hR_in
      omega

theorem del_row {r c : ℕ} {A : Fin (r + 1) → Fin c → Bool} (C : BCirc (r + 1 + c))
    (hR : RepresentsBip A C) (u : Fin (r + 1)) :
    ∃ C' : BCirc (r + c), RepresentsBip (fun i j => A (skipFin u i) j) C' ∧
      C'.gates.length ≤ C.gates.length ∧
      ((∃ j : Fin C.gates.length, (C.gates.getD j.val dGate).a = u.val ∨
        (C.gates.getD j.val dGate).b = u.val) → C'.gates.length + 1 ≤ C.gates.length) := by
  let env₀ : List WVal :=
    List.ofFn (fun i : Fin (r + 1) => unskipWVal u 0 i.val) ++
    List.ofFn (fun j : Fin c => .ref (r + j.val))
  have hlen0 : env₀.length = r + 1 + c := by simp [env₀]; omega
  have hwf0 : ∀ t < r + 1 + c, wvalLt (r + c) (env₀.getD t .c0) := by
    intro t ht; unfold env₀
    by_cases htl : t < r + 1
    · rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
      exact unskipWVal_lt u 0 (r + c) t htl (by omega)
    · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
        getD_ofFn, dif_pos (by omega : t - (r + 1) < c)]
      simp only [wvalLt]; omega
  let C' : BCirc (r + c) := mkSubstBCirc C (fun _ => false) env₀ hlen0 hwf0
  refine ⟨C', ?_, ?_, ?_⟩
  · intro i j
    have heq := mkSubstBCirc_eval_eq C (fun _ => false) env₀ hlen0 hwf0
      (oneEach (skipFin u i) j) (oneEach i j) (oneEach_len _ _) (oneEach_len _ _)
      (fun t ht => by
        rw [oneEach_getD]
        unfold env₀
        by_cases htl : t < r + 1
        · rw [if_pos htl, getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
          have h := eval_unskipWVal_opt u 0 t htl (some i) (oneEach i j)
            (fun y => by simpa [eq_comm] using oneEach_getD_L i j y)
          simpa [Option.map_some, Fin.ext_iff, eq_comm] using h
        · rw [if_neg htl, if_pos ht, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
            getD_ofFn, dif_pos (by omega : t - (r + 1) < c)]
          simp only [evalWVal, oneEach_getD, if_neg (by omega : ¬ r + (t - (r + 1)) < r),
            if_pos (by omega : r + (t - (r + 1)) < r + c), decide_eq_decide]
          omega)
      (fun _ _ hf => by cases hf)
    change C'.eval (oneEach i j) = A (skipFin u i) j
    rw [heq, hR]
  · have h := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 ∅ (fun _ hx => by cases hx)
    simpa [C'] using h
  · rintro ⟨j, hj⟩
    have hst_u : (substRun (r + c) (fun _ => false) env₀ C.gates).env.getD u.val .c0 = .c0 := by
      have htp := (substRun_take (r + c) (fun _ => false) env₀ C.gates 0).1 u.val
        (by simp [substRun, hlen0]; have := u.isLt; omega)
      simp only [List.take_zero, substRun_nil] at htp
      rw [htp]; unfold env₀
      rw [getD_app_lt _ _ _ _ (by simp [u.isLt]), getD_ofFn, dif_pos u.isLt]
      exact unskipWVal_self u 0
    have hsp := (substRun_gate_spec (r + 1 + c) (r + c) (fun _ => false) env₀ hlen0 hwf0 C.gates
      j.val j.isLt (C.wf j.val j.isLt).1 (C.wf j.val j.isLt).2.1).2 rfl
    have hk : (substRun (r + c) (fun _ => false) env₀ C.gates).kept.getD j.val true = false := by
      rw [hsp.2]
      rcases hj with ha | hb
      · rw [ha, hst_u, simpBin_none_of_c0_left]; rfl
      · rw [hb, hst_u, simpBin_none_of_c0_right]; rfl
    have h := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 {j} (by
      intro x hx; rw [Finset.mem_singleton.mp hx]; exact hk)
    simpa [C'] using h

theorem del_col {r c : ℕ} {A : Fin r → Fin (c + 1) → Bool} (C : BCirc (r + (c + 1)))
    (hR : RepresentsBip A C) (v : Fin (c + 1)) :
    ∃ C' : BCirc (r + c), RepresentsBip (fun i j => A i (skipFin v j)) C' ∧
      C'.gates.length ≤ C.gates.length ∧
      ((∃ j : Fin C.gates.length, (C.gates.getD j.val dGate).a = r + v.val ∨
        (C.gates.getD j.val dGate).b = r + v.val) → C'.gates.length + 1 ≤ C.gates.length) := by
  let env₀ : List WVal :=
    List.ofFn (fun i : Fin r => .ref i.val) ++
    List.ofFn (fun j : Fin (c + 1) => unskipWVal v r j.val)
  have hlen0 : env₀.length = r + (c + 1) := by simp [env₀]
  have hwf0 : ∀ t < r + (c + 1), wvalLt (r + c) (env₀.getD t .c0) := by
    intro t ht; unfold env₀
    by_cases htl : t < r
    · rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
      simp only [wvalLt]; omega
    · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
        getD_ofFn, dif_pos (by omega : t - r < c + 1)]
      exact unskipWVal_lt v r (r + c) (t - r) (by omega) le_rfl
  let C' : BCirc (r + c) := mkSubstBCirc C (fun _ => false) env₀ hlen0 hwf0
  refine ⟨C', ?_, ?_, ?_⟩
  · intro i j
    have heq := mkSubstBCirc_eval_eq C (fun _ => false) env₀ hlen0 hwf0
      (oneEach i (skipFin v j)) (oneEach i j) (oneEach_len _ _) (oneEach_len _ _)
      (fun t ht => by
        rw [oneEach_getD]
        unfold env₀
        by_cases htl : t < r
        · rw [if_pos htl, getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
          simp only [evalWVal, oneEach_getD, if_pos htl]
        · rw [if_neg htl, if_pos ht, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
            getD_ofFn, dif_pos (by omega : t - r < c + 1)]
          have h := eval_unskipWVal_opt v r (t - r) (by omega) (some j) (oneEach i j)
            (fun y => by simpa [eq_comm] using oneEach_getD_R i j y)
          have hsub : decide (t = r + (skipFin v j).val) =
              decide (Option.map (skipFin v) (some j) = some ⟨t - r, by omega⟩) := by
            simp only [Option.map_some, Option.some.injEq, Fin.ext_iff, decide_eq_decide]; omega
          rw [hsub]; exact h)
      (fun _ _ hf => by cases hf)
    change C'.eval (oneEach i j) = A i (skipFin v j)
    rw [heq, hR]
  · have h := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 ∅ (fun _ hx => by cases hx)
    simpa [C'] using h
  · rintro ⟨j, hj⟩
    have hst_v : (substRun (r + c) (fun _ => false) env₀ C.gates).env.getD (r + v.val) .c0 = .c0 := by
      have htp := (substRun_take (r + c) (fun _ => false) env₀ C.gates 0).1 (r + v.val)
        (by simp [substRun, hlen0]; omega)
      simp only [List.take_zero, substRun_nil] at htp
      rw [htp]; unfold env₀
      rw [getD_app_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
        getD_ofFn, dif_pos v.isLt]
      exact unskipWVal_self v r
    have hsp := (substRun_gate_spec (r + (c + 1)) (r + c) (fun _ => false) env₀ hlen0 hwf0 C.gates
      j.val j.isLt (C.wf j.val j.isLt).1 (C.wf j.val j.isLt).2.1).2 rfl
    have hk : (substRun (r + c) (fun _ => false) env₀ C.gates).kept.getD j.val true = false := by
      rw [hsp.2]
      rcases hj with ha | hb
      · rw [ha, hst_v, simpBin_none_of_c0_left]; rfl
      · rw [hb, hst_v, simpBin_none_of_c0_right]; rfl
    have h := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 {j} (by
      intro x hx; rw [Finset.mem_singleton.mp hx]; exact hk)
    simpa [C'] using h

theorem permute_bip {r c : ℕ} {A : Fin r → Fin c → Bool} (C : BCirc (r + c))
    (hR : RepresentsBip A C) (eL : Fin r ≃ Fin r) (eR : Fin c ≃ Fin c) :
    ∃ C' : BCirc (r + c), RepresentsBip (fun i j => A (eL i) (eR j)) C' ∧
      C'.gates.length ≤ C.gates.length := by
  let env₀ : List WVal :=
    List.ofFn (fun u : Fin r => .ref (eL.symm u).val) ++
    List.ofFn (fun v : Fin c => .ref (r + (eR.symm v).val))
  have hlen0 : env₀.length = r + c := by simp [env₀]
  have hwf0 : ∀ t < r + c, wvalLt (r + c) (env₀.getD t .c0) := by
    intro t ht; unfold env₀
    by_cases htl : t < r
    · rw [getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]; simp only [wvalLt]; omega
    · rw [getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
        getD_ofFn, dif_pos (by omega : t - r < c)]; simp only [wvalLt]; omega
  let C' : BCirc (r + c) := mkSubstBCirc C (fun _ => false) env₀ hlen0 hwf0
  refine ⟨C', fun i j => ?_, ?_⟩
  · have heq := mkSubstBCirc_eval_eq C (fun _ => false) env₀ hlen0 hwf0
      (oneEach (eL i) (eR j)) (oneEach i j) (oneEach_len _ _) (oneEach_len _ _)
      (fun t ht => by
        rw [oneEach_getD]
        unfold env₀
        by_cases htl : t < r
        · rw [if_pos htl, getD_app_lt _ _ _ _ (by simp [htl]), getD_ofFn, dif_pos htl]
          simp only [evalWVal, oneEach_getD_L, decide_eq_decide]
          constructor
          · intro h; have : (⟨t, htl⟩ : Fin r) = eL i := Fin.ext h
            rw [this, eL.symm_apply_apply]
          · intro h; have := congrArg eL h; rw [eL.apply_symm_apply] at this
            exact congrArg Fin.val this
        · rw [if_neg htl, if_pos ht, getD_app_right _ _ _ _ (by simp; omega), List.length_ofFn,
            getD_ofFn, dif_pos (by omega : t - r < c)]
          simp only [evalWVal, oneEach_getD_R, decide_eq_decide]
          constructor
          · intro h; have : (⟨t - r, by omega⟩ : Fin c) = eR j := Fin.ext (by dsimp; omega)
            rw [this, eR.symm_apply_apply]
          · intro h; have := congrArg eR h; rw [eR.apply_symm_apply] at this
            have := congrArg Fin.val this; dsimp at this; omega)
      (fun _ _ hf => by cases hf)
    change C'.eval (oneEach i j) = A (eL i) (eR j)
    rw [heq, hR]
  · have h := mkSubstBCirc_size_le C (fun _ => false) env₀ hlen0 hwf0 ∅ (fun _ hx => by cases hx)
    simpa [C'] using h

theorem reduce_rows (k c : ℕ) (hk : 3 ≤ k) :
    ∀ (r : ℕ) (A : Fin r → Fin c → Bool) (C : BCirc (r + c)),
      RepresentsBip A C →
      ∀ (u_rep : Fin k → Fin r) (v_rep : Fin k → Fin c) (U_extra : Finset (Fin r)),
        Function.Injective u_rep →
        (∀ i j : Fin k, A (u_rep i) (v_rep j) = decide (j.val ≤ i.val)) →
        (∀ u ∈ U_extra, ∀ i : Fin k, u ≠ u_rep i) →
        (∀ u ∈ U_extra, ∃ j : Fin k, A u (v_rep j) = true ∧ A (u_rep ⟨0, by omega⟩) (v_rep j) = false) →
        ∃ C' : BCirc (k + c), RepresentsBip (fun i v => A (u_rep i) v) C' ∧
          C'.gates.length + U_extra.card ≤ C.gates.length := by
  classical
  intro r
  induction r with
  | zero =>
    intro A C hR u_rep
    exact Fin.elim0 (u_rep ⟨0, by omega⟩)
  | succ r ih =>
    intro A C hR u_rep v_rep U_extra hu_inj hSt hDisj hWit
    have hk_le : k ≤ r + 1 := by
      have := Fintype.card_le_of_injective u_rep hu_inj
      simp at this; exact this
    by_cases hrk : r + 1 = k
    · subst hrk
      have hsurj : Function.Surjective u_rep := Finite.injective_iff_surjective.mp hu_inj
      have hU_emp : U_extra = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        obtain ⟨i, hi⟩ := hsurj u
        exact hDisj u hu i hi.symm
      rw [hU_emp, Finset.card_empty]
      simp only [add_zero]
      exact permute_bip C hR (Equiv.ofBijective u_rep ⟨hu_inj, hsurj⟩) (Equiv.refl (Fin c))
    · have hex_del : ∃ u_del : Fin (r + 1), u_del ∉ Finset.univ.image u_rep := by
        by_contra hall; push_neg at hall
        have hsub : (Finset.univ : Finset (Fin (r + 1))) ⊆ Finset.univ.image u_rep := fun x _ => hall x
        have hle := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin] at hle
        omega
      obtain ⟨u_del, hu_del_not_im⟩ := hex_del
      have hu_del_not : ∀ i : Fin k, u_rep i ≠ u_del := fun i he =>
        hu_del_not_im (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
      let u_rep' : Fin k → Fin r := fun i => Classical.choose (skipFin_surj u_del (u_rep i) (hu_del_not i))
      have hu_rep'_eq : ∀ i, skipFin u_del (u_rep' i) = u_rep i :=
        fun i => Classical.choose_spec (skipFin_surj u_del (u_rep i) (hu_del_not i))
      have hu_rep'_inj : Function.Injective u_rep' := by
        intro i j h
        exact hu_inj (by rw [← hu_rep'_eq i, ← hu_rep'_eq j, h])
      let U_extra' : Finset (Fin r) := Finset.univ.filter (fun u => skipFin u_del u ∈ U_extra)
      have hU'_card : U_extra'.card = (U_extra.erase u_del).card := by
        have hmap : U_extra'.map ⟨skipFin u_del, fun _ _ h => skipFin_inj u_del h⟩ = U_extra.erase u_del := by
          ext y
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk, Finset.mem_erase, U_extra']
          constructor
          · rintro ⟨x, hx, rfl⟩; exact ⟨skipFin_ne u_del x, hx⟩
          · rintro ⟨hne, hy⟩
            obtain ⟨x, rfl⟩ := skipFin_surj u_del y hne
            exact ⟨x, hy, rfl⟩
        rw [← hmap, Finset.card_map]
      obtain ⟨C1, hR1, hsz0, hsz1⟩ := del_row C hR u_del
      obtain ⟨C', hR', hsz_ih⟩ := ih (fun i j => A (skipFin u_del i) j) C1 hR1 u_rep' v_rep U_extra'
        hu_rep'_inj
        (fun i j => by rw [hu_rep'_eq i]; exact hSt i j)
        (fun u hu i he => hDisj (skipFin u_del u) (Finset.mem_filter.mp hu).2 i (by rw [← hu_rep'_eq i, he]))
        (fun u hu => by
          obtain ⟨j, hj1, hj0⟩ := hWit (skipFin u_del u) (Finset.mem_filter.mp hu).2
          exact ⟨j, hj1, by rw [hu_rep'_eq]; exact hj0⟩)
      have hR'_eq : RepresentsBip (fun i v => A (u_rep i) v) C' := by
        intro i v; rw [hR' i v]; dsimp only; rw [hu_rep'_eq i]
      refine ⟨C', hR'_eq, ?_⟩
      by_cases hmem : u_del ∈ U_extra
      · obtain ⟨j, hj1, hj0⟩ := hWit u_del hmem
        have hread := bip_read_L hR u_del (u_rep ⟨0, by omega⟩) (u_rep ⟨0, by omega⟩)
          (v_rep j) (v_rep ⟨0, by omega⟩) hj1 hj0 (hu_del_not ⟨0, by omega⟩)
          (by rw [hSt]; simp)
        have h1 := hsz1 hread
        have hcard : U_extra'.card + 1 = U_extra.card := by
          rw [hU'_card, Finset.card_erase_add_one hmem]
        omega
      · have hcard : U_extra'.card = U_extra.card := by
          rw [hU'_card, Finset.erase_eq_of_notMem hmem]
        omega

theorem reduce_cols (k : ℕ) (hk : 3 ≤ k) :
    ∀ (c : ℕ) (A : Fin k → Fin c → Bool) (C : BCirc (k + c)),
      RepresentsBip A C →
      ∀ (v_rep : Fin k → Fin c) (V_extra : Finset (Fin c)),
        Function.Injective v_rep →
        (∀ i j : Fin k, A i (v_rep j) = decide (j.val ≤ i.val)) →
        (∀ v ∈ V_extra, ∀ j : Fin k, v ≠ v_rep j) →
        (∀ v ∈ V_extra, ∃ i : Fin k, A i v = true ∧ A i (v_rep ⟨k - 1, by omega⟩) = false) →
        ∃ C' : BCirc (k + k), RepresentsBip (fun i j => decide (j.val ≤ i.val)) C' ∧
          C'.gates.length + V_extra.card ≤ C.gates.length := by
  classical
  intro c
  induction c with
  | zero =>
    intro A C hR v_rep
    exact Fin.elim0 (v_rep ⟨0, by omega⟩)
  | succ c ih =>
    intro A C hR v_rep V_extra hv_inj hSt hDisj hWit
    have hk_le : k ≤ c + 1 := by
      have := Fintype.card_le_of_injective v_rep hv_inj
      simp at this; exact this
    by_cases hck : c + 1 = k
    · subst hck
      have hsurj : Function.Surjective v_rep := Finite.injective_iff_surjective.mp hv_inj
      have hV_emp : V_extra = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨j, hj⟩ := hsurj v
        exact hDisj v hv j hj.symm
      rw [hV_emp, Finset.card_empty]
      simp only [add_zero]
      obtain ⟨C', hR', hsz⟩ := permute_bip C hR (Equiv.refl (Fin (c + 1)))
        (Equiv.ofBijective v_rep ⟨hv_inj, hsurj⟩)
      refine ⟨C', fun i j => ?_, hsz⟩
      rw [hR' i j]; exact hSt i j
    · have hex_del : ∃ v_del : Fin (c + 1), v_del ∉ Finset.univ.image v_rep := by
        by_contra hall; push_neg at hall
        have hsub : (Finset.univ : Finset (Fin (c + 1))) ⊆ Finset.univ.image v_rep := fun x _ => hall x
        have hle := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ hv_inj, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin] at hle
        omega
      obtain ⟨v_del, hv_del_not_im⟩ := hex_del
      have hv_del_not : ∀ j : Fin k, v_rep j ≠ v_del := fun j he =>
        hv_del_not_im (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he⟩)
      let v_rep' : Fin k → Fin c := fun j => Classical.choose (skipFin_surj v_del (v_rep j) (hv_del_not j))
      have hv_rep'_eq : ∀ j, skipFin v_del (v_rep' j) = v_rep j :=
        fun j => Classical.choose_spec (skipFin_surj v_del (v_rep j) (hv_del_not j))
      have hv_rep'_inj : Function.Injective v_rep' := by
        intro i j h
        exact hv_inj (by rw [← hv_rep'_eq i, ← hv_rep'_eq j, h])
      let V_extra' : Finset (Fin c) := Finset.univ.filter (fun v => skipFin v_del v ∈ V_extra)
      have hV'_card : V_extra'.card = (V_extra.erase v_del).card := by
        have hmap : V_extra'.map ⟨skipFin v_del, fun _ _ h => skipFin_inj v_del h⟩ = V_extra.erase v_del := by
          ext y
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk, Finset.mem_erase, V_extra']
          constructor
          · rintro ⟨x, hx, rfl⟩; exact ⟨skipFin_ne v_del x, hx⟩
          · rintro ⟨hne, hy⟩
            obtain ⟨x, rfl⟩ := skipFin_surj v_del y hne
            exact ⟨x, hy, rfl⟩
        rw [← hmap, Finset.card_map]
      obtain ⟨C1, hR1, hsz0, hsz1⟩ := del_col C hR v_del
      obtain ⟨C', hR', hsz_ih⟩ := ih (fun i j => A i (skipFin v_del j)) C1 hR1 v_rep' V_extra'
        hv_rep'_inj
        (fun i j => by rw [hv_rep'_eq j]; exact hSt i j)
        (fun v hv j he => hDisj (skipFin v_del v) (Finset.mem_filter.mp hv).2 j (by rw [← hv_rep'_eq j, he]))
        (fun v hv => by
          obtain ⟨i, hi1, hi0⟩ := hWit (skipFin v_del v) (Finset.mem_filter.mp hv).2
          exact ⟨i, hi1, by rw [hv_rep'_eq]; exact hi0⟩)
      refine ⟨C', hR', ?_⟩
      by_cases hmem : v_del ∈ V_extra
      · obtain ⟨i, hi1, hi0⟩ := hWit v_del hmem
        have hread := bip_read_R hR i ⟨k - 1, by omega⟩ v_del (v_rep ⟨k - 1, by omega⟩)
          (v_rep ⟨k - 1, by omega⟩) hi1 hi0 (hv_del_not ⟨k - 1, by omega⟩)
          (by rw [hSt]; simp)
        have h1 := hsz1 hread
        have hcard : V_extra'.card + 1 = V_extra.card := by
          rw [hV'_card, Finset.card_erase_add_one hmem]
        omega
      · have hcard : V_extra'.card = V_extra.card := by
          rw [hV'_card, Finset.erase_eq_of_notMem hmem]
        omega

theorem sortFinset : ∀ (k : ℕ) (S : Finset ℕ), S.card = k →
    ∃ f : Fin k → ℕ, (∀ i j : Fin k, i.val < j.val → f i < f j) ∧
      (∀ i : Fin k, f i ∈ S) ∧ (∀ x ∈ S, ∃ i : Fin k, f i = x) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun x hx => ?_⟩
    rw [Finset.card_eq_zero.mp hS] at hx; cases hx
  | succ k ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let m₀ := S.min' hne
    have hm₀_mem : m₀ ∈ S := Finset.min'_mem S hne
    let S' := S.erase m₀
    have hS'_card : S'.card = k := by
      dsimp only [S']; have := Finset.card_erase_add_one hm₀_mem; omega
    obtain ⟨f', hf'_inc, hf'_mem, hf'_surj⟩ := ih S' hS'_card
    have hm₀_lt : ∀ i : Fin k, m₀ < f' i := by
      intro i
      have hmem := Finset.mem_erase.mp (hf'_mem i)
      have hle := Finset.min'_le S (f' i) hmem.2
      exact lt_of_le_of_ne hle (Ne.symm hmem.1)
    let f : Fin (k + 1) → ℕ := fun i =>
      if h : i.val = 0 then m₀ else f' ⟨i.val - 1, by omega⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · intro i j hij
      dsimp only [f]
      split_ifs with hi hj
      · omega
      · exact hm₀_lt ⟨j.val - 1, by omega⟩
      · omega
      · exact hf'_inc ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ (by dsimp; omega)
    · intro i
      dsimp only [f]
      split_ifs with hi
      · exact hm₀_mem
      · exact Finset.mem_of_mem_erase (hf'_mem ⟨i.val - 1, by omega⟩)
    · intro x hx
      by_cases hxm : x = m₀
      · exact ⟨⟨0, by omega⟩, by simp [f, hxm]⟩
      · obtain ⟨i', hi'⟩ := hf'_surj x (Finset.mem_erase.mpr ⟨hxm, hx⟩)
        exact ⟨⟨i'.val + 1, by omega⟩, by simp [f, hi']⟩

theorem card_filter_comp {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun x => ¬ p x)).card = Fintype.card α := by
  have hdisj : Disjoint (Finset.univ.filter p) (Finset.univ.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hun : Finset.univ.filter p ∪ Finset.univ.filter (fun x => ¬ p x) = Finset.univ := by
    ext x; simp [em]
  rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ]

theorem main_aux :
    ∀ n k a b : ℕ, 4 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) →
      (Finset.univ.image t).card = k →
      (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a →
      (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
        (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
        (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b →
      ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s →
      2 * n + k - 4 - a - b ≤ s := by
  classical
  intro n k a b hk4 t ht_rng ht_max hk_card ha_card hb_card s hRep
  have hk : 3 ≤ k := by omega
  obtain ⟨C0, hM0, hsz0, hRep0⟩ := hRep
  obtain ⟨C, hC_sz, hC_eval⟩ := normCircuit_exists (n + n) C0 hM0
  have hC_rep : RepresentsBip (fun u v : Fin n => decide ((v : ℕ) < t u)) C := by
    intro u v
    rw [hC_eval (oneEach u v) (oneEach_len u v)]
    exact hRep0 u v
  obtain ⟨tv, htv_inc, htv_mem, htv_surj⟩ := sortFinset k (Finset.univ.image t) hk_card
  have htv_ge1 : ∀ i : Fin k, 1 ≤ tv i := by
    intro i
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (htv_mem i)
    rw [← hu]; exact (ht_rng u).1
  have htv_le_n : ∀ i : Fin k, tv i ≤ n := by
    intro i
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (htv_mem i)
    rw [← hu]; exact (ht_rng u).2
  have htv_mono : ∀ i j : Fin k, i.val ≤ j.val → tv i ≤ tv j := by
    intro i j hij
    by_cases he : i.val = j.val
    · rw [Fin.ext he]
    · exact Nat.le_of_lt (htv_inc i j (by omega))
  have htv_top : tv ⟨k - 1, by omega⟩ = n := by
    obtain ⟨u_max, hu_max⟩ := ht_max
    obtain ⟨i_max, hi_max⟩ := htv_surj n (Finset.mem_image.mpr ⟨u_max, Finset.mem_univ _, hu_max⟩)
    have hle1 := htv_le_n ⟨k - 1, by omega⟩
    have hle2 : tv i_max ≤ tv ⟨k - 1, by omega⟩ := htv_mono i_max ⟨k - 1, by omega⟩ (by dsimp; omega)
    omega
  have htv_lt_n : ∀ i : Fin k, i.val < k - 1 → tv i < n := by
    intro i hi
    rw [← htv_top]; exact htv_inc i ⟨k - 1, by omega⟩ hi
  have hn_ge_k : k ≤ n := by
    have := Finset.card_image_le (f := t) (s := (Finset.univ : Finset (Fin n)))
    rw [hk_card, Finset.card_univ, Fintype.card_fin] at this; exact this
  let u_rep : Fin k → Fin n := fun i =>
    Classical.choose (Finset.mem_image.mp (htv_mem i))
  have hu_rep_t : ∀ i : Fin k, t (u_rep i) = tv i :=
    fun i => (Classical.choose_spec (Finset.mem_image.mp (htv_mem i))).2
  have hu_inj : Function.Injective u_rep := by
    intro i j hij
    have hte : tv i = tv j := by rw [← hu_rep_t i, ← hu_rep_t j, hij]
    by_contra hne
    have : i.val < j.val ∨ j.val < i.val := by
      have : i.val ≠ j.val := fun e => hne (Fin.ext e); omega
    rcases this with h | h
    · exact absurd hte (Nat.ne_of_lt (htv_inc i j h))
    · exact absurd hte.symm (Nat.ne_of_lt (htv_inc j i h))
  let v_rep : Fin k → Fin n := fun j =>
    if h : j.val = 0 then ⟨0, by omega⟩
    else ⟨tv ⟨j.val - 1, by omega⟩, htv_lt_n ⟨j.val - 1, by omega⟩ (by dsimp; omega)⟩
  have hv_inj : Function.Injective v_rep := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp only [v_rep] at hv
    split_ifs at hv with hi hj
    · exact Fin.ext (by omega)
    · dsimp only at hv; have := htv_ge1 ⟨j.val - 1, by omega⟩; omega
    · dsimp only at hv; have := htv_ge1 ⟨i.val - 1, by omega⟩; omega
    · by_contra hne
      have hne' : i.val - 1 ≠ j.val - 1 := by
        have : i.val ≠ j.val := fun e => hne (Fin.ext e); omega
      by_cases hlt : i.val - 1 < j.val - 1
      · exact absurd hv (Nat.ne_of_lt (htv_inc ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ hlt))
      · exact absurd hv.symm (Nat.ne_of_lt (htv_inc ⟨j.val - 1, by omega⟩ ⟨i.val - 1, by omega⟩ (by dsimp; omega)))
  have hSt : ∀ i j : Fin k, decide ((v_rep j).val < t (u_rep i)) = decide (j.val ≤ i.val) := by
    intro i j
    rw [hu_rep_t i]
    simp only [decide_eq_decide]
    dsimp only [v_rep]
    split_ifs with hj
    · have h1 := htv_ge1 i; simp [hj]; omega
    · dsimp only
      constructor
      · intro hlt
        by_contra hgt
        have hle := htv_mono i ⟨j.val - 1, by omega⟩ (by dsimp; omega); omega
      · intro hle
        exact htv_inc ⟨j.val - 1, by omega⟩ i (by dsimp; omega)
  have hLeastRow : Finset.univ.filter (fun u : Fin n => ∀ u', t u ≤ t u') =
      Finset.univ.filter (fun u : Fin n => t u = tv ⟨0, by omega⟩) := by
    ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      have h1 := hall (u_rep ⟨0, by omega⟩)
      rw [hu_rep_t] at h1
      obtain ⟨iu, hiu⟩ := htv_surj (t u) (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
      have h2 := htv_mono ⟨0, by omega⟩ iu (Nat.zero_le _)
      omega
    · intro heq u'
      rw [heq]
      obtain ⟨iu', hiu'⟩ := htv_surj (t u') (Finset.mem_image.mpr ⟨u', Finset.mem_univ _, rfl⟩)
      rw [← hiu']; exact htv_mono ⟨0, by omega⟩ iu' (Nat.zero_le _)
  have hLeastCol : Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
        (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
        (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card) =
      Finset.univ.filter (fun v : Fin n => tv ⟨k - 2, by omega⟩ ≤ v.val) := by
    let vTop : Fin n := ⟨tv ⟨k - 2, by omega⟩, htv_lt_n ⟨k - 2, by omega⟩ (by dsimp; omega)⟩
    have hdeg_top : ∀ v : Fin n, tv ⟨k - 2, by omega⟩ ≤ v.val →
        Finset.univ.filter (fun u => v.val < t u) = Finset.univ.filter (fun u => t u = n) := by
      intro v hv; ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hlt
        obtain ⟨iu, hiu⟩ := htv_surj (t u) (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
        have : k - 2 < iu.val := by
          by_contra hle
          have := htv_mono iu ⟨k - 2, by omega⟩ (by dsimp; omega); omega
        have hiueq : iu = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [← hiu, hiueq, htv_top]
      · intro heq; rw [heq]; exact v.isLt
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      by_contra hlt
      have hle_deg := hall vTop
      have hsub : Finset.univ.filter (fun u => vTop.val < t u) ⊆ Finset.univ.filter (fun u => v.val < t u) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        dsimp only [vTop] at hu; omega
      have hstrict : (Finset.univ.filter (fun u => vTop.val < t u)).card <
          (Finset.univ.filter (fun u => v.val < t u)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsub, fun heq => ?_⟩
        have hmem : u_rep ⟨k - 2, by omega⟩ ∈ Finset.univ.filter (fun u => v.val < t u) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hu_rep_t]; omega
        rw [← heq] at hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hu_rep_t, vTop] at hmem; omega
      omega
    · intro hv v'
      rw [hdeg_top v hv]
      apply Finset.card_le_card
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [hu]; exact v'.isLt
  let U_act := Finset.univ.filter (fun u : Fin n => t u ≠ tv ⟨0, by omega⟩)
  let U_extra := U_act \ Finset.univ.image u_rep
  let V_act := Finset.univ.filter (fun v : Fin n => v.val < tv ⟨k - 2, by omega⟩)
  let V_extra := V_act \ Finset.univ.image v_rep
  have hU_act_card : U_act.card = n - a := by
    have hcomp := card_filter_comp (fun u : Fin n => t u = tv ⟨0, by omega⟩)
    rw [← hLeastRow, ha_card, Fintype.card_fin] at hcomp
    have hneg : Finset.univ.filter (fun u : Fin n => ¬ t u = tv ⟨0, by omega⟩) = U_act := rfl
    rw [hneg] at hcomp; omega
  have hU_inter_card : (U_act ∩ Finset.univ.image u_rep).card = k - 1 := by
    have heq : U_act ∩ Finset.univ.image u_rep =
        (Finset.univ.erase (⟨0, by omega⟩ : Fin k)).image u_rep := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
        Finset.mem_image, Finset.mem_erase, U_act]
      constructor
      · rintro ⟨hne, i, rfl⟩
        refine ⟨i, fun hi0 => hne (by rw [hi0, hu_rep_t]), rfl⟩
      · rintro ⟨i, hi0, rfl⟩
        refine ⟨?_, i, rfl⟩
        rw [hu_rep_t]
        exact Nat.ne_of_gt (htv_inc ⟨0, by omega⟩ i (by dsimp; have : i.val ≠ 0 := fun e => hi0 (Fin.ext e); omega))
    rw [heq, Finset.card_image_of_injective _ hu_inj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hU_extra_card : U_extra.card = n - a - (k - 1) := by
    have hs := Finset.card_sdiff_add_card_inter U_act (Finset.univ.image u_rep)
    rw [hU_act_card, hU_inter_card] at hs
    change U_extra.card + (k - 1) = n - a at hs; omega
  have hV_act_card : V_act.card = n - b := by
    have hcomp := card_filter_comp (fun v : Fin n => tv ⟨k - 2, by omega⟩ ≤ v.val)
    rw [← hLeastCol, hb_card, Fintype.card_fin] at hcomp
    have hneg : Finset.univ.filter (fun v : Fin n => ¬ tv ⟨k - 2, by omega⟩ ≤ v.val) = V_act := by
      ext v; simp [V_act]
    rw [hneg] at hcomp; omega
  have hV_inter_card : (V_act ∩ Finset.univ.image v_rep).card = k - 1 := by
    have heq : V_act ∩ Finset.univ.image v_rep =
        (Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k)).image v_rep := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
        Finset.mem_image, Finset.mem_erase, V_act]
      constructor
      · rintro ⟨hlt, j, rfl⟩
        refine ⟨j, fun hjk => ?_, rfl⟩
        rw [hjk] at hlt; dsimp only [v_rep] at hlt
        rw [dif_neg (by omega : k - 1 ≠ 0)] at hlt; dsimp only at hlt
        have heq_idx : (⟨k - 1 - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [heq_idx] at hlt; omega
      · rintro ⟨j, hjk, rfl⟩
        refine ⟨?_, j, rfl⟩
        dsimp only [v_rep]
        split_ifs with hj0
        · exact lt_of_lt_of_le (by omega : 0 < 1) (htv_ge1 _)
        · have hjlt : j.val - 1 < k - 2 := by
            have : j.val ≠ k - 1 := fun e => hjk (Fin.ext e); omega
          exact htv_inc ⟨j.val - 1, by omega⟩ ⟨k - 2, by omega⟩ (by dsimp; exact hjlt)
    rw [heq, Finset.card_image_of_injective _ hv_inj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hV_extra_card : V_extra.card = n - b - (k - 1) := by
    have hs := Finset.card_sdiff_add_card_inter V_act (Finset.univ.image v_rep)
    rw [hV_act_card, hV_inter_card] at hs
    change V_extra.card + (k - 1) = n - b at hs; omega
  have ha_ub : a + (k - 1) ≤ n := by
    have := Finset.card_le_card (Finset.inter_subset_left : U_act ∩ Finset.univ.image u_rep ⊆ U_act)
    rw [hU_inter_card, hU_act_card] at this
    have ha_le_n : a ≤ n := by
      rw [← ha_card]
      calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
    omega
  have hb_ub : b + (k - 1) ≤ n := by
    have := Finset.card_le_card (Finset.inter_subset_left : V_act ∩ Finset.univ.image v_rep ⊆ V_act)
    rw [hV_inter_card, hV_act_card] at this
    have hb_le_n : b ≤ n := by
      rw [← hb_card]
      calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
    omega
  obtain ⟨C1, hC1_rep, hC1_sz⟩ := reduce_rows k n hk n
    (fun u v : Fin n => decide ((v : ℕ) < t u)) C hC_rep u_rep v_rep U_extra hu_inj hSt
    (fun u hu i he => (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩))
    (fun u hu => by
      have hne0 : t u ≠ tv ⟨0, by omega⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
      obtain ⟨j, hj⟩ := htv_surj (t u) (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
      have hj0 : j.val ≠ 0 := fun e => hne0 (by
        have hje : j = ⟨0, by omega⟩ := Fin.ext e
        rw [← hj, hje])
      refine ⟨j, ?_, ?_⟩
      · simp only [decide_eq_true_eq, v_rep]
        rw [dif_neg hj0]; dsimp only
        rw [← hj]; exact htv_inc ⟨j.val - 1, by omega⟩ j (by dsimp; omega)
      · simp only [decide_eq_false_iff_not, hu_rep_t, v_rep]
        rw [dif_neg hj0]; dsimp only
        have := htv_mono ⟨0, by omega⟩ ⟨j.val - 1, by omega⟩ (Nat.zero_le _); omega)
  obtain ⟨C2, hC2_rep, hC2_sz⟩ := reduce_cols k hk n
    (fun i v => decide ((v : ℕ) < t (u_rep i))) C1 hC1_rep v_rep V_extra hv_inj hSt
    (fun v hv j he => (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he.symm⟩))
    (fun v hv => by
      have hlt : v.val < tv ⟨k - 2, by omega⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
      refine ⟨⟨k - 2, by omega⟩, ?_, ?_⟩
      · simp only [decide_eq_true_eq, hu_rep_t]; exact hlt
      · simp only [decide_eq_false_iff_not, hu_rep_t, v_rep]
        rw [dif_neg (by omega : k - 1 ≠ 0)]; dsimp only
        have heq_idx : (⟨k - 1 - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [heq_idx]; omega)
  have hSt_lb : 3 * k - 6 ≤ C2.gates.length := staircase_lb k hk C2 hC2_rep
  rw [hU_extra_card] at hC1_sz
  rw [hV_extra_card] at hC2_sz
  omega

end PEqualNP.Outside.L_meta_25026

theorem PEqualNP.Outside.L_meta_25026 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 4, 3, 1] u)) 8 ∧ ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 4, 3, 1] u)) s → 8 ≤ s :=
  ⟨⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [7, 14]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [12, 16]⟩], 17⟩, by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩,
    fun s h => by
      have := PEqualNP.Outside.L_meta_25026.main_aux 5 4 1 1 (by norm_num) ![5, 5, 4, 3, 1] (by decide) (by decide) (by decide) (by decide) (by decide) s h
      omega⟩
