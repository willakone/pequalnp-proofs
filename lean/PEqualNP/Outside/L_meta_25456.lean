import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25456

-- The construction is our parked L-meta-25452 proof (same session), copied unchanged.
-- stp, getD_snoc, ofn_get copied from our parked L-meta-25449 / L-meta-25307 proofs.

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem ofn_get (n : ℕ) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem stp_len (Y : List Bool) (g : Gate) : (stp Y g).length = Y.length + 1 := by
  simp [stp]

theorem stp_pre (Y : List Bool) (g : Gate) (i : ℕ) (h : i < Y.length) :
    (stp Y g).getD i false = Y.getD i false := by
  rw [stp, getD_snoc, if_pos h]

theorem stp_new (Y : List Bool) (g : Gate) (i : ℕ) (h : i = Y.length) :
    (stp Y g).getD i false = g.op.eval (g.inputs.map fun i => Y.getD i false) := by
  rw [stp, getD_snoc, if_neg (by omega), if_pos h]

theorem fold_len (gs : List Gate) : ∀ Y : List Bool, (gs.foldl stp Y).length = Y.length + gs.length := by
  induction gs with
  | nil => intro Y; simp
  | cons g gs ih => intro Y; simp only [List.foldl_cons]; rw [ih, stp_len]; simp; omega

theorem fold_pre (gs : List Gate) : ∀ (Y : List Bool) (i : ℕ), i < Y.length →
    (gs.foldl stp Y).getD i false = Y.getD i false := by
  induction gs with
  | nil => intro Y i _; simp
  | cons g gs ih =>
    intro Y i h
    simp only [List.foldl_cons]
    rw [ih _ _ (by rw [stp_len]; omega), stp_pre _ _ _ h]

theorem any_congr' (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem dd {p q : Prop} [Decidable p] [Decidable q] (h1 : p → q) (h2 : q → p) : decide p = decide q :=
  decide_eq_decide.mpr ⟨h1, h2⟩

def RB : ℕ → List Gate → Prop
  | _, [] => True
  | b, g :: gs => (∀ i ∈ g.inputs, i < b) ∧ RB (b + 1) gs

theorem RB_app (l1 : List Gate) : ∀ (b b' : ℕ) (l2 : List Gate), RB b l1 → RB b' l2 → b' = b + l1.length →
    RB b (l1 ++ l2) := by
  induction l1 with
  | nil => intro b b' l2 _ h2 e; simp at e; subst e; simpa using h2
  | cons g l1 ih =>
    intro b b' l2 h1 h2 e
    simp only [List.cons_append, RB] at h1 ⊢
    exact ⟨h1.1, ih (b + 1) b' l2 h1.2 h2 (by simp at e; omega)⟩

theorem RB_one (b : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < b) : RB b [g] := ⟨h, trivial⟩

theorem RB_get (gs : List Gate) : ∀ b, RB b gs → ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < b + j := by
  induction gs with
  | nil => intro b _ j hj; simp at hj
  | cons g gs ih =>
    intro b h j hj i hi
    cases j with
    | zero => simp at hi; have := h.1 i hi; omega
    | succ j =>
      simp at hi hj
      have := ih (b + 1) h.2 j hj i hi
      omega

def chain : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | a, w :: ws, b => ⟨GateOp.or, [a, w]⟩ :: chain b ws (b + 1)

def chainOut : ℕ → List ℕ → ℕ → ℕ
  | a, [], _ => a
  | _, _ :: ws, b => chainOut b ws (b + 1)

theorem chain_len (ws : List ℕ) : ∀ a b, (chain a ws b).length = ws.length := by
  induction ws with
  | nil => intro a b; rfl
  | cons w ws ih => intro a b; simp [chain, ih]

theorem chain_out_lt (ws : List ℕ) : ∀ a b, a < b → chainOut a ws b < b + ws.length := by
  induction ws with
  | nil => intro a b h; simp [chainOut]; exact h
  | cons w ws ih => intro a b _; have := ih b (b + 1) (by omega); simp [chainOut]; omega

theorem chain_rb (ws : List ℕ) : ∀ a b, a < b → (∀ w ∈ ws, w < b) → RB b (chain a ws b) := by
  induction ws with
  | nil => intro a b _ _; trivial
  | cons w ws ih =>
    intro a b ha hw
    refine ⟨?_, ih b (b + 1) (by omega) (fun x hx => by have := hw x (by simp [hx]); omega)⟩
    intro i hi
    simp at hi
    have := hw w (by simp)
    omega

theorem chain_mono (ws : List ℕ) : ∀ a b, ∀ g ∈ chain a ws b, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ws with
  | nil => intro a b g hg; simp [chain] at hg
  | cons w ws ih =>
    intro a b g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_val (ws : List ℕ) : ∀ (a b : ℕ) (Y : List Bool), Y.length = b → a < b → (∀ w ∈ ws, w < b) →
    ((chain a ws b).foldl stp Y).getD (chainOut a ws b) false =
      (Y.getD a false || ws.any (fun w => Y.getD w false)) := by
  induction ws with
  | nil => intro a b Y _ _ _; simp [chain, chainOut]
  | cons w ws ih =>
    intro a b Y hY ha hw
    simp only [chain, chainOut, List.foldl_cons]
    have hw0 := hw w (by simp)
    rw [ih b (b + 1) _ (by rw [stp_len]; omega) (by omega)
      (fun x hx => by have := hw x (by simp [hx]); omega)]
    rw [stp_new _ _ _ hY.symm]
    rw [any_congr' ws _ (fun x => Y.getD x false)
      (fun x hx => stp_pre _ _ _ (by have := hw x (by simp [hx]); omega))]
    simp [GateOp.eval, Bool.or_assoc]

section
variable {r c m : ℕ} (κr : Fin r → Fin m) (κc : Fin c → Fin m)

def cl (i : ℕ) : ℕ :=
  if h : i < r then (κr ⟨i, h⟩).val else if h2 : i - r < c then (κc ⟨i - r, h2⟩).val else 0

def ws (k : ℕ) : List ℕ := (List.range (r + c)).filter (fun i => decide (cl κr κc i = k))

def cnt (k : ℕ) : ℕ := ((List.range (r + c)).filter (fun i => decide (cl κr κc i ≤ k))).length

theorem cl_row (u : Fin r) : cl κr κc u.val = (κr u).val := by
  unfold cl; rw [dif_pos u.isLt]

theorem cl_col (v : Fin c) : cl κr κc (r + v.val) = (κc v).val := by
  unfold cl
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  ext
  simp

theorem cl_lt (hm : 0 < m) (i : ℕ) : cl κr κc i < m := by
  unfold cl
  split_ifs
  · exact Fin.isLt _
  · exact Fin.isLt _
  · exact hm

theorem flen (f : ℕ → ℕ) (k : ℕ) (l : List ℕ) :
    (l.filter (fun i => decide (f i ≤ k + 1))).length =
      (l.filter (fun i => decide (f i ≤ k))).length + (l.filter (fun i => decide (f i = k + 1))).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    by_cases h1 : f a ≤ k
    · rw [if_pos (by simp; omega), if_pos (by simpa using h1), if_neg (by simp; omega)]
      simp [ih]; omega
    · by_cases h2 : f a = k + 1
      · rw [if_pos (by simp; omega), if_neg (by simpa using h1), if_pos (by simpa using h2)]
        simp [ih]; omega
      · rw [if_neg (by simp; omega), if_neg (by simpa using h1), if_neg (by simpa using h2)]
        exact ih

theorem cnt_succ (k : ℕ) : cnt κr κc (k + 1) = cnt κr κc k + (ws κr κc (k + 1)).length := by
  unfold cnt ws; exact flen _ k _

theorem cnt_zero : cnt κr κc 0 = (ws κr κc 0).length := by
  unfold cnt ws
  congr 1
  apply List.filter_congr
  intro x _
  simp

theorem cnt_top (hm : 0 < m) : cnt κr κc (m - 1) = r + c := by
  unfold cnt
  rw [List.filter_eq_self.mpr]
  · simp
  · intro i _
    have := cl_lt κr κc hm i
    simp; omega

theorem ws_cons (hcls : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) (k : ℕ) (hk : k < m) :
    ∃ h t, ws κr κc k = h :: t ∧ h < r + c ∧ ∀ w ∈ t, w < r + c := by
  obtain ⟨⟨u0, hu0⟩, _⟩ := hcls ⟨k, hk⟩
  have hmem : u0.val ∈ ws κr κc k := by
    simp only [ws, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [cl_row, hu0]
  have hall : ∀ w ∈ ws κr κc k, w < r + c := by
    intro w hw
    simp only [ws, List.mem_filter, List.mem_range] at hw
    exact hw.1
  cases e : ws κr κc k with
  | nil => rw [e] at hmem; simp at hmem
  | cons h t =>
    rw [e] at hall
    exact ⟨h, t, rfl, hall h (by simp), fun w hw => hall w (by simp [hw])⟩

def ON (u : Fin r) (v : Fin c) (Y : List Bool) : Prop :=
  r + c ≤ Y.length ∧ ∀ i < r + c, Y.getD i false = decide (i = u.val ∨ i = r + v.val)

theorem on_x (u : Fin r) (v : Fin c) : ON (r := r) (c := c) u v (PEqualNP.Represents.oneEach u v) := by
  refine ⟨by simp [PEqualNP.Represents.oneEach], ?_⟩
  intro i hi
  unfold PEqualNP.Represents.oneEach
  by_cases h : i < r
  · rw [List.getD_append _ _ _ _ (by simpa using h), ofn_get _ _ _ h]
    simp [Fin.ext_iff] <;> omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
      ofn_get _ _ _ (by omega : i - r < c)]
    have hu := u.isLt
    have hv := v.isLt
    apply dd
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · rintro (e | e)
      · omega
      · exact Fin.ext (by simp; omega)

theorem on_fold (u : Fin r) (v : Fin c) (Y : List Bool) (gs : List Gate) (h : ON u v Y) :
    ON u v (gs.foldl stp Y) := by
  refine ⟨by rw [fold_len]; have := h.1; omega, fun i hi => ?_⟩
  rw [fold_pre _ _ _ (by have := h.1; omega)]
  exact h.2 i hi

theorem cls_val (u : Fin r) (v : Fin c) (Y : List Bool) (hY : ON u v Y) (k h : ℕ) (t : List ℕ)
    (e : ws κr κc k = h :: t) :
    (Y.getD h false || t.any (fun w => Y.getD w false)) =
      decide (cl κr κc u.val = k ∨ cl κr κc (r + v.val) = k) := by
  have e1 : (Y.getD h false || t.any (fun w => Y.getD w false)) =
      (ws κr κc k).any (fun w => Y.getD w false) := by rw [e]; simp
  rw [e1, any_congr' _ _ (fun w => decide (w = u.val ∨ w = r + v.val))]
  · apply Bool.eq_iff_iff.mpr
    simp only [ws, List.any_eq_true, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨x, ⟨_, hc⟩, hx⟩
      rcases hx with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr hc
    · rintro (hc | hc)
      · exact ⟨u.val, ⟨by omega, hc⟩, Or.inl rfl⟩
      · exact ⟨r + v.val, ⟨by omega, hc⟩, Or.inr rfl⟩
  · intro w hw
    simp only [ws, List.mem_filter, List.mem_range] at hw
    exact hY.2 w hw.1

theorem reach (hm : 2 ≤ m) (hcls : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) :
    ∀ k, 1 ≤ k → k < m → ∃ (gs : List Gate) (wW wU wg : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧ RB (r + c) gs ∧
      wW < r + c + gs.length ∧ wU < r + c + gs.length ∧ wg < r + c + gs.length ∧
      gs.length + 3 = cnt κr κc k + 2 * k ∧
      ∀ (u : Fin r) (v : Fin c),
        (gs.foldl stp (PEqualNP.Represents.oneEach u v)).getD wW false =
          decide (cl κr κc u.val ≤ k - 1 ∨ cl κr κc (r + v.val) ≤ k - 1) ∧
        (gs.foldl stp (PEqualNP.Represents.oneEach u v)).getD wU false =
          decide (cl κr κc u.val = k ∨ cl κr κc (r + v.val) = k) ∧
        (gs.foldl stp (PEqualNP.Represents.oneEach u v)).getD wg false =
          decide (cl κr κc u.val ≠ cl κr κc (r + v.val) ∧ cl κr κc u.val ≤ k ∧ cl κr κc (r + v.val) ≤ k) := by
  intro k hk1 hkm
  induction k, hk1 using Nat.le_induction with
  | base =>
    obtain ⟨h0, t0, e0, h0lt, t0lt⟩ := ws_cons κr κc hcls 0 (by omega)
    obtain ⟨h1, t1, e1, h1lt, t1lt⟩ := ws_cons κr κc hcls 1 (by omega)
    have lo0 := chain_out_lt t0 h0 (r + c) h0lt
    have lo1 := chain_out_lt t1 h1 (r + c + t0.length) (by omega)
    have l0 := chain_len t0 h0 (r + c)
    have l1 := chain_len t1 h1 (r + c + t0.length)
    have hc1 := cnt_succ κr κc 0
    have hc0 := cnt_zero κr κc
    rw [e0] at hc0
    rw [e1] at hc1
    simp only [List.length_cons, zero_add] at hc0 hc1
    refine ⟨chain h0 t0 (r + c) ++ chain h1 t1 (r + c + t0.length) ++
      [⟨GateOp.and, [chainOut h1 t1 (r + c + t0.length), chainOut h0 t0 (r + c)]⟩],
      chainOut h0 t0 (r + c), chainOut h1 t1 (r + c + t0.length), r + c + t0.length + t1.length,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · have := chain_mono _ _ _ g hg; exact ⟨Or.inr this.1, by omega⟩
      · have := chain_mono _ _ _ g hg; exact ⟨Or.inr this.1, by omega⟩
      · subst hg; simp
    · refine RB_app _ _ (r + c + t0.length + t1.length) _ (RB_app _ _ _ _ (chain_rb _ _ _ h0lt t0lt)
        (chain_rb _ _ _ (by omega) (fun w hw => by have := t1lt w hw; omega)) (by rw [l0])) ?_ ?_
      · apply RB_one
        intro i hi
        simp at hi
        omega
      · simp [l0, l1]; omega
    · simp [l0, l1]; omega
    · simp [l0, l1]; omega
    · simp [l0, l1]; omega
    · simp [l0, l1]; omega
    · intro u v
      have hX := on_x (r := r) (c := c) u v
      have hXl : (PEqualNP.Represents.oneEach u v).length = r + c := by
        simp [PEqualNP.Represents.oneEach]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have Y1l := fold_len (chain h0 t0 (r + c)) (PEqualNP.Represents.oneEach u v)
      have Y2l := fold_len (chain h1 t1 (r + c + t0.length))
        ((chain h0 t0 (r + c)).foldl stp (PEqualNP.Represents.oneEach u v))
      rw [Y1l, hXl, l0] at Y2l
      rw [hXl, l0] at Y1l
      have H1 := on_fold u v _ (chain h0 t0 (r + c)) hX
      have v0 : ((chain h1 t1 (r + c + t0.length)).foldl stp
          ((chain h0 t0 (r + c)).foldl stp (PEqualNP.Represents.oneEach u v))).getD
            (chainOut h0 t0 (r + c)) false =
          decide (cl κr κc u.val = 0 ∨ cl κr κc (r + v.val) = 0) := by
        rw [fold_pre _ _ _ (by omega), chain_val _ _ _ _ hXl h0lt t0lt]
        exact cls_val κr κc u v _ hX 0 h0 t0 e0
      have v1 : ((chain h1 t1 (r + c + t0.length)).foldl stp
          ((chain h0 t0 (r + c)).foldl stp (PEqualNP.Represents.oneEach u v))).getD
            (chainOut h1 t1 (r + c + t0.length)) false =
          decide (cl κr κc u.val = 1 ∨ cl κr κc (r + v.val) = 1) := by
        rw [chain_val _ _ _ _ Y1l (by omega) (fun w hw => by have := t1lt w hw; omega)]
        exact cls_val κr κc u v _ H1 1 h1 t1 e1
      refine ⟨?_, ?_, ?_⟩
      · rw [stp_pre _ _ _ (by omega), v0]
        exact dd (fun h => by omega) (fun h => by omega)
      · rw [stp_pre _ _ _ (by omega), v1]
      · rw [stp_new _ _ _ (by omega)]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, v0, v1]
        rw [← Bool.decide_and]
        exact dd (fun h => by omega) (fun h => by omega)
  | succ k hk ih =>
    obtain ⟨gs, wW, wU, wg, hmono, hrb, hW, hU, hg, hlen, hval⟩ := ih (by omega)
    obtain ⟨h, t, e, hlt, tlt⟩ := ws_cons κr κc hcls (k + 1) hkm
    have hcs := cnt_succ κr κc k
    rw [e] at hcs
    simp only [List.length_cons] at hcs
    have lo := chain_out_lt t h (r + c + gs.length + 1) (by omega)
    have lc := chain_len t h (r + c + gs.length + 1)
    refine ⟨gs ++ [⟨GateOp.or, [wW, wU]⟩] ++ chain h t (r + c + gs.length + 1) ++
      [⟨GateOp.and, [chainOut h t (r + c + gs.length + 1), r + c + gs.length]⟩] ++
      [⟨GateOp.or, [wg, r + c + gs.length + 1 + t.length]⟩],
      r + c + gs.length, chainOut h t (r + c + gs.length + 1), r + c + gs.length + 1 + t.length + 1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (((hg | hg) | hg) | hg) | hg
      · exact hmono g hg
      · subst hg; simp
      · have := chain_mono _ _ _ g hg; exact ⟨Or.inr this.1, by omega⟩
      · subst hg; simp
      · subst hg; simp
    · refine RB_app _ _ (r + c + gs.length + 1 + t.length + 1) _
        (RB_app _ _ (r + c + gs.length + 1 + t.length) _
        (RB_app _ _ (r + c + gs.length + 1) _ (RB_app _ _ (r + c + gs.length) _ hrb
        (RB_one _ _ ?_) rfl) (chain_rb _ _ _ (by omega) (fun w hw => by have := tlt w hw; omega)) ?_)
        (RB_one _ _ ?_) ?_) (RB_one _ _ ?_) ?_
      · intro i hi; simp at hi; omega
      · simp <;> omega
      · intro i hi; simp at hi; omega
      · simp [lc]; omega
      · intro i hi; simp at hi; omega
      · simp [lc]; omega
    · simp [lc] <;> omega
    · simp [lc]; omega
    · simp [lc] <;> omega
    · simp [lc]; omega
    · intro u v
      obtain ⟨vW, vU, vg⟩ := hval u v
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hXl : (PEqualNP.Represents.oneEach u v).length = r + c := by
        simp [PEqualNP.Represents.oneEach]
      have Yl := fold_len gs (PEqualNP.Represents.oneEach u v)
      rw [hXl] at Yl
      have HY := on_fold u v _ gs (on_x (r := r) (c := c) u v)
      have H1 : ON u v (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩) := by
        have := on_fold u v _ [⟨GateOp.or, [wW, wU]⟩] HY
        simpa using this
      have Y1l := stp_len (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩
      rw [Yl] at Y1l
      have Y2l := fold_len (chain h t (r + c + gs.length + 1))
        (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩)
      rw [Y1l, lc] at Y2l
      have f1 : (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩).getD
          (r + c + gs.length) false = decide (cl κr κc u.val ≤ k ∨ cl κr κc (r + v.val) ≤ k) := by
        rw [stp_new _ _ _ (by omega)]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, vW, vU]
        rw [← Bool.decide_or]
        exact dd (fun h => by omega) (fun h => by omega)
      have f2 : ((chain h t (r + c + gs.length + 1)).foldl stp
          (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩)).getD
            (chainOut h t (r + c + gs.length + 1)) false =
          decide (cl κr κc u.val = k + 1 ∨ cl κr κc (r + v.val) = k + 1) := by
        rw [chain_val _ _ _ _ Y1l (by omega) (fun w hw => by have := tlt w hw; omega)]
        exact cls_val κr κc u v _ H1 (k + 1) h t e
      have f1' : ((chain h t (r + c + gs.length + 1)).foldl stp
          (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩)).getD
            (r + c + gs.length) false = decide (cl κr κc u.val ≤ k ∨ cl κr κc (r + v.val) ≤ k) := by
        rw [fold_pre _ _ _ (by omega), f1]
      have f3 : (stp ((chain h t (r + c + gs.length + 1)).foldl stp
          (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩))
            ⟨GateOp.and, [chainOut h t (r + c + gs.length + 1), r + c + gs.length]⟩).getD
            (r + c + gs.length + 1 + t.length) false =
          decide ((cl κr κc u.val = k + 1 ∨ cl κr κc (r + v.val) = k + 1) ∧
            (cl κr κc u.val ≤ k ∨ cl κr κc (r + v.val) ≤ k)) := by
        rw [stp_new _ _ _ (by omega)]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, f2, f1']
        rw [← Bool.decide_and]
      have vg' : (stp ((chain h t (r + c + gs.length + 1)).foldl stp
          (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩))
            ⟨GateOp.and, [chainOut h t (r + c + gs.length + 1), r + c + gs.length]⟩).getD wg false =
          decide (cl κr κc u.val ≠ cl κr κc (r + v.val) ∧ cl κr κc u.val ≤ k ∧ cl κr κc (r + v.val) ≤ k) := by
        rw [stp_pre _ _ _ (by omega), fold_pre _ _ _ (by omega), stp_pre _ _ _ (by omega), vg]
      have Y3l := stp_len ((chain h t (r + c + gs.length + 1)).foldl stp
          (stp (gs.foldl stp (PEqualNP.Represents.oneEach u v)) ⟨GateOp.or, [wW, wU]⟩))
            ⟨GateOp.and, [chainOut h t (r + c + gs.length + 1), r + c + gs.length]⟩
      rw [Y2l] at Y3l
      refine ⟨?_, ?_, ?_⟩
      · rw [stp_pre _ _ _ (by omega), stp_pre _ _ _ (by omega), f1']
        exact dd (fun h => by omega) (fun h => by omega)
      · rw [stp_pre _ _ _ (by omega), stp_pre _ _ _ (by omega), f2]
      · rw [stp_new _ _ _ (by omega)]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, vg', f3]
        rw [← Bool.decide_or]
        exact dd (fun h => by omega) (fun h => by omega)

theorem main (hm : 2 ≤ m) (hcls : ∀ K : Fin m, (∃ u, κr u = K) ∧ (∃ v, κc v = K)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C ∧ C.size ≤ (r + c - m) + (3 * m - 5) ∧
      PEqualNP.Represents.Represents (fun (u : Fin r) (v : Fin c) => decide (κr u ≠ κc v)) C := by
  obtain ⟨gs, wW, wU, wg, hmono, hrb, _, _, _, hlen, hval⟩ := reach κr κc hm hcls (m - 1) (by omega) (by omega)
  have hrm : m ≤ r := by
    have hs : Function.Surjective κr := fun K => (hcls K).1
    simpa using Fintype.card_le_of_surjective κr hs
  rw [cnt_top κr κc (by omega)] at hlen
  refine ⟨⟨gs, wg⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 <;> simp [h1]
  · intro j hj i hi
    exact RB_get gs (r + c) hrb j hj i hi
  · show gs.length ≤ _
    omega
  · intro u v
    unfold Circuit.eval Circuit.wires
    change (gs.foldl stp (PEqualNP.Represents.oneEach u v)).getD wg false = _
    rw [(hval u v).2.2, cl_row, cl_col]
    have := (κr u).isLt
    have := (κc v).isLt
    exact dd (fun h e => h.1 (by rw [e])) (fun h => ⟨fun e => h (Fin.ext e), by omega, by omega⟩)

end

end PEqualNP.Outside.L_meta_25456

theorem PEqualNP.Outside.L_meta_25456 : ∀ (n m : ℕ) (f g : Fin n → Fin m), 2 ≤ m → (∀ k : Fin m, ∃ u, f u = k) → (∀ k : Fin m, ∃ v, g v = k) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (f u ≠ g v)) (2 * n + 2 * m - 5) := by
  intro n m f g hm hf hg
  obtain ⟨C, h1, _, h3, h4⟩ := PEqualNP.Outside.L_meta_25456.main f g hm (fun K => ⟨hf K, hg K⟩)
  have hnm : m ≤ n := by simpa using Fintype.card_le_of_surjective f hf
  exact ⟨C, h1, by omega, h4⟩
