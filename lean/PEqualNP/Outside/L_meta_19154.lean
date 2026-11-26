import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19154_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wstep_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private lemma foldl_wstep_getD_lt (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl wstep acc).getD j false = acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep acc g) (by simp [wstep]; omega)]
    rw [wstep, List.getD_append _ _ _ _ hj]

private lemma or_eval_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

private lemma and_eval_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

-- Build leave-one-out OR wires directly appended to `gs0` for an input slice at `[off, off + n)`
private lemma build_slice_left (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ pw : ℕ → ℕ,
          (∀ k ≤ m, pw k < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ k ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (pw k) false =
              decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, rfl, fun _ => off, fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD off false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨0, by omega⟩, le_rfl, by simpa using h⟩
    · rintro ⟨j, hj, hxj⟩
      have hj0 : j.val = 0 := by omega
      rw [hj0, Nat.add_zero] at hxj
      exact hxj
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, pw, hpbd, hpev⟩ := ih (by omega)
    let newG : Gate := ⟨.or, [pw m, off + (m + 1)]⟩
    let gs' : List Gate := gs ++ [newG]
    let pw' : ℕ → ℕ := fun k => if k = m + 1 then N + gs0.length + m else pw k
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], pw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro k hk
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · simp only [hkeq, ite_true]; omega
      · simp only [hkeq, ite_false]
        have := hpbd k (by omega)
        omega
    · intro inp hlen_inp k hk
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw m) false || w.getD (off + (m + 1)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · subst hkeq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hpev inp hlen_inp m le_rfl
        have h2 : w.getD (off + (m + 1)) false = inp.getD (off + (m + 1)) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + (m + 1)) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | hxm)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨⟨m + 1, by omega⟩, le_rfl, hxm⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : j.val ≤ m
          · exact Or.inl ⟨j, hjm, hxj⟩
          · have hjeq : j.val = m + 1 := by omega
            rw [hjeq] at hxj
            exact Or.inr hxj
      · simp only [hkeq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hpbd k (by omega))]
        exact hpev inp hlen_inp k (by omega)

private lemma build_slice_right (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ sw : ℕ → ℕ,
          (∀ r ≤ m, sw r < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ r ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (sw r) false =
              decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, rfl, fun _ => off + (n - 1), fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (n - 1)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨n - 1, by omega⟩, by dsimp only; omega, h⟩
    · rintro ⟨j, hj, hxj⟩
      have hjeq : j.val = n - 1 := by omega
      rwa [← hjeq]
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, sw, hsbd, hsev⟩ := ih (by omega)
    let idx : ℕ := n - 1 - (m + 1)
    let newG : Gate := ⟨.or, [off + idx, sw m]⟩
    let gs' : List Gate := gs ++ [newG]
    let sw' : ℕ → ℕ := fun r => if r = m + 1 then N + gs0.length + m else sw r
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], sw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro r hr
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · simp only [hreq, ite_true]; omega
      · simp only [hreq, ite_false]
        have := hsbd r (by omega)
        omega
    · intro inp hlen_inp r hr
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (off + idx) false || w.getD (sw m) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · subst hreq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hsev inp hlen_inp m le_rfl
        have h2 : w.getD (off + idx) false = inp.getD (off + idx) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + idx) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (hxidx | ⟨j, hj, hxj⟩)
          · exact ⟨⟨idx, by omega⟩, by dsimp only [idx]; omega, hxidx⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : n - 1 - m ≤ j.val
          · exact Or.inr ⟨j, hjm, hxj⟩
          · have hjeq : j.val = idx := by dsimp only [idx]; omega
            rw [hjeq] at hxj
            exact Or.inl hxj
      · simp only [hreq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hsbd r (by omega))]
        exact hsev inp hlen_inp r (by omega)

private lemma build_slice_mid (N off n : ℕ) (hn : 3 ≤ n) (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩)
    (pw sw : ℕ → ℕ)
    (hpbd : ∀ k ≤ n - 2, pw k < N + gs0.length)
    (hsbd : ∀ r ≤ n - 2, sw r < N + gs0.length)
    (hpev : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (pw k) false =
        decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))
    (hsev : ∀ (inp : List Bool), inp.length = N → ∀ r ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (sw r) false =
        decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true)) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ mw : ℕ → ℕ,
          (∀ i, 1 ≤ i → i ≤ m → mw i < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ i, 1 ≤ i → i ≤ m →
            (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (mw i) false =
              decide (∃ j : Fin n, j.val ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], by simpa using hM0, rfl, fun _ => 0, fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega⟩
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hlen, mw, hmbd, hmev⟩ := ih (by omega)
    let i0 : ℕ := m + 1
    let newG : Gate := ⟨.or, [pw (i0 - 1), sw (n - 2 - i0)]⟩
    let gs' : List Gate := gs ++ [newG]
    let mw' : ℕ → ℕ := fun i => if i = i0 then N + gs0.length + m else mw i
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, by simp [gs', hlen], mw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · intro i hi1 hi2
      dsimp only [mw']
      by_cases hieq : i = i0
      · simp only [hieq, ite_true]; omega
      · simp only [hieq, ite_false]
        have := hmbd i hi1 (by omega)
        omega
    · intro inp hlen_inp i hi1 hi2
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw (i0 - 1)) false || w.getD (sw (n - 2 - i0)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [mw']
      by_cases hieq : i = i0
      · subst hieq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have hkeep : ∀ u < N + gs0.length, w.getD u false = (Circuit.wires ⟨gs0, 0⟩ inp).getD u false := by
          intro u hu
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD u false = _
          rw [List.foldl_append]
          rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
          rfl
        rw [hkeep _ (hpbd (i0 - 1) (by omega)), hkeep _ (hsbd (n - 2 - i0) (by omega))]
        rw [hpev inp hlen_inp (i0 - 1) (by omega), hsev inp hlen_inp (n - 2 - i0) (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hlt : j.val < i0
          · exact Or.inl ⟨j, by omega, hxj⟩
          · exact Or.inr ⟨j, by omega, hxj⟩
      · simp only [hieq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hmbd i hi1 (by omega))]
        exact hmev inp hlen_inp i hi1 (by omega)

private inductive Rail where
  | ff : Rail
  | tt : Rail
  | wire : ℕ → Rail
  deriving DecidableEq

private def evalRail (dw : List Bool) : Rail → Bool
  | .ff => false
  | .tt => true
  | .wire i => dw.getD i false

private def railBound (L : ℕ) : Rail → Prop
  | .ff => True
  | .tt => True
  | .wire i => i < L

private lemma railBound_mono {L1 L2 : ℕ} (h : L1 ≤ L2) : ∀ {r : Rail}, railBound L1 r → railBound L2 r
  | .ff, _ => trivial
  | .tt, _ => trivial
  | .wire _, hi => Nat.lt_of_lt_of_le hi h

private lemma build_slice_loo (N off n : ℕ) (hn : 1 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) :
    ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ gs.length ≤ 3 * n - 6 ∧
      ∃ r : Fin n → Rail,
        (∀ i, railBound (N + gs0.length + gs.length) (r i)) ∧
        (∀ i, r i ≠ .tt) ∧
        (∀ (inp : List Bool), inp.length = N → ∀ i : Fin n,
          evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp) (r i) =
            decide (∃ j : Fin n, j ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨[], by simpa using hM0, by simp, fun _ => .ff, fun _ => trivial, fun _ h => Rail.noConfusion h, ?_⟩
    intro inp _ i
    symm
    dsimp only [evalRail]
    rw [decide_eq_false_iff_not]
    rintro ⟨j, hne, _⟩
    exact hne (Subsingleton.elim j i)
  by_cases hn2 : n = 2
  · subst hn2
    refine ⟨[], by simpa using hM0, by simp, fun i => .wire (off + (1 - i.val)),
      fun i => by dsimp only [railBound]; omega, fun _ h => Rail.noConfusion h, ?_⟩
    intro inp hlen i
    simp only [evalRail, List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (1 - i.val)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨⟨1 - i.val, by omega⟩, ?_, h⟩
      intro heq
      have := congrArg Fin.val heq
      dsimp only at this
      omega
    · rintro ⟨j, hne, hxj⟩
      have hjeq : j.val = 1 - i.val := by
        have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
        omega
      rwa [← hjeq]
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨gs1, hM1, hlen1, pw, hpbd1, hpev1⟩ := build_slice_left N off n (by omega) hbound gs0 hM0 (n - 2) le_rfl
    obtain ⟨gs2, hM2, hlen2, sw, hsbd2, hsev2⟩ := build_slice_right N off n (by omega) hbound (gs0 ++ gs1) hM1 (n - 2) le_rfl
    have hlen012 : ((gs0 ++ gs1) ++ gs2).length = gs0.length + 2 * (n - 2) := by
      simp only [List.length_append, hlen1, hlen2]; omega
    have hpbd12 : ∀ k ≤ n - 2, pw k < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro k hk; have := hpbd1 k hk; omega
    have hsbd12 : ∀ r ≤ n - 2, sw r < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro r hr; have := hsbd2 r hr; simp only [List.length_append, hlen1] at this; omega
    have hpev12 : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
        (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD (pw k) false =
          decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true) := by
      intro inp hlen_inp k hk
      unfold Circuit.wires
      change (((gs0 ++ gs1) ++ gs2).foldl wstep inp).getD (pw k) false = _
      rw [List.foldl_append]
      rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp, List.length_append, hlen1]; have := hpbd1 k hk; omega)]
      exact hpev1 inp hlen_inp k hk
    obtain ⟨gs3, hM3, hlen3, mw, hmbd3, hmev3⟩ :=
      build_slice_mid N off n hn3 ((gs0 ++ gs1) ++ gs2) hM2 pw sw hpbd12 hsbd12 hpev12 hsev2 (n - 2) le_rfl
    let gtot : List Gate := (gs1 ++ gs2) ++ gs3
    have hassoc : gs0 ++ gtot = ((gs0 ++ gs1) ++ gs2) ++ gs3 := by
      simp [gtot, List.append_assoc]
    let r : Fin n → Rail := fun i =>
      if i.val = 0 then .wire (sw (n - 2))
      else if i.val = n - 1 then .wire (pw (n - 2))
      else .wire (mw i.val)
    refine ⟨gtot, ?_, ?_, r, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gtot at hg
      rw [hassoc] at hg
      exact hM3 g hg
    · simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
    · intro i
      dsimp only [r]
      have htot : N + gs0.length + gtot.length = N + ((gs0 ++ gs1) ++ gs2).length + (n - 2) := by
        simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true, railBound]; have := hsbd12 (n - 2) le_rfl; omega
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true, railBound]; have := hpbd12 (n - 2) le_rfl; omega
        · simp only [hin, ite_false, railBound]; have := hmbd3 i.val (by omega) (by omega); omega
    · intro i
      dsimp only [r]
      split_ifs <;> intro h <;> cases h
    · intro inp hlen_inp i
      have hkeep : ∀ u < N + ((gs0 ++ gs1) ++ gs2).length,
          (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp).getD u false =
          (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD u false := by
        intro u hu
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change ((((gs0 ++ gs1) ++ gs2) ++ gs3).foldl wstep inp).getD u false = _
        rw [List.foldl_append]
        rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
        rfl
      dsimp only [r]
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true, evalRail]
        rw [hkeep _ (hsbd12 (n - 2) le_rfl), hsev2 inp hlen_inp (n - 2) le_rfl]
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
        · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true, evalRail]
          rw [hkeep _ (hpbd12 (n - 2) le_rfl), hpev12 inp hlen_inp (n - 2) le_rfl]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
          · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
        · simp only [hin, ite_false, evalRail]
          have heq : (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp) = Circuit.wires ⟨((gs0 ++ gs1) ++ gs2) ++ gs3, 0⟩ inp := by
            unfold Circuit.wires; dsimp only; rw [hassoc]
          rw [heq, hmev3 inp hlen_inp i.val (by omega) (by omega)]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (congrArg Fin.val h), hxj⟩
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (Fin.ext h), hxj⟩

private lemma evalRail_congr {dw1 dw2 : List Bool} {L : ℕ} (h : ∀ u < L, dw1.getD u false = dw2.getD u false) :
    ∀ {r : Rail}, railBound L r → evalRail dw1 r = evalRail dw2 r
  | .ff, _ => rfl
  | .tt, _ => rfl
  | .wire i, hi => h i hi

private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]

private lemma wires_keep (gs0 gs : List Gate) (inp : List Bool) (idx : ℕ)
    (h : idx < inp.length + gs0.length) :
    (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD idx false = (Circuit.wires ⟨gs0, 0⟩ inp).getD idx false := by
  unfold Circuit.wires
  change ((gs0 ++ gs).foldl wstep inp).getD idx false = (gs0.foldl wstep inp).getD idx false
  rw [List.foldl_append, foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len]; exact h)]

private lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    NestedCover.gateAt C j = C.gates[j] := by
  simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]

private lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [EdgeOwnership.coneStep]
    omega

private lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (EdgeOwnership.coneStep n (gs.foldl (EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (EdgeOwnership.coneStep n (gs.foldl (EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (EdgeOwnership.coneStep n (gs.foldl (EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (NestedCover.gateAt C j).inputs ∧ (i = k ∨ EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold EdgeOwnership.InCone EdgeOwnership.cones NestedCover.gateAt
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

private lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : EdgeOwnership.InCone n C a k) :
    ∀ j, EdgeOwnership.InCone n C k j → EdgeOwnership.InCone n C a j := by
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

private lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, EdgeOwnership.InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3 | h3⟩ := (inCone_iff n C i j).1 h
    · omega
    · have := ih k hk i h3; omega

private def wl : List Rail → List ℕ
  | [] => []
  | .ff :: rs => wl rs
  | .tt :: rs => wl rs
  | .wire i :: rs => i :: wl rs

private lemma wl_len (rs : List Rail) : (wl rs).length ≤ rs.length := by
  induction rs with
  | nil => simp [wl]
  | cons r rs ih => cases r <;> simp only [wl, List.length_cons] <;> omega

private def emitG : Bool → List Rail → Gate
  | true, rs => if Rail.ff ∈ rs then ⟨.or, []⟩ else ⟨.and, wl rs⟩
  | false, rs => if Rail.tt ∈ rs then ⟨.and, []⟩ else ⟨.or, wl rs⟩

private def bval : Bool → List Bool → Bool
  | true, l => l.all id
  | false, l => l.any id

private lemma bval_not (b : Bool) (l : List Bool) : (!bval b l) = bval (!b) (l.map not) := by
  induction l with
  | nil => cases b <;> rfl
  | cons a l ih =>
    cases b
    · change (!(a || l.any id)) = (!a && (l.map not).all id)
      have ih' : (!l.any id) = (l.map not).all id := ih
      rw [← ih']; cases a <;> rfl
    · change (!(a && l.all id)) = (!a || (l.map not).any id)
      have ih' : (!l.all id) = (l.map not).any id := ih
      rw [← ih']; cases a <;> rfl

private lemma emitG_mono (b : Bool) (rs : List Rail) (h : rs.length ≤ 2) :
    (emitG b rs).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (emitG b rs).inputs.length ≤ 2 := by
  have h2 := wl_len rs
  cases b <;> simp only [emitG] <;> split_ifs <;> exact ⟨by simp, by simp <;> omega⟩

private lemma all_wl (W : List Bool) (rs : List Rail) (h : Rail.ff ∉ rs) :
    ((wl rs).map fun i => W.getD i false).all id = (rs.map (evalRail W)).all id := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h2 : Rail.ff ∉ rs := fun h' => h (List.mem_cons_of_mem _ h')
    cases r with
    | ff => exact (h (by simp)).elim
    | tt =>
      change _ = (true && (rs.map (evalRail W)).all id)
      rw [Bool.true_and]; exact ih h2
    | wire i =>
      change (W.getD i false && ((wl rs).map fun i => W.getD i false).all id) =
        (W.getD i false && (rs.map (evalRail W)).all id)
      rw [ih h2]

private lemma any_wl (W : List Bool) (rs : List Rail) (h : Rail.tt ∉ rs) :
    ((wl rs).map fun i => W.getD i false).any id = (rs.map (evalRail W)).any id := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h2 : Rail.tt ∉ rs := fun h' => h (List.mem_cons_of_mem _ h')
    cases r with
    | tt => exact (h (by simp)).elim
    | ff =>
      change _ = (false || (rs.map (evalRail W)).any id)
      rw [Bool.false_or]; exact ih h2
    | wire i =>
      change (W.getD i false || ((wl rs).map fun i => W.getD i false).any id) =
        (W.getD i false || (rs.map (evalRail W)).any id)
      rw [ih h2]

private lemma all_ff (W : List Bool) (rs : List Rail) (h : Rail.ff ∈ rs) :
    (rs.map (evalRail W)).all id = false := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · rfl
    · change (evalRail W r && (rs.map (evalRail W)).all id) = false
      rw [ih h', Bool.and_false]

private lemma any_tt (W : List Bool) (rs : List Rail) (h : Rail.tt ∈ rs) :
    (rs.map (evalRail W)).any id = true := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · rfl
    · change (evalRail W r || (rs.map (evalRail W)).any id) = true
      rw [ih h', Bool.or_true]

private lemma emit_eval (W : List Bool) (b : Bool) (rs : List Rail) :
    (emitG b rs).op.eval ((emitG b rs).inputs.map fun i => W.getD i false) =
      bval b (rs.map (evalRail W)) := by
  cases b
  · simp only [emitG]
    split_ifs with h
    · exact (any_tt W rs h).symm
    · exact any_wl W rs h
  · simp only [emitG]
    split_ifs with h
    · exact (all_ff W rs h).symm
    · exact all_wl W rs h

private lemma push (gs0 gs : List Gate) (g : Gate) (inp : List Bool) :
    Circuit.wires ⟨gs0 ++ (gs ++ [g]), 0⟩ inp = Circuit.wires ⟨gs0 ++ gs, 0⟩ inp ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD i false)] := by
  unfold Circuit.wires
  dsimp only
  rw [← List.append_assoc, List.foldl_append]
  rfl

private lemma getD_snoc (l : List Bool) (x : Bool) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i false = x := by
  subst hi
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

private lemma rail_app (W : List Bool) (x : Bool) (r : Rail) (hr : railBound W.length r) :
    evalRail (W ++ [x]) r = evalRail W r := by
  cases r with
  | ff => rfl
  | tt => rfl
  | wire i => exact List.getD_append _ _ _ _ hr

private lemma mono_push (G : List Gate) (g : Gate) (hM : Monotone2 ⟨G, 0⟩)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Monotone2 ⟨G ++ [g], 0⟩ := by
  intro x hx
  change x ∈ G ++ [g] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hM x hx
  · rw [List.mem_singleton.1 hx]; exact hg


theorem rep_main (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (p h : ℕ)
    (Cn P : ℕ → Prop) {dP : DecidablePred P}
    (hF : FanInTwo C) (hsz : C.size ≤ s) (hRep : Represents A C) (hp : p < C.gates.length)
    (hpop : (NestedCover.gateAt C p).op = GateOp.not)
    (hph : (NestedCover.gateAt C p).inputs.head? = some (n + m + h)) (hhp : h < p)
    (hone : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.not → j = p)
    (hCh : Cn h) (hCp : ∀ j, Cn j → j ≠ p)
    (hCdown : ∀ i j, Cn j → EdgeOwnership.InCone (n + m) C i j → Cn i)
    (hPout : ∀ r, Cn r → C.output = n + m + r → P r)
    (hPread : ∀ r j, Cn r → j < C.gates.length → ¬ Cn j → j ≠ p →
      n + m + r ∈ (NestedCover.gateAt C j).inputs → P r)
    (hPdown : ∀ i r, Cn i → P r → EdgeOwnership.InCone (n + m) C i r → P i) :
    RepSizeAtMost A (s - 1 + ((Finset.range C.gates.length).filter P).card +
      ((3 * n - 6) + (3 * m - 6))) := by
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun u => Fin.elim0 u⟩
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨⟨[], 0⟩, fun _ h => by simp at h, by simp [Circuit.size], fun _ v => Fin.elim0 v⟩
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  let N := n + m
  obtain ⟨gL, hML, hlenL, rL, hbdL, hntL, hevL⟩ :=
    build_slice_loo N 0 n hn1 (by omega) [] (fun _ h => by simp at h)
  obtain ⟨gR, hMR, hlenR, rR, hbdR, hntR, hevR⟩ :=
    build_slice_loo N n m hm1 (by omega) ([] ++ gL) hML
  let gs0 : List Gate := ([] ++ gL) ++ gR
  have hM0 : Monotone2 ⟨gs0, 0⟩ := hMR
  have hlen0 : gs0.length ≤ (3 * n - 6) + (3 * m - 6) := by
    simp only [gs0, List.nil_append, List.length_append]; omega
  let pos0 : ℕ → Rail := fun w => if w < N then .wire w else .ff
  let neg0 : ℕ → Rail := fun w =>
    if h1 : w < n then rL ⟨w, h1⟩
    else if h2 : w - n < m then rR ⟨w - n, h2⟩
    else .tt
  have hneg_bd : ∀ w < N, railBound (N + gs0.length) (neg0 w) := by
    intro w hw
    dsimp only [neg0]
    split_ifs with h1 h2
    · have hb := hbdL ⟨w, h1⟩
      simp only [List.length_nil, Nat.add_zero] at hb
      apply railBound_mono _ hb
      simp only [gs0, List.nil_append, List.length_append]; omega
    · have hb := hbdR ⟨w - n, h2⟩
      apply railBound_mono _ hb
      simp only [gs0, List.length_append]; omega
    · trivial
  have hneg_ntt : ∀ w < N, neg0 w ≠ .tt := by
    intro w hw
    dsimp only [neg0]
    split_ifs with h1 h2
    · exact hntL _
    · exact hntR _
    · exfalso; omega
  have hneg_ev : ∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N →
      evalRail (Circuit.wires ⟨gs0, 0⟩ (oneEach u v)) (neg0 w) = !((oneEach u v).getD w false) := by
    intro u v w hw
    dsimp only [neg0]
    by_cases h1 : w < n
    · simp only [h1, dite_true]
      have hkeepL : ∀ idx < N + ([] ++ gL).length,
          (Circuit.wires ⟨gs0, 0⟩ (oneEach u v)).getD idx false =
          (Circuit.wires ⟨[] ++ gL, 0⟩ (oneEach u v)).getD idx false := by
        intro idx hidx
        exact wires_keep ([] ++ gL) gR (oneEach u v) idx (by rw [oneEach_len]; exact hidx)
      have hbL := hbdL ⟨w, h1⟩
      rw [evalRail_congr hkeepL (by simpa using hbL)]
      rw [hevL (oneEach u v) (oneEach_len u v) ⟨w, h1⟩]
      have hleft := oneEach_getD_left u v ⟨w, h1⟩
      rw [hleft]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      constructor
      · rintro ⟨j, hne, hj⟩
        have hj' := oneEach_getD_left u v j
        simp only [Nat.zero_add] at hj
        rw [hj', decide_eq_true_eq] at hj
        subst hj
        exact hne.symm
      · intro hne
        refine ⟨u, fun h => hne h.symm, ?_⟩
        simp only [Nat.zero_add]
        rw [oneEach_getD_left]
        simp
    · have h2 : w - n < m := by omega
      simp only [h1, h2, dite_false, dite_true]
      have hEqR : Circuit.wires ⟨gs0, 0⟩ (oneEach u v) =
          Circuit.wires ⟨([] ++ gL) ++ gR, 0⟩ (oneEach u v) := rfl
      rw [hEqR, hevR (oneEach u v) (oneEach_len u v) ⟨w - n, h2⟩]
      have hw_eq : w = n + (w - n) := by omega
      conv_rhs => rw [hw_eq]
      rw [oneEach_getD_right u v ⟨w - n, h2⟩]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      constructor
      · rintro ⟨j, hne, hj⟩
        have hj' := oneEach_getD_right u v j
        rw [hj', decide_eq_true_eq] at hj
        subst hj
        exact hne.symm
      · intro hne
        refine ⟨v, fun h => hne h.symm, ?_⟩
        rw [oneEach_getD_right]
        simp
  have hold_len : ∀ (u : Fin n) (v : Fin m) k, k ≤ C.gates.length →
      ((C.gates.take k).foldl wstep (oneEach u v)).length = N + k := by
    intro u v k hk
    rw [foldl_wstep_len, oneEach_len, List.length_take, Nat.min_eq_left hk]
  have hWlen : ∀ (gs : List Gate) (u : Fin n) (v : Fin m),
      (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).length = N + gs0.length + gs.length := by
    intro gs u v
    unfold Circuit.wires
    change ((gs0 ++ gs).foldl wstep (oneEach u v)).length = _
    rw [foldl_wstep_len, oneEach_len, List.length_append]
    omega
  have hkeepG : ∀ (G : List Gate) (x : Gate) (u : Fin n) (v : Fin m) (r : Rail),
      railBound (N + gs0.length + G.length) r →
      evalRail (Circuit.wires ⟨gs0 ++ (G ++ [x]), 0⟩ (oneEach u v)) r =
        evalRail (Circuit.wires ⟨gs0 ++ G, 0⟩ (oneEach u v)) r := by
    intro G x u v r hr
    rw [push]
    exact rail_app _ _ _ (by rw [hWlen G u v]; exact hr)
  have hnewG : ∀ (G : List Gate) (x : Gate) (u : Fin n) (v : Fin m),
      evalRail (Circuit.wires ⟨gs0 ++ (G ++ [x]), 0⟩ (oneEach u v)) (.wire (N + gs0.length + G.length)) =
        x.op.eval (x.inputs.map fun i => (Circuit.wires ⟨gs0 ++ G, 0⟩ (oneEach u v)).getD i false) := by
    intro G x u v
    rw [push]
    exact getD_snoc _ _ _ (hWlen G u v).symm
  have hSim : ∀ k ≤ C.gates.length,
      ∃ (gs : List Gate) (pM dM : ℕ → Rail),
        Monotone2 ⟨gs0 ++ gs, 0⟩ ∧
        gs.length + (if p < k then 1 else 0) ≤ k + ((Finset.range k).filter P).card ∧
        (∀ w < N + k, railBound (N + gs0.length + gs.length) (pM w) ∧ pM w ≠ .tt ∧
          railBound (N + gs0.length + gs.length) (dM w) ∧ dM w ≠ .tt) ∧
        (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + k → (w < N ∨ ¬ (Cn (w - N) ∧ ¬ P (w - N))) →
          evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (pM w) =
            ((C.gates.take k).foldl wstep (oneEach u v)).getD w false) ∧
        (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + k → (w < N ∨ Cn (w - N)) →
          evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (dM w) =
            !((C.gates.take k).foldl wstep (oneEach u v)).getD w false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => .wire w, neg0, by simpa using hM0, by simp, ?_, ?_, ?_⟩
      · intro w hw
        refine ⟨?_, fun h' => Rail.noConfusion h', railBound_mono (by simp) (hneg_bd w (by omega)),
          hneg_ntt w (by omega)⟩
        show w < N + gs0.length + ([] : List Gate).length
        simp only [List.length_nil]; omega
      · intro u v w hw _
        rw [List.take_zero, List.foldl_nil]
        show (Circuit.wires ⟨gs0 ++ [], 0⟩ (oneEach u v)).getD w false = _
        rw [wires_keep gs0 [] (oneEach u v) w (by rw [oneEach_len]; omega)]
        unfold Circuit.wires
        change (gs0.foldl wstep (oneEach u v)).getD w false = _
        rw [foldl_wstep_getD_lt _ _ _ (by rw [oneEach_len]; omega)]
      · intro u v w hw _
        rw [List.take_zero, List.foldl_nil]
        rw [evalRail_congr (fun idx hidx => wires_keep gs0 [] (oneEach u v) idx
          (by rw [oneEach_len]; exact hidx)) (hneg_bd w (by omega))]
        exact hneg_ev u v w (by omega)
    | succ k ih =>
      intro hk1
      have hk : k < C.gates.length := by omega
      obtain ⟨gs, pM, dM, hM, hcnt, hbd, hevP, hevD⟩ := ih (Nat.le_of_lt hk)
      set g := C.gates[k] with hg_def
      have hgk : NestedCover.gateAt C k = g := gateAt_eq hk
      have hg_mem : g ∈ C.gates := List.getElem_mem hk
      have hglen : g.inputs.length ≤ 2 := (hF g hg_mem).2
      have hcard_mono : ((Finset.range k).filter P).card ≤ ((Finset.range (k + 1)).filter P).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
      have hold_next : ∀ (u : Fin n) (v : Fin m), (C.gates.take (k + 1)).foldl wstep (oneEach u v) =
          (C.gates.take k).foldl wstep (oneEach u v) ++
            [g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (oneEach u v)).getD i false)] := by
        intro u v
        rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hold_lt : ∀ (u : Fin n) (v : Fin m) (i : ℕ), ¬ i < N + k →
          ((C.gates.take k).foldl wstep (oneEach u v)).getD i false = false := by
        intro u v i hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hold_len u v k hk.le]; omega)]
        rfl
      have hfinish : ∀ (gs' : List Gate) (pN dN : Rail),
          Monotone2 ⟨gs0 ++ gs', 0⟩ →
          gs'.length + (if p < k + 1 then 1 else 0) ≤ k + 1 + ((Finset.range (k + 1)).filter P).card →
          gs.length ≤ gs'.length →
          (∀ (u : Fin n) (v : Fin m) (r : Rail), railBound (N + gs0.length + gs.length) r →
            evalRail (Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)) r =
              evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) r) →
          railBound (N + gs0.length + gs'.length) pN → pN ≠ .tt →
          railBound (N + gs0.length + gs'.length) dN → dN ≠ .tt →
          (∀ (u : Fin n) (v : Fin m), ¬ (Cn k ∧ ¬ P k) →
            evalRail (Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)) pN =
              g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (oneEach u v)).getD i false)) →
          (∀ (u : Fin n) (v : Fin m), Cn k →
            evalRail (Circuit.wires ⟨gs0 ++ gs', 0⟩ (oneEach u v)) dN =
              !(g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (oneEach u v)).getD i false))) →
          ∃ (gs : List Gate) (pM dM : ℕ → Rail),
            Monotone2 ⟨gs0 ++ gs, 0⟩ ∧
            gs.length + (if p < k + 1 then 1 else 0) ≤ k + 1 + ((Finset.range (k + 1)).filter P).card ∧
            (∀ w < N + (k + 1), railBound (N + gs0.length + gs.length) (pM w) ∧ pM w ≠ .tt ∧
              railBound (N + gs0.length + gs.length) (dM w) ∧ dM w ≠ .tt) ∧
            (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + (k + 1) → (w < N ∨ ¬ (Cn (w - N) ∧ ¬ P (w - N))) →
              evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (pM w) =
                ((C.gates.take (k + 1)).foldl wstep (oneEach u v)).getD w false) ∧
            (∀ (u : Fin n) (v : Fin m) (w : ℕ), w < N + (k + 1) → (w < N ∨ Cn (w - N)) →
              evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (dM w) =
                !((C.gates.take (k + 1)).foldl wstep (oneEach u v)).getD w false) := by
        intro gs' pN dN hM' hcnt' hge hkeep hbP hnP hbD hnD hvP hvD
        refine ⟨gs', fun w => if w = N + k then pN else pM w, fun w => if w = N + k then dN else dM w,
          hM', hcnt', ?_, ?_, ?_⟩
        · intro w hw
          by_cases hwk : w = N + k
          · subst hwk
            simp only [eq_self_iff_true, ite_true]
            exact ⟨hbP, hnP, hbD, hnD⟩
          · simp only [hwk, ite_false]
            obtain ⟨b1, b2, b3, b4⟩ := hbd w (by omega)
            exact ⟨railBound_mono (by omega) b1, b2, railBound_mono (by omega) b3, b4⟩
        · intro u v w hw hc
          rw [hold_next u v]
          by_cases hwk : w = N + k
          · subst hwk
            simp only [eq_self_iff_true, ite_true]
            rw [getD_snoc _ _ _ (hold_len u v k hk.le).symm]
            have hk' : N + k - N = k := by omega
            rw [hk'] at hc
            exact hvP u v (hc.resolve_left (by omega))
          · simp only [hwk, ite_false]
            rw [List.getD_append _ _ _ _ (by rw [hold_len u v k hk.le]; omega)]
            rw [hkeep u v _ (hbd w (by omega)).1]
            exact hevP u v w (by omega) hc
        · intro u v w hw hc
          rw [hold_next u v]
          by_cases hwk : w = N + k
          · subst hwk
            simp only [eq_self_iff_true, ite_true]
            rw [getD_snoc _ _ _ (hold_len u v k hk.le).symm]
            have hk' : N + k - N = k := by omega
            rw [hk'] at hc
            exact hvD u v (hc.resolve_left (by omega))
          · simp only [hwk, ite_false]
            rw [List.getD_append _ _ _ _ (by rw [hold_len u v k hk.le]; omega)]
            rw [hkeep u v _ (hbd w (by omega)).2.2.1]
            exact hevD u v w (by omega) hc
      by_cases hkp : k = p
      · subst hkp
        rw [hgk] at hpop hph
        obtain ⟨rest, hgi⟩ : ∃ rest, g.inputs = (N + h) :: rest := by
          cases hgi : g.inputs with
          | nil => rw [hgi] at hph; simp at hph
          | cons a rest =>
            rw [hgi] at hph
            simp only [List.head?_cons, Option.some.injEq] at hph
            exact ⟨rest, by rw [hph]⟩
        obtain ⟨_, _, b3, b4⟩ := hbd (N + h) (by omega)
        refine hfinish gs (dM (N + h)) .ff hM ?_ le_rfl (fun _ _ _ _ => rfl) b3 b4 trivial
          (fun h' => Rail.noConfusion h') ?_ ?_
        · rw [if_neg (lt_irrefl _)] at hcnt
          rw [if_pos (Nat.lt_succ_self _)]
          omega
        · intro u v _
          rw [hpop, hgi]
          rw [hevD u v (N + h) (by omega) (Or.inr (by simpa using hCh))]
          rfl
        · intro u v hc
          exact absurd rfl (hCp _ hc)
      · have hgop : g.op = .and ∨ g.op = .or := by
          have h1 := (hF g hg_mem).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
          rcases h1 with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
          · exact absurd (hone k hk (by rw [hgk]; exact h1)) hkp
        obtain ⟨bk, hbk⟩ : ∃ b : Bool, ∀ l, g.op.eval l = bval b l := by
          rcases hgop with h1 | h1
          · exact ⟨true, fun l => by rw [h1]; rfl⟩
          · exact ⟨false, fun l => by rw [h1]; rfl⟩
        have hcnt0 : gs.length + (if p < k + 1 then 1 else 0) ≤ k + ((Finset.range k).filter P).card := by
          by_cases hpk : p < k
          · rw [if_pos hpk] at hcnt; rw [if_pos (by omega)]; exact hcnt
          · rw [if_neg hpk] at hcnt; rw [if_neg (by omega)]; exact hcnt
        let getP : ℕ → Rail := fun i => if i < N + k then pM i else .ff
        let getN : ℕ → Rail := fun i => if i < N + k then dM i else .tt
        have hgetP_bd : ∀ i, railBound (N + gs0.length + gs.length) (getP i) := by
          intro i
          by_cases hi : i < N + k
          · simp only [getP, hi, ite_true]; exact (hbd i hi).1
          · simp only [getP, hi, ite_false]; trivial
        have hgetN_bd : ∀ i, railBound (N + gs0.length + gs.length) (getN i) := by
          intro i
          by_cases hi : i < N + k
          · simp only [getN, hi, ite_true]; exact (hbd i hi).2.2.1
          · simp only [getN, hi, ite_false]; trivial
        have hmemk : ∀ i ∈ g.inputs, ¬ i < N → i < N + k →
            EdgeOwnership.InCone (n + m) C (i - N) k := by
          intro i hi hiN hik
          refine (inCone_iff _ _ _ _).2 ⟨hk, i - N, by omega, ?_, Or.inl rfl⟩
          rw [hgk]
          convert hi using 1
          omega
        have hrdP : ¬ (Cn k ∧ ¬ P k) → ∀ (u : Fin n) (v : Fin m), ∀ i ∈ g.inputs,
            evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (getP i) =
              ((C.gates.take k).foldl wstep (oneEach u v)).getD i false := by
          intro hdk u v i hi
          by_cases hik : i < N + k
          · simp only [getP, hik, ite_true]
            apply hevP u v i hik
            by_cases hiN : i < N
            · exact Or.inl hiN
            · right
              rintro ⟨hc, hnp⟩
              have hin := hmemk i hi hiN hik
              by_cases hck : Cn k
              · have hPk : P k := by
                  by_contra h'
                  exact hdk ⟨hck, h'⟩
                exact hnp (hPdown _ _ hc hPk hin)
              · refine hnp (hPread _ k hc hk hck hkp ?_)
                rw [hgk]
                convert hi using 1
                omega
          · simp only [getP, hik, ite_false]
            rw [hold_lt u v i hik]
            rfl
        have hrdD : Cn k → ∀ (u : Fin n) (v : Fin m), ∀ i ∈ g.inputs,
            evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) (getN i) =
              !((C.gates.take k).foldl wstep (oneEach u v)).getD i false := by
          intro hck u v i hi
          by_cases hik : i < N + k
          · simp only [getN, hik, ite_true]
            apply hevD u v i hik
            by_cases hiN : i < N
            · exact Or.inl hiN
            · exact Or.inr (hCdown _ k hck (hmemk i hi hiN hik))
          · simp only [getN, hik, ite_false]
            rw [hold_lt u v i hik]
            rfl
        obtain ⟨pg, hpg⟩ : ∃ x : Gate, x = emitG bk (g.inputs.map getP) := ⟨_, rfl⟩
        obtain ⟨dg, hdg⟩ : ∃ x : Gate, x = emitG (!bk) (g.inputs.map getN) := ⟨_, rfl⟩
        have hpg_mono : pg.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ pg.inputs.length ≤ 2 := by
          rw [hpg]; exact emitG_mono _ _ (by rw [List.length_map]; exact hglen)
        have hdg_mono : dg.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ dg.inputs.length ≤ 2 := by
          rw [hdg]; exact emitG_mono _ _ (by rw [List.length_map]; exact hglen)
        have hpg_val : ∀ (u : Fin n) (v : Fin m) (W' : List Bool),
            (∀ r, railBound (N + gs0.length + gs.length) r →
              evalRail W' r = evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) r) →
            ¬ (Cn k ∧ ¬ P k) →
            pg.op.eval (pg.inputs.map fun i => W'.getD i false) =
              g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (oneEach u v)).getD i false) := by
          intro u v W' hW' hdk
          rw [hpg, emit_eval, hbk, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          show evalRail W' (getP i) = ((C.gates.take k).foldl wstep (oneEach u v)).getD i false
          rw [hW' _ (hgetP_bd i)]
          exact hrdP hdk u v i hi
        have hdg_val : ∀ (u : Fin n) (v : Fin m) (W' : List Bool),
            (∀ r, railBound (N + gs0.length + gs.length) r →
              evalRail W' r = evalRail (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)) r) →
            Cn k →
            dg.op.eval (dg.inputs.map fun i => W'.getD i false) =
              !(g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl wstep (oneEach u v)).getD i false)) := by
          intro u v W' hW' hck
          rw [hdg, emit_eval, hbk, bval_not]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          show evalRail W' (getN i) = !((C.gates.take k).foldl wstep (oneEach u v)).getD i false
          rw [hW' _ (hgetN_bd i)]
          exact hrdD hck u v i hi
        by_cases hck : Cn k
        · by_cases hPk : P k
          · -- dual and primal
            have hc1 : ((Finset.range (k + 1)).filter P).card = ((Finset.range k).filter P).card + 1 := by
              rw [Finset.range_add_one, Finset.filter_insert, if_pos hPk,
                Finset.card_insert_of_notMem (by simp)]
            refine hfinish ((gs ++ [dg]) ++ [pg]) (.wire (N + gs0.length + (gs ++ [dg]).length))
              (.wire (N + gs0.length + gs.length)) ?_ ?_ (by simp) ?_ ?_ (fun h' => Rail.noConfusion h')
              ?_ (fun h' => Rail.noConfusion h') ?_ ?_
            · rw [← List.append_assoc]
              exact mono_push _ _ (by rw [← List.append_assoc]; exact mono_push _ _ hM hdg_mono) hpg_mono
            · simp only [List.length_append, List.length_singleton]; omega
            · intro u v r hr
              rw [hkeepG (gs ++ [dg]) pg u v r (railBound_mono (by simp) hr), hkeepG gs dg u v r hr]
            · show _ < _
              simp only [List.length_append, List.length_singleton]; omega
            · show _ < _
              simp only [List.length_append, List.length_singleton]; omega
            · intro u v _
              rw [hnewG]
              exact hpg_val u v _ (fun r hr => hkeepG gs dg u v r hr) (fun h' => h'.2 hPk)
            · intro u v _
              rw [hkeepG (gs ++ [dg]) pg u v (.wire (N + gs0.length + gs.length)) (by
                show _ < _
                simp only [List.length_append, List.length_singleton]; omega), hnewG]
              exact hdg_val u v _ (fun _ _ => rfl) hck
          · -- dual only
            refine hfinish (gs ++ [dg]) .ff (.wire (N + gs0.length + gs.length)) ?_ ?_ (by simp) ?_
              trivial (fun h' => Rail.noConfusion h') ?_ (fun h' => Rail.noConfusion h') ?_ ?_
            · rw [← List.append_assoc]; exact mono_push _ _ hM hdg_mono
            · simp only [List.length_append, List.length_singleton]; omega
            · intro u v r hr
              exact hkeepG _ _ u v r hr
            · show _ < _
              simp only [List.length_append, List.length_singleton]; omega
            · intro u v hc
              exact absurd ⟨hck, hPk⟩ hc
            · intro u v _
              rw [hnewG]
              exact hdg_val u v _ (fun _ _ => rfl) hck
        · -- primal only
          refine hfinish (gs ++ [pg]) (.wire (N + gs0.length + gs.length)) .ff ?_ ?_ (by simp) ?_
            ?_ (fun h' => Rail.noConfusion h') trivial (fun h' => Rail.noConfusion h') ?_ ?_
          · rw [← List.append_assoc]; exact mono_push _ _ hM hpg_mono
          · simp only [List.length_append, List.length_singleton]; omega
          · intro u v r hr
            exact hkeepG _ _ u v r hr
          · show _ < _
            simp only [List.length_append, List.length_singleton]; omega
          · intro u v _
            rw [hnewG]
            exact hpg_val u v _ (fun _ _ => rfl) (fun h' => hck h'.1)
          · intro u v hc
            exact absurd hc hck
  obtain ⟨gs, pM, dM, hM, hcnt, hbd, hevP, -⟩ := hSim C.gates.length le_rfl
  rw [if_pos hp] at hcnt
  have hsz' : C.gates.length ≤ s := hsz
  have hlenT : (gs0 ++ gs).length ≤ s - 1 + ((Finset.range C.gates.length).filter P).card +
      ((3 * n - 6) + (3 * m - 6)) := by
    rw [List.length_append]; omega
  have hfalse : ∀ (u : Fin n) (v : Fin m),
      (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false = false := by
    intro u v
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · have hl : (gs0 ++ gs).length = gs0.length + gs.length := by simp
      rw [hWlen gs u v]; omega
  have hold_full : ∀ (u : Fin n) (v : Fin m),
      (C.gates.take C.gates.length).foldl wstep (oneEach u v) = C.wires (oneEach u v) := by
    intro u v; rw [List.take_length]; rfl
  by_cases hout : C.output < N + C.gates.length
  · have hc : C.output < N ∨ ¬ (Cn (C.output - N) ∧ ¬ P (C.output - N)) := by
      by_cases hoN : C.output < N
      · exact Or.inl hoN
      · exact Or.inr fun h' => h'.2 (hPout _ h'.1 (by omega))
    obtain ⟨_, hnt, -⟩ := hbd C.output hout
    cases hpo : pM C.output with
    | tt => exact absurd hpo hnt
    | ff =>
      refine ⟨⟨gs0 ++ gs, N + (gs0 ++ gs).length⟩, hM, hlenT, fun u v => ?_⟩
      rw [← hRep u v]
      have h1 := hevP u v C.output hout hc
      rw [hpo, hold_full] at h1
      unfold Circuit.eval
      change (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false = _
      rw [hfalse]
      show false = (C.wires (oneEach u v)).getD C.output false
      rw [← h1]
      rfl
    | wire x =>
      refine ⟨⟨gs0 ++ gs, x⟩, hM, hlenT, fun u v => ?_⟩
      rw [← hRep u v]
      have h1 := hevP u v C.output hout hc
      rw [hpo, hold_full] at h1
      exact h1
  · refine ⟨⟨gs0 ++ gs, N + (gs0 ++ gs).length⟩, hM, hlenT, fun u v => ?_⟩
    rw [← hRep u v]
    unfold Circuit.eval
    change (Circuit.wires ⟨gs0 ++ gs, 0⟩ (oneEach u v)).getD (N + (gs0 ++ gs).length) false = _
    rw [hfalse]
    symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · unfold Circuit.wires
      change (C.gates.foldl wstep (oneEach u v)).length ≤ _
      rw [foldl_wstep_len, oneEach_len]
      omega

end PEqualNP.Outside.L_meta_19154_aux

theorem PEqualNP.Outside.L_meta_19154 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → p < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → h < p → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p) → PEqualNP.Represents.RepSizeAtMost A (s - 1 + ((Finset.range C.gates.length).filter (fun i => (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ ∃ r < C.gates.length, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) ∧ (i = r ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i r) ∧ (C.output = n + m + r ∨ ∃ j < C.gates.length, ¬ (j = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C j h) ∧ j ≠ p ∧ n + m + r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs))).card + ((3 * n - 6) + (3 * m - 6))) := by
  intro n m s A C p h hF hsz hRep hp hpop hph hhp hone
  have hlt := PEqualNP.Outside.L_meta_19154_aux.inCone_lt (n + m) C
  have htr := PEqualNP.Outside.L_meta_19154_aux.inCone_trans (n + m) C
  have hClen : ∀ r, (r = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C r h) → r < C.gates.length := by
    rintro r (rfl | hr)
    · omega
    · have := hlt h r hr; omega
  refine PEqualNP.Outside.L_meta_19154_aux.rep_main n m s A C p h
    (fun i => i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) _ hF hsz hRep hp hpop hph hhp hone
    (Or.inl rfl) ?_ ?_ ?_ ?_ ?_
  · rintro j (rfl | hj)
    · omega
    · have := hlt h j hj; omega
  · rintro i j (rfl | hj) hij
    · exact Or.inr hij
    · exact Or.inr (htr i j hij h hj)
  · intro r hr ho
    exact ⟨hr, r, hClen r hr, hr, Or.inl rfl, Or.inl ho⟩
  · intro r j hr hj hnc hjp hmem
    exact ⟨hr, r, hClen r hr, hr, Or.inl rfl, Or.inr ⟨j, hj, hnc, hjp, hmem⟩⟩
  · rintro i r hi ⟨_, r', hr', hcr', hrr', hexp⟩ hir
    refine ⟨hi, r', hr', hcr', Or.inr ?_, hexp⟩
    rcases hrr' with rfl | hrr'
    · exact hir
    · exact htr i r hir r' hrr'
