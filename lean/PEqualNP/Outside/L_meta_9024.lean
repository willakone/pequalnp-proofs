import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9024_aux

namespace DualB
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def pw (n i : ℕ) : ℕ := if i < n then i else 2 * n + 2 * (i - n)

def nw (n i : ℕ) : ℕ := if i < n then n + i else 2 * n + 2 * (i - n) + 1

def posG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.and, g.inputs.map (pw n)⟩ else ⟨GateOp.or, []⟩
  | GateOp.or => ⟨GateOp.or, (g.inputs.filter (fun i => decide (i < L))).map (pw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.and, []⟩
    | a :: _ => if a < L then ⟨GateOp.and, [nw n a]⟩ else ⟨GateOp.and, []⟩

def negG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.or, g.inputs.map (nw n)⟩ else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, (g.inputs.filter (fun i => decide (i < L))).map (nw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.or, []⟩
    | a :: _ => if a < L then ⟨GateOp.or, [pw n a]⟩ else ⟨GateOp.or, []⟩

def Rel (n : ℕ) (U U' : List Bool) : Prop :=
  ∀ i, i < U.length → U'.getD (pw n i) false = U.getD i false ∧ U'.getD (nw n i) false = !U.getD i false

theorem dm1 : ∀ l : List Bool, (l.map fun b => !b).any id = !(l.all id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_and]

theorem dm2 : ∀ l : List Bool, (l.map fun b => !b).all id = !(l.any id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_or]

theorem any_filter (p : ℕ → Bool) (f : ℕ → Bool) : ∀ ins : List ℕ, (∀ i ∈ ins, p i = false → f i = false) →
    ((ins.filter p).map f).any id = (ins.map f).any id := by
  intro ins
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have iht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.any_cons, iht]
    · have hp' : p a = false := by simpa using hp
      have hf := h a (List.mem_cons_self ..) hp'
      simp only [List.filter_cons, hp', Bool.false_eq_true, if_false, List.map_cons, List.any_cons, iht, hf, id,
        Bool.false_or]

theorem gate_dual (n L : ℕ) (U U' : List Bool) (hL : U.length = L) (hR : Rel n U U') (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (posG n L g).op.eval ((posG n L g).inputs.map fun i => U'.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) ∧
    (negG n L g).op.eval ((negG n L g).inputs.map fun i => U'.getD i false)
      = !(g.op.eval (g.inputs.map fun i => U.getD i false)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  have hinv : ∀ i, ¬ i < L → U.getD i false = false := fun i hi =>
    List.getD_eq_default _ _ (by omega)
  have hmp : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (pw n)).map (fun i => U'.getD i false) = l.map fun i => U.getD i false := by
    intro l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).1
  have hmn : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (nw n)).map (fun i => U'.getD i false)
      = (l.map fun i => U.getD i false).map fun b => !b := by
    intro l hl
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).2
  rcases hop with rfl | rfl | rfl
  · by_cases hall : ins.all (fun i => decide (i < L)) = true
    · have hl : ∀ i ∈ ins, i < L := fun i hi => by simpa using List.all_eq_true.1 hall i hi
      simp only [posG, negG, hall, if_true]
      constructor
      · show ((ins.map (pw n)).map fun i => U'.getD i false).all id = (ins.map fun i => U.getD i false).all id
        rw [hmp ins hl]
      · show ((ins.map (nw n)).map fun i => U'.getD i false).any id = !((ins.map fun i => U.getD i false).all id)
        rw [hmn ins hl, dm1]
    · simp only [posG, negG, hall, if_false]
      have hf : (ins.map fun i => U.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hc
        apply hall
        rw [List.all_eq_true] at hc ⊢
        intro i hi
        by_contra hlt
        have h1 := hc (U.getD i false) (List.mem_map.2 ⟨i, hi, rfl⟩)
        rw [hinv i (by simpa using hlt)] at h1
        exact absurd h1 (by simp)
      constructor
      · show ([] : List Bool).any id = (ins.map fun i => U.getD i false).all id
        rw [hf]; rfl
      · show ([] : List Bool).all id = !((ins.map fun i => U.getD i false).all id)
        rw [hf]; rfl
  · have hl : ∀ i ∈ ins.filter (fun i => decide (i < L)), i < L := fun i hi => by
      simpa using (List.mem_filter.1 hi).2
    have hfa := any_filter (fun i => decide (i < L)) (fun i => U.getD i false) ins
      (fun i _ hp => hinv i (by simpa using hp))
    simp only [posG, negG]
    constructor
    · show (((ins.filter fun i => decide (i < L)).map (pw n)).map fun i => U'.getD i false).any id
        = (ins.map fun i => U.getD i false).any id
      rw [hmp _ hl, hfa]
    · show (((ins.filter fun i => decide (i < L)).map (nw n)).map fun i => U'.getD i false).all id
        = !((ins.map fun i => U.getD i false).any id)
      rw [hmn _ hl, dm2, hfa]
  · cases ins with
    | nil =>
      simp only [posG, negG]
      exact ⟨rfl, rfl⟩
    | cons a t =>
      by_cases ha : a < L
      · simp only [posG, negG, ha, if_true]
        have h1 := hR a (by rw [hL]; exact ha)
        constructor
        · show (U'.getD (nw n a) false && true) = !(U.getD a false)
          rw [h1.2, Bool.and_true]
        · show (U'.getD (pw n a) false || false) = !!(U.getD a false)
          rw [h1.1, Bool.or_false, Bool.not_not]
      · simp only [posG, negG, ha, if_false]
        have h0 := hinv a ha
        constructor
        · show true = !(U.getD a false)
          rw [h0]; rfl
        · show false = !!(U.getD a false)
          rw [h0]; rfl

def dual (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => posG n L g :: negG n L g :: dual n (L + 1) t

theorem dual_len (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (dual n L gs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp only [dual, List.length_cons, ih]; omega

theorem pn_ok (n L : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ((posG n L g).op = GateOp.and ∨ (posG n L g).op = GateOp.or) ∧ (posG n L g).inputs.length ≤ 2 ∧
    ((negG n L g).op = GateOp.and ∨ (negG n L g).op = GateOp.or) ∧ (negG n L g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  simp only at hlen
  have hfl := List.length_filter_le (fun i => decide (i < L)) ins
  cases op with
  | and => simp only [posG, negG]; split_ifs <;> simp <;> omega
  | or => simp only [posG, negG]; simp; omega
  | not =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | mod m =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | maj =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp

theorem dual_ok (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ dual n L gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro L _ g hg; simp [dual] at hg
  | cons g0 t ih =>
    intro L h g hg
    simp only [dual, List.mem_cons] at hg
    have hp := pn_ok n L g0 (h g0 (List.mem_cons_self ..))
    rcases hg with rfl | rfl | hg
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ih (L + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) g hg

theorem dual_sim (n : ℕ) : ∀ (gs : List Gate) (L : ℕ) (U U' : List Bool), U.length = L → n ≤ L →
    U'.length = 2 * n + 2 * (L - n) → Rel n U U' →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    Rel n (wf gs U) (wf (dual n L gs) U') := by
  intro gs
  induction gs with
  | nil => intro L U U' _ _ _ hR _; exact hR
  | cons g t ih =>
    intro L U U' hL hn hL' hR hop
    have hpl : ∀ i, i < L → pw n i < U'.length ∧ nw n i < U'.length := by
      intro i hi
      unfold pw nw
      constructor <;> split_ifs <;> omega
    have hg := gate_dual n L U U' hL hR g (hop g (List.mem_cons_self ..))
    generalize hv : g.op.eval (g.inputs.map fun i => U.getD i false) = v at hg
    have hR1 : Rel n U (U' ++ [v]) := by
      intro i hi
      have := hpl i (by omega)
      rw [getD_snoc_lt U' _ _ this.1, getD_snoc_lt U' _ _ this.2]
      exact hR i hi
    have hg2 := gate_dual n L U _ hL hR1 g (hop g (List.mem_cons_self ..))
    rw [hv] at hg2
    show Rel n (wf (g :: t) U) (wf (posG n L g :: negG n L g :: dual n (L + 1) t) U')
    rw [wf_cons, wf_cons, wf_cons, hv, hg.1, hg2.2]
    refine ih (L + 1) _ _ (by simp [hL]) (by omega) (by simp [hL']; omega) ?_
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    have hi' : i < L + 1 := by simpa [hL] using hi
    by_cases hil : i < L
    · have h12 := hpl i hil
      constructor
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.1,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).1
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.2,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).2
    · have hie : i = L := by omega
      subst hie
      have e1 : pw n i = U'.length := by unfold pw; rw [if_neg (by omega)]; omega
      have e2 : nw n i = (U' ++ [v]).length := by
        unfold nw; rw [if_neg (by omega), List.length_append]; simp; omega
      constructor
      · rw [e1, getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; simp), getD_snoc_eq, ← hL, getD_snoc_eq]
      · rw [e2, getD_snoc_eq, ← hL, getD_snoc_eq]


theorem dualRail : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  intro n s f ⟨C, hF, hs, hf⟩
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := fun g hg => by
    simpa using (hF g hg).1
  refine ⟨⟨dual n n C.gates, if C.output < n + C.gates.length then pw n C.output else 2 * n + 2 * C.gates.length⟩,
    fun g hg => ?_, ?_, fun x => ?_⟩
  · have := dual_ok n C.gates n (fun g' hg' => (hF g' hg').2) g hg
    exact ⟨by rcases this.1 with h | h <;> simp [h], this.2⟩
  · show (dual n n C.gates).length ≤ 2 * s
    rw [dual_len]
    have : C.gates.length ≤ s := hs
    omega
  · have hR0 : Rel n (List.ofFn x) (List.ofFn x ++ List.ofFn fun i => !x i) := by
      intro i hi
      have hi' : i < n := by simpa using hi
      unfold pw nw
      rw [if_pos hi', if_pos hi', List.getD_append _ _ _ _ (by simpa using hi'),
        List.getD_append_right _ _ _ _ (by simp)]
      have e1 := getD_ofFn x ⟨i, hi'⟩
      have e2 := getD_ofFn (fun i => !x i) ⟨i, hi'⟩
      simp only at e1 e2
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [e1, e2]
      simp
    have hR := dual_sim n C.gates n (List.ofFn x) _ (by simp) le_rfl (by simp; omega) hR0 hop
    rw [← hf x]
    show (wf (dual n n C.gates) (List.ofFn x ++ List.ofFn fun i => !x i)).getD _ false
      = (wf C.gates (List.ofFn x)).getD C.output false
    by_cases ho : C.output < n + C.gates.length
    · rw [if_pos ho]
      exact (hR C.output (by rw [wf_len]; simpa using ho)).1
    · rw [if_neg ho, List.getD_eq_default _ _ (by rw [wf_len, dual_len]; simp; omega),
        List.getD_eq_default _ _ (by rw [wf_len]; simp; omega)]
end DualB


namespace LitA
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def sg (N a i : ℕ) : ℕ := if i < N then i else i + a

def rgS (N a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg N a)⟩

theorem keyS (N : ℕ) (x A G : List Bool) (hx : x.length = N) (i : ℕ) :
    (x ++ G).getD i false = (x ++ A ++ G).getD (sg N A.length i) false := by
  unfold sg
  by_cases hi : i < N
  · rw [if_pos hi, List.getD_append _ _ _ _ (by omega), List.append_assoc,
      List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp
    omega

theorem simSh (N : ℕ) (x A : List Bool) (hx : x.length = N) : ∀ (gs : List Gate) (G : List Bool),
    ∃ G' : List Bool, G'.length = G.length + gs.length ∧ wf gs (x ++ G) = x ++ G' ∧
      wf (gs.map (rgS N A.length)) (x ++ A ++ G) = x ++ A ++ G' := by
  intro gs
  induction gs with
  | nil => intro G; exact ⟨G, rfl, rfl, rfl⟩
  | cons g gs ih =>
    intro G
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (rgS N A.length g).op.eval ((rgS N A.length g).inputs.map fun i => (x ++ A ++ G).getD i false)
        = g.op.eval (g.inputs.map fun i => (x ++ G).getD i false) := by
      show g.op.eval ((g.inputs.map (sg N A.length)).map fun i => (x ++ A ++ G).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (keyS N x A G hx a).symm
    rw [hv, List.append_assoc x G, List.append_assoc (x ++ A) G]
    obtain ⟨G', h1, h2, h3⟩ := ih (G ++ [g.op.eval (g.inputs.map fun i => (x ++ G).getD i false)])
    exact ⟨G', by simp at h1 ⊢; omega, h2, h3⟩

theorem gof {α : Type} (n : ℕ) (f : Fin n → α) (i : ℕ) (d : α) (h : i < n) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]

theorem app_read : ∀ (E : List Gate) (U V : List Bool), (∀ g ∈ E, ∀ a ∈ g.inputs, a < U.length) →
    wf E (U ++ V) = U ++ V ++ E.map (fun g => g.op.eval (g.inputs.map fun a => U.getD a false)) := by
  intro E
  induction E with
  | nil => intro U V _; simp [wf]
  | cons g E ih =>
    intro U V h
    rw [wf_cons, List.append_assoc U V, ih U _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    have hv : g.op.eval (g.inputs.map fun i => (U ++ V).getD i false)
        = g.op.eval (g.inputs.map fun a => U.getD a false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact List.getD_append _ _ _ _ (h g (List.mem_cons_self ..) a ha)
    rw [hv]
    simp

theorem split_ex (k : ℕ) (P : ℕ → Prop) :
    (∃ t < 2 ^ (k + 1), P t) ↔ (∃ t < 2 ^ k, P t) ∨ ∃ t < 2 ^ k, P (2 ^ k + t) := by
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  constructor
  · rintro ⟨t, ht, hP⟩
    by_cases h : t < 2 ^ k
    · exact Or.inl ⟨t, h, hP⟩
    · refine Or.inr ⟨t - 2 ^ k, by omega, ?_⟩
      have : 2 ^ k + (t - 2 ^ k) = t := by omega
      rw [this]
      exact hP
  · rintro (⟨t, ht, hP⟩ | ⟨t, ht, hP⟩)
    · exact ⟨t, by omega, hP⟩
    · exact ⟨2 ^ k + t, by omega, hP⟩

def Lit (N o k : ℕ) (gs : List Gate) (w : ℕ → Bool → ℕ) (tw : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i < k, ∀ b, w i b < N + gs.length) ∧ tw < N + gs.length ∧
  ∀ x : List Bool, x.length = N →
    (∀ i < k, ∀ b, (wf gs x).getD (w i b) false
      = decide (∃ t < 2 ^ k, t.testBit i = b ∧ x.getD (o + t) false = true)) ∧
    (wf gs x).getD tw false = decide (∃ t < 2 ^ k, x.getD (o + t) false = true)

def orG (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

theorem orG_eval (a b : ℕ) (f : ℕ → Bool) :
    (orG a b).op.eval ((orG a b).inputs.map f) = (f a || f b) := by
  simp [orG, GateOp.eval]

theorem lit : ∀ (k o N : ℕ), o + 2 ^ k ≤ N → ∃ (gs : List Gate) (w : ℕ → Bool → ℕ) (tw : ℕ),
    Lit N o k gs w tw ∧ gs.length + 2 * k + 3 ≤ 3 * 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro o N h
    refine ⟨[], fun _ _ => 0, o, ⟨fun g hg => by simp at hg, fun i hi => by omega, by simp at h ⊢; omega,
      fun x hx => ⟨fun i hi => by omega, ?_⟩⟩, by simp⟩
    show x.getD o false = decide (∃ t < 2 ^ 0, x.getD (o + t) false = true)
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    constructor
    · intro hh
      exact ⟨0, by simp, by simpa using hh⟩
    · rintro ⟨t, ht, hx'⟩
      have ht0 : t = 0 := by simpa using ht
      subst ht0
      simpa using hx'
  | succ k ih =>
    intro o N h
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    rw [hp] at h
    obtain ⟨P, w1, t1, ⟨hP1, hP2, hP3, hP4⟩, hPl⟩ := ih o N
      (Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) o) h)
    obtain ⟨Q, w2, t2, ⟨hQ1, hQ2, hQ3, hQ4⟩, hQl⟩ := ih (o + 2 ^ k) N (by rw [Nat.add_assoc]; exact h)
    let E : List Gate := List.ofFn (fun j : Fin (2 * k + 1) =>
      if j.val < 2 * k then orG (w1 (j.val / 2) (decide (j.val % 2 = 1))) (sg N P.length (w2 (j.val / 2) (decide (j.val % 2 = 1))))
      else orG t1 (sg N P.length t2))
    let base : ℕ := N + P.length + Q.length
    refine ⟨P ++ Q.map (rgS N P.length) ++ E,
      fun i b => if i < k then base + (2 * i + (if b then 1 else 0)) else (if b then sg N P.length t2 else t1),
      base + 2 * k, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact hP1 g hg
        · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          exact ⟨(hQ1 g0 hg0).1, by simpa [rgS] using (hQ1 g0 hg0).2⟩
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        dsimp only
        split_ifs <;> exact ⟨Or.inr rfl, le_refl 2⟩
    · intro i hi b
      simp only [List.length_append, List.length_map, List.length_ofFn, E, base]
      split_ifs
      · omega
      · omega
      · unfold sg; split_ifs <;> omega
      · omega
    · simp only [List.length_append, List.length_map, List.length_ofFn, E, base]
      omega
    · intro x hx
      obtain ⟨A, hA1, hA2, _⟩ := simSh N x [] hx P []
      rw [List.append_nil] at hA2
      have hA1' : A.length = P.length := by simpa using hA1
      obtain ⟨B, hB1, hB2, hB3⟩ := simSh N x A hx Q []
      rw [List.append_nil] at hB2 hB3
      have hB1' : B.length = Q.length := by simpa using hB1
      rw [hA1'] at hB3
      have hUlen : (x ++ A ++ B).length = base := by simp [base]; omega
      have hold1 : ∀ p, p < N + P.length → (x ++ A ++ B).getD p false = (wf P x).getD p false := by
        intro p hp'
        rw [hA2, List.getD_append _ _ _ _ (by simp; omega)]
      have hold2 : ∀ q, (x ++ A ++ B).getD (sg N P.length q) false = (wf Q x).getD q false := by
        intro q
        rw [hB2]
        have := keyS N x A B hx q
        rw [hA1'] at this
        exact this.symm
      have hEin : ∀ g ∈ E, ∀ a ∈ g.inputs, a < (x ++ A ++ B).length := by
        intro g hg a ha
        rw [hUlen]
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        dsimp only at ha
        split_ifs at ha with hj
        · simp only [orG, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hP2 (j.val / 2) (by omega) (decide (j.val % 2 = 1)); omega
          · have := hQ2 (j.val / 2) (by omega) (decide (j.val % 2 = 1)); unfold sg; split_ifs <;> omega
        · simp only [orG, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · omega
          · unfold sg; split_ifs <;> omega
      have hW : wf (P ++ Q.map (rgS N P.length) ++ E) x
          = x ++ A ++ B ++ E.map (fun g => g.op.eval (g.inputs.map fun a => (x ++ A ++ B).getD a false)) := by
        rw [wf_append, wf_append, hA2, hB3]
        have := app_read E (x ++ A ++ B) [] hEin
        rw [List.append_nil] at this
        exact this
      have hnew : ∀ j (hj : j < 2 * k + 1), (wf (P ++ Q.map (rgS N P.length) ++ E) x).getD (base + j) false
          = (if j < 2 * k then
              ((wf P x).getD (w1 (j / 2) (decide (j % 2 = 1))) false || (wf Q x).getD (w2 (j / 2) (decide (j % 2 = 1))) false)
            else ((wf P x).getD t1 false || (wf Q x).getD t2 false)) := by
        intro j hj
        rw [hW, List.getD_append_right _ _ _ _ (by omega), hUlen, Nat.add_sub_cancel_left]
        simp only [E, List.map_ofFn]
        rw [gof _ _ _ _ hj]
        simp only [Function.comp]
        split_ifs with hj2
        · have := hP2 (j / 2) (by omega) (decide (j % 2 = 1))
          rw [orG_eval, hold1 _ this, hold2]
        · rw [orG_eval, hold1 _ hP3, hold2]
      have hkeep : ∀ p, p < base → (wf (P ++ Q.map (rgS N P.length) ++ E) x).getD p false
          = (x ++ A ++ B).getD p false := by
        intro p hp'
        rw [hW, List.getD_append _ _ _ _ (by omega)]
      obtain ⟨hPa, hPb⟩ := hP4 x hx
      obtain ⟨hQa, hQb⟩ := hQ4 x hx
      constructor
      · intro i hi b
        dsimp only
        by_cases hik : i < k
        · rw [if_pos hik]
          have hj : 2 * i + (if b then 1 else 0) < 2 * k + 1 := by split_ifs <;> omega
          rw [hnew _ hj, if_pos (by split_ifs <;> omega)]
          have e1 : (2 * i + (if b then 1 else 0)) / 2 = i := by split_ifs <;> omega
          have e2 : decide ((2 * i + (if b then 1 else 0)) % 2 = 1) = b := by cases b <;> simp <;> omega
          rw [e1, e2, hPa i hik b, hQa i hik b]
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_iff]
          rw [split_ex k (fun t => t.testBit i = b ∧ x.getD (o + t) false = true)]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨t, ht, hb, hx'⟩
            exact ⟨t, ht, by rw [Nat.testBit_two_pow_add_gt hik]; exact hb, by rw [← Nat.add_assoc]; exact hx'⟩
          · rintro ⟨t, ht, hb, hx'⟩
            exact ⟨t, ht, by rw [Nat.testBit_two_pow_add_gt hik] at hb; exact hb, by rw [Nat.add_assoc]; exact hx'⟩
        · have hie : i = k := by omega
          subst hie
          rw [if_neg hik]
          rw [Bool.eq_iff_iff, decide_eq_true_iff,
            split_ex i (fun t => t.testBit i = b ∧ x.getD (o + t) false = true)]
          cases b with
          | false =>
            simp only [Bool.false_eq_true, if_false]
            rw [hkeep t1 (by omega), hold1 t1 hP3, hPb, decide_eq_true_iff]
            constructor
            · rintro ⟨t, ht, hx'⟩
              exact Or.inl ⟨t, ht, Nat.testBit_lt_two_pow ht, hx'⟩
            · rintro (⟨t, ht, _, hx'⟩ | ⟨t, ht, hb, _⟩)
              · exact ⟨t, ht, hx'⟩
              · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht] at hb
                simp at hb
          | true =>
            simp only [if_true]
            rw [hkeep _ (by unfold sg; split_ifs <;> omega), hold2 t2, hQb, decide_eq_true_iff]
            constructor
            · rintro ⟨t, ht, hx'⟩
              exact Or.inr ⟨t, ht, by rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht]; rfl,
                by rw [← Nat.add_assoc]; exact hx'⟩
            · rintro (⟨t, ht, hb, _⟩ | ⟨t, ht, _, hx'⟩)
              · rw [Nat.testBit_lt_two_pow ht] at hb
                simp at hb
              · exact ⟨t, ht, by rw [Nat.add_assoc]; exact hx'⟩
      · rw [hnew (2 * k) (by omega), if_neg (by omega), hPb, hQb, Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff]
        rw [split_ex k (fun t => x.getD (o + t) false = true)]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨t, ht, hx'⟩
          exact ⟨t, ht, by rw [← Nat.add_assoc]; exact hx'⟩
        · rintro ⟨t, ht, hx'⟩
          exact ⟨t, ht, by rw [Nat.add_assoc]; exact hx'⟩
    · simp only [List.length_append, List.length_map, List.length_ofFn, E]
      have e3 : 3 * 2 ^ (k + 1) = 3 * 2 ^ k + 3 * 2 ^ k := by rw [pow_succ]; ring
      rw [e3]
      omega

end LitA

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp only [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem run_read (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])).getD i false = _
    rw [ih _ (by simp only [List.length_append]; omega), List.getD_append _ _ _ _ hi]

private theorem read_tail (a t : List Bool) (i : ℕ) :
    (a ++ t).getD (a.length + i) false = t.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private theorem read_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

private theorem mono_append {gs hs : List Gate}
    (hg : Monotone2 (⟨gs, 0⟩ : Circuit)) (hh : Monotone2 (⟨hs, 0⟩ : Circuit)) :
    Monotone2 (⟨gs ++ hs, 0⟩ : Circuit) := by
  intro g h
  exact (List.mem_append.mp h).elim (hg g) (hh g)

private def liftWire (n base limit : ℕ) (w : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then w ⟨i, h⟩ else base + min (i - n) limit

private def liftGate (n base limit : ℕ) (w : Fin n → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftWire n base limit w)⟩

private theorem run_lift {n base limit : ℕ} {w : Fin n → ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = base) (hw : ∀ i, w i < base)
    (hread : ∀ i, y.getD (w i) false = x.getD i.val false)
    (gs : List Gate) (t : List Bool) (ht : t.length + gs.length ≤ limit) (i : ℕ) :
    (run (gs.map (liftGate n base limit w)) (y ++ t)).getD (liftWire n base limit w i) false =
      (run gs (x ++ t)).getD i false := by
  have reads (t : List Bool) (hlen : t.length ≤ limit) (j : ℕ) :
      (y ++ t).getD (liftWire n base limit w j) false = (x ++ t).getD j false := by
    unfold liftWire
    split
    · rename_i hj
      rw [List.getD_append _ _ _ _ (hy ▸ hw ⟨j, hj⟩),
        List.getD_append _ _ _ _ (hx ▸ hj)]
      exact hread ⟨j, hj⟩
    · rename_i hj
      rw [← hy, read_tail, List.getD_append_right _ _ _ _ (by omega), hx]
      by_cases h : j - n ≤ limit
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
  induction gs generalizing t with
  | nil => exact reads t (by simpa using ht) i
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun j => (x ++ t).getD j false)
    have ht' : t.length ≤ limit := by omega
    have hz : g.op.eval (g.inputs.map ((fun j => (y ++ t).getD j false) ∘
        liftWire n base limit w)) = z := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro j _
      exact reads t ht' j
    change (run (gs.map (liftGate n base limit w))
      ((y ++ t) ++ [g.op.eval (((g.inputs.map (liftWire n base limit w)).map
        fun j => (y ++ t).getD j false))])).getD _ false =
        (run gs ((x ++ t) ++ [z])).getD i false
    simp only [List.map_map, hz, List.append_assoc]
    apply ih (t ++ [z])
    simp only [List.length_append, List.length_cons, List.length_nil] at *
    omega

private theorem tableIndex_decodes (k u : ℕ) (hu : u < 2 ^ k) :
    tableIndex (fun i : Fin k => u.testBit i) = u := by
  induction k generalizing u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    simp [tableIndex, hz]
  | succ k ih =>
    have hd : u / 2 < 2 ^ k := by
      rw [pow_succ] at hu
      omega
    unfold tableIndex
    rw [Fin.sum_univ_succ]
    have hsum : (∑ i : Fin k, if u.testBit (i.succ.val) = true then 2 ^ (i.succ.val) else 0) =
        2 * tableIndex (fun i : Fin k => (u / 2).testBit i) := by
      rw [tableIndex, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, ← Nat.testBit_div_two, pow_succ]
      split <;> simp [Nat.mul_comm]
    rw [hsum, ih _ hd]
    simp only [Fin.val_zero, pow_zero, Nat.testBit_zero, decide_eq_true_eq]
    split <;> omega

private def joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) : Fin (k + l) → α :=
  Fin.addCases f g

private theorem ofFn_joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) :
    List.ofFn (joinFin f g) = List.ofFn f ++ List.ofFn g := by
  rw [List.ofFn_add]
  have hl (i : Fin k) : joinFin f g (Fin.castLE (Nat.le_add_right k l) i) = f i :=
    Fin.addCases_left i
  have hr (i : Fin l) : joinFin f g (Fin.natAdd k i) = g i := Fin.addCases_right i
  simp only [hl, hr]

private theorem bitGraph {k l : ℕ} (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) :
    adjFun A (joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)) =
      A u v := by
  simp only [adjFun, joinFin, Fin.addCases_left, Fin.addCases_right,
    tableIndex_decodes k u.val u.isLt, tableIndex_decodes l v.val v.isLt]
  congr 1
  · apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt
  · apply Fin.ext
    exact Nat.mod_eq_of_lt v.isLt

private theorem buildEnc (k o base : ℕ) (hob : o + 2 ^ k ≤ base) :
    ∃ (gs : List Gate) (w : Fin k → Bool → ℕ),
      Monotone2 (⟨gs, 0⟩ : Circuit) ∧ gs.length ≤ 3 * 2 ^ k ∧
      (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : Fin (2 ^ k)), x.length = base →
        (∀ j < 2 ^ k, x.getD (o + j) false = decide (j = u.val)) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.val.testBit i = b) := by
  obtain ⟨gs, w, tw, ⟨h1, h2, _, h4⟩, hl⟩ := LitA.lit k o base hob
  refine ⟨gs, fun i b => w i.val b,
    fun g hg => ⟨by rcases (h1 g hg).1 with h | h <;> simp [h], (h1 g hg).2⟩, by omega,
    fun i b => h2 i.val i.isLt b, ?_⟩
  intro x u hx hval i b
  have := (h4 x hx).1 i.val i.isLt b
  change (LitA.wf gs x).getD (w i.val b) false = _
  rw [this, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, hb, hx'⟩
    rw [hval t ht, decide_eq_true_iff] at hx'
    rw [← hx']
    exact hb
  · intro hb
    exact ⟨u.val, u.isLt, hb, by rw [hval u.val u.isLt]; simp⟩

private theorem assemble (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : HasLitSize (k + l) (adjFun A) s) :
    RepSizeAtMost A (s + 3 * 2 ^ k + 3 * 2 ^ l) := by
  obtain ⟨C, hCm, hCs, hCe⟩ := h
  let base : ℕ := 2 ^ k + 2 ^ l
  obtain ⟨gsL, wL, hmL, hsL, hwL, heL⟩ :=
    buildEnc k 0 base (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)
  obtain ⟨gsR, wR, hmR, hsR, hwR, heR⟩ :=
    buildEnc l (2 ^ k) (base + gsL.length) (Nat.le_add_right (2 ^ k + 2 ^ l) gsL.length)
  let endL := base + gsL.length
  let endR := endL + gsR.length
  let w (b : Bool) := joinFin (fun i => wL i b) (fun j => wR j b)
  let litW := joinFin (w true) (w false)
  let n := (k + l) + (k + l)
  let gs := C.gates.map (liftGate n endR C.gates.length litW)
  have hgm : Monotone2 (⟨gs, 0⟩ : Circuit) := by
    intro g hg
    change g ∈ C.gates.map (liftGate n endR C.gates.length litW) at hg
    obtain ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hg
    rw [← hEq]
    simpa only [liftGate, List.length_map] using hCm orig hOrig
  refine ⟨⟨gsL ++ gsR ++ gs, liftWire n endR C.gates.length litW C.output⟩,
    mono_append (mono_append hmL hmR) hgm, ?_, ?_⟩
  · change C.gates.length ≤ s at hCs
    simp only [Circuit.size, List.length_append, gs, List.length_map]
    omega
  intro u v
  let a := oneEach u v
  let aL := run gsL a
  let aR := run gsR aL
  have ha : a.length = base := by simp [a, base, oneEach]
  have haL : aL.length = endL := by simp only [aL, run_length, ha, endL]
  have haR : aR.length = endR := by simp only [aR, run_length, haL, endR]
  have inL (j : ℕ) (hj : j < 2 ^ k) : a.getD (0 + j) false = decide (j = u.val) := by
    rw [Nat.zero_add]
    have hleft : j < (List.ofFn (fun i : Fin (2 ^ k) => decide (i = u))).length := by simp [hj]
    simp only [a, oneEach]
    rw [List.getD_append _ _ _ _ hleft]
    exact (read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff)
  have inR (j : ℕ) (hj : j < 2 ^ l) : aL.getD (2 ^ k + j) false = decide (j = v.val) := by
    change (run gsL a).getD (2 ^ k + j) false = _
    rw [run_read gsL _ (by rw [ha]; dsimp [base]; omega)]
    have ht := read_tail (List.ofFn fun i : Fin (2 ^ k) => decide (i = u))
      (List.ofFn fun i : Fin (2 ^ l) => decide (i = v)) j
    simp only [List.length_ofFn] at ht
    exact ht.trans ((read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff))
  let x := joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)
  have hwl (i : Fin k) (b : Bool) : wL i b < aL.length := haL ▸ hwL i b
  have hbound₁ (i : Fin (k + l)) (b : Bool) : w b i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hb := hwL j b
      simp only [w, joinFin, Fin.addCases_left, endR, endL]
      omega
    · simpa only [w, joinFin, Fin.addCases_right, endR, endL] using hwR j b
  have hbound (i : Fin n) : litW i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [litW, joinFin, Fin.addCases_left] using hbound₁ j true
    · simpa only [litW, joinFin, Fin.addCases_right] using hbound₁ j false
  have hlit (i : Fin (k + l)) (b : Bool) : aR.getD (w b i) false = decide (x i = b) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [w, x, joinFin, Fin.addCases_left, aR]
      rw [run_read gsR _ (hwl j b)]
      exact heL a u ha inL j b
    · simp only [w, x, joinFin, Fin.addCases_right]
      exact heR aL v haL inR j b
  let litX := joinFin x (fun i => !x i)
  have hx : List.ofFn litX = List.ofFn x ++ List.ofFn (fun i => !x i) := ofFn_joinFin _ _
  have hread (i : Fin n) : aR.getD (litW i) false = (List.ofFn litX).getD i.val false := by
    rw [read_ofFn]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [litW, litX, joinFin, Fin.addCases_left, hlit]
      cases x j <;> rfl
    · simp only [litW, litX, joinFin, Fin.addCases_right, hlit]
      cases x j <;> rfl
  change (run (gsL ++ gsR ++ gs) a).getD _ false = A u v
  simp only [run_append]
  change (run gs aR).getD _ false = A u v
  have hlift := run_lift (limit := C.gates.length) (x := List.ofFn litX) (y := aR)
    List.length_ofFn haR hbound hread C.gates [] (by simp) C.output
  simp only [List.append_nil] at hlift
  rw [hlift]
  change C.eval (List.ofFn litX) = A u v
  rw [hx, hCe]
  exact bitGraph A u v


theorem main (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s) :
    PEqualNP.Represents.RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) :=
  assemble k l (2 * s) A (DualB.dualRail (k + l) s _ h)

theorem poly_le (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [one_pow, mul_one]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem exp_beats (M d K : ℕ) : ∃ k, K ≤ k ∧ 1 ≤ k ∧ M * (2 * k) ^ d ≤ 2 ^ k := by
  have hT := tendsto_pow_const_div_const_pow_of_one_lt d (r := (2 : ℝ)) one_lt_two
  have hB : (0 : ℝ) < 1 / ((M : ℝ) * 2 ^ d + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hB))
  refine ⟨max K (max N 1), le_max_left _ _, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  set k := max K (max N 1)
  have hk := hN k (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hpos : (0 : ℝ) < (M : ℝ) * 2 ^ d + 1 := by positivity
  rw [div_lt_div_iff₀ h2 hpos, one_mul] at hk
  have hR : ((M * (2 * k) ^ d : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast hR

theorem len_eq (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (x : List Bool) (k : ℕ) :
    ∀ m, m = k → PEqualNP.Represents.adjFun (k := m) (l := m) (A m) (fun i => x.getD i false) =
      PEqualNP.Represents.adjFun (k := k) (l := k) (A k) (fun i => x.getD i false) := by
  intro m hm
  subst hm
  rfl

theorem main24 (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (c K : ℕ) (hc : 0 < c)
    (hA : ∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) ((6 + c) * 2 ^ k))
    (hNP : {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP) :
    ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hsub
  obtain ⟨p, hp⟩ := hsub hNP
  obtain ⟨k, hKk, hk1, hbig⟩ := exp_beats (2 * p.eval 1) p.natDegree K
  obtain ⟨C, hg, hs, hdec⟩ := hp (k + k)
  have hfun : PEqualNP.MetaComplexity.HasCircuitSize (k + k) (PEqualNP.Represents.adjFun (A k)) (p.eval ((k + k : ℕ) : ℕ)) := by
    refine ⟨C, hg, hs, fun y => ?_⟩
    have hlen : (List.ofFn y).length = k + k := List.length_ofFn
    have hd := hdec (List.ofFn y) hlen
    have hm : (List.ofFn y).length / 2 = k := by rw [hlen]; omega
    have hy : (fun i : Fin (k + k) => (List.ofFn y).getD i false) = y := by
      funext i
      simp [List.getD_eq_getElem?_getD]
    apply Bool.eq_iff_iff.mpr
    rw [hd]
    change (Even (List.ofFn y).length ∧ _) ↔ _
    rw [len_eq A (List.ofFn y) k _ hm, hy, hlen]
    exact ⟨fun h => h.2, fun h => ⟨⟨k, rfl⟩, h⟩⟩
  obtain ⟨D, hDm, hDs, hDr⟩ := main k k _ (A k) hfun
  apply hA k hKk
  refine ⟨D, hDm, le_trans hDs ?_, hDr⟩
  have hpe := poly_le p (k + k) (by omega)
  have h2k : k + k = 2 * k := by omega
  rw [h2k] at hpe
  have hc2 : 2 ^ k ≤ c * 2 ^ k := Nat.le_mul_of_pos_left _ hc
  have : 2 * p.eval ((k + k : ℕ) : ℕ) ≤ 2 ^ k := by
    rw [h2k]
    calc 2 * p.eval (2 * k) ≤ 2 * (p.eval 1 * (2 * k) ^ p.natDegree) := Nat.mul_le_mul_left 2 hpe
      _ = 2 * p.eval 1 * (2 * k) ^ p.natDegree := by ring
      _ ≤ 2 ^ k := hbig
  nlinarith

end PEqualNP.Outside.L_meta_9024_aux

theorem PEqualNP.Outside.L_meta_9024 : ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (c K : ℕ), 0 < c → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) ((6 + c) * 2 ^ k)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  exact PEqualNP.Outside.L_meta_9024_aux.main24
