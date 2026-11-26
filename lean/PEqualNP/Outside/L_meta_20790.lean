import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20790_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def chain (b a : ℕ) : List ℕ → List Gate
  | [] => []
  | c :: L => ⟨GateOp.or, [a, c]⟩ :: chain (b + 1) b L

def last (b a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => last (b + 1) b L

theorem chain_good (b a : ℕ) (L : List ℕ) :
    ∀ g ∈ chain b a L, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction L generalizing b a with
  | nil => simp [chain]
  | cons c L ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_len (b a : ℕ) (L : List ℕ) : (chain b a L).length = L.length := by
  induction L generalizing b a with
  | nil => rfl
  | cons c L ih => simp [chain, ih]

theorem pre_stp (x : List Bool) (g : Gate) (w : ℕ) (h : w < x.length) :
    (stp x g).getD w false = x.getD w false := by
  rw [stp, getD_snoc, if_pos h]

theorem anyc {f g : ℕ → Bool} : ∀ (L : List ℕ), (∀ c ∈ L, f c = g c) → L.any f = L.any g
  | [], _ => rfl
  | c :: L, h => by
    rw [List.any_cons, List.any_cons, h c (by simp), anyc L fun c' h' => h c' (by simp [h'])]

theorem chain_val (L : List ℕ) : ∀ (x : List Bool) (a : ℕ), (∀ c ∈ L, c < x.length) →
    a < x.length →
    ((chain x.length a L).foldl stp x).getD (last x.length a L) false =
      (x.getD a false || L.any fun c => x.getD c false) := by
  induction L with
  | nil => intro x a _ ha; simp [chain, last]
  | cons c L ih =>
    intro x a hc ha
    have hl : (stp x ⟨GateOp.or, [a, c]⟩).length = x.length + 1 := by simp [stp]
    have hc' : ∀ c' ∈ L, c' < (stp x ⟨GateOp.or, [a, c]⟩).length := fun c' h => by
      have := hc c' (by simp [h]); omega
    have h2 := ih (stp x ⟨GateOp.or, [a, c]⟩) x.length hc' (by omega)
    simp only [chain, last, List.foldl_cons]
    rw [hl] at h2
    have : ∀ c' ∈ L, (stp x ⟨GateOp.or, [a, c]⟩).getD c' false = x.getD c' false :=
      fun c' h => pre_stp _ _ _ (hc c' (by simp [h]))
    rw [h2, anyc L this, stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
    simp [GateOp.eval, Bool.or_assoc]

def ev (x : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => x.getD i false)

theorem lay : ∀ (gs : List Gate) (x : List Bool), (∀ g ∈ gs, ∀ i ∈ g.inputs, i < x.length) →
    gs.foldl stp x = x ++ gs.map (ev x)
  | [], x, _ => by simp
  | g :: gs, x, h => by
    rw [List.foldl_cons, lay gs (stp x g) fun g' hg' i hi => by
      have := h g' (by simp [hg']) i hi; simp [stp]; omega]
    have : gs.map (ev (stp x g)) = gs.map (ev x) := List.map_congr_left fun g' hg' => by
      unfold ev; congr 1
      exact List.map_congr_left fun i hi => pre_stp _ _ _ (h g' (by simp [hg']) i hi)
    rw [this]; simp [stp, ev]

def G (n : ℕ) : List Gate := (List.range n).map fun i => ⟨GateOp.and, [i, n + i]⟩
def L (n : ℕ) : List ℕ := (List.range (n - 1)).map (n + n + 1 + ·)
def X1 {n : ℕ} (u v : Fin n) : List Bool := oneEach u v ++ (G n).map (ev (oneEach u v))

theorem hx {n : ℕ} (u v : Fin n) : (oneEach u v).length = n + n := by simp [oneEach]
theorem hx1 {n : ℕ} (u v : Fin n) : (X1 u v).length = n + n + n := by simp [X1, G, hx]

theorem flen : ∀ (gs : List Gate) (x : List Bool), (gs.foldl stp x).length = x.length + gs.length
  | [], _ => rfl
  | g :: gs, x => by rw [List.foldl_cons, flen gs, stp]; simp; omega

theorem wires_eq {n : ℕ} (u v : Fin n) (ch : List Gate) :
    (G n ++ ch).foldl stp (oneEach u v) = ch.foldl stp (X1 u v) := by
  rw [List.foldl_append, lay (G n) _ ?_]
  · rfl
  · intro g hg i hi
    simp only [G, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hx]; omega

theorem hg {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (X1 u v).getD (n + n + i) false = true ↔ (i = u.val ∧ i = v.val) := by
  have e : (X1 u v).getD (n + n + i) false =
      ((oneEach u v).getD i false && (oneEach u v).getD (n + i) false) := by
    rw [X1, List.getD_append_right _ _ _ _ (by rw [hx]; omega), hx]
    simp [G, ev, GateOp.eval, List.getD_eq_getElem?_getD, hi]
  rw [e, Bool.and_eq_true, oe, oe]
  have := u.2
  have := v.2
  omega

theorem main (n : ℕ) (hn : 1 ≤ n) : ∃ C : Circuit, FanInTwo C ∧
    Represents (fun u v : Fin n => decide (u ≠ v)) C ∧ C.size ≤ 2 * n := by
  refine ⟨⟨G n ++ (chain (n + n + n) (n + n) (L n) ++
    [⟨GateOp.not, [last (n + n + n) (n + n) (L n)]⟩]), n + n + n + (n - 1)⟩,
    fun g hg => ?_, fun u v => ?_, ?_⟩
  · simp only [List.mem_append, G, List.mem_map, List.mem_singleton] at hg
    rcases hg with ⟨i, -, rfl⟩ | hg | rfl
    · simp
    · have := chain_good _ _ _ g hg; simp [this.1, this.2]
    · simp
  · have h2 := chain_val (L n) (X1 u v) (n + n)
      (fun c hc => by
        simp only [L, List.mem_map, List.mem_range] at hc
        obtain ⟨k, hk, rfl⟩ := hc; rw [hx1]; omega) (by rw [hx1]; omega)
    rw [hx1] at h2
    simp only [Circuit.eval, Circuit.wires]
    change (List.foldl stp _ _).getD _ _ = _
    rw [wires_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl : (List.foldl stp (X1 u v) (chain (n + n + n) (n + n) (L n))).length =
        n + n + n + (n - 1) := by
      rw [flen, hx1, chain_len]; simp [L]
    rw [stp, getD_snoc, hl, if_neg (lt_irrefl _), if_pos rfl]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [h2]
    have key : ((X1 u v).getD (n + n) false || (L n).any fun c => (X1 u v).getD c false) =
        decide (u = v) := by
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Fin.ext_iff]
      constructor
      · rintro (h | ⟨c, hc, h⟩)
        · have := (hg u v 0 (by omega)).1 (by simpa using h)
          omega
        · simp only [L, List.mem_map, List.mem_range] at hc
          obtain ⟨k, hk, rfl⟩ := hc
          have := (hg u v (k + 1) (by omega)).1
            (by rw [show n + n + (k + 1) = n + n + 1 + k by omega]; exact h)
          omega
      · intro h
        by_cases h0 : u.val = 0
        · left
          have := (hg u v 0 (by omega)).2 ⟨h0.symm, by omega⟩
          simpa using this
        · right
          refine ⟨_, List.mem_map.2 ⟨u.val - 1, List.mem_range.2 (by have := u.2; omega), rfl⟩, ?_⟩
          rw [show n + n + 1 + (u.val - 1) = n + n + u.val by omega]
          exact (hg u v u.val u.2).2 ⟨rfl, h⟩
    rw [key]
    by_cases h : u = v <;> simp [h]
  · simp only [Circuit.size, List.length_append, chain_len, G, L, List.length_map,
      List.length_range, List.length_singleton]
    omega

end PEqualNP.Outside.L_meta_20790_aux

theorem PEqualNP.Outside.L_meta_20790 : ∀ (N : ℕ), 1 ≤ N → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C ∧ C.size ≤ 2 * N :=
  PEqualNP.Outside.L_meta_20790_aux.main
