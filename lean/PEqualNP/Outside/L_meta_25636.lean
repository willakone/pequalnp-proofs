import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25636 : let sites := List.range 22
let full := (1 <<< (2 ^ 22) : Nat) - 1
let lowHalf := fun (j : Nat) =>
  (List.range (21 - j)).foldl
    (fun x s => x ||| (x <<< (2 ^ (j + 1 + s)))) ((1 <<< (2 ^ j) : Nat) - 1)
let masks := (sites.map lowHalf).toArray
let readSite := fun (v : Array Nat) (j : Nat) => v[j % 22]?.getD 0
let key := (sites.map (fun j => readSite masks j <<< (2 ^ j))).toArray
let start := (sites.map (fun j => readSite key (j + 21))).toArray
let round := fun (x : Array Nat) (t : Nat) =>
  let m := (sites.map (fun j =>
    readSite x (j + 21) ^^^ readSite x j ^^^ readSite x (j + 1))).toArray
  (sites.map (fun j =>
    readSite m j ^^^ ((full ^^^ readSite m (j + 1)) &&& readSite m (j + 2)) ^^^
      readSite key (j + 22 - 2 * t))).toArray
let last := (List.range 5).foldl round start
let same := fun (j : Nat) =>
  let x := readSite last j
  let low := readSite masks 13
  let shift := 2 ^ 13
  let mate := ((x &&& low) <<< shift) ||| ((x >>> shift) &&& low)
  full ^^^ (x ^^^ mate)
let count := fun (x : Nat) => sites.foldl (fun acc j =>
  let low := readSite masks j
  (acc &&& low) + ((acc >>> (2 ^ j)) &&& low)) x
let both := count (same 21 &&& same 0)
let firstCount := count (same 21)
both = 62976 ∧ firstCount = 125952 ∧
  2 * both = firstCount ∧ 2 ^ 15 ≤ both ∧ both ≤ 3 * 2 ^ 15 := by
  set_option maxRecDepth 100000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; nlinarith)
  | (intros; positivity)
  | (intros; aesop)
