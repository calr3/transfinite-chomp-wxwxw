import Chomp.Basic

/-!
# Positions over seven columns of the `3 × 3` base

The position `A = (ω,ω,1 | ω,ω,1 | 2,0,0)` of notes/25 and everything below it live on the
seven columns

  `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`, `(0,2)`, `(1,2)`, `(2,0)`

of the base, with heights `a, b, c, d, e, f, k` (in this order). The first four may be
infinite. This file sets up:

* `PE a b c d e f k`: the position as a set of cells of `ℕ³`, with `Option Nat` heights on
  the first four columns (`none` is `ω`);
* `F7`: finite positions as vectors of seven heights, with `F7.cut X i t` for the bite in
  column `i` at height `t`;
* every option of a position is a cut (`PE_moves`, `F7.isP_iff`, `F7.isN_iff`);
* every finite position is N or P (`F7.total`);
* a closure principle (`closed_isP`): a set of finite positions that is closed under replies,
  up to a family of exceptions handled separately, consists of P-positions;
* the Fundamental Theorem for these positions (`fundamental`): if only the poison column is
  infinite, the position is N.
-/

namespace Chomp

/-- `z` is below the height `h`; `none` is the infinite height. -/
def ltO (z : Nat) : Option Nat → Prop
  | none => True
  | some n => z < n

/-- Cut a height at `t`. -/
def cutO (h : Option Nat) (t : Nat) : Option Nat :=
  match h with
  | none => some t
  | some n => some (min n t)

@[simp] theorem ltO_none (z : Nat) : ltO z none = True := rfl
@[simp] theorem ltO_some (z n : Nat) : ltO z (some n) = (z < n) := rfl
@[simp] theorem cutO_none (t : Nat) : cutO none t = some t := rfl
@[simp] theorem cutO_some (n t : Nat) : cutO (some n) t = some (min n t) := rfl

theorem ltO_cutO (z t : Nat) (h : Option Nat) : ltO z (cutO h t) ↔ (ltO z h ∧ z < t) := by
  cases h with
  | none => simp
  | some n => simp only [cutO_some, ltO_some]; omega

/-- The height of the column over `(x, y)`: `a, b, c, d` (possibly infinite) on `(0,0)`,
`(0,1)`, `(1,0)`, `(1,1)`, and `e, f, k` on `(0,2)`, `(1,2)`, `(2,0)`; no other column. -/
def colH (a b c d : Option Nat) (e f k : Nat) : Nat → Nat → Option Nat
  | 0, 0 => a
  | 0, 1 => b
  | 0, 2 => some e
  | 0, _ + 3 => some 0
  | 1, 0 => c
  | 1, 1 => d
  | 1, 2 => some f
  | 1, _ + 3 => some 0
  | 2, 0 => some k
  | 2, _ + 1 => some 0
  | _ + 3, _ => some 0

/-- The position with these column heights. -/
def PE (a b c d : Option Nat) (e f k : Nat) : Pos := fun p => ltO p.z (colH a b c d e f k p.x p.y)

/-- Taking the cell `(x0, y0, t)` cuts the columns over `(x, y) ≥ (x0, y0)` at `t`. -/
theorem take_col (H H' : Nat → Nat → Option Nat) (x0 y0 t : Nat)
    (h : ∀ x y, H' x y = if x0 ≤ x ∧ y0 ≤ y then cutO (H x y) t else H x y) :
    take (fun p => ltO p.z (H p.x p.y)) ⟨x0, y0, t⟩ = fun p => ltO p.z (H' p.x p.y) := by
  funext p; apply propext
  simp only [take, Pt.le, h]
  by_cases hc : x0 ≤ p.x ∧ y0 ≤ p.y
  · have e : (if x0 ≤ p.x ∧ y0 ≤ p.y then cutO (H p.x p.y) t else H p.x p.y) = cutO (H p.x p.y) t := by
      simp [hc]
    rw [e, ltO_cutO]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨h1, Nat.lt_of_not_le fun h3 => h2 ⟨hc.1, hc.2, h3⟩⟩
    · intro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => Nat.not_le_of_lt h2 h3.2.2⟩
  · have e : (if x0 ≤ p.x ∧ y0 ≤ p.y then cutO (H p.x p.y) t else H p.x p.y) = H p.x p.y := by
      simp [hc]
    rw [e]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h1; exact ⟨h1, fun h3 => hc ⟨h3.1, h3.2.1⟩⟩

/-! ## The seven bites -/

theorem take_PE_00 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨0, 0, t⟩ =
      PE (cutO a t) (cutO b t) (cutO c t) (cutO d t) (min e t) (min f t) (min k t) := by
  refine take_col _ _ 0 0 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_01 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨0, 1, t⟩ = PE a (cutO b t) c (cutO d t) (min e t) (min f t) k := by
  refine take_col _ _ 0 1 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_10 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨1, 0, t⟩ = PE a b (cutO c t) (cutO d t) e (min f t) (min k t) := by
  refine take_col _ _ 1 0 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_11 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨1, 1, t⟩ = PE a b c (cutO d t) e (min f t) k := by
  refine take_col _ _ 1 1 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_02 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨0, 2, t⟩ = PE a b c d (min e t) (min f t) k := by
  refine take_col _ _ 0 2 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_12 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨1, 2, t⟩ = PE a b c d e (min f t) k := by
  refine take_col _ _ 1 2 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

theorem take_PE_20 (a b c d : Option Nat) (e f k t : Nat) :
    take (PE a b c d e f k) ⟨2, 0, t⟩ = PE a b c d e f (min k t) := by
  refine take_col _ _ 2 0 t fun x y => ?_
  match x, y with
  | 0, 0 | 0, 1 | 0, 2 | 0, _ + 3 | 1, 0 | 1, 1 | 1, 2 | 1, _ + 3 | 2, 0 | 2, _ + 1 | _ + 3, _ =>
    simp [colH]

/-- Membership in `PE …`, column by column. -/
theorem PE_mem (a b c d : Option Nat) (e f k x y z : Nat) :
    PE a b c d e f k ⟨x, y, z⟩ = ltO z (colH a b c d e f k x y) := rfl

/-- Every legal move of `PE …` is a bite in one of the seven columns. -/
theorem PE_moves {a b c d : Option Nat} {e f k : Nat} {m : Pt} (hm : PE a b c d e f k m)
    (h0 : m ≠ poison) :
    (m = ⟨0, 0, m.z⟩ ∧ 1 ≤ m.z ∧ ltO m.z a) ∨ (m = ⟨0, 1, m.z⟩ ∧ ltO m.z b) ∨
    (m = ⟨1, 0, m.z⟩ ∧ ltO m.z c) ∨ (m = ⟨1, 1, m.z⟩ ∧ ltO m.z d) ∨
    (m = ⟨0, 2, m.z⟩ ∧ m.z < e) ∨ (m = ⟨1, 2, m.z⟩ ∧ m.z < f) ∨ (m = ⟨2, 0, m.z⟩ ∧ m.z < k) := by
  obtain ⟨x, y, z⟩ := m
  rw [PE_mem] at hm
  match x, y, hm with
  | 0, 0, hm =>
    refine Or.inl ⟨rfl, ?_, hm⟩
    have : z ≠ 0 := fun h => h0 (by subst h; rfl)
    show 1 ≤ z; omega
  | 0, 1, hm => exact Or.inr (Or.inl ⟨rfl, hm⟩)
  | 1, 0, hm => exact Or.inr (Or.inr (Or.inl ⟨rfl, hm⟩))
  | 1, 1, hm => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hm⟩)))
  | 0, 2, hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hm⟩))))
  | 1, 2, hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hm⟩)))))
  | 2, 0, hm => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hm⟩)))))
  | 0, _ + 3, hm => simp [colH] at hm
  | 1, _ + 3, hm => simp [colH] at hm
  | 2, _ + 1, hm => simp [colH] at hm
  | _ + 3, _, hm => simp [colH] at hm

/-- Inversion: a P-position has only N options. -/
theorem IsP.opt {X Y : Pos} (h : IsP X) (hY : Opt X Y) : IsN Y := by
  cases h with
  | lose hall => exact hall Y hY

/-- Inversion: an N-position has a P option. -/
theorem IsN.opt {X : Pos} (h : IsN X) : ∃ Y, Opt X Y ∧ IsP Y := by
  cases h with
  | win hopt hY => exact ⟨_, hopt, hY⟩

/-! ## Finite positions as vectors -/

/-- A finite position: the heights of the seven columns. -/
structure F7 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  k : Nat
  deriving DecidableEq, Repr

namespace F7

/-- The position as a set of cells. -/
def toPos (X : F7) : Pos := PE (some X.a) (some X.b) (some X.c) (some X.d) X.e X.f X.k

/-- The bite in column `i` (0 to 6, in the order `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`, `(0,2)`,
`(1,2)`, `(2,0)`) at height `t`. -/
def cut (X : F7) : Nat → Nat → F7
  | 0, t => ⟨min X.a t, min X.b t, min X.c t, min X.d t, min X.e t, min X.f t, min X.k t⟩
  | 1, t => ⟨X.a, min X.b t, X.c, min X.d t, min X.e t, min X.f t, X.k⟩
  | 2, t => ⟨X.a, X.b, min X.c t, min X.d t, X.e, min X.f t, min X.k t⟩
  | 3, t => ⟨X.a, X.b, X.c, min X.d t, X.e, min X.f t, X.k⟩
  | 4, t => ⟨X.a, X.b, X.c, X.d, min X.e t, min X.f t, X.k⟩
  | 5, t => ⟨X.a, X.b, X.c, X.d, X.e, min X.f t, X.k⟩
  | _, t => ⟨X.a, X.b, X.c, X.d, X.e, X.f, min X.k t⟩

/-- The bite in column `i` at height `t` is a legal move. -/
def legal (X : F7) : Nat → Nat → Prop
  | 0, t => 1 ≤ t ∧ t < X.a
  | 1, t => t < X.b
  | 2, t => t < X.c
  | 3, t => t < X.d
  | 4, t => t < X.e
  | 5, t => t < X.f
  | 6, t => t < X.k
  | _, _ => False

/-- The number of cells. -/
def size (X : F7) : Nat := X.a + X.b + X.c + X.d + X.e + X.f + X.k

theorem size_cut {X : F7} {i t : Nat} (h : X.legal i t) : (X.cut i t).size < X.size := by
  match i, h with
  | 0, h => simp only [legal] at h; simp only [cut, size]; omega
  | 1, h => simp only [legal] at h; simp only [cut, size]; omega
  | 2, h => simp only [legal] at h; simp only [cut, size]; omega
  | 3, h => simp only [legal] at h; simp only [cut, size]; omega
  | 4, h => simp only [legal] at h; simp only [cut, size]; omega
  | 5, h => simp only [legal] at h; simp only [cut, size]; omega
  | 6, h => simp only [legal] at h; simp only [cut, size]; omega

/-- A legal bite is an option. -/
theorem opt_cut {X : F7} {i t : Nat} (h : X.legal i t) : Opt X.toPos (X.cut i t).toPos := by
  match i, h with
  | 0, h =>
    simp only [legal] at h
    refine ⟨⟨0, 0, t⟩, (show ltO t (some X.a) from h.2), ne_poison (Or.inr (Or.inr (by show t ≠ 0; omega))), ?_⟩
    simp only [toPos, cut, take_PE_00, cutO_some]
  | 1, h =>
    simp only [legal] at h
    refine ⟨⟨0, 1, t⟩, (show ltO t (some X.b) from h), ne_poison (Or.inr (Or.inl (by simp))), ?_⟩
    simp only [toPos, cut, take_PE_01, cutO_some]
  | 2, h =>
    simp only [legal] at h
    refine ⟨⟨1, 0, t⟩, (show ltO t (some X.c) from h), ne_poison (Or.inl (by simp)), ?_⟩
    simp only [toPos, cut, take_PE_10, cutO_some]
  | 3, h =>
    simp only [legal] at h
    refine ⟨⟨1, 1, t⟩, (show ltO t (some X.d) from h), ne_poison (Or.inl (by simp)), ?_⟩
    simp only [toPos, cut, take_PE_11, cutO_some]
  | 4, h =>
    simp only [legal] at h
    refine ⟨⟨0, 2, t⟩, (show ltO t (some X.e) from h),
      ne_poison (Or.inr (Or.inl (by simp))), ?_⟩
    simp only [toPos, cut, take_PE_02]
  | 5, h =>
    simp only [legal] at h
    refine ⟨⟨1, 2, t⟩, (show ltO t (some X.f) from h),
      ne_poison (Or.inl (by simp)), ?_⟩
    simp only [toPos, cut, take_PE_12]
  | 6, h =>
    simp only [legal] at h
    refine ⟨⟨2, 0, t⟩, (show ltO t (some X.k) from h),
      ne_poison (Or.inl (by simp)), ?_⟩
    simp only [toPos, cut, take_PE_20]

/-- Every option is a legal bite. -/
theorem opt_inv {X : F7} {Y : Pos} (h : Opt X.toPos Y) : ∃ i t, X.legal i t ∧ Y = (X.cut i t).toPos := by
  obtain ⟨m, hm, h0, rfl⟩ := h
  rcases PE_moves hm h0 with ⟨e, h1, h2⟩ | ⟨e, h2⟩ | ⟨e, h2⟩ | ⟨e, h2⟩ | ⟨e, h2⟩ | ⟨e, h2⟩ | ⟨e, h2⟩
  · refine ⟨0, m.z, ⟨h1, h2⟩, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_00, cutO_some]
  · refine ⟨1, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_01, cutO_some]
  · refine ⟨2, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_10, cutO_some]
  · refine ⟨3, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_11, cutO_some]
  · refine ⟨4, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_02]
  · refine ⟨5, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_12]
  · refine ⟨6, m.z, h2, ?_⟩
    rw [e]; simp only [toPos, cut, take_PE_20]

/-- `X` is a P-position. -/
abbrev P (X : F7) : Prop := IsP X.toPos
/-- `X` is an N-position. -/
abbrev N (X : F7) : Prop := IsN X.toPos

theorem isP_of {X : F7} (h : ∀ i t, X.legal i t → (X.cut i t).N) : X.P := by
  apply Out.lose
  intro Y hY
  obtain ⟨i, t, hl, rfl⟩ := opt_inv hY
  exact h i t hl

theorem isN_of {X : F7} {i t : Nat} (hl : X.legal i t) (h : (X.cut i t).P) : X.N :=
  Out.win (opt_cut hl) h

theorem P.cut {X : F7} (h : X.P) {i t : Nat} (hl : X.legal i t) : (X.cut i t).N :=
  IsP.opt h (opt_cut hl)

theorem N.cut {X : F7} (h : X.N) : ∃ i t, X.legal i t ∧ (X.cut i t).P := by
  obtain ⟨Y, hY, hP⟩ := IsN.opt h
  obtain ⟨i, t, hl, rfl⟩ := opt_inv hY
  exact ⟨i, t, hl, hP⟩

theorem not_both {X : F7} (hN : X.N) (hP : X.P) : False := hN.not_isP hP

/-- Every finite position is N or P. -/
theorem total (X : F7) : X.N ∨ X.P := by
  generalize hn : X.size = n
  induction n using Nat.strongRecOn generalizing X with
  | _ n ih =>
    by_cases h : ∃ i t, X.legal i t ∧ (X.cut i t).P
    · obtain ⟨i, t, hl, hP⟩ := h
      exact Or.inl (isN_of hl hP)
    · refine Or.inr (isP_of fun i t hl => ?_)
      rcases ih _ (by rw [← hn]; exact size_cut hl) (X.cut i t) rfl with hN | hP
      · exact hN
      · exact absurd ⟨i, t, hl, hP⟩ h

/-- `Y` has a legal bite into the set `S`. -/
def Reply (S : F7 → Prop) (Y : F7) : Prop := ∃ i t, Y.legal i t ∧ S (Y.cut i t)

end F7

open F7

/-- **Closure principle.** Let `S` be a set of finite positions and `W` a set of exceptions.
Suppose every option of a position of `S` is in `W` or has an option in `S`, and every
position of `W` is N as soon as all smaller positions of `S` are P. Then every position of
`S` is P and every position of `W` is N. -/
theorem closed_isP (S W : F7 → Prop)
    (hS : ∀ X, S X → ∀ i t, X.legal i t → W (X.cut i t) ∨ Reply S (X.cut i t))
    (hW : ∀ Y, W Y → (∀ X, S X → X.size < Y.size → X.P) → Y.N) :
    (∀ X, S X → X.P) ∧ (∀ Y, W Y → Y.N) := by
  have key : ∀ n, (∀ X, S X → X.size < n → X.P) := by
    intro n
    induction n with
    | zero => intro X _ h; omega
    | succ n ih =>
      intro X hX hlt
      refine isP_of fun i t hl => ?_
      have hsz := size_cut hl
      rcases hS X hX i t hl with hw | ⟨j, s, hl2, hZ⟩
      · exact hW _ hw fun X' hX' hlt' => ih X' hX' (by omega)
      · exact isN_of hl2 (ih _ hZ (by have := size_cut hl2; omega))
  have hP : ∀ X, S X → X.P := fun X hX => key (X.size + 1) X hX (by omega)
  exact ⟨hP, fun Y hY => hW Y hY fun X hX _ => hP X hX⟩

/-! ## The Fundamental Theorem: one infinite column -/

/-- The finite cuts of a position with only the poison column infinite. -/
theorem take_PE_none_00 (b c d e f k h : Nat) :
    take (PE none (some b) (some c) (some d) e f k) ⟨0, 0, h⟩ =
      (F7.mk h (min b h) (min c h) (min d h) (min e h) (min f h) (min k h)).toPos := by
  simp only [toPos, take_PE_00, cutO_none, cutO_some]

/-- For a fixed rest, at most one height of the poison column above the rest gives a
P-position, so the heights that do are bounded. -/
theorem P_bounded (r : F7) (M : Nat) (hM : r.b ≤ M ∧ r.c ≤ M ∧ r.d ≤ M ∧ r.e ≤ M ∧ r.f ≤ M ∧ r.k ≤ M)
    (hM1 : 1 ≤ M) :
    ∃ B, ∀ a, M ≤ a → (F7.mk a r.b r.c r.d r.e r.f r.k).P → a ≤ B := by
  by_cases h : ∃ a0, M ≤ a0 ∧ (F7.mk a0 r.b r.c r.d r.e r.f r.k).P
  · obtain ⟨a0, h0, hP0⟩ := h
    refine ⟨a0, fun a ha hP => ?_⟩
    apply Classical.byContradiction
    intro hlt
    -- `a0 < a`: cutting the poison column of the taller one at `a0` gives the shorter one
    have hl : (F7.mk a r.b r.c r.d r.e r.f r.k).legal 0 a0 := by simp only [legal]; omega
    have hc : (F7.mk a r.b r.c r.d r.e r.f r.k).cut 0 a0 = F7.mk a0 r.b r.c r.d r.e r.f r.k := by
      simp only [F7.cut, F7.mk.injEq]; omega
    have := hP.cut hl
    rw [hc] at this
    exact not_both this hP0
  · exact ⟨0, fun a ha hP => absurd ⟨a, ha, hP⟩ h⟩

/-- A bound that works for all heights `t < T` of a bite in one column. -/
theorem bound_range (Q : Nat → Nat → Prop) (hmono : ∀ t B B', Q t B → B ≤ B' → Q t B')
    (hex : ∀ t, ∃ B, Q t B) (T : Nat) : ∃ B, ∀ t, t < T → Q t B := by
  induction T with
  | zero => exact ⟨0, fun t h => by omega⟩
  | succ T ih =>
    obtain ⟨B1, h1⟩ := ih
    obtain ⟨B2, h2⟩ := hex T
    refine ⟨max B1 B2, fun t ht => ?_⟩
    by_cases h : t < T
    · exact hmono t B1 _ (h1 t h) (Nat.le_max_left _ _)
    · have : t = T := by omega
      subst this
      exact hmono t B2 _ h2 (Nat.le_max_right _ _)

/-- **Fundamental Theorem** for these positions: if only the poison column is infinite, some
cut of the poison column leaves a P-position, so the position is N. -/
theorem fundamental (b c d e f k : Nat) : IsN (PE none (some b) (some c) (some d) e f k) := by
  -- it is enough to find a finite cut that is P
  suffices h : ∃ h, 1 ≤ h ∧ (F7.mk h (min b h) (min c h) (min d h) (min e h) (min f h) (min k h)).P by
    obtain ⟨h, h1, hP⟩ := h
    refine isN_of_move ⟨0, 0, h⟩ (show ltO h none from trivial)
      (ne_poison (Or.inr (Or.inr (by show h ≠ 0; omega)))) ?_
    rw [take_PE_none_00]; exact hP
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ h, 1 ≤ h → ¬ (F7.mk h (min b h) (min c h) (min d h) (min e h) (min f h) (min k h)).P :=
    fun h h1 hP => hno ⟨h, h1, hP⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = b + c + d + e + f + k + 1 := ⟨_, rfl⟩
  -- for each column `i ≥ 1`, a bound on the heights `a ≥ M` with `(a, r cut at (i,t))` in P
  have hcol : ∀ i, ∃ B, ∀ t, t < M → ∀ a, M ≤ a → ((F7.mk a b c d e f k).cut i t).P → a ≤ B ∨ i = 0 := by
    intro i
    apply bound_range (fun t B => ∀ a, M ≤ a → ((F7.mk a b c d e f k).cut i t).P → a ≤ B ∨ i = 0)
    · intro t B B' h hle a ha hP
      rcases h a ha hP with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    · intro t
      match i with
      | 0 => exact ⟨0, fun a _ _ => Or.inr rfl⟩
      | 1 =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, min b t, c, min d t, min e t, min f t, k⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
      | 2 =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, b, min c t, min d t, e, min f t, min k t⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
      | 3 =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, b, c, min d t, e, min f t, k⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
      | 4 =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, b, c, d, min e t, min f t, k⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
      | 5 =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, b, c, d, e, min f t, k⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
      | (n + 6) =>
        obtain ⟨B, hB⟩ := P_bounded ⟨0, b, c, d, e, f, min k t⟩ M
          (by simp only; omega) (by omega)
        exact ⟨B, fun a ha hP => Or.inl (hB a ha (by simpa only [F7.cut] using hP))⟩
  obtain ⟨B1, h1⟩ := hcol 1
  obtain ⟨B2, h2⟩ := hcol 2
  obtain ⟨B3, h3⟩ := hcol 3
  obtain ⟨B4, h4⟩ := hcol 4
  obtain ⟨B5, h5⟩ := hcol 5
  obtain ⟨B6, h6⟩ := hcol 6
  -- a height above all the bounds
  obtain ⟨a, hadef⟩ : ∃ a, a = M + B1 + B2 + B3 + B4 + B5 + B6 + 1 := ⟨_, rfl⟩
  have ha : M ≤ a := by omega
  have hcutA : F7.mk a (min b a) (min c a) (min d a) (min e a) (min f a) (min k a) = F7.mk a b c d e f k := by
    rw [Nat.min_eq_left (show b ≤ a by omega), Nat.min_eq_left (show c ≤ a by omega),
      Nat.min_eq_left (show d ≤ a by omega), Nat.min_eq_left (show e ≤ a by omega),
      Nat.min_eq_left (show f ≤ a by omega), Nat.min_eq_left (show k ≤ a by omega)]
  rcases total (F7.mk a b c d e f k) with hN | hP
  · obtain ⟨i, t, hl, hPc⟩ := hN.cut
    match i, hl with
    | 0, hl =>
      have hl' : 1 ≤ t ∧ t < a := hl
      exact hno' t hl'.1 (by simpa only [F7.cut, Nat.min_eq_right (Nat.le_of_lt hl'.2)] using hPc)
    | 1, hl =>
      have hl' : t < b := hl
      rcases h1 t (by omega) a ha hPc with h | h <;> omega
    | 2, hl =>
      have hl' : t < c := hl
      rcases h2 t (by omega) a ha hPc with h | h <;> omega
    | 3, hl =>
      have hl' : t < d := hl
      rcases h3 t (by omega) a ha hPc with h | h <;> omega
    | 4, hl =>
      have hl' : t < e := hl
      rcases h4 t (by omega) a ha hPc with h | h <;> omega
    | 5, hl =>
      have hl' : t < f := hl
      rcases h5 t (by omega) a ha hPc with h | h <;> omega
    | 6, hl =>
      have hl' : t < k := hl
      rcases h6 t (by omega) a ha hPc with h | h <;> omega
  · exact hno' a (by omega) (by rw [hcutA]; exact hP)

end Chomp
