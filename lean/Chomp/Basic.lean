/-!
# Chomp on `ℕ³`: the game, outcomes, symmetry and the antichain lemma

A position is the set of cells still on the board, given as a predicate on `ℕ³`. A move takes a
cell `m` other than the poison `(0,0,0)` and removes every cell `≥ m` (componentwise). A player
who has only the poison left has no move and loses.

Outcomes are defined inductively, so no well-foundedness argument is needed to state them:
`Out true X` means the player to move from `X` can force a win, `Out false X` means the player
to move loses against best play.
-/

namespace Chomp

/-- A cell of the board `ℕ³`. -/
structure Pt where
  x : Nat
  y : Nat
  z : Nat

/-- The componentwise order on cells. -/
def Pt.le (p q : Pt) : Prop := p.x ≤ q.x ∧ p.y ≤ q.y ∧ p.z ≤ q.z

/-- The poison cell. -/
def poison : Pt := ⟨0, 0, 0⟩

theorem Pt.ext' {p q : Pt} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p; cases q; simp_all

theorem ne_poison {m : Pt} (h : m.x ≠ 0 ∨ m.y ≠ 0 ∨ m.z ≠ 0) : m ≠ poison := by
  intro e; subst e; simp [poison] at h

/-- A position: the set of cells still on the board. -/
abbrev Pos := Pt → Prop

/-- The whole board `ℕ³`. -/
def full : Pos := fun _ => True

/-- The position after taking the cell `m`. -/
def take (X : Pos) (m : Pt) : Pos := fun p => X p ∧ ¬ m.le p

/-- `Y` is an option of `X`. -/
def Opt (X Y : Pos) : Prop := ∃ m, X m ∧ m ≠ poison ∧ Y = take X m

/-- `Out true X`: the player to move wins; `Out false X`: the player to move loses. -/
inductive Out : Bool → Pos → Prop
  | win {X Y : Pos} : Opt X Y → Out false Y → Out true X
  | lose {X : Pos} : (∀ Y, Opt X Y → Out true Y) → Out false X

/-- An N-position: the player to move wins. -/
abbrev IsN (X : Pos) : Prop := Out true X
/-- A P-position: the player to move loses. -/
abbrev IsP (X : Pos) : Prop := Out false X

/-- No position is both N and P. -/
theorem Out.not_both {b : Bool} {X : Pos} (h : Out b X) : ¬ Out (!b) X := by
  induction h with
  | win hopt _ ih =>
    intro h'
    change Out false _ at h'
    cases h' with
    | lose hall => exact ih (hall _ hopt)
  | lose _ ih =>
    intro h'
    change Out true _ at h'
    cases h' with
    | win hopt hY => exact ih _ hopt hY

theorem IsN.not_isP {X : Pos} (h : IsN X) : ¬ IsP X := Out.not_both h
theorem IsP.not_isN {X : Pos} (h : IsP X) : ¬ IsN X := Out.not_both h

/-- To show `X` is N, exhibit one move to a P-position. -/
theorem isN_of_move {X : Pos} (m : Pt) (hm : X m) (h0 : m ≠ poison) (hP : IsP (take X m)) : IsN X :=
  Out.win ⟨m, hm, h0, rfl⟩ hP

/-- To show `X` is P, show every move leads to an N-position. -/
theorem isP_of_all {X : Pos} (h : ∀ m, X m → m ≠ poison → IsN (take X m)) : IsP X := by
  apply Out.lose
  intro Y ⟨m, hm, h0, hY⟩
  subst hY
  exact h m hm h0

/-! ## Symmetry -/

/-- An involution of `ℕ³` preserving the order and the poison, e.g. swapping two axes. -/
structure Sym where
  f : Pt → Pt
  inv : ∀ p, f (f p) = p
  le_iff : ∀ p q, (f p).le (f q) ↔ p.le q
  fix : f poison = poison

/-- The image of a position under a symmetry. -/
def Sym.act (σ : Sym) (X : Pos) : Pos := fun p => X (σ.f p)

theorem Sym.act_act (σ : Sym) (X : Pos) : σ.act (σ.act X) = X := by
  funext p; simp [Sym.act, σ.inv]

theorem Sym.le_swap (σ : Sym) (m p : Pt) : m.le (σ.f p) ↔ (σ.f m).le p := by
  have := σ.le_iff m (σ.f p)
  rw [σ.inv] at this
  exact this.symm

theorem Sym.act_take (σ : Sym) (X : Pos) (m : Pt) : σ.act (take X m) = take (σ.act X) (σ.f m) := by
  funext p
  apply propext
  simp only [Sym.act, take, σ.le_swap]

theorem Sym.opt (σ : Sym) {X Y : Pos} (h : Opt X Y) : Opt (σ.act X) (σ.act Y) := by
  obtain ⟨m, hm, h0, rfl⟩ := h
  refine ⟨σ.f m, ?_, ?_, σ.act_take X m⟩
  · show X (σ.f (σ.f m)); rw [σ.inv]; exact hm
  · intro e; apply h0
    have := congrArg σ.f e
    rwa [σ.inv, σ.fix] at this

/-- Outcomes are invariant under symmetries. -/
theorem Sym.out (σ : Sym) {b : Bool} {X : Pos} (h : Out b X) : Out b (σ.act X) := by
  induction h with
  | win hopt _ ih => exact Out.win (σ.opt hopt) ih
  | @lose X0 _ ih =>
    apply Out.lose
    intro Y' hY'
    have h2 : Opt X0 (σ.act Y') := by
      have := σ.opt hY'
      rwa [σ.act_act] at this
    have := ih _ h2
    rwa [σ.act_act] at this

/-- Swap the `y` and `z` axes. -/
def swapYZ : Sym where
  f p := ⟨p.x, p.z, p.y⟩
  inv p := by cases p; rfl
  le_iff p q := by
    simp only [Pt.le]
    exact ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩
  fix := rfl

/-- Swap the `x` and `z` axes. -/
def swapXZ : Sym where
  f p := ⟨p.z, p.y, p.x⟩
  inv p := by cases p; rfl
  le_iff p q := by
    simp only [Pt.le]
    exact ⟨fun ⟨a, b, c⟩ => ⟨c, b, a⟩, fun ⟨a, b, c⟩ => ⟨c, b, a⟩⟩
  fix := rfl

/-- Swap the `x` and `y` axes. -/
def swapXY : Sym where
  f p := ⟨p.y, p.x, p.z⟩
  inv p := by cases p; rfl
  le_iff p q := by
    simp only [Pt.le]
    exact ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩
  fix := rfl

theorem Sym.act_full (σ : Sym) : σ.act full = full := rfl

/-! ## Winning moves form an antichain -/

theorem take_take_of_le {X : Pos} {m m' : Pt} (h : m.le m') : take (take X m') m = take X m := by
  funext p
  apply propext
  simp only [take, Pt.le] at *
  constructor
  · intro ⟨⟨hx, _⟩, hm⟩; exact ⟨hx, hm⟩
  · intro ⟨hx, hm⟩
    refine ⟨⟨hx, ?_⟩, hm⟩
    intro h'
    apply hm
    omega

/-- If `m < m'` are both legal, then taking `m` is an option of the position after `m'`. -/
theorem opt_of_lt {X : Pos} {m m' : Pt} (hm : X m) (h0 : m ≠ poison) (hle : m.le m') (hne : m ≠ m') :
    Opt (take X m') (take X m) := by
  refine ⟨m, ⟨hm, ?_⟩, h0, (take_take_of_le hle).symm⟩
  intro h'
  apply hne
  simp only [Pt.le] at hle h'
  exact Pt.ext' (by omega) (by omega) (by omega)

/-- Two comparable moves cannot both be winning: the winning moves of any position form an
antichain. -/
theorem not_both_winning {X : Pos} {m m' : Pt} (hm : X m) (h0 : m ≠ poison) (hle : m.le m')
    (hne : m ≠ m') (hP : IsP (take X m)) : ¬ IsP (take X m') := by
  intro hP'
  exact hP'.not_isN (Out.win (opt_of_lt hm h0 hle hne) hP)

end Chomp
