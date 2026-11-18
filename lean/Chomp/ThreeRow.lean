import Chomp.SideClass

/-!
# Three-row Chomp and the function `f(q,r)`

A three-row position `[a,b,c]` has rows of lengths `a ≥ b ≥ c`, with the poison at the start of
the first row. A move shortens one row and cuts the rows above it to at most the same length;
taking the poison (shortening the first row to `0`) is not allowed.

This file defines the game on triples, proves the statements about the function `f(q,r)` of
Brouwer, Horváth, Molnár-Sáska and Szabó that `SideClass.lean` takes as hypotheses (they are
due to Sheiner, arXiv:2605.23837), and so obtains the side-class theorem for three-row Chomp
with no assumption: `ThreeRow.side_density` and `ThreeRow.side_unbounded`.
-/

namespace Chomp.ThreeRow

open Chomp.SideClass

/-- A three-row position, by its row lengths. -/
structure T3 where
  a : Nat
  b : Nat
  c : Nat

/-- The moves: shorten row 1 to `k ≥ 1`, row 2 to `j`, or row 3 to `j`. -/
def Move (X Y : T3) : Prop :=
  (∃ k, 1 ≤ k ∧ k < X.a ∧ Y = ⟨k, min X.b k, min X.c k⟩) ∨
  (∃ j, j < X.b ∧ Y = ⟨X.a, j, min X.c j⟩) ∨
  (∃ j, j < X.c ∧ Y = ⟨X.a, X.b, j⟩)

/-- `Out true X`: the player to move wins; `Out false X`: the player to move loses. -/
inductive Out : Bool → T3 → Prop
  | win {X Y : T3} : Move X Y → Out false Y → Out true X
  | lose {X : T3} : (∀ Y, Move X Y → Out true Y) → Out false X

abbrev IsN (X : T3) : Prop := Out true X
abbrev IsP (X : T3) : Prop := Out false X

theorem Out.not_both {b : Bool} {X : T3} (h : Out b X) : ¬ Out (!b) X := by
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

theorem not_both {X : T3} (hP : IsP X) (hN : IsN X) : False := Out.not_both hP hN

/-- A move from a P-position does not lead to a P-position. -/
theorem no_move {X Y : T3} (hX : IsP X) (hm : Move X Y) (hY : IsP Y) : False := by
  cases hX with
  | lose hall => exact not_both hY (hall Y hm)

theorem isN_exists {X : T3} (h : IsN X) : ∃ Y, Move X Y ∧ IsP Y := by
  cases h with
  | win hm hY => exact ⟨_, hm, hY⟩

/-- Every position is P or N. -/
theorem determined : ∀ (n : Nat) (X : T3), X.a + X.b + X.c = n → IsP X ∨ IsN X := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro X hX
    by_cases h : ∃ Y, Move X Y ∧ IsP Y
    · obtain ⟨Y, hm, hY⟩ := h
      exact Or.inr (Out.win hm hY)
    · refine Or.inl (Out.lose ?_)
      intro Y hm
      have hlt : Y.a + Y.b + Y.c < n := by
        rcases hm with ⟨k, _, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> simp only <;> omega
      rcases ih _ hlt Y rfl with hP | hN
      · exact absurd ⟨Y, hm, hP⟩ h
      · exact hN

theorem isN_of_not_isP {X : T3} (h : ¬ IsP X) : IsN X := by
  rcases determined _ X rfl with hP | hN
  · exact absurd hP h
  · exact hN

theorem move_cases {a b c : Nat} {Y : T3} (h : Move ⟨a, b, c⟩ Y) :
    (∃ k, 1 ≤ k ∧ k < a ∧ Y = ⟨k, min b k, min c k⟩) ∨
    (∃ j, j < b ∧ Y = ⟨a, j, min c j⟩) ∨
    (∃ j, j < c ∧ Y = ⟨a, b, j⟩) := h

theorem move_row1 {a b c k b' c' : Nat} (h1 : 1 ≤ k) (hk : k < a) (hb : b' = min b k)
    (hc : c' = min c k) : Move ⟨a, b, c⟩ ⟨k, b', c'⟩ := by
  subst hb hc; exact Or.inl ⟨k, h1, hk, rfl⟩

theorem move_row2 {a b c j c' : Nat} (hj : j < b) (hc : c' = min c j) :
    Move ⟨a, b, c⟩ ⟨a, j, c'⟩ := by
  subst hc; exact Or.inr (Or.inl ⟨j, hj, rfl⟩)

theorem move_row3 {a b c j : Nat} (hj : j < c) : Move ⟨a, b, c⟩ ⟨a, b, j⟩ :=
  Or.inr (Or.inr ⟨j, hj, rfl⟩)

theorem IsP.cast {a b c a' b' c' : Nat} (h : IsP ⟨a, b, c⟩) (ha : a = a') (hb : b = b')
    (hc : c = c') : IsP ⟨a', b', c'⟩ := by
  subst ha hb hc; exact h

/-- Rectangles are N-positions (strategy stealing). -/
theorem rect_isN {k : Nat} (hk : 1 ≤ k) : IsN ⟨k, k, k⟩ := by
  by_cases h : IsP ⟨k, k, k - 1⟩
  · exact Out.win (move_row3 (by omega)) h
  · obtain ⟨Z, hm, hZ⟩ := isN_exists (isN_of_not_isP h)
    rcases move_cases hm with ⟨k', h1, hk', rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact Out.win (move_row1 h1 hk' rfl (by omega)) hZ
    · exact Out.win (move_row2 hj (by omega)) hZ
    · exact Out.win (move_row3 (by omega)) hZ

/-! ## The function `f` -/

/-- `Enc q r p`: `p` is the value encoded at `(q,r)`. -/
def Enc (q r p : Nat) : Prop :=
  r < p ∧ ((p < q ∧ IsP ⟨p, p, r⟩) ∨ (q ≤ p ∧ IsP ⟨p, q, r⟩))

/-- The position of the chain `(q,r)` with first row `p`. -/
theorem Enc.unique {q r p₁ p₂ : Nat} (h₁ : Enc q r p₁) (h₂ : Enc q r p₂) : p₁ = p₂ := by
  -- the position for the larger value moves to the position for the smaller one
  have key : ∀ p p', p < p' → Enc q r p → Enc q r p' → False := by
    intro p p' hlt h h'
    obtain ⟨hr, hcase⟩ := h
    obtain ⟨hr', hcase'⟩ := h'
    rcases hcase' with ⟨hq', hP'⟩ | ⟨hq', hP'⟩
    · -- p' < q, so p < q
      rcases hcase with ⟨hq, hP⟩ | ⟨hq, hP⟩
      · exact no_move hP' (move_row1 (by omega) hlt (by omega) (by omega)) hP
      · omega
    · rcases hcase with ⟨hq, hP⟩ | ⟨hq, hP⟩
      · exact no_move hP' (move_row1 (by omega) hlt (by omega) (by omega)) hP
      · exact no_move hP' (move_row1 (by omega) hlt (by omega) (by omega)) hP
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key _ _ h h₁ h₂
  · exact key _ _ h h₂ h₁

/-- Two P-positions with the same second and third rows have the same first row. -/
theorem first_row_unique {p p' q r : Nat} (hq : q ≤ p) (hq' : q ≤ p')
    (hr : r < p) (hr' : r < p') (h : IsP ⟨p, q, r⟩) (h' : IsP ⟨p', q, r⟩) : p = p' :=
  Enc.unique ⟨hr, Or.inr ⟨hq, h⟩⟩ ⟨hr', Or.inr ⟨hq', h'⟩⟩

theorem Enc.exists {q r : Nat} (hqr : r ≤ q) : ∃ p, Enc q r p := by
  apply Classical.byContradiction
  intro hno
  -- every p ≥ q + r + 1 has a P option in one of the q + r lower chains
  have h := cnt_le_of_rel (fun p => q + r + 1 ≤ p) (fun _ => True)
    (fun c p => q + r + 1 ≤ p ∧
      ((c < q ∧ IsP ⟨p, c, min r c⟩) ∨ (q ≤ c ∧ c - q < r ∧ IsP ⟨p, q, c - q⟩)))
    (q + r + 1 + (q + r + 1)) (q + r)
    (by
      intro p _ hp
      have hN : IsN ⟨p, q, r⟩ :=
        isN_of_not_isP (fun hP => hno ⟨p, by omega, Or.inr ⟨by omega, hP⟩⟩)
      obtain ⟨Z, hm, hZ⟩ := isN_exists hN
      rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exfalso
        by_cases hkr : k ≤ r
        · exact not_both (hZ.cast rfl (by omega) (by omega)) (rect_isN h1)
        · by_cases hkq : k < q
          · exact hno ⟨k, by omega, Or.inl ⟨hkq, hZ.cast rfl (by omega) (by omega)⟩⟩
          · exact hno ⟨k, by omega, Or.inr ⟨by omega, hZ.cast rfl (by omega) (by omega)⟩⟩
      · exact ⟨j, by omega, trivial, hp, Or.inl ⟨hj, hZ⟩⟩
      · exact ⟨q + j, by omega, trivial, hp,
          Or.inr ⟨by omega, by omega, hZ.cast rfl rfl (by omega)⟩⟩)
    (by
      intro c p p' _ _ _ _ h h'
      obtain ⟨hp, hc⟩ := h
      obtain ⟨hp', hc'⟩ := h'
      rcases hc with ⟨hcq, hP⟩ | ⟨hcq, hj, hP⟩
      · rcases hc' with ⟨_, hP'⟩ | ⟨hcq', _, _⟩
        · exact first_row_unique (by omega) (by omega) (by omega) (by omega) hP hP'
        · omega
      · rcases hc' with ⟨hcq', _⟩ | ⟨_, _, hP'⟩
        · omega
        · exact first_row_unique (by omega) (by omega) (by omega) (by omega) hP hP')
  rw [cnt_ge, cnt_true] at h
  omega

open Classical in
/-- The function of Brouwer, Horváth, Molnár-Sáska and Szabó. -/
noncomputable def f (q r : Nat) : Nat :=
  if h : ∃ p, Enc q r p then Classical.choose h else 0

theorem f_spec {q r : Nat} (hqr : r ≤ q) : Enc q r (f q r) := by
  have h := Enc.exists hqr
  have e : f q r = Classical.choose h := by simp only [f, h, dite_true]
  rw [e]; exact Classical.choose_spec h

theorem f_eq {q r p : Nat} (hqr : r ≤ q) (h : Enc q r p) : f q r = p :=
  Enc.unique (f_spec hqr) h

theorem f_gt {q r : Nat} (hqr : r ≤ q) : r < f q r := (f_spec hqr).1

theorem isP_f {q r : Nat} (hqr : r ≤ q) (h : q ≤ f q r) : IsP ⟨f q r, q, r⟩ := by
  rcases (f_spec hqr).2 with ⟨hlt, _⟩ | ⟨_, hP⟩
  · omega
  · exact hP

theorem isP_f_lt {q r : Nat} (hqr : r ≤ q) (h : f q r < q) : IsP ⟨f q r, f q r, r⟩ := by
  rcases (f_spec hqr).2 with ⟨_, hP⟩ | ⟨hge, _⟩
  · exact hP
  · omega

theorem isP_of_f_eq {p q r : Nat} (hqr : r ≤ q) (h : f q r = p) (hq : q ≤ p) :
    IsP ⟨p, q, r⟩ := by
  have := isP_f hqr (by omega)
  rw [h] at this; exact this

theorem f_eq_of_isP {p q r : Nat} (hqr : r ≤ q) (hr : r < p) (hq : q ≤ p)
    (hP : IsP ⟨p, q, r⟩) : f q r = p :=
  f_eq hqr ⟨hr, Or.inr ⟨hq, hP⟩⟩

theorem f_eq_of_partner {p q r : Nat} (hr : r < p) (hq : p < q) (hP : IsP ⟨p, p, r⟩) :
    f q r = p :=
  f_eq (by omega) ⟨hr, Or.inl ⟨hq, hP⟩⟩

/-- `[p,p,r]` is a P-position iff `f p r = p`. -/
theorem partner_isP {p r : Nat} (hr : r < p) (h : f p r = p) : IsP ⟨p, p, r⟩ :=
  isP_of_f_eq (by omega) h (Nat.le_refl p)

/-! ## Sheiner's lemmas -/

theorem f_enc {q r : Nat} (hqr : r ≤ q) (h : f q r < q) : f (f q r) r = f q r :=
  f_eq_of_isP (by have := f_gt hqr; omega) (f_gt hqr) (Nat.le_refl _) (isP_f_lt hqr h)

theorem f_const {r k q : Nat} (hrk : r < k) (hk : f k r = k) (hkq : k ≤ q) : f q r = k := by
  have hP := partner_isP hrk hk
  by_cases h : k = q
  · subst h; exact hk
  · exact f_eq_of_partner hrk (by omega) hP

/-- Lemma 2.3(a). -/
theorem f_row_inj {q b₁ b₂ : Nat} (hb : b₁ < b₂) (hq : b₂ ≤ q) : f q b₁ ≠ f q b₂ := by
  intro heq
  by_cases h : q ≤ f q b₂
  · have h2 := isP_f hq h
    have h1 : IsP ⟨f q b₂, q, b₁⟩ := isP_of_f_eq (by omega) heq h
    exact no_move h2 (move_row3 hb) h1
  · have h2 := isP_f_lt hq (by omega)
    have h1 : IsP ⟨f q b₂, f q b₂, b₁⟩ := by
      have := isP_f_lt (q := q) (r := b₁) (by omega) (by omega)
      rw [heq] at this; exact this
    exact no_move h2 (move_row3 hb) h1

/-- Lemma 2.3(b). -/
theorem f_col_once {s t₁ t₂ p : Nat} (hs : s < t₁) (ht : t₁ < t₂) (hp : t₂ < p)
    (h1 : f t₁ s = p) : f t₂ s ≠ p := by
  intro h2
  have hP1 : IsP ⟨p, t₁, s⟩ := isP_of_f_eq (by omega) h1 (by omega)
  have hP2 : IsP ⟨p, t₂, s⟩ := isP_of_f_eq (by omega) h2 (by omega)
  exact no_move hP2 (move_row2 ht (by omega)) hP1

theorem f_diag_inj {a b : Nat} (hab : a < b) : f a a ≠ f b b := by
  intro heq
  have ha := f_gt (Nat.le_refl a)
  have hb := f_gt (Nat.le_refl b)
  have hPb := isP_f (Nat.le_refl b) (by omega)
  have hPa : IsP ⟨f b b, a, a⟩ := isP_of_f_eq (Nat.le_refl a) heq (by omega)
  exact no_move hPb (move_row2 hab (by omega)) hPa

/-- Proposition 4.4, the easy half: every `h ≥ 1` is a partner or a diagonal value. -/
theorem f_cover {h : Nat} (hh : 1 ≤ h) :
    (∃ r, r < h ∧ f h r = h) ∨ (∃ a, f a a = h) := by
  obtain ⟨Z, hm, hZ⟩ := isN_exists (rect_isN hh)
  rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact absurd (rect_isN h1) (fun hN => not_both (hZ.cast rfl (by omega) (by omega)) hN)
  · exact Or.inr ⟨j, f_eq_of_isP (Nat.le_refl j) hj (by omega) (hZ.cast rfl rfl (by omega))⟩
  · exact Or.inl ⟨j, hj, f_eq_of_isP (by omega) hj (Nat.le_refl h) hZ⟩

/-- The recurrence at a diagonal cell: every value below `f a a` is blocked. -/
theorem f_diag_mex {a v : Nat} (hv : 1 ≤ v) (hlt : v < f a a) :
    (∃ c, c < a ∧ f c c = v) ∨ (∃ b, b < a ∧ f a b = v) := by
  by_cases hva : a ≤ v
  · have hN : IsN ⟨v, a, a⟩ := by
      by_cases hav : v = a
      · subst hav; exact rect_isN hv
      · refine isN_of_not_isP (fun hP => ?_)
        have := f_eq_of_isP (Nat.le_refl a) (by omega) hva hP
        omega
    obtain ⟨Z, hm, hZ⟩ := isN_exists hN
    rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exfalso
      by_cases hka : k ≤ a
      · exact not_both (hZ.cast rfl (by omega) (by omega)) (rect_isN h1)
      · have := f_eq_of_isP (Nat.le_refl a) (by omega) (by omega)
          (hZ.cast rfl (by omega) (by omega))
        omega
    · exact Or.inl ⟨j, hj, f_eq_of_isP (Nat.le_refl j) (by omega) (by omega)
        (hZ.cast rfl rfl (by omega))⟩
    · exact Or.inr ⟨j, hj, f_eq_of_isP (by omega) (by omega) hva hZ⟩
  · obtain ⟨Z, hm, hZ⟩ := isN_exists (rect_isN hv)
    rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact absurd (rect_isN h1) (fun hN => not_both (hZ.cast rfl (by omega) (by omega)) hN)
    · exact Or.inl ⟨j, by omega, f_eq_of_isP (Nat.le_refl j) hj (by omega)
        (hZ.cast rfl rfl (by omega))⟩
    · exact Or.inr ⟨j, by omega, f_eq_of_partner hj (by omega) hZ⟩

/-- Lemma 4.2, row-start propagation, in terms of positions: if `[p,p,r]` is P and `r < q < p`
then some `[p,q,b]` with `b < r` is P. -/
theorem row_start_isP {p r : Nat} (hP : IsP ⟨p, p, r⟩) :
    ∀ (n q : Nat), p - q = n → r < q → q < p → ∃ b, b < r ∧ IsP ⟨p, q, b⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro q hn hrq hqp
    apply Classical.byContradiction
    intro hno
    have h := cnt_le_of_rel (fun t => q ≤ t) (fun k => q + 1 ≤ k)
      (fun k t => ∃ s, IsP ⟨k, q, s⟩ ∧
        ((t = q ∧ s = r) ∨ (q < t ∧ s < r ∧ IsP ⟨p, t, s⟩))) p p
      (by
        intro t htp hqt
        by_cases htq : t = q
        · -- the position [p,q,r]
          have hN : IsN ⟨p, q, r⟩ :=
            isN_of_not_isP (fun hQ => no_move hP (move_row2 hqp (by omega)) hQ)
          obtain ⟨Z, hm, hZ⟩ := isN_exists hN
          rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · by_cases hkq : k ≤ q
            · exact absurd hZ (fun hQ => no_move hP (move_row1 h1 hk (by omega) rfl) hQ)
            · exact ⟨k, hk, by omega, r, hZ.cast rfl (by omega) (by omega), Or.inl ⟨htq, rfl⟩⟩
          · exact absurd hZ (fun hQ => no_move hP (move_row2 (by omega) rfl) hQ)
          · exact absurd ⟨j, hj, hZ⟩ hno
        · -- a level t above q: its witness row s
          obtain ⟨s, hs, hPs⟩ := ih (p - t) (by omega) t rfl (by omega) htp
          have hN : IsN ⟨p, q, s⟩ :=
            isN_of_not_isP (fun hQ => no_move hPs (move_row2 (by omega) (by omega)) hQ)
          obtain ⟨Z, hm, hZ⟩ := isN_exists hN
          rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · by_cases hkq : k ≤ q
            · exact absurd hZ
                (fun hQ => no_move hPs (move_row1 h1 hk (by omega) rfl) hQ)
            · exact ⟨k, hk, by omega, s, hZ.cast rfl (by omega) (by omega),
                Or.inr ⟨by omega, hs, hPs⟩⟩
          · exact absurd hZ (fun hQ => no_move hPs (move_row2 (by omega) rfl) hQ)
          · exact absurd ⟨j, by omega, hZ⟩ hno)
      (by
        intro k t t2 ht ht2 hqt hqt2 h1 h2
        obtain ⟨s, hks, hcase⟩ := h1
        obtain ⟨s2, hks2, hcase2⟩ := h2
        have hss : s = s2 := by
          apply Classical.byContradiction
          intro hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact no_move hks2 (move_row3 hlt) hks
          · exact no_move hks (move_row3 hgt) hks2
        subst hss
        rcases hcase with ⟨h1, _⟩ | ⟨h1, hsr, hPt⟩
        · rcases hcase2 with ⟨h2, _⟩ | ⟨_, hsr2, _⟩
          · omega
          · omega
        · rcases hcase2 with ⟨_, h2⟩ | ⟨h2, _, hPt2⟩
          · omega
          · apply Classical.byContradiction
            intro hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · exact no_move hPt2 (move_row2 hlt (by omega)) hPt
            · exact no_move hPt (move_row2 hgt (by omega)) hPt2)
    rw [cnt_ge, cnt_ge] at h
    omega

/-- Lemma 4.2. -/
theorem f_row_start {p r q : Nat} (hrq : r < q) (hqp : q < p) (hp : f p r = p) :
    ∃ b, b < r ∧ f q b = p := by
  obtain ⟨b, hb, hPb⟩ := row_start_isP (partner_isP (by omega) hp) (p - q) q rfl hrq hqp
  exact ⟨b, hb, f_eq_of_isP (by omega) (by omega) (by omega) hPb⟩

/-- Proposition 4.3. -/
theorem f_diag_ne_partner {a p r : Nat} (hrp : r < p) (hp : f p r = p) : f a a ≠ p := by
  intro ha
  have hPp := partner_isP hrp hp
  have hap : a < p := by have := f_gt (Nat.le_refl a); omega
  have hPa : IsP ⟨p, a, a⟩ := isP_of_f_eq (Nat.le_refl a) ha (by omega)
  by_cases hra : a ≤ r
  · exact no_move hPp (move_row2 hap (by omega)) hPa
  · obtain ⟨b, hb, hfb⟩ := f_row_start (show r < a by omega) hap hp
    have hPb : IsP ⟨p, a, b⟩ := isP_of_f_eq (by omega) hfb (by omega)
    exact no_move hPa (move_row3 (by omega)) hPb

theorem exists_argmax (g : Nat → Nat) : ∀ n, ∃ r, r ≤ n ∧ ∀ s, s ≤ n → g s ≤ g r := by
  intro n
  induction n with
  | zero =>
    refine ⟨0, Nat.le_refl 0, fun s hs => ?_⟩
    have : s = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨r, hr, hmax⟩ := ih
    by_cases h : g r ≤ g (n + 1)
    · refine ⟨n + 1, Nat.le_refl _, fun s hs => ?_⟩
      by_cases hs2 : s = n + 1
      · subst hs2; exact Nat.le_refl _
      · have := hmax s (by omega); omega
    · refine ⟨r, by omega, fun s hs => ?_⟩
      by_cases hs2 : s = n + 1
      · subst hs2; omega
      · exact hmax s (by omega)

/-- Lemma 4.1: the diagonal value is the largest of its level. -/
theorem f_diag_max {q r : Nat} (hrq : r ≤ q) : f q r ≤ f q q := by
  obtain ⟨r₀, hr₀, hmax⟩ := exists_argmax (fun s => f q s) q
  by_cases h0 : r₀ = q
  · subst h0; exact hmax r hrq
  · exfalso
    have hr₀q : r₀ < q := by omega
    have hMq : q < f q r₀ := by
      have := f_gt (Nat.le_refl q); have := hmax q (Nat.le_refl q); omega
    have h := cnt_le_of_rel (fun s => r₀ + 1 ≤ s) (fun j => r₀ + 1 ≤ j)
      (fun j s => j < f q s ∧ IsP ⟨f q s, j, r₀⟩) (q + 1) q
      (by
        intro s hsq hs
        have hsM : f q s < f q r₀ := by
          have := hmax s (by omega)
          have := f_row_inj (q := q) (show r₀ < s by omega) (by omega)
          omega
        have hsv := f_gt (show s ≤ q by omega)
        by_cases hvq : q ≤ f q s
        · have hPs := isP_f (show s ≤ q by omega) hvq
          have hN : IsN ⟨f q s, q, r₀⟩ := by
            refine isN_of_not_isP (fun hQ => ?_)
            have := f_eq_of_isP (show r₀ ≤ q by omega) (by omega) hvq hQ
            omega
          obtain ⟨Z, hm, hZ⟩ := isN_exists hN
          rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · exfalso
            by_cases hkr : k ≤ r₀
            · exact not_both (hZ.cast rfl (by omega) (by omega)) (rect_isN h1)
            · by_cases hkq : k < q
              · have := f_eq_of_partner (q := q) (show r₀ < k by omega) hkq
                  (hZ.cast rfl (by omega) (by omega))
                omega
              · have := f_eq_of_isP (show r₀ ≤ q by omega) (by omega) (show q ≤ k by omega)
                  (hZ.cast rfl (by omega) (by omega))
                omega
          · by_cases hjr : j ≤ r₀
            · exact absurd hZ
                (fun hQ => no_move hPs (move_row2 (c' := j) hj (by omega))
                  (hQ.cast rfl rfl (by omega)))
            · exact ⟨j, hj, by omega, by omega, hZ.cast rfl rfl (by omega)⟩
          · exact absurd hZ (fun hQ => no_move hPs (move_row3 (by omega)) hQ)
        · have hPs := isP_f_lt (show s ≤ q by omega) (by omega)
          have hN : IsN ⟨f q s, f q s, r₀⟩ := by
            refine isN_of_not_isP (fun hQ => ?_)
            have := f_eq_of_partner (q := q) (show r₀ < f q s by omega) (by omega) hQ
            omega
          obtain ⟨Z, hm, hZ⟩ := isN_exists hN
          rcases move_cases hm with ⟨k, h1, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · exfalso
            by_cases hkr : k ≤ r₀
            · exact not_both (hZ.cast rfl (by omega) (by omega)) (rect_isN h1)
            · have := f_eq_of_partner (q := q) (show r₀ < k by omega) (by omega)
                (hZ.cast rfl (by omega) (by omega))
              omega
          · by_cases hjr : j ≤ r₀
            · exact absurd hZ
                (fun hQ => no_move hPs (move_row2 (c' := j) hj (by omega))
                  (hQ.cast rfl rfl (by omega)))
            · exact ⟨j, by omega, by omega, hj, hZ.cast rfl rfl (by omega)⟩
          · exact absurd hZ (fun hQ => no_move hPs (move_row3 (by omega)) hQ))
      (by
        intro j s s2 hs hs2 hsr hsr2 h1 h2
        have hv := f_gt (show s ≤ q by omega)
        have hv2 := f_gt (show s2 ≤ q by omega)
        have heq : f q s = f q s2 :=
          first_row_unique (by omega) (by omega) (by omega) (by omega) h1.2 h2.2
        apply Classical.byContradiction
        intro hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact f_row_inj hlt (by omega) heq
        · exact f_row_inj hgt (by omega) heq.symm)
    rw [cnt_ge, cnt_ge] at h
    omega

/-! ## The side-class theorem for three-row Chomp -/

/-- The function `f` of three-row Chomp satisfies all the hypotheses of `SideClass.lean`. -/
theorem table : Table f where
  gt_row := fun _ _ h => f_gt h
  enc := fun _ _ h1 h2 => f_enc h1 h2
  const := fun _ _ _ h1 h2 h3 => f_const h1 h2 h3
  row_inj := fun _ _ _ h1 h2 => f_row_inj h1 h2
  col_once := fun _ _ _ _ h1 h2 h3 h4 => f_col_once h1 h2 h3 h4
  row_start := fun _ _ _ h1 h2 h3 => f_row_start h1 h2 h3
  diag_ne_partner := fun _ _ _ h1 h2 => f_diag_ne_partner h1 h2
  cover := fun _ h => f_cover h
  diag_mex := fun _ _ h1 h2 => f_diag_mex h1 h2
  diag_max := fun _ _ h => f_diag_max h
  diag_inj := fun _ _ h => f_diag_inj h

/-- The side class: the `x` with no P-position `[p,p,x]`, `p > x`. -/
def Side (x : Nat) : Prop := ∀ p, x < p → ¬ IsP ⟨p, p, x⟩

theorem side_iff (x : Nat) : Side x ↔ SideClass.Side f x := by
  constructor
  · intro h p hp hfp; exact h p hp (partner_isP hp hfp)
  · intro h p hp hP; exact h p hp (f_eq_of_isP (by omega) hp (Nat.le_refl p) hP)

/-- **More than `v/5` of the numbers `0, …, v` are in the side class, for every `v`.** -/
theorem side_density (v : Nat) : v < 5 * cnt Side (v + 1) := by
  have h := table.side_density v
  have e : cnt Side (v + 1) = cnt (SideClass.Side f) (v + 1) :=
    cnt_congr _ (fun x _ => side_iff x)
  omega

/-- **The side class of three-row Chomp is infinite.** -/
theorem side_unbounded (N : Nat) : ∃ x, N ≤ x ∧ Side x := by
  obtain ⟨x, hx, hs⟩ := table.side_unbounded N
  exact ⟨x, hx, (side_iff x).2 hs⟩

/-- **A P-position `[p,p,x]` has `3p ≤ 5x + 3`.** -/
theorem partner_le {x p : Nat} (hxp : x < p) (hP : IsP ⟨p, p, x⟩) : 3 * p ≤ 5 * x + 3 :=
  table.partner_le hxp (f_eq_of_isP (by omega) hxp (Nat.le_refl p) hP)

/-- **The rows `x < T` with a P-position `[p,p,x]`, `p ≤ T`, number at most twice the side
elements below `T`.** -/
theorem partners_le_two_side (T : Nat) :
    cnt (fun x => ∃ p, x < p ∧ p ≤ T ∧ IsP ⟨p, p, x⟩) T ≤ 2 * cnt Side T := by
  have h := table.dead_le_two_side T
  have e1 : cnt (fun x => ∃ p, x < p ∧ p ≤ T ∧ IsP ⟨p, p, x⟩) T = nDead f T :=
    cnt_congr _ (fun x _ => ⟨
      fun ⟨p, hxp, hpT, hP⟩ => ⟨p, hxp, hpT, f_eq_of_isP (by omega) hxp (Nat.le_refl p) hP⟩,
      fun ⟨p, hxp, hpT, hfp⟩ => ⟨p, hxp, hpT, partner_isP hxp hfp⟩⟩)
  have e2 : cnt Side T = cnt (SideClass.Side f) T := cnt_congr _ (fun x _ => side_iff x)
  omega

/-- **Diagonal positions lie above the partners of the rows below them:** if `[p,p,x]` and
`[d,a,a]` are P-positions with `x ≤ a`, then `p < d`. -/
theorem partner_lt_diag {x p a d : Nat} (hxp : x < p) (hP : IsP ⟨p, p, x⟩) (hxa : x ≤ a)
    (had : a < d) (hD : IsP ⟨d, a, a⟩) : p < d := by
  have h := table.diag_gt_partner hxp (f_eq_of_isP (by omega) hxp (Nat.le_refl p) hP) hxa
  have e := f_eq_of_isP (Nat.le_refl a) had (by omega) hD
  omega

end Chomp.ThreeRow
