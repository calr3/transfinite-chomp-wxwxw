/-!
# The side class of three-row Chomp is infinite

This file checks the counting argument of `notes/13-side-class-theorem.md`. It does not define
three-row Chomp. Instead it takes an arbitrary function `f : Nat → Nat → Nat` and assumes, as
the fields of `Table f`, the statements about the function `f(q,r)` of Brouwer, Horváth,
Molnár-Sáska and Szabó that are proved in E. Sheiner, *Unique Winning Opening Move in Three-Row
Chomp* (arXiv:2605.23837v2). From these it derives:

* `Table.remaining` — the remaining-lifetime lemma;
* `Table.dead_le_two_side` — the P-positions `[h,h,x]` with `h ≤ T` number at most twice the
  side elements below `T`;
* `Table.partner_le` — a partner satisfies `3·τ(r) ≤ 5r + 3`;
* `Table.side_density` — more than `v/5` side elements up to `v`, for every `v`;
* `Table.side_unbounded` — the side class is infinite.

Everything is in Lean core (no Mathlib), so finite sets are replaced by a counting function
`cnt P n = #{x < n : P x}`.
-/

namespace Chomp.SideClass

open Classical

/-! ## Counting -/

/-- `cnt P n` is the number of `x < n` with `P x`. -/
noncomputable def cnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt P n + (if P n then 1 else 0)

theorem cnt_succ_pos {P : Nat → Prop} {n : Nat} (h : P n) : cnt P (n + 1) = cnt P n + 1 := by
  simp [cnt, h]

theorem cnt_succ_neg {P : Nat → Prop} {n : Nat} (h : ¬ P n) : cnt P (n + 1) = cnt P n := by
  simp [cnt, h]

theorem cnt_succ_le (P : Nat → Prop) (n : Nat) : cnt P (n + 1) ≤ cnt P n + 1 := by
  by_cases h : P n
  · rw [cnt_succ_pos h]; exact Nat.le_refl _
  · rw [cnt_succ_neg h]; exact Nat.le_succ _

theorem cnt_le_succ (P : Nat → Prop) (n : Nat) : cnt P n ≤ cnt P (n + 1) := by
  by_cases h : P n
  · rw [cnt_succ_pos h]; exact Nat.le_succ _
  · rw [cnt_succ_neg h]; exact Nat.le_refl _

theorem cnt_le (P : Nat → Prop) (n : Nat) : cnt P n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => have := cnt_succ_le P n; omega

theorem cnt_mono (P : Nat → Prop) {n m : Nat} (h : n ≤ m) : cnt P n ≤ cnt P m := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; exact Nat.le_refl _
    · have := ih (by omega)
      have := cnt_le_succ P m
      omega

theorem cnt_le_add (P : Nat → Prop) (n k : Nat) : cnt P (n + k) ≤ cnt P n + k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => have := cnt_succ_le P (n + k); rw [← Nat.add_assoc]; omega

theorem cnt_congr {P Q : Nat → Prop} :
    ∀ n, (∀ x, x < n → (P x ↔ Q x)) → cnt P n = cnt Q n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have ih' := ih (fun x hx => h x (by omega))
    by_cases hP : P n
    · have hQ : Q n := (h n (by omega)).1 hP
      rw [cnt_succ_pos hP, cnt_succ_pos hQ, ih']
    · have hQ : ¬ Q n := fun hq => hP ((h n (by omega)).2 hq)
      rw [cnt_succ_neg hP, cnt_succ_neg hQ, ih']

theorem cnt_mono_pred {P Q : Nat → Prop} :
    ∀ n, (∀ x, x < n → P x → Q x) → cnt P n ≤ cnt Q n := by
  intro n
  induction n with
  | zero => intro _; exact Nat.le_refl _
  | succ n ih =>
    intro h
    have ih' := ih (fun x hx => h x (by omega))
    by_cases hP : P n
    · have hQ : Q n := h n (by omega) hP
      rw [cnt_succ_pos hP, cnt_succ_pos hQ]; omega
    · rw [cnt_succ_neg hP]; have := cnt_le_succ Q n; omega

theorem cnt_false (n : Nat) : cnt (fun _ => False) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ_neg (fun h => h), ih]

theorem cnt_add_not (P : Nat → Prop) (n : Nat) : cnt P n + cnt (fun x => ¬ P x) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hP : P n
    · rw [cnt_succ_pos hP, cnt_succ_neg (show ¬ ¬ P n from fun h => h hP)]; omega
    · rw [cnt_succ_neg hP, cnt_succ_pos (show ¬ P n from hP)]; omega

/-- Two predicates that never hold together. -/
theorem cnt_add_le_of_disj {P Q R : Nat → Prop} :
    ∀ n, (∀ x, x < n → P x → R x) → (∀ x, x < n → Q x → R x) →
      (∀ x, x < n → ¬ (P x ∧ Q x)) → cnt P n + cnt Q n ≤ cnt R n := by
  intro n
  induction n with
  | zero => intro _ _ _; exact Nat.le_refl _
  | succ n ih =>
    intro hP hQ hd
    have ih' := ih (fun x hx => hP x (by omega)) (fun x hx => hQ x (by omega))
      (fun x hx => hd x (by omega))
    by_cases h1 : P n
    · have h2 : ¬ Q n := fun h => hd n (by omega) ⟨h1, h⟩
      rw [cnt_succ_pos h1, cnt_succ_neg h2, cnt_succ_pos (hP n (by omega) h1)]; omega
    · by_cases h2 : Q n
      · rw [cnt_succ_neg h1, cnt_succ_pos h2, cnt_succ_pos (hQ n (by omega) h2)]; omega
      · rw [cnt_succ_neg h1, cnt_succ_neg h2]; have := cnt_le_succ R n; omega

/-- Every `x < n` with `R x` satisfies `P x` or `Q x`. -/
theorem cnt_le_add_of_cover {P Q R : Nat → Prop} :
    ∀ n, (∀ x, x < n → R x → P x ∨ Q x) → cnt R n ≤ cnt P n + cnt Q n := by
  intro n
  induction n with
  | zero => intro _; exact Nat.le_refl _
  | succ n ih =>
    intro h
    have ih' := ih (fun x hx => h x (by omega))
    have hp := cnt_le_succ P n
    have hq := cnt_le_succ Q n
    by_cases hR : R n
    · rw [cnt_succ_pos hR]
      rcases h n (by omega) hR with h1 | h1
      · rw [cnt_succ_pos h1]; omega
      · rw [cnt_succ_pos h1]; omega
    · rw [cnt_succ_neg hR]; omega

theorem cnt_ge (a : Nat) (n : Nat) : cnt (fun x => a ≤ x) n = n - a := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    by_cases h : a ≤ n
    · rw [cnt_succ_pos h, ih]; omega
    · rw [cnt_succ_neg h, ih]; omega

theorem cnt_lt (m : Nat) (n : Nat) : cnt (fun x => x < m) n = min m n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    by_cases h : n < m
    · rw [cnt_succ_pos (P := fun x => x < m) h, ih]; omega
    · rw [cnt_succ_neg (P := fun x => x < m) h, ih]; omega

theorem cnt_true (n : Nat) : cnt (fun _ => True) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ_pos trivial, ih]

/-- Removing one element lowers the count by one. -/
theorem cnt_remove {T : Nat → Prop} {t0 : Nat} (hT : T t0) :
    ∀ m, t0 < m → cnt T m = cnt (fun t => T t ∧ t ≠ t0) m + 1 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    by_cases hm : m = t0
    · subst hm
      have h1 : cnt T (m + 1) = cnt T m + 1 := cnt_succ_pos hT
      have h2 : cnt (fun t => T t ∧ t ≠ m) (m + 1) = cnt (fun t => T t ∧ t ≠ m) m :=
        cnt_succ_neg (fun h => h.2 rfl)
      have h3 : cnt T m = cnt (fun t => T t ∧ t ≠ m) m :=
        cnt_congr m (fun x hx => ⟨fun hx' => ⟨hx', by omega⟩, fun hx' => hx'.1⟩)
      omega
    · have ih' := ih (by omega)
      by_cases hTm : T m
      · rw [cnt_succ_pos hTm, cnt_succ_pos (show T m ∧ m ≠ t0 from ⟨hTm, hm⟩)]; omega
      · rw [cnt_succ_neg hTm, cnt_succ_neg (show ¬ (T m ∧ m ≠ t0) from fun h => hTm h.1)]
        omega

/-- Pigeonhole: an injection from `{t < m : T t}` into `{x < n : P x}`. -/
theorem cnt_inj (g : Nat → Nat) : ∀ (n : Nat) (T P : Nat → Prop) (m : Nat),
    (∀ t, t < m → T t → g t < n ∧ P (g t)) →
    (∀ t t', t < m → t' < m → T t → T t' → g t = g t' → t = t') →
    cnt T m ≤ cnt P n := by
  intro n
  induction n with
  | zero =>
    intro T P m hmap _
    have h : cnt T m = cnt (fun _ => False) m :=
      cnt_congr m (fun x hx => ⟨fun h => by have := (hmap x hx h).1; omega, fun h => h.elim⟩)
    rw [h, cnt_false]; exact Nat.zero_le _
  | succ n ih =>
    intro T P m hmap hinj
    by_cases hex : ∃ t0, t0 < m ∧ T t0 ∧ g t0 = n
    · obtain ⟨t0, h0, hT0, hg0⟩ := hex
      have hPn : P n := by have := (hmap t0 h0 hT0).2; rwa [hg0] at this
      have key := ih (fun t => T t ∧ t ≠ t0) P m
        (fun t ht hTt => by
          have h1 := hmap t ht hTt.1
          have h2 : g t ≠ n := fun hgt => hTt.2 (hinj t t0 ht h0 hTt.1 hT0 (by omega))
          exact ⟨by omega, h1.2⟩)
        (fun t t' ht ht' hTt hTt' => hinj t t' ht ht' hTt.1 hTt'.1)
      rw [cnt_remove hT0 m h0, cnt_succ_pos hPn]; omega
    · have key := ih T P m
        (fun t ht hTt => by
          have h1 := hmap t ht hTt
          have h2 : g t ≠ n := fun hgt => hex ⟨t, ht, hTt, hgt⟩
          exact ⟨by omega, h1.2⟩)
        hinj
      have h2 := cnt_le_succ P n
      omega

/-- Pigeonhole in relational form. Every `t < m` with `T t` is related to some `c < n` with
`P c`, and `c` determines `t`. -/
theorem cnt_le_of_rel (T P : Nat → Prop) (R : Nat → Nat → Prop) (m n : Nat)
    (hex : ∀ t, t < m → T t → ∃ c, c < n ∧ P c ∧ R c t)
    (hinj : ∀ c t t', t < m → t' < m → T t → T t' → R c t → R c t' → t = t') :
    cnt T m ≤ cnt P n := by
  let g : Nat → Nat := fun t =>
    if h : ∃ c, c < n ∧ P c ∧ R c t then Classical.choose h else 0
  have hg : ∀ t, t < m → T t → g t < n ∧ P (g t) ∧ R (g t) t := by
    intro t ht hTt
    have h := hex t ht hTt
    have e : g t = Classical.choose h := by simp only [g, h, dite_true]
    rw [e]; exact Classical.choose_spec h
  refine cnt_inj g n T P m (fun t ht hTt => ⟨(hg t ht hTt).1, (hg t ht hTt).2.1⟩) ?_
  intro t t' ht ht' hTt hTt' heq
  have h1 := (hg t ht hTt).2.2
  have h2 := (hg t' ht' hTt').2.2
  rw [← heq] at h2
  exact hinj (g t) t t' ht ht' hTt hTt' h1 h2

/-! ## The table of three-row Chomp, abstractly

`f q r` (`r ≤ q`) stands for the function of Brouwer, Horváth, Molnár-Sáska and Szabó: the
unique `p > r` such that either `r < p < q` and `[p,p,r]` is a P-position, or `p ≥ q` and
`[p,q,r]` is a P-position. So `[p,p,r]` is P iff `r < p` and `f p r = p`. The fields are:

* `gt_row`, `enc`, `const`: the definition of `f` (Sheiner, Lemma 2.1);
* `row_inj`, `col_once`: Lemma 2.3(a),(b);
* `row_start`: Lemma 4.2 (row-start propagation);
* `diag_ne_partner`, `cover`: Propositions 4.3 and 4.4;
* `diag_mex`: the recurrence at a diagonal cell, `f(a,a) = mex B(a,a)`;
* `diag_max`: Lemma 4.1;
* `diag_inj`: `a ↦ f(a,a)` is injective (proof of Theorem 1.1).
-/

structure Table (f : Nat → Nat → Nat) : Prop where
  gt_row : ∀ q r, r ≤ q → r < f q r
  enc : ∀ q r, r ≤ q → f q r < q → f (f q r) r = f q r
  const : ∀ r k q, r < k → f k r = k → k ≤ q → f q r = k
  row_inj : ∀ q b₁ b₂, b₁ < b₂ → b₂ ≤ q → f q b₁ ≠ f q b₂
  col_once : ∀ s t₁ t₂ p, s < t₁ → t₁ < t₂ → t₂ < p → f t₁ s = p → f t₂ s ≠ p
  row_start : ∀ p r q, r < q → q < p → f p r = p → ∃ b, b < r ∧ f q b = p
  diag_ne_partner : ∀ a p r, r < p → f p r = p → f a a ≠ p
  cover : ∀ h, 1 ≤ h → (∃ r, r < h ∧ f h r = h) ∨ (∃ a, f a a = h)
  diag_mex : ∀ a v, 1 ≤ v → v < f a a →
    (∃ c, c < a ∧ f c c = v) ∨ (∃ b, b < a ∧ f a b = v)
  diag_max : ∀ q r, r ≤ q → f q r ≤ f q q
  diag_inj : ∀ a b, a < b → f a a ≠ f b b

/-- Row `x` has got its P-position `[p,p,x]` by time `t`. -/
def Dead (f : Nat → Nat → Nat) (x t : Nat) : Prop := ∃ p, x < p ∧ p ≤ t ∧ f p x = p

/-- Row `x` is born and has no P-position `[p,p,x]` with `p ≤ t`. -/
def Alive (f : Nat → Nat → Nat) (x t : Nat) : Prop := x < t ∧ ¬ Dead f x t

/-- `x` is in the side class: no `[p,p,x]` with `p > x` is a P-position. -/
def Side (f : Nat → Nat → Nat) (x : Nat) : Prop := ∀ p, x < p → f p x ≠ p

/-- The number of rows alive at time `t`. -/
noncomputable def nAlive (f : Nat → Nat → Nat) (t : Nat) : Nat := cnt (fun x => Alive f x t) t

/-- The number of rows `x` with a P-position `[p,p,x]`, `p ≤ t`. -/
noncomputable def nDead (f : Nat → Nat → Nat) (t : Nat) : Nat := cnt (fun x => Dead f x t) t

/-- `v` is a partner: some `[v,v,x]` is P. -/
def PV (f : Nat → Nat → Nat) (v : Nat) : Prop := ∃ x, x < v ∧ f v x = v

/-- `v` is a diagonal value: some `[v,a,a]` is P. -/
def DV (f : Nat → Nat → Nat) (v : Nat) : Prop := ∃ a, f a a = v

theorem alive_add_dead (f : Nat → Nat → Nat) (t : Nat) : nAlive f t + nDead f t = t := by
  have h1 : nAlive f t = cnt (fun x => ¬ Dead f x t) t :=
    cnt_congr t (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
  have h2 := cnt_add_not (fun x => Dead f x t) t
  have h3 : nDead f t = cnt (fun x => Dead f x t) t := rfl
  omega

namespace Table

variable {f : Nat → Nat → Nat}

theorem partner_unique (H : Table f) {x p p' : Nat} (hp : x < p) (h : f p x = p)
    (hp' : x < p') (h' : f p' x = p') : p = p' := by
  by_cases hle : p ≤ p'
  · have := H.const x p p' hp h hle; omega
  · have := H.const x p' p hp' h' (by omega); omega

/-- **Remaining lifetime.** If `[p,p,x]` is P and `x < q < p`, then `p - q` is at most the
number of rows below `x` that are alive at time `q`. -/
theorem remaining (H : Table f) {x q p : Nat} (hxq : x < q) (hqp : q < p) (hp : f p x = p) :
    p - q ≤ cnt (fun b => Alive f b q) x := by
  have h := cnt_le_of_rel (fun t => q ≤ t) (fun b => Alive f b q)
    (fun b t => b < x ∧ f t b = p) p x
    (by
      intro t ht hqt
      obtain ⟨b, hb, hfb⟩ := H.row_start p x t (by omega) ht hp
      refine ⟨b, hb, ⟨by omega, ?_⟩, hb, hfb⟩
      rintro ⟨k, hbk, hkq, hk⟩
      have := H.const b k t hbk hk (by omega)
      omega)
    (by
      intro b t t' ht ht' hqt hqt' h1 h2
      by_cases hne : t = t'
      · exact hne
      · exfalso
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact H.col_once b t t' p (by omega) hlt ht' h1.2 h2.2
        · exact H.col_once b t' t p (by omega) hgt ht h2.2 h1.2)
  rw [cnt_ge] at h
  exact h

/-- A row alive at time `q` and still alive `nAlive f q` steps later is in the side class. -/
theorem side_of_alive (H : Table f) {a q : Nat} (haq : a < q)
    (hal : Alive f a (q + nAlive f q)) : Side f a := by
  intro p hap hp
  have hpq : q + nAlive f q < p := by
    apply Nat.lt_of_not_le; intro hle; exact hal.2 ⟨p, hap, hle, hp⟩
  have hrem := H.remaining haq (by omega) hp
  have haq' : Alive f a q :=
    ⟨haq, fun ⟨k, hak, hkq, hk⟩ => hal.2 ⟨k, hak, by omega, hk⟩⟩
  have h1 : cnt (fun b => Alive f b q) (a + 1) = cnt (fun b => Alive f b q) a + 1 :=
    cnt_succ_pos haq'
  have h2 : cnt (fun b => Alive f b q) (a + 1) ≤ nAlive f q := cnt_mono _ (by omega)
  omega

theorem diag_le (H : Table f) (a : Nat) : f a a ≤ 2 * a + 1 := by
  have hc : cnt (fun v => 1 ≤ v) (f a a) ≤
      cnt (fun v => ∃ c, c < a ∧ f c c = v) (f a a) +
        cnt (fun v => ∃ b, b < a ∧ f a b = v) (f a a) :=
    cnt_le_add_of_cover (f a a) (fun v hv h1 => H.diag_mex a v h1 hv)
  have h1 : cnt (fun v => ∃ c, c < a ∧ f c c = v) (f a a) ≤ cnt (fun _ => True) a :=
    cnt_le_of_rel _ _ (fun c v => f c c = v) (f a a) a
      (fun v _ ⟨c, hc, hv⟩ => ⟨c, hc, trivial, hv⟩)
      (fun c v v' _ _ _ _ h h' => by omega)
  have h2 : cnt (fun v => ∃ b, b < a ∧ f a b = v) (f a a) ≤ cnt (fun _ => True) a :=
    cnt_le_of_rel _ _ (fun b v => f a b = v) (f a a) a
      (fun v _ ⟨b, hb, hv⟩ => ⟨b, hb, trivial, hv⟩)
      (fun b v v' _ _ _ _ h h' => by omega)
  rw [cnt_true] at h1 h2
  rw [cnt_ge] at hc
  omega

theorem dead_le_pv (H : Table f) (t : Nat) : nDead f t ≤ cnt (PV f) (t + 1) := by
  unfold nDead
  exact cnt_le_of_rel _ _ (fun v x => x < v ∧ f v x = v) t (t + 1)
    (fun x _ ⟨p, hxp, hpt, hp⟩ => ⟨p, by omega, ⟨x, hxp, hp⟩, hxp, hp⟩)
    (fun v x x' _ _ _ _ h h' => by
      by_cases hne : x = x'
      · exact hne
      · exfalso
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact H.row_inj v x x' hlt (by omega) (by omega)
        · exact H.row_inj v x' x hgt (by omega) (by omega))

theorem pv_le_dead (H : Table f) (t : Nat) : cnt (PV f) (t + 1) ≤ nDead f t := by
  unfold nDead
  exact cnt_le_of_rel _ _ (fun x v => x < v ∧ f v x = v) (t + 1) t
    (fun v hv ⟨x, hx, hfx⟩ => ⟨x, by omega, ⟨v, hx, by omega, hfx⟩, hx, hfx⟩)
    (fun x v v' _ _ _ _ h h' => H.partner_unique h.1 h.2 h'.1 h'.2)

theorem diag_count (H : Table f) (t : Nat) : (t + 1) / 2 ≤ cnt (DV f) (t + 1) := by
  have h : cnt (fun a => a < (t + 1) / 2) t ≤ cnt (DV f) (t + 1) :=
    cnt_le_of_rel _ _ (fun v a => f a a = v) t (t + 1)
      (fun a _ ha => ⟨f a a, by have := H.diag_le a; omega, ⟨a, rfl⟩, rfl⟩)
      (fun v a a' _ _ _ _ h h' => by
        by_cases hne : a = a'
        · exact hne
        · exfalso
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact H.diag_inj a a' hlt (by omega)
          · exact H.diag_inj a' a hgt (by omega))
  rw [cnt_lt] at h
  omega

/-- At most half of the rows below `t` have their P-position `[p,p,x]` with `p ≤ t`. -/
theorem two_dead_le (H : Table f) (t : Nat) : 2 * nDead f t ≤ t := by
  have h1 := H.dead_le_pv t
  have h2 := H.diag_count t
  have h3 : cnt (PV f) (t + 1) + cnt (DV f) (t + 1) ≤ cnt (fun v => 1 ≤ v) (t + 1) :=
    cnt_add_le_of_disj (t + 1)
      (fun v _ ⟨x, hx, _⟩ => by omega)
      (fun v _ ⟨a, ha⟩ => by have := H.gt_row a a (Nat.le_refl a); omega)
      (fun v _ ⟨⟨x, hx, hv⟩, ⟨a, ha⟩⟩ => H.diag_ne_partner a v x hx hv ha)
  rw [cnt_ge] at h3
  omega

theorem two_alive_ge (H : Table f) (t : Nat) : t ≤ 2 * nAlive f t := by
  have := alive_add_dead f t
  have := H.two_dead_le t
  omega

/-- **The P-positions `[p,p,x]` with `p ≤ T` number at most twice the side elements below
`T`.** -/
theorem dead_le_two_side (H : Table f) (T : Nat) : nDead f T ≤ 2 * cnt (Side f) T := by
  have hsum := alive_add_dead f T
  have h1 : nAlive f (T + nAlive f T) ≤
      cnt (fun x => Alive f x (T + nAlive f T)) T + nAlive f T :=
    cnt_le_add _ T (nAlive f T)
  have h2 : cnt (fun x => Alive f x (T + nAlive f T)) T ≤ cnt (Side f) T :=
    cnt_mono_pred T (fun a ha hal => H.side_of_alive ha hal)
  have h3 := H.two_alive_ge (T + nAlive f T)
  omega

theorem alive_pick_gt (H : Table f) {b a : Nat} (h : Alive f b a) : a < f a b := by
  have hb := h.1
  have h0 := H.gt_row a b (by omega)
  apply Nat.lt_of_not_le; intro hle
  by_cases heq : f a b = a
  · exact h.2 ⟨a, hb, Nat.le_refl a, heq⟩
  · have hlt : f a b < a := by omega
    exact h.2 ⟨f a b, h0, by omega, H.enc a b (by omega) hlt⟩

/-- The diagonal value exceeds the values of all rows alive at that level. -/
theorem diag_ge (H : Table f) (a : Nat) : a + nAlive f a + 1 ≤ f a a := by
  have h : nAlive f a ≤ cnt (fun v => a + 1 ≤ v) (f a a) :=
    cnt_le_of_rel _ _ (fun v b => b < a ∧ f a b = v) a (f a a)
      (fun b hb hal => ⟨f a b, by
          have h1 := H.diag_max a b (by omega)
          have h2 := H.row_inj a b a hb (Nat.le_refl a)
          omega,
        by have := H.alive_pick_gt hal; omega, hb, rfl⟩)
      (fun v b b' _ _ _ _ h h' => by
        by_cases hne : b = b'
        · exact hne
        · exfalso
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact H.row_inj a b b' hlt (by omega) (by omega)
          · exact H.row_inj a b' b hgt (by omega) (by omega))
  rw [cnt_ge] at h
  have := H.gt_row a a (Nat.le_refl a)
  omega

theorem nAlive_le (H : Table f) (t : Nat) : 3 * nAlive f t ≤ 2 * t + 1 := by
  have hsum := alive_add_dead f t
  have hpv := H.pv_le_dead t
  have hcov : cnt (fun v => 1 ≤ v) (t + 1) ≤
      cnt (fun v => 1 ≤ v ∧ ¬ PV f v) (t + 1) + cnt (PV f) (t + 1) :=
    cnt_le_add_of_cover (t + 1) (fun v _ h1 => by
      by_cases hp : PV f v
      · exact Or.inr hp
      · exact Or.inl ⟨h1, hp⟩)
  rw [cnt_ge] at hcov
  have hdiag : cnt (fun v => 1 ≤ v ∧ ¬ PV f v) (t + 1) ≤
      cnt (fun a => a < (2 * t + 1) / 3) (t + 1) :=
    cnt_le_of_rel _ _ (fun a v => f a a = v) (t + 1) (t + 1)
      (fun v hv ⟨h1, hnp⟩ => by
        rcases H.cover v h1 with ⟨r, hr, hfr⟩ | ⟨a, ha⟩
        · exact absurd ⟨r, hr, hfr⟩ hnp
        · have hge := H.diag_ge a
          have h2 := H.two_alive_ge a
          exact ⟨a, by omega, by omega, ha⟩)
      (fun a v v' _ _ _ _ h h' => by omega)
  rw [cnt_lt] at hdiag
  omega

theorem partner_le_alive (H : Table f) {r p : Nat} (hrp : r < p) (hp : f p r = p) :
    p ≤ r + nAlive f (r + 1) := by
  by_cases h1 : p = r + 1
  · have := H.two_alive_ge (r + 1); omega
  · have hrem := H.remaining (show r < r + 1 by omega) (by omega) hp
    have hal : Alive f r (r + 1) := ⟨by omega, fun ⟨k, hrk, hk1, hk⟩ => by
      have := H.partner_unique hrk hk hrp hp; omega⟩
    have h2 : cnt (fun b => Alive f b (r + 1)) (r + 1) =
        cnt (fun b => Alive f b (r + 1)) r + 1 := cnt_succ_pos hal
    have h3 : nAlive f (r + 1) = cnt (fun b => Alive f b (r + 1)) (r + 1) := rfl
    omega

theorem nDead_succ_le (H : Table f) (t : Nat) : nDead f (t + 1) ≤ nDead f t + 1 := by
  have h1 : cnt (fun x => Dead f x (t + 1)) (t + 1) ≤
      cnt (fun x => Dead f x t) (t + 1) + cnt (fun x => x < t + 1 ∧ f (t + 1) x = t + 1) (t + 1) :=
    cnt_le_add_of_cover (t + 1) (fun x _ ⟨p, hxp, hpt, hp⟩ => by
      by_cases hpe : p = t + 1
      · subst hpe; exact Or.inr ⟨hxp, hp⟩
      · exact Or.inl ⟨p, hxp, by omega, hp⟩)
  have h2 : cnt (fun x => Dead f x t) (t + 1) = cnt (fun x => Dead f x t) t :=
    cnt_succ_neg (fun ⟨p, htp, hpt, _⟩ => by omega)
  have h3 : cnt (fun x => x < t + 1 ∧ f (t + 1) x = t + 1) (t + 1) ≤ cnt (fun _ => True) 1 :=
    cnt_le_of_rel _ _ (fun _ x => x < t + 1 ∧ f (t + 1) x = t + 1) (t + 1) 1
      (fun x _ hx => ⟨0, by omega, trivial, hx⟩)
      (fun _ x x' _ _ _ _ h h' => by
        by_cases hne : x = x'
        · exact hne
        · exfalso
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact H.row_inj (t + 1) x x' hlt (by omega) (by omega)
          · exact H.row_inj (t + 1) x' x hgt (by omega) (by omega))
  rw [cnt_true] at h3
  have h4 : nDead f (t + 1) = cnt (fun x => Dead f x (t + 1)) (t + 1) := rfl
  have h5 : nDead f t = cnt (fun x => Dead f x t) t := rfl
  omega

theorem nDead_le_succ (f : Nat → Nat → Nat) (t : Nat) : nDead f t ≤ nDead f (t + 1) := by
  have h1 : cnt (fun x => Dead f x t) t ≤ cnt (fun x => Dead f x (t + 1)) t :=
    cnt_mono_pred t (fun x _ ⟨p, hxp, hpt, hp⟩ => ⟨p, hxp, by omega, hp⟩)
  have h2 := cnt_le_succ (fun x => Dead f x (t + 1)) t
  have h4 : nDead f (t + 1) = cnt (fun x => Dead f x (t + 1)) (t + 1) := rfl
  have h5 : nDead f t = cnt (fun x => Dead f x t) t := rfl
  omega

/-- The number of alive rows never decreases, and grows by at most one per step. -/
theorem nAlive_succ (H : Table f) (t : Nat) :
    nAlive f t ≤ nAlive f (t + 1) ∧ nAlive f (t + 1) ≤ nAlive f t + 1 := by
  have := alive_add_dead f t
  have := alive_add_dead f (t + 1)
  have := H.nDead_succ_le t
  have := nDead_le_succ f t
  omega

theorem nAlive_mono (H : Table f) {s t : Nat} (h : s ≤ t) : nAlive f s ≤ nAlive f t := by
  induction t with
  | zero => have : s = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ t ih =>
    by_cases hs : s = t + 1
    · subst hs; exact Nat.le_refl _
    · have := ih (by omega)
      have := (H.nAlive_succ t).1
      omega

/-- **No diagonal value of a row `a ≥ r` lies below the partner of `r`.** -/
theorem diag_gt_partner (H : Table f) {r p a : Nat} (hrp : r < p) (hp : f p r = p)
    (hra : r ≤ a) : p < f a a := by
  have hpa := H.partner_le_alive hrp hp
  have hge := H.diag_ge a
  by_cases hr : a = r
  · subst hr
    have h1 := (H.nAlive_succ a).2
    have h2 := H.diag_ne_partner a p a hrp hp
    omega
  · have h1 := H.nAlive_mono (show r + 1 ≤ a by omega)
    omega

/-- **A partner is at most `(5r+3)/3`.** -/
theorem partner_le (H : Table f) {r p : Nat} (hrp : r < p) (hp : f p r = p) :
    3 * p ≤ 5 * r + 3 := by
  have := H.partner_le_alive hrp hp
  have := H.nAlive_le (r + 1)
  omega

/-- **More than `v/5` side elements up to `v`, for every `v`.** -/
theorem side_density (H : Table f) (v : Nat) : v < 5 * cnt (Side f) (v + 1) := by
  have hmain := H.dead_le_two_side (v + 1)
  have hX : 3 * v / 5 + 1 ≤ v + 1 := by omega
  have h1 : cnt (fun x => ¬ Side f x) (3 * v / 5 + 1) ≤
      cnt (fun x => Dead f x (v + 1)) (3 * v / 5 + 1) :=
    cnt_mono_pred _ (fun x hx hns => by
      have hex : ∃ p, x < p ∧ f p x = p := by
        apply Classical.byContradiction; intro hno
        exact hns (fun p hp hfp => hno ⟨p, hp, hfp⟩)
      obtain ⟨p, hxp, hfp⟩ := hex
      have := H.partner_le hxp hfp
      exact ⟨p, hxp, by omega, hfp⟩)
  have h2 : cnt (fun x => Dead f x (v + 1)) (3 * v / 5 + 1) ≤ nDead f (v + 1) :=
    cnt_mono _ hX
  have h3 := cnt_add_not (Side f) (3 * v / 5 + 1)
  have h4 : cnt (Side f) (3 * v / 5 + 1) ≤ cnt (Side f) (v + 1) := cnt_mono _ hX
  omega

/-- **The side class is infinite.** -/
theorem side_unbounded (H : Table f) (N : Nat) : ∃ x, N ≤ x ∧ Side f x := by
  apply Classical.byContradiction; intro hno
  have h1 : cnt (Side f) (5 * N + 1) ≤ cnt (fun x => x < N) (5 * N + 1) :=
    cnt_mono_pred _ (fun x _ hs => by
      apply Nat.lt_of_not_le; intro hle; exact hno ⟨x, hle, hs⟩)
  rw [cnt_lt] at h1
  have := H.side_density (5 * N)
  omega

end Table

end Chomp.SideClass

/-! The main statements depend only on the standard axioms. -/
