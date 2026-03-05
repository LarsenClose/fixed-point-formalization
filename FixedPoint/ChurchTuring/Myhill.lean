/-
  Myhill.lean

  Proof of the effective Myhill isomorphism lemma via the back-and-forth
  (BFF) construction. This replaces the axiom in RogersIsomorphism.lean
  with a fully verified theorem.

  The construction builds a computable bijection h : ℕ ≃ ℕ from
  computable padding functions, then lifts to arbitrary Denumerable types.

  Structure:
  - Section BFFDefs: core definitions (list ops, findFresh, bffStep, bffState)
  - Section BFFTotality: every element is eventually matched
  - Section BFFBijectivity: the partial bijection invariant
  - Section BFFRPreservation: all pairs are R-related
  - Section BFFComputability: all operations are Computable
  - Section Assembly: combine into effective_myhill_nat and lift
-/

import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Halting
import Mathlib.Logic.Denumerable
import Mathlib.Computability.Reduce
import Mathlib.Data.Set.Finite.Basic

open Denumerable Encodable

-- ════════════════════════════════════════════════════════════════════
-- Section 1: BFF Definitions
-- ════════════════════════════════════════════════════════════════════

namespace Myhill

/-- Check if `a` is in the domain (first components) of an association list. -/
def inDomain (state : List (ℕ × ℕ)) (a : ℕ) : Bool :=
  state.any (fun p => p.1 == a)

/-- Check if `b` is in the range (second components) of an association list. -/
def inRange (state : List (ℕ × ℕ)) (b : ℕ) : Bool :=
  state.any (fun p => p.2 == b)

/-- Forward lookup: find the partner of `a` in the domain. -/
def lookupFwd (state : List (ℕ × ℕ)) (a : ℕ) : Option ℕ :=
  (state.find? (fun p => p.1 == a)).map Prod.snd

/-- Backward lookup: find the partner of `b` in the range. -/
def lookupBwd (state : List (ℕ × ℕ)) (b : ℕ) : Option ℕ :=
  (state.find? (fun p => p.2 == b)).map Prod.fst

-- ────────────────────────────────────────────────────────────────
-- Existence of fresh elements (needed for Nat.find)
-- ────────────────────────────────────────────────────────────────

/-- An injective function from ℕ to ℕ cannot have its range contained
    in a finite set, so there exists j with pad a j not in the range. -/
lemma findFreshFwd_exists (pad_f : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (state : List (ℕ × ℕ)) (a : ℕ) :
    ∃ j, inRange state (pad_f a j) = false := by
  by_contra h
  simp only [not_exists, Bool.not_eq_false] at h
  -- h : ∀ j, inRange state (pad_f a j) = true
  have hinf := Set.infinite_range_of_injective (pad_f_inj a)
  apply hinf
  apply Set.Finite.subset (state.map Prod.snd).toFinset.finite_toSet
  intro b ⟨j, hj⟩
  rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  have hj' := h j
  simp only [inRange, List.any_eq_true, beq_iff_eq] at hj'
  obtain ⟨p, hp_mem, hp_eq⟩ := hj'
  exact ⟨p, hp_mem, by rw [← hj]; exact hp_eq⟩

/-- Symmetric: fresh element exists for backward pass. -/
lemma findFreshBwd_exists (pad_g : ℕ → ℕ → ℕ)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (b : ℕ) :
    ∃ j, inDomain state (pad_g b j) = false := by
  by_contra h
  simp only [not_exists, Bool.not_eq_false] at h
  have hinf := Set.infinite_range_of_injective (pad_g_inj b)
  apply hinf
  apply Set.Finite.subset (state.map Prod.fst).toFinset.finite_toSet
  intro a ⟨j, hj⟩
  rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  have hj' := h j
  simp only [inDomain, List.any_eq_true, beq_iff_eq] at hj'
  obtain ⟨p, hp_mem, hp_eq⟩ := hj'
  exact ⟨p, hp_mem, by rw [← hj]; exact hp_eq⟩

-- ────────────────────────────────────────────────────────────────
-- Find least fresh index
-- ────────────────────────────────────────────────────────────────

/-- Find the least j such that `pad_f a j` is not in the range of state. -/
noncomputable def findFreshFwd (pad_f : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (state : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  Nat.find (findFreshFwd_exists pad_f pad_f_inj state a)

/-- Find the least j such that `pad_g b j` is not in the domain of state. -/
noncomputable def findFreshBwd (pad_g : ℕ → ℕ → ℕ)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (b : ℕ) : ℕ :=
  Nat.find (findFreshBwd_exists pad_g pad_g_inj state b)

lemma findFreshFwd_spec (pad_f : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (state : List (ℕ × ℕ)) (a : ℕ) :
    inRange state (pad_f a (findFreshFwd pad_f pad_f_inj state a)) = false :=
  Nat.find_spec (findFreshFwd_exists pad_f pad_f_inj state a)

lemma findFreshBwd_spec (pad_g : ℕ → ℕ → ℕ)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (b : ℕ) :
    inDomain state (pad_g b (findFreshBwd pad_g pad_g_inj state b)) = false :=
  Nat.find_spec (findFreshBwd_exists pad_g pad_g_inj state b)

-- ────────────────────────────────────────────────────────────────
-- BFF step function
-- ────────────────────────────────────────────────────────────────

/-- One step of the back-and-forth construction.
    - Even stages (n = 2k): match element k in the domain
    - Odd stages (n = 2k+1): match element k in the range -/
noncomputable def bffStep (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (n : ℕ) : List (ℕ × ℕ) :=
  if n % 2 = 0 then
    -- Forward pass: match element n/2 in the domain
    let a := n / 2
    if inDomain state a then state
    else
      let j := findFreshFwd pad_f pad_f_inj state a
      state ++ [(a, pad_f a j)]
  else
    -- Backward pass: match element n/2 in the range
    let b := n / 2
    if inRange state b then state
    else
      let j := findFreshBwd pad_g pad_g_inj state b
      state ++ [(pad_g b j, b)]

/-- BFF state after n stages. -/
noncomputable def bffState (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => bffStep pad_f pad_g pad_f_inj pad_g_inj
      (bffState pad_f pad_g pad_f_inj pad_g_inj n) n

/-- Helper: if `inDomain state a = true` then `lookupFwd state a` is `some`. -/
private lemma lookupFwd_isSome_of_inDomain' {state : List (ℕ × ℕ)} {a : ℕ}
    (h : inDomain state a = true) :
    (lookupFwd state a).isSome = true := by
  simp only [inDomain, List.any_eq_true] at h
  obtain ⟨⟨a', b⟩, hp_mem, hp_eq⟩ := h
  simp only [lookupFwd, Option.isSome_map]
  rw [List.find?_isSome]
  exact ⟨(a', b), hp_mem, hp_eq⟩

/-- Helper: if `inRange state b = true` then `lookupBwd state b` is `some`. -/
private lemma lookupBwd_isSome_of_inRange' {state : List (ℕ × ℕ)} {b : ℕ}
    (h : inRange state b = true) :
    (lookupBwd state b).isSome = true := by
  simp only [inRange, List.any_eq_true] at h
  obtain ⟨⟨a, b'⟩, hp_mem, hp_eq⟩ := h
  simp only [lookupBwd, Option.isSome_map]
  rw [List.find?_isSome]
  exact ⟨(a, b'), hp_mem, hp_eq⟩

/-- Element a is in the domain by stage 2a+1 (the forward pass at stage 2a).
    Proved here (before bffFwd) so the definition can use it. -/
lemma bffFwd_total (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (a : ℕ) :
    inDomain (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a = true := by
  change inDomain (bffStep pad_f pad_g pad_f_inj pad_g_inj
    (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a)) (2 * a)) a = true
  simp only [bffStep, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left a (by omega : 0 < 2)]
  split
  · assumption
  · simp only [inDomain, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
               Bool.or_eq_true, beq_iff_eq]
    right; trivial

/-- Element b is in the range by stage 2b+2 (the backward pass at stage 2b+1). -/
lemma bffBwd_total (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (b : ℕ) :
    inRange (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b = true := by
  change inRange (bffStep pad_f pad_g pad_f_inj pad_g_inj
    (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 1)) (2 * b + 1)) b = true
  simp only [bffStep]
  have hne : ¬ ((2 * b + 1) % 2 = 0) := by omega
  have hdiv : (2 * b + 1) / 2 = b := by omega
  rw [if_neg hne, hdiv]
  split
  · assumption
  · simp only [inRange, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
               Bool.or_eq_true, beq_iff_eq]
    right; trivial

/-- The forward map: look up element a's partner. -/
noncomputable def bffFwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (a : ℕ) : ℕ :=
  (lookupFwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a).get
    (lookupFwd_isSome_of_inDomain' (bffFwd_total pad_f pad_g pad_f_inj pad_g_inj a))

/-- The backward map: look up element b's partner. -/
noncomputable def bffBwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (b : ℕ) : ℕ :=
  (lookupBwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b).get
    (lookupBwd_isSome_of_inRange' (bffBwd_total pad_f pad_g pad_f_inj pad_g_inj b))

-- ════════════════════════════════════════════════════════════════════
-- Section 2: Monotonicity and basic properties
-- ════════════════════════════════════════════════════════════════════

/-- bffStep either keeps state unchanged or appends one element. -/
lemma bffStep_prefix (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (n : ℕ) :
    state <+: bffStep pad_f pad_g pad_f_inj pad_g_inj state n := by
  unfold bffStep
  split <;> dsimp only <;> split
  · exact List.prefix_rfl
  · exact List.prefix_append _ _
  · exact List.prefix_rfl
  · exact List.prefix_append _ _

/-- Unfolding lemma for bffState at successor. -/
lemma bffState_succ (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (n : ℕ) :
    bffState pad_f pad_g pad_f_inj pad_g_inj (n + 1) =
      bffStep pad_f pad_g pad_f_inj pad_g_inj
        (bffState pad_f pad_g pad_f_inj pad_g_inj n) n := by
  rfl

/-- bffState is monotonically growing. -/
lemma bffState_mono (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (n m : ℕ) (h : n ≤ m) :
    bffState pad_f pad_g pad_f_inj pad_g_inj n <+:
      bffState pad_f pad_g pad_f_inj pad_g_inj m := by
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.mp h
    subst this; exact List.prefix_rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · have hle : n ≤ m := Nat.lt_succ_iff.mp hlt
      exact List.IsPrefix.trans (ih hle)
        (bffState_succ pad_f pad_g pad_f_inj pad_g_inj m ▸
          bffStep_prefix _ _ _ _ _ _)

/-- If a pair is in bffState n, it remains in bffState m for m ≥ n. -/
lemma bffState_mem_mono (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    {n m : ℕ} (h : n ≤ m) {p : ℕ × ℕ}
    (hp : p ∈ bffState pad_f pad_g pad_f_inj pad_g_inj n) :
    p ∈ bffState pad_f pad_g pad_f_inj pad_g_inj m :=
  List.IsPrefix.subset (bffState_mono pad_f pad_g pad_f_inj pad_g_inj n m h) hp

/-- If a is in domain at stage n, it remains in domain at stage m ≥ n. -/
lemma inDomain_mono (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    {n m : ℕ} (h : n ≤ m) {a : ℕ}
    (ha : inDomain (bffState pad_f pad_g pad_f_inj pad_g_inj n) a = true) :
    inDomain (bffState pad_f pad_g pad_f_inj pad_g_inj m) a = true := by
  unfold inDomain at ha ⊢
  rw [List.any_eq_true] at ha ⊢
  exact ha.imp fun p ⟨hp_mem, hp_eq⟩ =>
    ⟨bffState_mem_mono pad_f pad_g pad_f_inj pad_g_inj h hp_mem, hp_eq⟩

/-- If b is in range at stage n, it remains in range at stage m ≥ n. -/
lemma inRange_mono (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    {n m : ℕ} (h : n ≤ m) {b : ℕ}
    (hb : inRange (bffState pad_f pad_g pad_f_inj pad_g_inj n) b = true) :
    inRange (bffState pad_f pad_g pad_f_inj pad_g_inj m) b = true := by
  unfold inRange at hb ⊢
  rw [List.any_eq_true] at hb ⊢
  exact hb.imp fun p ⟨hp_mem, hp_eq⟩ =>
    ⟨bffState_mem_mono pad_f pad_g pad_f_inj pad_g_inj h hp_mem, hp_eq⟩

-- ════════════════════════════════════════════════════════════════════
-- Section 4: Partial injection invariant and bijectivity
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────────────────
-- Helper lemmas for nodup and inverse proofs
-- ────────────────────────────────────────────────────────────────

/-- If `inDomain state a = false`, then `a` is not among the first
    components of `state`. -/
private lemma not_mem_fst_of_inDomain_false
    {state : List (ℕ × ℕ)} {a : ℕ}
    (h : inDomain state a = false) : a ∉ state.map Prod.fst := by
  intro hmem; rw [List.mem_map] at hmem
  obtain ⟨p, hp_mem, hp_eq⟩ := hmem
  have : inDomain state a = true := by
    unfold inDomain; rw [List.any_eq_true]
    exact ⟨p, hp_mem, by simp [← hp_eq]⟩
  rw [this] at h; exact absurd h (by decide)

/-- If `inRange state b = false`, then `b` is not among the second
    components of `state`. -/
private lemma not_mem_snd_of_inRange_false
    {state : List (ℕ × ℕ)} {b : ℕ}
    (h : inRange state b = false) : b ∉ state.map Prod.snd := by
  intro hmem; rw [List.mem_map] at hmem
  obtain ⟨p, hp_mem, hp_eq⟩ := hmem
  have : inRange state b = true := by
    unfold inRange; rw [List.any_eq_true]
    exact ⟨p, hp_mem, by simp [← hp_eq]⟩
  rw [this] at h; exact absurd h (by decide)

/-- Extract a witness pair from `inDomain state a = true`. -/
private lemma mem_of_inDomain {state : List (ℕ × ℕ)} {a : ℕ}
    (h : inDomain state a = true) : ∃ b, (a, b) ∈ state := by
  unfold inDomain at h; rw [List.any_eq_true] at h
  obtain ⟨⟨a', b⟩, hp_mem, hp_eq⟩ := h
  simp only [beq_iff_eq] at hp_eq
  exact ⟨b, by rwa [hp_eq] at hp_mem⟩

/-- Extract a witness pair from `inRange state b = true`. -/
private lemma mem_of_inRange {state : List (ℕ × ℕ)} {b : ℕ}
    (h : inRange state b = true) : ∃ a, (a, b) ∈ state := by
  unfold inRange at h; rw [List.any_eq_true] at h
  obtain ⟨⟨a, b'⟩, hp_mem, hp_eq⟩ := h
  simp only [beq_iff_eq] at hp_eq
  exact ⟨a, by rwa [hp_eq] at hp_mem⟩

/-- In a list with no duplicate first components, two pairs with
    the same first component must have the same second component. -/
private lemma nodup_fst_mem_unique {l : List (ℕ × ℕ)}
    (hnd : (l.map Prod.fst).Nodup)
    {a b₁ b₂ : ℕ} (h₁ : (a, b₁) ∈ l) (h₂ : (a, b₂) ∈ l) :
    b₁ = b₂ := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    rw [List.map_cons] at hnd
    have hnd_tl := hnd.of_cons
    have hd_not := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp h₁ with rfl | h₁'
    · rcases List.mem_cons.mp h₂ with heq | h₂'
      · exact (Prod.mk.inj heq).2.symm
      · exfalso; apply hd_not
        rw [List.mem_map]; exact ⟨(a, b₂), h₂', rfl⟩
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · exfalso; apply hd_not
        rw [List.mem_map]; exact ⟨(a, b₁), h₁', rfl⟩
      · exact ih hnd_tl h₁' h₂'

/-- In a list with no duplicate second components, two pairs with
    the same second component must have the same first component. -/
private lemma nodup_snd_mem_unique {l : List (ℕ × ℕ)}
    (hnd : (l.map Prod.snd).Nodup)
    {a₁ a₂ b : ℕ} (h₁ : (a₁, b) ∈ l) (h₂ : (a₂, b) ∈ l) :
    a₁ = a₂ := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    rw [List.map_cons] at hnd
    have hnd_tl := hnd.of_cons
    have hd_not := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp h₁ with rfl | h₁'
    · rcases List.mem_cons.mp h₂ with heq | h₂'
      · exact (Prod.mk.inj heq).1.symm
      · exfalso; apply hd_not
        rw [List.mem_map]; exact ⟨(a₂, b), h₂', rfl⟩
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · exfalso; apply hd_not
        rw [List.mem_map]; exact ⟨(a₁, b), h₁', rfl⟩
      · exact ih hnd_tl h₁' h₂'

/-- If `(a, b) ∈ state` and first components are unique, then
    `lookupFwd state a = some b`. -/
private lemma lookupFwd_of_mem_nodup
    {state : List (ℕ × ℕ)} {a b : ℕ}
    (hmem : (a, b) ∈ state)
    (hnd : (state.map Prod.fst).Nodup) :
    lookupFwd state a = some b := by
  induction state with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons] at hnd
    unfold lookupFwd; rw [List.find?_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp
    · split
      · rename_i h; rw [beq_iff_eq] at h; exfalso
        exact (List.nodup_cons.mp hnd).1
          (by rw [List.mem_map, h]; exact ⟨(a, b), hmem', rfl⟩)
      · exact ih hmem' hnd.of_cons

/-- If `(a, b) ∈ state` and second components are unique, then
    `lookupBwd state b = some a`. -/
private lemma lookupBwd_of_mem_nodup
    {state : List (ℕ × ℕ)} {a b : ℕ}
    (hmem : (a, b) ∈ state)
    (hnd : (state.map Prod.snd).Nodup) :
    lookupBwd state b = some a := by
  induction state with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons] at hnd
    unfold lookupBwd; rw [List.find?_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp
    · split
      · rename_i h; rw [beq_iff_eq] at h; exfalso
        exact (List.nodup_cons.mp hnd).1
          (by rw [List.mem_map, h]; exact ⟨(a, b), hmem', rfl⟩)
      · exact ih hmem' hnd.of_cons

/-- Extract a membership proof from a `lookupFwd` result. -/
private lemma mem_of_lookupFwd_eq_some
    {state : List (ℕ × ℕ)} {a b : ℕ}
    (h : lookupFwd state a = some b) : (a, b) ∈ state := by
  unfold lookupFwd at h
  cases hfind : state.find? (fun p => p.1 == a) with
  | none => rw [hfind, Option.map] at h; cases h
  | some p =>
    rw [hfind] at h; cases h
    have hp_mem := List.mem_of_find?_eq_some hfind
    have hp_pred := List.find?_some hfind
    rw [beq_iff_eq] at hp_pred
    exact hp_pred ▸ hp_mem

/-- Extract a membership proof from a `lookupBwd` result. -/
private lemma mem_of_lookupBwd_eq_some
    {state : List (ℕ × ℕ)} {a b : ℕ}
    (h : lookupBwd state b = some a) : (a, b) ∈ state := by
  unfold lookupBwd at h
  cases hfind : state.find? (fun p => p.2 == b) with
  | none => rw [hfind, Option.map] at h; cases h
  | some p =>
    rw [hfind] at h; cases h
    have hp_mem := List.mem_of_find?_eq_some hfind
    have hp_pred := List.find?_some hfind
    rw [beq_iff_eq] at hp_pred
    exact hp_pred ▸ hp_mem

-- ────────────────────────────────────────────────────────────────
-- Nodup proofs
-- ────────────────────────────────────────────────────────────────

/-- The state is always a valid partial injection: no duplicate
    domain elements and no duplicate range elements. -/
lemma bffState_nodup_fst (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (n : ℕ) :
    (bffState pad_f pad_g pad_f_inj pad_g_inj n |>.map Prod.fst).Nodup := by
  induction n with
  | zero => simp [bffState]
  | succ n ih =>
    simp only [bffState, bffStep]
    split
    · -- even case: forward pass
      split
      · exact ih
      · rename_i heven hdom
        have hdom_false : inDomain
            (bffState pad_f pad_g pad_f_inj pad_g_inj n) (n / 2) =
            false := by cases b : inDomain _ _ <;> simp_all
        rw [List.map_append, List.nodup_append]
        refine ⟨ih, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.map, List.mem_singleton] at hy
        subst hy
        exact Ne.symm (fun heq =>
          not_mem_fst_of_inDomain_false hdom_false (heq ▸ hx))
    · -- odd case: backward pass
      split
      · exact ih
      · rename_i hodd hran
        rw [List.map_append, List.nodup_append]
        refine ⟨ih, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.map, List.mem_singleton] at hy
        subst hy
        have hfresh := findFreshBwd_spec pad_g pad_g_inj
            (bffState pad_f pad_g pad_f_inj pad_g_inj n) (n / 2)
        exact Ne.symm (fun heq =>
          not_mem_fst_of_inDomain_false hfresh (heq ▸ hx))

lemma bffState_nodup_snd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (n : ℕ) :
    (bffState pad_f pad_g pad_f_inj pad_g_inj n |>.map Prod.snd).Nodup := by
  induction n with
  | zero => simp [bffState]
  | succ n ih =>
    simp only [bffState, bffStep]
    split
    · -- even case: forward pass
      split
      · exact ih
      · rename_i heven hdom
        rw [List.map_append, List.nodup_append]
        refine ⟨ih, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.map, List.mem_singleton] at hy
        subst hy
        have hfresh := findFreshFwd_spec pad_f pad_f_inj
            (bffState pad_f pad_g pad_f_inj pad_g_inj n) (n / 2)
        exact Ne.symm (fun heq =>
          not_mem_snd_of_inRange_false hfresh (heq ▸ hx))
    · -- odd case: backward pass
      split
      · exact ih
      · rename_i hodd hran
        have hran_false : inRange
            (bffState pad_f pad_g pad_f_inj pad_g_inj n) (n / 2) =
            false := by cases b : inRange _ _ <;> simp_all
        rw [List.map_append, List.nodup_append]
        refine ⟨ih, List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.map, List.mem_singleton] at hy
        subst hy
        exact Ne.symm (fun heq =>
          not_mem_snd_of_inRange_false hran_false (heq ▸ hx))

/-- Forward and backward are inverse: bffBwd (bffFwd a) = a. -/
lemma bffBwd_bffFwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (a : ℕ) :
    bffBwd pad_f pad_g pad_f_inj pad_g_inj
      (bffFwd pad_f pad_g pad_f_inj pad_g_inj a) = a := by
  set b := bffFwd pad_f pad_g pad_f_inj pad_g_inj a
  -- lookupFwd (bffState (2*a+1)) a = some b
  have hfwd_some : lookupFwd
      (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a =
      some b :=
    (Option.some_get _).symm
  -- (a, b) ∈ bffState (2*a+1)
  have hmem_fwd := mem_of_lookupFwd_eq_some hfwd_some
  -- (a, b) ∈ bffState (2*b+2) by case split on stage ordering
  have hmem_bwd : (a, b) ∈
      bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2) := by
    rcases Nat.le_total (2 * a + 1) (2 * b + 2) with h | h
    · exact bffState_mem_mono pad_f pad_g pad_f_inj pad_g_inj
        h hmem_fwd
    · obtain ⟨a', ha'⟩ := mem_of_inRange
        (bffBwd_total pad_f pad_g pad_f_inj pad_g_inj b)
      have ha'_later := bffState_mem_mono
        pad_f pad_g pad_f_inj pad_g_inj h ha'
      have := nodup_snd_mem_unique
        (bffState_nodup_snd pad_f pad_g pad_f_inj pad_g_inj
          (2 * a + 1))
        ha'_later hmem_fwd
      rwa [this] at ha'
  -- lookupBwd (bffState (2*b+2)) b = some a
  have hbwd_some := lookupBwd_of_mem_nodup hmem_bwd
    (bffState_nodup_snd pad_f pad_g pad_f_inj pad_g_inj _)
  -- bffBwd b = a
  change (lookupBwd (bffState pad_f pad_g pad_f_inj pad_g_inj
    (2 * b + 2)) b).get _ = a
  simp [hbwd_some]

/-- Forward and backward are inverse: bffFwd (bffBwd b) = b. -/
lemma bffFwd_bffBwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (b : ℕ) :
    bffFwd pad_f pad_g pad_f_inj pad_g_inj
      (bffBwd pad_f pad_g pad_f_inj pad_g_inj b) = b := by
  set a := bffBwd pad_f pad_g pad_f_inj pad_g_inj b
  -- lookupBwd (bffState (2*b+2)) b = some a
  have hbwd_some : lookupBwd
      (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b =
      some a :=
    (Option.some_get _).symm
  -- (a, b) ∈ bffState (2*b+2)
  have hmem_bwd := mem_of_lookupBwd_eq_some hbwd_some
  -- (a, b) ∈ bffState (2*a+1) by case split on stage ordering
  have hmem_fwd : (a, b) ∈
      bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1) := by
    rcases Nat.le_total (2 * b + 2) (2 * a + 1) with h | h
    · exact bffState_mem_mono pad_f pad_g pad_f_inj pad_g_inj
        h hmem_bwd
    · obtain ⟨b', hb'⟩ := mem_of_inDomain
        (bffFwd_total pad_f pad_g pad_f_inj pad_g_inj a)
      have hb'_later := bffState_mem_mono
        pad_f pad_g pad_f_inj pad_g_inj h hb'
      have := nodup_fst_mem_unique
        (bffState_nodup_fst pad_f pad_g pad_f_inj pad_g_inj
          (2 * b + 2))
        hb'_later hmem_bwd
      rwa [this] at hb'
  -- lookupFwd (bffState (2*a+1)) a = some b
  have hfwd_some := lookupFwd_of_mem_nodup hmem_fwd
    (bffState_nodup_fst pad_f pad_g pad_f_inj pad_g_inj _)
  -- bffFwd a = b
  change (lookupFwd (bffState pad_f pad_g pad_f_inj pad_g_inj
    (2 * a + 1)) a).get _ = b
  simp [hfwd_some]

-- ════════════════════════════════════════════════════════════════════
-- Section 5: R-preservation
-- ════════════════════════════════════════════════════════════════════

/-- Every pair added to the BFF state is R-related. -/
lemma bffState_R {R : ℕ → ℕ → Prop} (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_R : ∀ a k, R a (pad_f a k))
    (pad_g_R : ∀ b k, R (pad_g b k) b)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (n : ℕ) (a b : ℕ)
    (h : (a, b) ∈ bffState pad_f pad_g pad_f_inj pad_g_inj n) :
    R a b := by
  induction n with
  | zero => simp [bffState] at h
  | succ n ih =>
    simp only [bffState] at h
    unfold bffStep at h
    split at h
    · -- even case (forward pass)
      dsimp only at h
      split at h
      · exact ih h
      · rw [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact ih h
        · rw [Prod.mk.injEq] at h
          rw [h.1, h.2]
          exact pad_f_R _ _
    · -- odd case (backward pass)
      dsimp only at h
      split at h
      · exact ih h
      · rw [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact ih h
        · rw [Prod.mk.injEq] at h
          rw [h.1, h.2]
          exact pad_g_R _ _

-- ════════════════════════════════════════════════════════════════════
-- Section 6: Computability
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────────────────
-- Sub-task 6a: List operations are Computable
-- ────────────────────────────────────────────────────────────────

/-- BEq on ℕ is commutative. -/
private lemma beq_comm_nat (a b : ℕ) : (a == b) = (b == a) := by
  simp [BEq.beq, @eq_comm ℕ a b]

/-- inDomain equals List.lookup composed with Option.isSome. -/
private lemma inDomain_eq_lookup_isSome (state : List (ℕ × ℕ)) (a : ℕ) :
    inDomain state a = (List.lookup a state).isSome := by
  induction state with
  | nil => rfl
  | cons p ps ih =>
    simp only [inDomain, List.any_cons, beq_comm_nat p.1 a]
    show (a == p.1 || ps.any fun p ↦ p.1 == a) = (List.lookup a (p :: ps)).isSome
    rw [show List.lookup a (p :: ps) = match a == p.1 with
      | true => some p.2 | false => List.lookup a ps from rfl]
    cases (a == p.1)
    · simp only [Bool.false_or]; exact ih
    · simp

/-- inRange equals lookup on the swapped list. -/
private lemma inRange_eq_lookup_swap_isSome (state : List (ℕ × ℕ)) (b : ℕ) :
    inRange state b = (List.lookup b (state.map Prod.swap)).isSome := by
  induction state with
  | nil => rfl
  | cons p ps ih =>
    simp only [inRange, List.any_cons, List.map_cons, beq_comm_nat p.2 b]
    show (b == p.2 || ps.any fun p ↦ p.2 == b) =
      (List.lookup b (p.swap :: ps.map Prod.swap)).isSome
    rw [show List.lookup b (p.swap :: ps.map Prod.swap) = match b == p.swap.1 with
      | true => some p.swap.2 | false => List.lookup b (ps.map Prod.swap) from rfl]
    simp only [Prod.swap]
    cases (b == p.2)
    · simp only [Bool.false_or]; exact ih
    · simp

/-- lookupFwd equals List.lookup. -/
private lemma lookupFwd_eq_lookup (state : List (ℕ × ℕ)) (a : ℕ) :
    lookupFwd state a = List.lookup a state := by
  induction state with
  | nil => rfl
  | cons p ps ih =>
    unfold lookupFwd at ih ⊢
    simp only [List.find?_cons]
    rw [show (p.1 == a) = (a == p.1) from beq_comm_nat p.1 a]
    rw [show List.lookup a (p :: ps) = match a == p.1 with
      | true => some p.2 | false => List.lookup a ps from rfl]
    cases (a == p.1) <;> [exact ih; rfl]

/-- lookupBwd equals List.lookup on the swapped list. -/
private lemma lookupBwd_eq_lookup_swap (state : List (ℕ × ℕ)) (b : ℕ) :
    lookupBwd state b = List.lookup b (state.map Prod.swap) := by
  induction state with
  | nil => rfl
  | cons p ps ih =>
    unfold lookupBwd at ih ⊢
    simp only [List.find?_cons, List.map_cons]
    rw [show (p.2 == b) = (b == p.2) from beq_comm_nat p.2 b]
    rw [show List.lookup b (p.swap :: ps.map Prod.swap) = match b == p.swap.1 with
      | true => some p.swap.2 | false => List.lookup b (ps.map Prod.swap) from rfl]
    simp only [Prod.swap]
    cases (b == p.2) <;> [exact ih; rfl]

/-- Primrec helper: mapping Prod.swap over a list. -/
private def mapSwapPrimrec :
    Primrec (fun (state : List (ℕ × ℕ)) => state.map Prod.swap) :=
  Primrec.list_map Primrec.id
    ((Primrec.pair (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to₂)

lemma inDomain_computable : Computable₂ inDomain := by
  unfold Computable₂
  exact Computable.of_eq
    (Primrec.option_isSome.comp
      (Primrec.listLookup.comp Primrec.snd Primrec.fst)).to_comp
    (fun ⟨state, a⟩ => (inDomain_eq_lookup_isSome state a).symm)

lemma inRange_computable : Computable₂ inRange := by
  unfold Computable₂
  exact Computable.of_eq
    (Primrec.option_isSome.comp
      (Primrec.listLookup.comp Primrec.snd
        (mapSwapPrimrec.comp Primrec.fst))).to_comp
    (fun ⟨state, b⟩ => (inRange_eq_lookup_swap_isSome state b).symm)

lemma lookupFwd_computable : Computable₂ lookupFwd := by
  unfold Computable₂
  exact Computable.of_eq
    (Primrec.listLookup.comp Primrec.snd Primrec.fst).to_comp
    (fun ⟨state, a⟩ => (lookupFwd_eq_lookup state a).symm)

lemma lookupBwd_computable : Computable₂ lookupBwd := by
  unfold Computable₂
  exact Computable.of_eq
    (Primrec.listLookup.comp Primrec.snd
      (mapSwapPrimrec.comp Primrec.fst)).to_comp
    (fun ⟨state, b⟩ => (lookupBwd_eq_lookup_swap state b).symm)

-- ────────────────────────────────────────────────────────────────
-- Sub-task 6b: findFresh is Computable (via Partrec.rfind)
-- ────────────────────────────────────────────────────────────────

/-- Nat.rfind with a total Boolean predicate equals Nat.find. -/
private lemma rfind_total_eq_find {p : ℕ → Bool} (h : ∃ n, p n = true) :
    Nat.rfind (fun n => Part.some (p n)) = Part.some (Nat.find h) := by
  apply Part.eq_some_iff.mpr
  rw [Nat.mem_rfind]
  constructor
  · rw [Part.mem_some_iff]; exact (Nat.find_spec h).symm
  · intro m hm
    rw [Part.mem_some_iff]
    have hmin := Nat.find_min h hm
    cases hp : p m
    · rfl
    · exact absurd hp hmin

lemma findFreshFwd_computable {pad_f : ℕ → ℕ → ℕ} (pad_f_comp : Computable₂ pad_f)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a)) :
    Computable₂ (findFreshFwd pad_f pad_f_inj) := by
  unfold Computable₂
  -- The predicate (state, a, j) ↦ !inRange state (pad_f a j) is computable
  have h_pred_comp : Computable (fun (p : (List (ℕ × ℕ) × ℕ) × ℕ) =>
      !inRange p.1.1 (pad_f p.1.2 p.2)) :=
    Primrec.not.to_comp.comp
      (inRange_computable.comp
        (Computable.fst.comp Computable.fst)
        (pad_f_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  -- Nat.rfind of this predicate is Partrec
  have h_rfind : Partrec (fun ctx : List (ℕ × ℕ) × ℕ =>
      Nat.rfind (fun j => Part.some (!inRange ctx.1 (pad_f ctx.2 j)))) :=
    Partrec.rfind h_pred_comp.partrec
  -- The rfind equals Part.some (findFreshFwd ...) by rfind_total_eq_find
  apply Partrec.of_eq h_rfind
  intro ⟨state, a⟩
  have hex : ∃ j, (!inRange state (pad_f a j)) = true := by
    obtain ⟨j, hj⟩ := findFreshFwd_exists pad_f pad_f_inj state a
    exact ⟨j, by simp [hj]⟩
  rw [rfind_total_eq_find hex]
  unfold findFreshFwd
  congr 1
  rw [Nat.find_eq_iff hex]
  constructor
  · have := Nat.find_spec (findFreshFwd_exists pad_f pad_f_inj state a)
    simp [this]
  · intro m hm
    have := Nat.find_min (findFreshFwd_exists pad_f pad_f_inj state a) hm
    intro h; apply this
    cases inRange state (pad_f a m) <;> simp_all

lemma findFreshBwd_computable {pad_g : ℕ → ℕ → ℕ} (pad_g_comp : Computable₂ pad_g)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    Computable₂ (findFreshBwd pad_g pad_g_inj) := by
  unfold Computable₂
  have h_pred_comp : Computable (fun (p : (List (ℕ × ℕ) × ℕ) × ℕ) =>
      !inDomain p.1.1 (pad_g p.1.2 p.2)) :=
    Primrec.not.to_comp.comp
      (inDomain_computable.comp
        (Computable.fst.comp Computable.fst)
        (pad_g_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  have h_rfind : Partrec (fun ctx : List (ℕ × ℕ) × ℕ =>
      Nat.rfind (fun j => Part.some (!inDomain ctx.1 (pad_g ctx.2 j)))) :=
    Partrec.rfind h_pred_comp.partrec
  apply Partrec.of_eq h_rfind
  intro ⟨state, b⟩
  have hex : ∃ j, (!inDomain state (pad_g b j)) = true := by
    obtain ⟨j, hj⟩ := findFreshBwd_exists pad_g pad_g_inj state b
    exact ⟨j, by simp [hj]⟩
  rw [rfind_total_eq_find hex]
  unfold findFreshBwd
  congr 1
  rw [Nat.find_eq_iff hex]
  constructor
  · have := Nat.find_spec (findFreshBwd_exists pad_g pad_g_inj state b)
    simp [this]
  · intro m hm
    have := Nat.find_min (findFreshBwd_exists pad_g pad_g_inj state b) hm
    intro h; apply this
    cases inDomain state (pad_g b m) <;> simp_all

-- ────────────────────────────────────────────────────────────────
-- Sub-task 6c: bffStep is Computable
-- ────────────────────────────────────────────────────────────────

/-- bffStep expressed with Bool conditionals for computability proofs. -/
private lemma bffStep_eq_bif (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (state : List (ℕ × ℕ)) (n : ℕ) :
    bffStep pad_f pad_g pad_f_inj pad_g_inj state n =
    bif (n % 2 == 0) then
      bif (inDomain state (n / 2)) then state
      else state ++ [(n / 2,
        pad_f (n / 2) (findFreshFwd pad_f pad_f_inj state (n / 2)))]
    else
      bif (inRange state (n / 2)) then state
      else state ++ [(pad_g (n / 2)
        (findFreshBwd pad_g pad_g_inj state (n / 2)), n / 2)] := by
  unfold bffStep
  cases h : n % 2 == 0 <;> simp_all [BEq.beq]

lemma bffStep_computable {pad_f pad_g : ℕ → ℕ → ℕ}
    (pad_f_comp : Computable₂ pad_f) (pad_g_comp : Computable₂ pad_g)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    Computable₂ (bffStep pad_f pad_g pad_f_inj pad_g_inj) := by
  unfold Computable₂
  -- We show the bif version is computable, then use bffStep_eq_bif
  -- Context type: α = List (ℕ × ℕ) × ℕ
  -- Abbreviations for readability:
  -- state = fst, n = snd, a = n / 2 = snd / 2
  let s : List (ℕ × ℕ) × ℕ → List (ℕ × ℕ) := Prod.fst
  let n_val : List (ℕ × ℕ) × ℕ → ℕ := Prod.snd
  -- n % 2 == 0 is computable
  have h_even : Computable (fun ctx : List (ℕ × ℕ) × ℕ => ctx.2 % 2 == 0) :=
    (Primrec₂.comp Primrec.beq
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
      (Primrec.const 0)).to_comp
  -- n / 2 is computable
  have h_half : Computable (fun ctx : List (ℕ × ℕ) × ℕ => ctx.2 / 2) :=
    (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)).to_comp
  -- inDomain state (n/2) is computable
  have h_inDom : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      inDomain ctx.1 (ctx.2 / 2)) :=
    inDomain_computable.comp Computable.fst h_half
  -- inRange state (n/2) is computable
  have h_inRng : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      inRange ctx.1 (ctx.2 / 2)) :=
    inRange_computable.comp Computable.fst h_half
  -- findFreshFwd pad_f pad_f_inj state (n/2) is computable
  have h_freshFwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      findFreshFwd pad_f pad_f_inj ctx.1 (ctx.2 / 2)) :=
    (findFreshFwd_computable pad_f_comp pad_f_inj).comp Computable.fst h_half
  -- findFreshBwd pad_g pad_g_inj state (n/2) is computable
  have h_freshBwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      findFreshBwd pad_g pad_g_inj ctx.1 (ctx.2 / 2)) :=
    (findFreshBwd_computable pad_g_comp pad_g_inj).comp Computable.fst h_half
  -- pad_f (n/2) (findFreshFwd ...) is computable
  have h_padFwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      pad_f (ctx.2 / 2) (findFreshFwd pad_f pad_f_inj ctx.1 (ctx.2 / 2))) :=
    pad_f_comp.comp h_half h_freshFwd
  -- pad_g (n/2) (findFreshBwd ...) is computable
  have h_padBwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      pad_g (ctx.2 / 2) (findFreshBwd pad_g pad_g_inj ctx.1 (ctx.2 / 2))) :=
    pad_g_comp.comp h_half h_freshBwd
  -- state ++ [(n/2, pad_f ...)] is computable
  have h_appendFwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      ctx.1 ++ [(ctx.2 / 2,
        pad_f (ctx.2 / 2) (findFreshFwd pad_f pad_f_inj ctx.1 (ctx.2 / 2)))]) :=
    Primrec.list_append.to_comp.comp Computable.fst
      (Primrec.list_cons.to_comp.comp
        (Computable.pair h_half h_padFwd)
        (Computable.const []))
  -- state ++ [(pad_g ..., n/2)] is computable
  have h_appendBwd : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      ctx.1 ++ [(pad_g (ctx.2 / 2)
        (findFreshBwd pad_g pad_g_inj ctx.1 (ctx.2 / 2)), ctx.2 / 2)]) :=
    Primrec.list_append.to_comp.comp Computable.fst
      (Primrec.list_cons.to_comp.comp
        (Computable.pair h_padBwd h_half)
        (Computable.const []))
  -- Inner forward conditional: bif inDomain ... then state else state ++ [...]
  have h_fwdBranch : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      bif inDomain ctx.1 (ctx.2 / 2) then ctx.1 else
        ctx.1 ++ [(ctx.2 / 2,
          pad_f (ctx.2 / 2) (findFreshFwd pad_f pad_f_inj ctx.1 (ctx.2 / 2)))]) :=
    Computable.cond h_inDom Computable.fst h_appendFwd
  -- Inner backward conditional
  have h_bwdBranch : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      bif inRange ctx.1 (ctx.2 / 2) then ctx.1 else
        ctx.1 ++ [(pad_g (ctx.2 / 2)
          (findFreshBwd pad_g pad_g_inj ctx.1 (ctx.2 / 2)), ctx.2 / 2)]) :=
    Computable.cond h_inRng Computable.fst h_appendBwd
  -- Outer conditional: bif (n % 2 == 0) then fwdBranch else bwdBranch
  have h_full : Computable (fun ctx : List (ℕ × ℕ) × ℕ =>
      bif (ctx.2 % 2 == 0) then
        bif (inDomain ctx.1 (ctx.2 / 2)) then ctx.1 else
          ctx.1 ++ [(ctx.2 / 2,
            pad_f (ctx.2 / 2) (findFreshFwd pad_f pad_f_inj ctx.1 (ctx.2 / 2)))]
      else
        bif (inRange ctx.1 (ctx.2 / 2)) then ctx.1 else
          ctx.1 ++ [(pad_g (ctx.2 / 2)
            (findFreshBwd pad_g pad_g_inj ctx.1 (ctx.2 / 2)), ctx.2 / 2)]) :=
    Computable.cond h_even h_fwdBranch h_bwdBranch
  exact Computable.of_eq h_full
    (fun ⟨state, n⟩ => (bffStep_eq_bif pad_f pad_g pad_f_inj pad_g_inj state n).symm)

-- ────────────────────────────────────────────────────────────────
-- Sub-task 6d: bffState is Computable (via Computable.nat_rec)
-- ────────────────────────────────────────────────────────────────

lemma bffState_computable {pad_f pad_g : ℕ → ℕ → ℕ}
    (pad_f_comp : Computable₂ pad_f) (pad_g_comp : Computable₂ pad_g)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    Computable (bffState pad_f pad_g pad_f_inj pad_g_inj) := by
  -- bffState n = Nat.rec [] (fun k IH => bffStep ... IH k) n
  -- Use Computable.nat_rec with α = ℕ, f = id, g = const [], h = step
  -- Computable.nat_rec : Computable f → Computable g → Computable₂ h →
  --   Computable (fun a => Nat.rec (g a) (fun y IH => h a (y, IH)) (f a))
  -- We need α = ℕ, and the step function h _ (k, state) = bffStep ... state k
  -- h : ℕ → ℕ × List (ℕ × ℕ) → List (ℕ × ℕ), h _ (k, state) = bffStep ... state k
  -- Computable₂ h means Computable (fun (ctx, (k, state)) => bffStep ... state k)
  have h_step : Computable₂ (fun (_ : ℕ) (p : ℕ × List (ℕ × ℕ)) =>
      bffStep pad_f pad_g pad_f_inj pad_g_inj p.2 p.1) := by
    unfold Computable₂
    exact (bffStep_computable pad_f_comp pad_g_comp pad_f_inj pad_g_inj).comp
      (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)
  apply Computable.of_eq
    (Computable.nat_rec Computable.id (Computable.const []) h_step)
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change bffStep pad_f pad_g pad_f_inj pad_g_inj
      (Nat.rec [] (fun y IH => bffStep pad_f pad_g pad_f_inj pad_g_inj IH y) n) n =
      bffState pad_f pad_g pad_f_inj pad_g_inj (n + 1)
    conv_rhs => rw [bffState]
    congr 1

-- ────────────────────────────────────────────────────────────────
-- Sub-task 6e: bffFwd and bffBwd are Computable
-- ────────────────────────────────────────────────────────────────

/-- inDomain being true implies lookupFwd returns some. -/
private lemma lookupFwd_isSome_of_inDomain {state : List (ℕ × ℕ)} {a : ℕ}
    (h : inDomain state a = true) :
    (lookupFwd state a).isSome = true := by
  rwa [lookupFwd_eq_lookup, ← inDomain_eq_lookup_isSome]

/-- inRange being true implies lookupBwd returns some. -/
private lemma lookupBwd_isSome_of_inRange {state : List (ℕ × ℕ)} {b : ℕ}
    (h : inRange state b = true) :
    (lookupBwd state b).isSome = true := by
  rwa [lookupBwd_eq_lookup_swap, ← inRange_eq_lookup_swap_isSome]

/-- lookupFwd state a = some (bffFwd a) at the relevant stage. -/
private lemma lookupFwd_bffFwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (a : ℕ) :
    lookupFwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a =
      some (bffFwd pad_f pad_g pad_f_inj pad_g_inj a) := by
  unfold bffFwd
  exact (Option.some_get _).symm

/-- lookupBwd state b = some (bffBwd b) at the relevant stage. -/
private lemma lookupBwd_bffBwd (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (b : ℕ) :
    lookupBwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b =
      some (bffBwd pad_f pad_g pad_f_inj pad_g_inj b) := by
  unfold bffBwd
  exact (Option.some_get _).symm

lemma bffFwd_computable {pad_f pad_g : ℕ → ℕ → ℕ}
    (pad_f_comp : Computable₂ pad_f) (pad_g_comp : Computable₂ pad_g)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    Computable (bffFwd pad_f pad_g pad_f_inj pad_g_inj) := by
  -- Step 1: fun a => lookupFwd (bffState ... (2*a+1)) a : ℕ → Option ℕ is computable
  have h_arith : Computable (fun a : ℕ => 2 * a + 1) :=
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp
  have h_state : Computable (fun a : ℕ =>
      bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) :=
    (bffState_computable pad_f_comp pad_g_comp pad_f_inj pad_g_inj).comp h_arith
  have h_opt : Computable (fun a : ℕ =>
      lookupFwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a) :=
    lookupFwd_computable.comp h_state Computable.id
  -- Step 2: Partrec (fun a => ↑(lookupFwd ...))
  have h_partrec : Partrec (fun a : ℕ =>
      (↑(lookupFwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1)) a) : Part ℕ)) :=
    h_opt.ofOption
  -- Step 3: This equals Part.some (bffFwd ... a) by totality
  exact Partrec.of_eq h_partrec (fun a => by
    rw [lookupFwd_bffFwd]
    rfl)

lemma bffBwd_computable {pad_f pad_g : ℕ → ℕ → ℕ}
    (pad_f_comp : Computable₂ pad_f) (pad_g_comp : Computable₂ pad_g)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    Computable (bffBwd pad_f pad_g pad_f_inj pad_g_inj) := by
  have h_arith : Computable (fun b : ℕ => 2 * b + 2) :=
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 2)).to_comp
  have h_state : Computable (fun b : ℕ =>
      bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) :=
    (bffState_computable pad_f_comp pad_g_comp pad_f_inj pad_g_inj).comp h_arith
  have h_opt : Computable (fun b : ℕ =>
      lookupBwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b) :=
    lookupBwd_computable.comp h_state Computable.id
  have h_partrec : Partrec (fun b : ℕ =>
      (↑(lookupBwd (bffState pad_f pad_g pad_f_inj pad_g_inj (2 * b + 2)) b) : Part ℕ)) :=
    h_opt.ofOption
  exact Partrec.of_eq h_partrec (fun b => by
    rw [lookupBwd_bffBwd]
    rfl)

-- ════════════════════════════════════════════════════════════════════
-- Section 7: Assembly
-- ════════════════════════════════════════════════════════════════════

/-- If lookupFwd returns some value, the pair is in the list. -/
lemma lookupFwd_mem {state : List (ℕ × ℕ)} {a b : ℕ}
    (h : lookupFwd state a = some b) : (a, b) ∈ state :=
  mem_of_lookupFwd_eq_some h

/-- The pair (a, bffFwd a) is in the bffState at stage 2a+1. -/
lemma bffFwd_mem (pad_f pad_g : ℕ → ℕ → ℕ)
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    (pad_g_inj : ∀ b, Function.Injective (pad_g b))
    (a : ℕ) :
    (a, bffFwd pad_f pad_g pad_f_inj pad_g_inj a) ∈
      bffState pad_f pad_g pad_f_inj pad_g_inj (2 * a + 1) :=
  mem_of_lookupFwd_eq_some (Option.some_get _).symm

/-- The effective Myhill isomorphism lemma on ℕ. -/
theorem effective_myhill_nat
    {R : ℕ → ℕ → Prop}
    {pad_f : ℕ → ℕ → ℕ} (pad_f_comp : Computable₂ pad_f)
    (pad_f_R : ∀ a k, R a (pad_f a k))
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    {pad_g : ℕ → ℕ → ℕ} (pad_g_comp : Computable₂ pad_g)
    (pad_g_R : ∀ b k, R (pad_g b k) b)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ a, R a (e a) := by
  -- Construct the equivalence from bffFwd/bffBwd with inverse proofs
  let e : ℕ ≃ ℕ :=
    { toFun := bffFwd pad_f pad_g pad_f_inj pad_g_inj
      invFun := bffBwd pad_f pad_g pad_f_inj pad_g_inj
      left_inv := bffBwd_bffFwd pad_f pad_g pad_f_inj pad_g_inj
      right_inv := bffFwd_bffBwd pad_f pad_g pad_f_inj pad_g_inj }
  refine ⟨e, ?_, ?_⟩
  · -- Computability
    exact ⟨bffFwd_computable pad_f_comp pad_g_comp pad_f_inj pad_g_inj,
           bffBwd_computable pad_f_comp pad_g_comp pad_f_inj pad_g_inj⟩
  · -- R-preservation
    intro a
    change R a (bffFwd pad_f pad_g pad_f_inj pad_g_inj a)
    have hmem := bffFwd_mem pad_f pad_g pad_f_inj pad_g_inj a
    exact bffState_R pad_f pad_g pad_f_R pad_g_R pad_f_inj pad_g_inj
      (2 * a + 1) a (bffFwd pad_f pad_g pad_f_inj pad_g_inj a) hmem

/-- Lift from ℕ to arbitrary Denumerable types. -/
theorem effective_myhill_general {α β : Type*} [Denumerable α] [Denumerable β]
    {R : α → β → Prop}
    {pad_f : α → ℕ → β} (pad_f_comp : Computable₂ pad_f)
    (pad_f_R : ∀ a k, R a (pad_f a k))
    (pad_f_inj : ∀ a, Function.Injective (pad_f a))
    {pad_g : β → ℕ → α} (pad_g_comp : Computable₂ pad_g)
    (pad_g_R : ∀ b k, R (pad_g b k) b)
    (pad_g_inj : ∀ b, Function.Injective (pad_g b)) :
    ∃ e : α ≃ β, e.Computable ∧ ∀ a, R a (e a) := by
  -- Encode everything to ℕ
  let pad_f' : ℕ → ℕ → ℕ := fun n k => Encodable.encode (pad_f (ofNat α n) k)
  let pad_g' : ℕ → ℕ → ℕ := fun n k => Encodable.encode (pad_g (ofNat β n) k)
  let R' : ℕ → ℕ → Prop := fun i j => R (ofNat α i) (ofNat β j)
  -- pad_f' is computable
  have pad_f'_comp : Computable₂ pad_f' := by
    exact Computable.encode.comp
      (pad_f_comp.comp ((Computable.ofNat α).comp Computable.fst) Computable.snd)
  -- pad_g' is computable
  have pad_g'_comp : Computable₂ pad_g' := by
    exact Computable.encode.comp
      (pad_g_comp.comp ((Computable.ofNat β).comp Computable.fst) Computable.snd)
  -- pad_f' preserves R'
  have pad_f'_R : ∀ n k, R' n (pad_f' n k) := by
    intro n k
    change R (ofNat α n) (ofNat β (Encodable.encode (pad_f (ofNat α n) k)))
    rw [Denumerable.ofNat_encode]
    exact pad_f_R (ofNat α n) k
  -- pad_g' preserves R'
  have pad_g'_R : ∀ n k, R' (pad_g' n k) n := by
    intro n k
    change R (ofNat α (Encodable.encode (pad_g (ofNat β n) k))) (ofNat β n)
    rw [Denumerable.ofNat_encode]
    exact pad_g_R (ofNat β n) k
  -- pad_f' is injective in the second argument
  have pad_f'_inj : ∀ n, Function.Injective (pad_f' n) := by
    intro n k₁ k₂ h
    change Encodable.encode (pad_f (ofNat α n) k₁) =
      Encodable.encode (pad_f (ofNat α n) k₂) at h
    have := Encodable.encode_injective h
    exact pad_f_inj (ofNat α n) this
  -- pad_g' is injective in the second argument
  have pad_g'_inj : ∀ n, Function.Injective (pad_g' n) := by
    intro n k₁ k₂ h
    change Encodable.encode (pad_g (ofNat β n) k₁) =
      Encodable.encode (pad_g (ofNat β n) k₂) at h
    have := Encodable.encode_injective h
    exact pad_g_inj (ofNat β n) this
  -- Apply the ℕ version
  obtain ⟨e_nat, he_comp, he_R⟩ := effective_myhill_nat
    pad_f'_comp pad_f'_R pad_f'_inj pad_g'_comp pad_g'_R pad_g'_inj
  -- Lift to α ≃ β
  let e : α ≃ β := (Denumerable.eqv α).trans (e_nat.trans (Denumerable.eqv β).symm)
  refine ⟨e, ?_, ?_⟩
  · -- Computability: compose three computable equivs
    exact (Computable.eqv α).trans (he_comp.trans (Computable.eqv β).symm)
  · -- R-preservation
    intro a
    -- e a unfolds to ofNat β (e_nat (encode a)) by definition
    -- he_R gives R' (encode a) (e_nat (encode a))
    -- i.e. R (ofNat α (encode a)) (ofNat β (e_nat (encode a)))
    have := he_R (Encodable.encode a)
    change R (ofNat α (Encodable.encode a)) (ofNat β (e_nat (Encodable.encode a))) at this
    rwa [Denumerable.ofNat_encode] at this

end Myhill
