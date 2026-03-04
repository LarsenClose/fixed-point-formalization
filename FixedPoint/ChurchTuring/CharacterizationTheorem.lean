/-
  CharacterizationTheorem.lean

  The Church-Turing thesis reframed as a Lindstrom-type characterization
  theorem: any two acceptable numberings of the partial recursive functions
  are equivalent — they compute exactly the same class of partial functions.

  The key insight from the paper series: the thesis explains
  equivalence-once-universal, not universality itself. Universality is
  a precondition; the characterization says that once you cross the
  threshold, there is exactly one equivalence class.

  The connection to the fixed-point story: self-reference capacity is
  what Kleene's recursion theorem provides, and Kleene's theorem is
  itself a fixed-point result (F(X) ≅ X at the level of programs).
  With an acceptable numbering — Denumerable programs, universal
  evaluation, representability (no junk), and the s-m-n property —
  Kleene's recursion theorem follows from the structure fields. See
  `HasSelfReference` below.

  The `CompModel` structure follows approach (d) from the analysis in
  `docs/alternative-approaches-computability.md`: define a computation
  model as an acceptable numbering directly, absorbing `Representable`
  into the definition and aligning with Rogers (Ch. 2), Soare (Ch. II),
  and Cutland. Mathlib's `Nat.Partrec.Code` serves as the canonical
  witness (`codeModel`).
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Computability.PartrecCode

open Nat.Partrec

namespace FixedPoint.ChurchTuring

/-- A model of computation structured as an acceptable numbering.

    `Prog` is the type of program indices, which must be `Denumerable`
    (countably enumerable with a computable encoding). The `eval` function
    maps each program to the partial function it computes. The four fields
    ensure the numbering is acceptable:

    - `representable`: every program computes a partial recursive function
      (no junk — the model does not overshoot).
    - `universal`: every partial recursive function is computed by some
      program (surjectivity — the model does not undershoot).
    - `smn`: computable currying is internal to the model (the s-m-n
      theorem).

    Together, `representable + universal` say the model computes *exactly*
    the partial recursive functions. The `smn` field, combined with
    universality, gives the full recursion-theoretic toolbox: Kleene's
    recursion theorem (self-reference), Rice's theorem, etc. -/
structure CompModel where
  /-- The type of programs / indices. -/
  Prog : Type
  /-- The evaluation function: each program denotes a partial function
      ℕ →. ℕ. -/
  eval : Prog → ℕ →. ℕ
  /-- Programs are countably enumerable with a computable encoding. -/
  [denumerable : Denumerable Prog]
  /-- Every program computes a partial recursive function (no junk). -/
  representable :
    ∀ p : Prog, ∃ c : Code, ∀ n, eval p n = Code.eval c n
  /-- Every partial recursive function is computed by some program
      (universality / surjectivity). -/
  universal :
    ∀ c : Code, ∃ p : Prog, ∀ n, eval p n = Code.eval c n
  /-- The evaluation function, viewed as a function ℕ → ℕ →. ℕ via
      the Denumerable encoding of `Prog`, is partial recursive. This
      is the uniform computability requirement for an acceptable
      numbering: not only does each individual program compute a
      partial recursive function (which `representable` ensures), but
      the map `(i, n) ↦ eval (ofNat Prog i) n` is itself partial
      recursive as a function of both the program index and the input.
      This corresponds to the existence of a universal function in
      Rogers' sense (Definition 2-10). -/
  eval_partrec :
    Partrec₂ (fun (i : ℕ) (n : ℕ) => eval (Denumerable.ofNat Prog i) n)
  /-- Internal currying: a computable function that, given a program `p`
      and an input `n`, produces a program computing `x ↦ eval p ⟨n, x⟩`.
      This is the s-m-n theorem internalized in the model.

      The s-m-n function `s` is required to be `Computable₂` (computable
      as a function of both arguments), matching the standard requirement
      in recursion theory that the s-m-n function is computable (in fact,
      primitive recursive). This computability is essential for deriving
      the recursion theorem (Kleene's fixed-point theorem) from the
      CompModel axioms. -/
  smn :
    ∃ s : Prog → ℕ → Prog,
      Computable₂ s ∧ ∀ p n x, eval (s p n) x = eval p (Nat.pair n x)

attribute [instance] CompModel.denumerable

/-- `Nat.Partrec.Code` itself forms a `CompModel`, witnessing that the
    structure is non-vacuous. `Code` is the canonical acceptable
    numbering provided by Mathlib: `Denumerable Code` is
    `Code.instDenumerable`, universality and representability are
    trivial (identity), and s-m-n is `Code.curry` / `Code.eval_curry`. -/
def codeModel : CompModel where
  Prog := Code
  eval := Code.eval
  representable := fun c => ⟨c, fun _ => rfl⟩
  universal := fun c => ⟨c, fun _ => rfl⟩
  eval_partrec :=
    (Code.eval_part.comp ((Computable.ofNat Code).comp Computable.fst)
      Computable.snd).to₂
  smn := ⟨Code.curry, Code.primrec₂_curry.to_comp, Code.eval_curry⟩

-- ────────────────────────────────────────────────────────────────
-- Backward-compatible standalone predicates
-- ────────────────────────────────────────────────────────────────

/-- A model is universal if it simulates all partial recursive
    functions. Now a consequence of the structure field. -/
def CompModel.Universal (m : CompModel) : Prop :=
  ∀ c : Code, ∃ p : m.Prog, ∀ n, m.eval p n = Code.eval c n

/-- Every program in the model computes a partial recursive function.
    Now a consequence of the structure field. -/
def CompModel.Representable (m : CompModel) : Prop :=
  ∀ p : m.Prog, ∃ c : Code, ∀ n, m.eval p n = Code.eval c n

/-- Self-reference capacity (Kleene property): for every endomorphism
    on programs, a semantic fixed point exists.

    This is the abstract version of Kleene's recursion theorem — the
    fixed-point result that connects computation to the F(X) ≅ X
    story. With an acceptable numbering, it follows from the s-m-n
    theorem and universality via the standard proof of Kleene's
    recursion theorem (see `Code.fixed_point` in Mathlib for the
    concrete version on `Code`).

    The derivation from the CompModel axioms (eval_partrec + smn +
    universal) is given in `CompModel.hasSelfReference_of_computable`
    (in RogersIsomorphism.lean), which proves it for computable
    endomorphisms `f`. The unrestricted version (all endomorphisms)
    is retained here as a definition for the narrative connecting
    the characterization to the fixed-point story. -/
def CompModel.HasSelfReference (m : CompModel) : Prop :=
  ∀ f : m.Prog → m.Prog,
    ∃ p : m.Prog, ∀ n, m.eval (f p) n = m.eval p n

-- ────────────────────────────────────────────────────────────────
-- Structure fields as standalone lemmas
-- ────────────────────────────────────────────────────────────────

/-- Every `CompModel` is universal by construction. -/
theorem CompModel.universal_of (m : CompModel) : m.Universal :=
  m.universal

/-- Every `CompModel` is representable by construction. -/
theorem CompModel.representable_of (m : CompModel) :
    m.Representable :=
  m.representable

-- ────────────────────────────────────────────────────────────────
-- Two models are equivalent
-- ────────────────────────────────────────────────────────────────

/-- Two models are equivalent when they compute the same partial
    functions (mutual simulation). -/
def CompModel.Equiv (m₁ m₂ : CompModel) : Prop :=
  (∀ p : m₁.Prog, ∃ q : m₂.Prog,
    ∀ n, m₁.eval p n = m₂.eval q n) ∧
  (∀ q : m₂.Prog, ∃ p : m₁.Prog,
    ∀ n, m₁.eval p n = m₂.eval q n)

-- ────────────────────────────────────────────────────────────────
-- The characterization theorem
-- ────────────────────────────────────────────────────────────────

/-- **Characterization theorem** (Lindstrom-type):
    Any two acceptable numberings are equivalent — they compute
    exactly the same class of partial functions.

    This is the Church-Turing thesis reframed: it does not explain
    *why* any particular model is universal, but rather that
    acceptable numberings pin down a unique equivalence class.
    The self-reference / fixed-point structure (Kleene's recursion
    theorem, derivable from s-m-n + universality) is the mechanism
    connecting this result to the broader F(X) ≅ X story.

    The proof: for any program `p` in `m₁`, representability gives
    a `Code` `c` computing the same function; universality of `m₂`
    gives a program `q` in `m₂` that simulates `c`. The reverse
    direction is symmetric. -/
theorem characterization (m₁ m₂ : CompModel) :
    m₁.Equiv m₂ := by
  constructor
  · intro p
    obtain ⟨c, hc⟩ := m₁.representable p
    obtain ⟨q, hq⟩ := m₂.universal c
    exact ⟨q, fun n => by rw [hc, hq]⟩
  · intro q
    obtain ⟨c, hc⟩ := m₂.representable q
    obtain ⟨p, hp⟩ := m₁.universal c
    exact ⟨p, fun n => by rw [hp, hc]⟩

-- ────────────────────────────────────────────────────────────────
-- Equivalence is an equivalence relation
-- ────────────────────────────────────────────────────────────────

/-- Equivalence is reflexive. -/
theorem equiv_refl (m : CompModel) : m.Equiv m :=
  ⟨fun p => ⟨p, fun _ => rfl⟩,
   fun p => ⟨p, fun _ => rfl⟩⟩

/-- Equivalence is symmetric. -/
theorem equiv_symm {m₁ m₂ : CompModel}
    (h : m₁.Equiv m₂) : m₂.Equiv m₁ :=
  ⟨fun q =>
    let ⟨p, hp⟩ := h.2 q; ⟨p, fun n => (hp n).symm⟩,
   fun p =>
    let ⟨q, hq⟩ := h.1 p; ⟨q, fun n => (hq n).symm⟩⟩

/-- Equivalence is transitive. -/
theorem equiv_trans {m₁ m₂ m₃ : CompModel}
    (h₁₂ : m₁.Equiv m₂) (h₂₃ : m₂.Equiv m₃) :
    m₁.Equiv m₃ := by
  constructor
  · intro p
    obtain ⟨q, hq⟩ := h₁₂.1 p
    obtain ⟨r, hr⟩ := h₂₃.1 q
    exact ⟨r, fun n => by rw [hq, hr]⟩
  · intro r
    obtain ⟨q, hq⟩ := h₂₃.2 r
    obtain ⟨p, hp⟩ := h₁₂.2 q
    exact ⟨p, fun n => by rw [hp, hq]⟩

end FixedPoint.ChurchTuring
