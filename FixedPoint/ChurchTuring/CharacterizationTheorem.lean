/-
  CharacterizationTheorem.lean

  The Church-Turing thesis reframed as a Lindstrom-type characterization
  theorem: any computation model that is (a) universal, (b) has
  self-reference capacity, and (c) is representable (no junk programs)
  is equivalent to any other such model.

  The key insight from the paper series: the thesis explains
  equivalence-once-universal, not universality itself. Universality is
  a precondition; the characterization says that once you cross the
  threshold, there is exactly one equivalence class.

  The connection to the fixed-point story: self-reference capacity is
  what Kleene's recursion theorem provides, and Kleene's theorem is
  itself a fixed-point result (F(X) ≅ X at the level of programs).
  See `ideal/Formal/Derivation/ChomskyMathlib.lean` for the full
  formalization of the Chomsky hierarchy, self-reference capacity,
  and the Kleene witness from Mathlib's `Code.fixed_point`.

  Note on representability: Universal says the model can simulate every
  Code program (surjectivity onto partial recursive functions).
  Representable says every program in the model computes a partial
  recursive function (no junk — the model does not overshoot).
  Together they say the model computes *exactly* the partial recursive
  functions. Without Representable, a model could contain programs
  computing non-recursive functions, and equivalence would fail.
  HasSelfReference is retained as a structural condition connecting
  the result to the fixed-point story, even though the current proof
  factors through Representable + Universal alone.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Computability.PartrecCode

open Nat.Partrec

namespace FixedPoint.ChurchTuring

/-- A model of computation: programs and a partial evaluation function. -/
structure CompModel where
  Prog : Type
  eval : Prog → ℕ →. ℕ

/-- Two models are equivalent when they compute the same partial functions. -/
def CompModel.Equiv (m₁ m₂ : CompModel) : Prop :=
  (∀ p : m₁.Prog, ∃ q : m₂.Prog, ∀ n, m₁.eval p n = m₂.eval q n) ∧
  (∀ q : m₂.Prog, ∃ p : m₁.Prog, ∀ n, m₁.eval p n = m₂.eval q n)

/-- A model is universal if it simulates all partial recursive functions. -/
def CompModel.Universal (m : CompModel) : Prop :=
  ∀ c : Code, ∃ p : m.Prog, ∀ n, m.eval p n = Code.eval c n

/-- A model has self-reference capacity (Kleene property): for every
    computable endomorphism on programs, a semantic fixed point exists.
    This is the abstract version of Kleene's recursion theorem — the
    fixed-point result that connects computation to the F(X) ≅ X story. -/
def CompModel.HasSelfReference (m : CompModel) : Prop :=
  ∀ f : m.Prog → m.Prog,
    ∃ p : m.Prog, ∀ n, m.eval (f p) n = m.eval p n

/-- Every program in the model computes a partial recursive function
    (i.e., is representable by some Code). This ensures the model has
    no "junk" programs computing non-recursive functions. Together with
    `Universal`, it says the model computes *exactly* the partial
    recursive functions. -/
def CompModel.Representable (m : CompModel) : Prop :=
  ∀ p : m.Prog, ∃ c : Code, ∀ n, m.eval p n = Code.eval c n

/-- **Characterization theorem** (Lindstrom-type):
    Any two computation models that are universal, representable, and have
    self-reference capacity are equivalent.

    This is the Church-Turing thesis reframed: it does not explain *why*
    any particular model is universal, but rather that universality plus
    representability pins down a unique equivalence class. The fixed-point
    structure (Kleene / self-reference) is the mechanism connecting this
    result to the broader F(X) ≅ X story.

    The proof: for any program p in m₁, representability gives a Code c
    computing the same function; universality of m₂ gives a program q in
    m₂ that simulates c. The reverse direction is symmetric. -/
theorem characterization
    (m₁ m₂ : CompModel)
    (u₁ : m₁.Universal) (u₂ : m₂.Universal)
    (_sr₁ : m₁.HasSelfReference) (_sr₂ : m₂.HasSelfReference)
    (r₁ : m₁.Representable) (r₂ : m₂.Representable) :
    m₁.Equiv m₂ := by
  exact ⟨
    fun p => let ⟨c, hc⟩ := r₁ p; let ⟨q, hq⟩ := u₂ c; ⟨q, fun n => by rw [hc, hq]⟩,
    fun q => let ⟨c, hc⟩ := r₂ q; let ⟨p, hp⟩ := u₁ c; ⟨p, fun n => by rw [hp, hc]⟩
  ⟩

/-- Equivalence from the characterization is reflexive. -/
theorem equiv_refl (m : CompModel) : m.Equiv m :=
  ⟨fun p => ⟨p, fun _ => rfl⟩, fun p => ⟨p, fun _ => rfl⟩⟩

/-- Equivalence from the characterization is symmetric. -/
theorem equiv_symm {m₁ m₂ : CompModel} (h : m₁.Equiv m₂) : m₂.Equiv m₁ :=
  ⟨fun q => let ⟨p, hp⟩ := h.2 q; ⟨p, fun n => (hp n).symm⟩,
   fun p => let ⟨q, hq⟩ := h.1 p; ⟨q, fun n => (hq n).symm⟩⟩

end FixedPoint.ChurchTuring
