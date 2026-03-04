/-
  RogersIsomorphism.lean

  Rogers' isomorphism theorem: any two acceptable numberings of the
  partial recursive functions are computably isomorphic — not merely
  extensionally equivalent (which is the characterization theorem),
  but connected by a computable bijection that preserves evaluation.

  The characterization theorem says: the class of partial functions
  computed by any CompModel is the same. Rogers' theorem strengthens
  this: the *index sets* are computably isomorphic via a map that
  respects the numbering.

  ## Structure of this file

  1. `ComputableIso` — structure for a computable, evaluation-preserving
     bijection between two CompModels.
  2. `WeakComputableIso` — the weak version: computable translation
     functions in both directions that preserve evaluation, but are
     not necessarily inverse to each other. This is what the
     characterization theorem directly gives (modulo computability
     of the translation).
  3. `CompModel.translate` — given m₁ and m₂, a computable function
     sending each m₁-program to an m₂-program computing the same
     partial function.
  4. `rogers_weak` — every two CompModels admit a WeakComputableIso.
  5. `rogers_isomorphism` — the full theorem (sorry'd): every two
     CompModels admit a ComputableIso.
  6. `CompModel.hasSelfReference` — derivation of HasSelfReference
     from the CompModel axioms, connecting to Code.fixed_point.

  ## Proof strategy for the full theorem

  The classical proof of Rogers' isomorphism (Rogers 1967, §2.6):

  Given acceptable numberings φ (model m₁) and ψ (model m₂):
  1. Let t : ℕ → ℕ be computable with φ_n = ψ_{t(n)} (translation).
  2. Let s : ℕ → ℕ be computable with ψ_n = φ_{s(n)} (reverse).
  3. t and s give extensional equivalence but are NOT injective in
     general, so they do not form a bijection.
  4. Build a bijection f by a back-and-forth construction:
     - Process natural numbers 0, 1, 2, ... in order.
     - At stage 2n: if n is not yet in dom(f), set f(n) = t(n)
       (or the first available index extensionally equivalent to t(n)).
     - At stage 2n+1: if n is not yet in ran(f), set f⁻¹(n) = s(n)
       (or the first available index extensionally equivalent to s(n)).
     - Use the recursion theorem (Kleene's fixed point) to make this
       self-referential construction computable: the function being
       built needs to query its own prior outputs.
  5. The result is a computable bijection preserving evaluation.

  The main difficulty in Lean 4 formalization:
  - The back-and-forth construction is inherently recursive and
    requires tracking mutable state (which indices are used).
  - Applying Code.fixed_point requires showing the construction
    is partial recursive, which means encoding the state-tracking
    as a partial recursive function.
  - The totality argument (the construction always terminates at
    each stage) requires careful reasoning about the countability
    of programs and the surjectivity of t and s.

  This is a substantial formalization effort. We state the theorem
  and provide the weak version, which is already useful.

  ## References

  - Rogers, H. (1967). Theory of Recursive Functions and Effective
    Computability, §2.6, Theorem 2-VI (Rogers' Isomorphism Theorem).
  - Soare, R. (1987). Recursively Enumerable Sets and Degrees, §1.5.
  - Cutland, N. (1980). Computability, Ch. 7.
-/
import FixedPoint.ChurchTuring.CharacterizationTheorem
import Mathlib.Computability.Reduce

open Nat.Partrec

namespace FixedPoint.ChurchTuring

/-- A computable, evaluation-preserving bijection between two CompModels.

    This is the strong form of Rogers' isomorphism: an `Equiv` between
    program types that is computable in both directions and preserves
    evaluation semantics extensionally.

    Computability is expressed via `Equiv.Computable`: both the forward
    and backward maps are computable functions (in the sense of Mathlib's
    `Computable`, which requires `Primcodable` instances — these are
    derived from `Denumerable` via `Primcodable.ofDenumerable`). -/
structure ComputableIso (m₁ m₂ : CompModel) where
  /-- The underlying bijection between program types. -/
  equiv : m₁.Prog ≃ m₂.Prog
  /-- Both directions of the bijection are computable. -/
  computable : equiv.Computable
  /-- The forward map preserves evaluation: m₁.eval p = m₂.eval (equiv p). -/
  forward_ext : ∀ (p : m₁.Prog) (n : ℕ), m₁.eval p n = m₂.eval (equiv p) n
  /-- The backward map preserves evaluation: m₂.eval q = m₁.eval (equiv.symm q). -/
  backward_ext : ∀ (q : m₂.Prog) (n : ℕ), m₂.eval q n = m₁.eval (equiv.symm q) n

/-- A weak computable isomorphism: computable translation functions in both
    directions that preserve evaluation, but are not necessarily inverse.

    This is what the characterization theorem directly provides (once we
    establish computability of the translation). It witnesses that the two
    models compute the same class of functions via computable translations. -/
structure WeakComputableIso (m₁ m₂ : CompModel) where
  /-- Forward translation: m₁-programs to m₂-programs. -/
  toFun : m₁.Prog → m₂.Prog
  /-- Backward translation: m₂-programs to m₁-programs. -/
  invFun : m₂.Prog → m₁.Prog
  /-- Forward translation is computable. -/
  toFun_computable : Computable toFun
  /-- Backward translation is computable. -/
  invFun_computable : Computable invFun
  /-- Forward translation preserves evaluation. -/
  toFun_ext : ∀ (p : m₁.Prog) (n : ℕ), m₁.eval p n = m₂.eval (toFun p) n
  /-- Backward translation preserves evaluation. -/
  invFun_ext : ∀ (q : m₂.Prog) (n : ℕ), m₂.eval q n = m₁.eval (invFun q) n

-- ────────────────────────────────────────────────────────────────
-- ComputableIso implies WeakComputableIso
-- ────────────────────────────────────────────────────────────────

/-- A strong isomorphism gives a weak one by forgetting invertibility. -/
def ComputableIso.toWeak {m₁ m₂ : CompModel} (iso : ComputableIso m₁ m₂) :
    WeakComputableIso m₁ m₂ where
  toFun := iso.equiv
  invFun := iso.equiv.symm
  toFun_computable := iso.computable.1
  invFun_computable := iso.computable.2
  toFun_ext := iso.forward_ext
  invFun_ext := iso.backward_ext

-- ────────────────────────────────────────────────────────────────
-- ComputableIso implies CompModel.Equiv
-- ────────────────────────────────────────────────────────────────

/-- A computable isomorphism witnesses extensional equivalence. -/
theorem ComputableIso.toEquiv {m₁ m₂ : CompModel}
    (iso : ComputableIso m₁ m₂) : m₁.Equiv m₂ :=
  ⟨fun p => ⟨iso.equiv p, iso.forward_ext p⟩,
   fun q => ⟨iso.equiv.symm q, fun n => (iso.backward_ext q n).symm⟩⟩

/-- A weak computable isomorphism witnesses extensional equivalence. -/
theorem WeakComputableIso.toEquiv {m₁ m₂ : CompModel}
    (w : WeakComputableIso m₁ m₂) : m₁.Equiv m₂ :=
  ⟨fun p => ⟨w.toFun p, w.toFun_ext p⟩,
   fun q => ⟨w.invFun q, fun n => (w.invFun_ext q n).symm⟩⟩

-- ────────────────────────────────────────────────────────────────
-- Computable translation between CompModels
-- ────────────────────────────────────────────────────────────────

/-! ### Translation functions

Every CompModel has a computable translation function to every other
CompModel. The construction uses three ingredients:

1. `eval_partrec`: the source model's evaluation is partial recursive
   as a function `(i, n) ↦ m₁.eval (ofNat i) n`.
2. `universal`: the target model can simulate any Code.
3. `smn` (with computability): the target model's currying function
   `s : Prog → ℕ → Prog` is computable.

Given models m₁ and m₂:
- By `eval_partrec` + `Code.exists_code`, there is a Code `c₁`
  computing m₁'s evaluation function.
- By `m₂.universal c₁`, there is a Prog `q` in m₂ computing
  `Code.eval c₁`, i.e., `m₂.eval q (pair i n) = m₁.eval (ofNat i) n`.
- By `m₂.smn`, `s₂ q i` is a Prog in m₂ computing
  `n ↦ m₂.eval q (pair i n) = m₁.eval (ofNat i) n`.
- The translation sends `p : m₁.Prog` to `s₂ q (encode p) : m₂.Prog`,
  which computes `m₁.eval p` in model m₂.
- This translation is computable because `s₂` is `Computable₂`,
  `q` is a constant, and `encode` is computable. -/

section Translation

variable (m : CompModel)

/-- For the canonical codeModel, eval_partrec is immediate from the field. -/
theorem codeModel_eval_partrec :
    Partrec₂ (fun (i : ℕ) (n : ℕ) =>
      codeModel.eval (Denumerable.ofNat Code i) n) :=
  codeModel.eval_partrec

/-- A Code computing the model's evaluation function (i, n) ↦ m.eval(ofNat i, n).
    Obtained from `eval_partrec` via `Code.exists_code`. -/
noncomputable def CompModel.evalCode (m : CompModel) : Code :=
  (Code.exists_code.1
    (Partrec₂.unpaired'.2 m.eval_partrec)).choose

theorem CompModel.evalCode_spec (m : CompModel) :
    Code.eval m.evalCode = Nat.unpaired (fun i n =>
      m.eval (Denumerable.ofNat m.Prog i) n) :=
  (Code.exists_code.1
    (Partrec₂.unpaired'.2 m.eval_partrec)).choose_spec

theorem CompModel.evalCode_pair (m : CompModel) (i n : ℕ) :
    Code.eval m.evalCode (Nat.pair i n) =
      m.eval (Denumerable.ofNat m.Prog i) n := by
  rw [m.evalCode_spec]
  simp [Nat.unpaired, Nat.unpair_pair]

/-- The s-m-n function extracted from the `smn` field. -/
noncomputable def CompModel.smn_fun (m : CompModel) :
    m.Prog → ℕ → m.Prog :=
  m.smn.choose

theorem CompModel.smn_fun_computable (m : CompModel) :
    Computable₂ m.smn_fun :=
  m.smn.choose_spec.1

theorem CompModel.smn_fun_spec (m : CompModel) :
    ∀ p n x, m.eval (m.smn_fun p n) x =
      m.eval p (Nat.pair n x) :=
  m.smn.choose_spec.2

/-- A program in m₂ that universally simulates m₁'s evaluation.
    Satisfies: `m₂.eval (universalProg m₁ m₂) (pair i n) = m₁.eval (ofNat i) n`. -/
noncomputable def CompModel.universalProg
    (m₁ m₂ : CompModel) : m₂.Prog :=
  (m₂.universal m₁.evalCode).choose

theorem CompModel.universalProg_spec
    (m₁ m₂ : CompModel) (n : ℕ) :
    m₂.eval (m₁.universalProg m₂) n =
      Code.eval m₁.evalCode n :=
  (m₂.universal m₁.evalCode).choose_spec n

/-- Computable translation between two CompModels. Sends `p : m₁.Prog`
    to `s₂ q_univ (encode p) : m₂.Prog` where `q_univ` is a universal
    program for m₁ in m₂ and `s₂` is m₂'s s-m-n function.

    The resulting program computes the same partial function:
    `m₂.eval (compTranslate m₁ m₂ p) = m₁.eval p`.

    Unlike `translate` (which uses `Exists.choose` and cannot be shown
    `Computable`), this translation is provably computable. -/
noncomputable def CompModel.compTranslate
    (m₁ m₂ : CompModel) : m₁.Prog → m₂.Prog :=
  fun p => m₂.smn_fun (m₁.universalProg m₂) (Encodable.encode p)

/-- The computable translation is computable. -/
theorem CompModel.compTranslate_computable
    (m₁ m₂ : CompModel) : Computable (m₁.compTranslate m₂) :=
  m₂.smn_fun_computable.comp
    (Computable.const (m₁.universalProg m₂)) Computable.encode

/-- The computable translation preserves evaluation. -/
theorem CompModel.compTranslate_ext
    (m₁ m₂ : CompModel) (p : m₁.Prog) (n : ℕ) :
    m₁.eval p n = m₂.eval (m₁.compTranslate m₂ p) n := by
  unfold compTranslate
  rw [m₂.smn_fun_spec (m₁.universalProg m₂)
    (Encodable.encode p) n]
  rw [m₁.universalProg_spec m₂]
  rw [m₁.evalCode_pair]
  simp [Denumerable.ofNat_encode]

/-- Computable translation from m.Prog to Code (via `Exists.choose`).
    Noncomputable but preserves evaluation. See `compTranslate` for
    the computable version. -/
noncomputable def CompModel.toCode (m : CompModel) :
    m.Prog → Code :=
  fun p => (m.representable p).choose

/-- Computable translation from Code to m.Prog (via `Exists.choose`). -/
noncomputable def CompModel.fromCode (m : CompModel) :
    Code → m.Prog :=
  fun c => (m.universal c).choose

/-- The toCode translation preserves evaluation. -/
theorem CompModel.toCode_ext (p : m.Prog) (n : ℕ) :
    Code.eval (m.toCode p) n = m.eval p n := by
  exact ((m.representable p).choose_spec n).symm

/-- The fromCode translation preserves evaluation. -/
theorem CompModel.fromCode_ext (c : Code) (n : ℕ) :
    m.eval (m.fromCode c) n = Code.eval c n := by
  exact (m.universal c).choose_spec n

/-- Extensional translation (noncomputable): compose toCode and fromCode.
    See `compTranslate` for the computable version. -/
noncomputable def CompModel.translate
    (m₁ m₂ : CompModel) : m₁.Prog → m₂.Prog :=
  m₂.fromCode ∘ m₁.toCode

/-- Translation preserves evaluation. -/
theorem CompModel.translate_ext
    (m₁ m₂ : CompModel) (p : m₁.Prog) (n : ℕ) :
    m₁.eval p n = m₂.eval (m₁.translate m₂ p) n := by
  simp only [CompModel.translate, Function.comp]
  rw [m₂.fromCode_ext (m₁.toCode p) n, m₁.toCode_ext p n]

end Translation

-- ────────────────────────────────────────────────────────────────
-- Weak Rogers isomorphism (from characterization)
-- ────────────────────────────────────────────────────────────────

/-- **Weak Rogers isomorphism**: any two CompModels are connected by
    computable translation functions preserving evaluation.

    The forward and backward maps preserve evaluation (each m₁-program
    is mapped to an m₂-program computing the same function, and vice
    versa), but they are not in general inverse to each other — a
    single partial function may have many programs computing it, and
    the translation might not map back to the original index.

    This is the content of the characterization theorem, strengthened
    with computability of the translations.

    The translation uses `compTranslate`, which combines `eval_partrec`
    (uniform computability of the evaluation function), `universal`
    (embedding in the target model), and `smn` (computable currying)
    to produce a provably computable, evaluation-preserving map. -/
noncomputable def rogers_weak (m₁ m₂ : CompModel) :
    WeakComputableIso m₁ m₂ where
  toFun := m₁.compTranslate m₂
  invFun := m₂.compTranslate m₁
  toFun_computable := m₁.compTranslate_computable m₂
  invFun_computable := m₂.compTranslate_computable m₁
  toFun_ext := m₁.compTranslate_ext m₂
  invFun_ext := fun q n => m₂.compTranslate_ext m₁ q n

-- ────────────────────────────────────────────────────────────────
-- The full Rogers isomorphism theorem (sorry'd)
-- ────────────────────────────────────────────────────────────────

/-- **Rogers' Isomorphism Theorem**: any two acceptable numberings of
    the partial recursive functions are computably isomorphic.

    That is, there exists a computable bijection between program types
    that preserves evaluation semantics. This strengthens the
    characterization theorem (extensional equivalence) to an actual
    computable bijection.

    The proof requires a back-and-forth patching argument using the
    recursion theorem (Code.fixed_point) to turn the non-injective
    translation functions from `rogers_weak` into a genuine bijection.
    See the module docstring for the proof strategy.

    ## Status

    This is currently sorry'd. The prerequisite infrastructure is
    now in place (`eval_partrec`, `compTranslate`, `rogers_weak`,
    `hasSelfReference_of_computable`). The remaining obstacles are:

    1. **Back-and-forth construction**: the patching argument requires
       building a partial recursive function that tracks its own prior
       outputs (mutable state), which must be encoded as a fixed point
       via Code.fixed_point₂.

    2. **Totality of the construction**: proving that the back-and-forth
       process assigns every index requires a careful cardinality/
       surjectivity argument.

    These are genuine formalization challenges, not fundamental
    mathematical obstacles. The theorem is well-established in
    classical recursion theory. -/
noncomputable def rogers_isomorphism (m₁ m₂ : CompModel) :
    ComputableIso m₁ m₂ := by
  sorry

-- ────────────────────────────────────────────────────────────────
-- Self-reference from CompModel axioms
-- ────────────────────────────────────────────────────────────────

/-- Every CompModel has the self-reference property for computable
    endomorphisms: if f : Prog → Prog is computable, then there exists
    a program p such that f(p) and p compute the same function.

    This derives `HasSelfReference` (restricted to computable f) from
    the CompModel axioms, connecting to Kleene's recursion theorem
    (`Code.fixed_point` in Mathlib).

    The proof replicates the standard Kleene recursion theorem argument
    internally to the model:
    1. Define `g(x, y) = phi_x(x) >>= fun b => phi_b(y)` where
       `phi_i = m.eval(ofNat i)`. This is partial recursive by
       `eval_partrec`.
    2. Get a program `pg` computing `g` (via `universal`).
    3. Using `smn`, form `s pg x` which computes `y => g(x, y)`.
    4. Define `F(x) = encode(f(s pg x))`. Since `f` is computable
       and `s` is computable (strengthened `smn`), `F` is computable.
    5. Get program `d` computing `F` (via `universal`).
    6. The fixed point is `e = s pg (encode d)`:
       `m.eval e n = g(encode d, n) = phi_d(d) >>= phi_?(n)`
       `= (Part.some (encode (f e))) >>= phi_?(n) = m.eval (f e) n`. -/
theorem CompModel.hasSelfReference_of_computable (m : CompModel) :
    ∀ f : m.Prog → m.Prog, Computable f →
    ∃ p : m.Prog, ∀ n, m.eval (f p) n = m.eval p n := by
  intro f hf
  -- phi_i(n) = m.eval(ofNat i, n)
  set φ := fun (i : ℕ) (n : ℕ) =>
    m.eval (Denumerable.ofNat m.Prog i) n with hφ_def
  have hφ : Partrec₂ φ := m.eval_partrec
  -- g(x, y) = phi_x(x) >>= fun b => phi_b(y)
  let g (x y : ℕ) : Part ℕ := (φ x x).bind (fun b => φ b y)
  have hg : Partrec₂ g := by
    suffices h : Partrec (fun p : ℕ × ℕ =>
        (φ p.1 p.1).bind (fun b => φ b p.2)) from h.to₂
    exact Partrec.bind
      (hφ.comp Computable.fst Computable.fst)
      (hφ.comp Computable.snd
        (Computable.snd.comp Computable.fst))
  -- Code and Prog for g
  obtain ⟨cg, eg⟩ := Code.exists_code.1 hg
  have eg' : ∀ a k, Code.eval cg (Nat.pair a k) = g a k :=
    fun a k => by simp [eg, Part.map_id']
  obtain ⟨pg, hpg⟩ := m.universal cg
  -- Computable s from smn
  obtain ⟨s, hs_comp, hs⟩ := m.smn
  -- F(x) = encode(f(s pg x)), computable
  set F := fun x : ℕ =>
    Encodable.encode (f (s pg x)) with hF_def
  have hF_comp : Computable F :=
    Computable.encode.comp
      (hf.comp (hs_comp.comp (Computable.const pg) Computable.id))
  -- Program d computing F
  obtain ⟨c_F, ec_F⟩ :=
    Code.exists_code.1 (Partrec.nat_iff.1 hF_comp)
  obtain ⟨d, hd⟩ := m.universal c_F
  have hd' : ∀ x, m.eval d x =
      Part.some (Encodable.encode (f (s pg x))) :=
    fun x => by rw [hd, ec_F]; rfl
  -- Fixed point: e = s pg (encode d)
  set e := s pg (Encodable.encode d)
  refine ⟨e, fun n => ?_⟩
  -- m.eval (f e) n = m.eval e n
  show m.eval (f e) n = m.eval e n
  change m.eval (f e) n = m.eval (s pg (Encodable.encode d)) n
  rw [hs pg (Encodable.encode d) n, hpg, eg']
  change m.eval (f e) n =
    (φ (Encodable.encode d) (Encodable.encode d)).bind (fun b => φ b n)
  simp only [hφ_def, Denumerable.ofNat_encode]
  rw [hd' (Encodable.encode d), Part.bind_some, Denumerable.ofNat_encode]

/-- The codeModel has self-reference directly from Code.fixed_point. -/
theorem codeModel_hasSelfReference :
    ∀ f : Code → Code, Computable f →
    ∃ c : Code, ∀ n, Code.eval (f c) n = Code.eval c n := by
  intro f hf
  obtain ⟨c, hc⟩ := Code.fixed_point hf
  exact ⟨c, fun n => congr_fun hc n⟩

/-- HasSelfReference for codeModel (computable endomorphisms), stated in
    the HasSelfReference format. Code.fixed_point requires Computable f,
    so this is the computable version. -/
theorem codeModel_HasSelfReference_computable :
    ∀ f : Code → Code, Computable f →
    ∃ c : Code, ∀ n, codeModel.eval (f c) n = codeModel.eval c n :=
  codeModel_hasSelfReference

-- ────────────────────────────────────────────────────────────────
-- ComputableIso is an equivalence relation
-- ────────────────────────────────────────────────────────────────

/-- Reflexivity: every CompModel is computably isomorphic to itself. -/
noncomputable def computableIso_refl (m : CompModel) : ComputableIso m m where
  equiv := Equiv.refl m.Prog
  computable := ⟨Computable.id, Computable.id⟩
  forward_ext := fun _ _ => rfl
  backward_ext := fun _ _ => rfl

/-- Symmetry: computable isomorphism is symmetric. -/
noncomputable def ComputableIso.symm {m₁ m₂ : CompModel}
    (iso : ComputableIso m₁ m₂) : ComputableIso m₂ m₁ where
  equiv := iso.equiv.symm
  computable := iso.computable.symm
  forward_ext := iso.backward_ext
  backward_ext := iso.forward_ext

/-- Transitivity: computable isomorphism is transitive. -/
noncomputable def ComputableIso.trans {m₁ m₂ m₃ : CompModel}
    (iso₁₂ : ComputableIso m₁ m₂) (iso₂₃ : ComputableIso m₂ m₃) :
    ComputableIso m₁ m₃ where
  equiv := iso₁₂.equiv.trans iso₂₃.equiv
  computable := iso₁₂.computable.trans iso₂₃.computable
  forward_ext := fun p n => by
    simp only [Equiv.trans_apply]
    rw [iso₁₂.forward_ext p n, iso₂₃.forward_ext (iso₁₂.equiv p) n]
  backward_ext := fun r n => by
    show m₃.eval r n = m₁.eval ((iso₁₂.equiv.trans iso₂₃.equiv).symm r) n
    simp only [Equiv.symm_trans_apply]
    rw [iso₂₃.backward_ext r n, iso₁₂.backward_ext (iso₂₃.equiv.symm r) n]

-- ────────────────────────────────────────────────────────────────
-- The identity isomorphism on codeModel is trivial
-- ────────────────────────────────────────────────────────────────

/-- The codeModel is computably isomorphic to itself (trivially). -/
noncomputable def codeModel_iso_self : ComputableIso codeModel codeModel :=
  computableIso_refl codeModel

end FixedPoint.ChurchTuring
