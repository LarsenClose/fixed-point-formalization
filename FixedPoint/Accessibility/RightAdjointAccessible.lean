/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

# Right adjoints between locally presentable categories are accessible

This file formalizes Adamek-Rosicky Theorem 2.23: if G : D => C is a right
adjoint and both C, D are locally kappa-presentable, then G is kappa'-accessible
for some regular cardinal kappa'.

This is the key theorem needed to eliminate the `PreservesColimit` hypothesis in
`FixedPoint.Specification.SubstrateIndependent`.

## Proof Strategy

Let adj : F -| G with C, D both kappa-locally presentable.

1. G preserves all limits (right adjoint).
2. For kappa-presentable X in C, Hom(X, G(-)) ~= Hom(FX, -) by adjunction.
3. F(X) is presentable in D (every object in a locally presentable category is).
4. Take kappa' large enough that F(X) is kappa'-presentable for all
   kappa-presentable X (using essential smallness of the set of presentable objects).
5. Then Hom(X, G(-)) preserves kappa'-filtered colimits for all kappa-presentable X.
6. Since kappa-presentable objects form a strong generator / dense subcategory,
   this suffices to conclude G preserves kappa'-filtered colimits.

## References

* [Adamek, J. and Rosicky, J., *Locally presentable and accessible categories*,
  Theorem 2.23][Adamek_Rosicky_1994]
-/
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace FixedPoint.Accessibility

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-! ## Subtask 1: Cardinal supremum for presentability

Given an essentially small collection of objects in a locally presentable category,
find a single regular cardinal kappa' such that all of them are kappa'-presentable. -/

/-- In a locally presentable category, given an essentially small property P,
    there exists a regular cardinal such that all objects satisfying P are
    presentable at that cardinal.

    This follows from essential smallness: there are only set-many objects
    (up to iso) satisfying P, each is presentable at some cardinal, and the
    supremum of set-many regular cardinals (raised to the next regular) works.

    Note: In a locally presentable category, every object is presentable
    (`IsPresentable`), so `IsPresentable.exists_cardinal` gives a cardinal
    for each object. The challenge is finding a uniform one. -/
theorem exists_uniform_cardinal_presentable
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ]
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular),
      ∀ (X : C), P X → IsCardinalPresentable X κ' := by
  -- Step 1: Get a small property Q with Q ≤ P and P ≤ Q.isoClosure
  obtain ⟨Q, hQsmall, hQP, hPQ⟩ :=
    ObjectProperty.EssentiallySmall.exists_small_le P
  -- Step 2: Every object in C is presentable (locally presentable => presentable)
  obtain ⟨Pgen, _, hgen⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  have hPres : ∀ (Y : C), Q Y →
      ∃ (κ_Y : Cardinal.{w}) (_ : Fact κ_Y.IsRegular),
        IsCardinalPresentable Y κ_Y := fun Y _ =>
    (hgen.presentable Y).exists_cardinal
  -- Step 3: Build a small index type and extract cardinals
  let ι := Shrink.{w} (Subtype Q)
  let obj : ι → C := fun i => ((equivShrink (Subtype Q)).symm i).val
  let κ_of : ι → Cardinal.{w} := fun i =>
    (hPres (obj i) ((equivShrink (Subtype Q)).symm i).property).choose
  -- Step 4: Take sup + aleph0, then successor to get regular
  let κ' := Order.succ ((⨆ i, κ_of i) ⊔ Cardinal.aleph0)
  have hκ'_reg : Fact κ'.IsRegular := ⟨isRegular_succ le_sup_right⟩
  refine ⟨κ', hκ'_reg, ?_⟩
  intro X hX
  -- X satisfies P, hence is in Q.isoClosure: ∃ Y with Q Y and X ≅ Y
  obtain ⟨Y, hQY, ⟨e⟩⟩ := hPQ _ hX
  let i : ι := equivShrink (Subtype Q) ⟨Y, hQY⟩
  have hY_spec := (hPres (obj i)
    ((equivShrink (Subtype Q)).symm i).property).choose_spec
  have hobj_eq : obj i = Y := by simp only [obj, i, Equiv.symm_apply_apply]
  obtain ⟨hFact_i, hPres_i⟩ := hY_spec
  -- Transfer presentability from obj i to Y, then use monotonicity
  have hPres_Y_at_i : IsCardinalPresentable Y (κ_of i) := hobj_eq ▸ hPres_i
  have hle : κ_of i ≤ κ' :=
    le_trans (le_trans (le_ciSup (bddAbove_range κ_of) i) le_sup_left)
      (Order.le_succ _)
  haveI : Fact (κ_of i).IsRegular := hFact_i
  haveI : IsCardinalPresentable Y (κ_of i) := hPres_Y_at_i
  have hPres_Y : IsCardinalPresentable Y κ' := isCardinalPresentable_of_le Y hle
  -- Transfer along iso from Y to X
  haveI : IsCardinalPresentable Y κ' := hPres_Y
  exact isCardinalPresentable_of_iso e.symm κ'

/-! ## Subtask 2: Uniform presentability of left adjoint on generators

Given adj : F -| G with D locally presentable, for any essentially small
collection of objects in C, there exists kappa' such that F sends them all
to kappa'-presentable objects in D. -/

/-- The left adjoint F sends any essentially small collection of objects in C
    to a collection that is uniformly kappa'-presentable in D, for some
    regular kappa'. This uses the fact that every object in a locally
    presentable category is presentable. -/
theorem exists_uniform_presentable_left_adjoint
    {F : C ⥤ D}
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable D κ]
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular),
      ∀ (X : C), P X → IsCardinalPresentable (F.obj X) κ' := by
  obtain ⟨κ', hκ', h⟩ := exists_uniform_cardinal_presentable (C := D) κ (P := P.map F)
  exact ⟨κ', hκ', fun X hX => h (F.obj X) ⟨X, hX, ⟨Iso.refl _⟩⟩⟩

/-! ## Subtask 3: Adjunction isomorphism on Hom-functors

The adjunction F -| G gives a natural isomorphism
  Hom(X, G(-)) ~= Hom(FX, -)
which transfers accessibility from the representable Hom(FX, -) to
the composite Hom(X, G(-)). -/

/-- If F(X) is kappa'-presentable, then the composite G followed by
    coyoneda.obj (op X) is kappa'-accessible.
    This follows from the adjunction isomorphism
    Hom(X, G(-)) ~= Hom(F(X), -) and the fact that
    Hom(F(X), -) is kappa'-accessible when F(X) is kappa'-presentable. -/
theorem isCardinalAccessible_coyoneda_comp_rightAdj
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular]
    (X : C) [IsCardinalPresentable (F.obj X) κ'] :
    (G ⋙ coyoneda.obj (op X)).IsCardinalAccessible κ' := by
  -- By adjunction, Hom(X, G(-)) ≅ Hom(FX, -) naturally. Since FX is κ'-presentable,
  -- Hom(FX, -) preserves κ'-filtered colimits, hence so does Hom(X, G(-)).
  -- The proof uses uliftCoyoneda to bridge the universe gap between v₁ and v₂,
  -- then strips the ULift using the fact that uliftFunctor reflects colimits.
  -- Step 1: IsCardinalPresentable (F.obj X) κ' gives uliftCoyoneda accessibility
  haveI : ((F.op ⋙ uliftCoyoneda.{v₁, v₂, u₂}).obj (op X)).IsCardinalAccessible κ' :=
    (@isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v₁, w, v₂, u₂}
      D _ (F.obj X) κ' _).mp inferInstance
  -- Step 2: Transfer via adj.compUliftCoyonedaIso (natural iso on ULift Hom-functors)
  haveI : (G ⋙ uliftCoyoneda.{v₂, v₁, u₁}.obj (op X)).IsCardinalAccessible κ' :=
    Functor.isCardinalAccessible_of_natIso
      (@Adjunction.compUliftCoyonedaIso.{0} _ _ _ _ _ _ adj |>.app (op X)) κ'
  -- Step 3: Strip uliftFunctor (uliftCoyoneda.obj = coyoneda.obj ⋙ uliftFunctor)
  -- using the fact that uliftFunctor reflects colimits
  constructor
  intro J _ _
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (G ⋙ uliftCoyoneda.{v₂, v₁, u₁}.obj (op X)) κ' J
  exact {
    preservesColimit {K} := {
      preserves {c} hc := ⟨isColimitOfReflects (uliftFunctor.{v₂, v₁})
        (isColimitOfPreserves
          (G ⋙ uliftCoyoneda.{v₂, v₁, u₁}.obj (op X)) hc)⟩
    }
  }

/-! ## Subtask 4: Detection of colimit preservation by generators

This is the core technical content. If Hom(X, G(-)) preserves kappa'-filtered
colimits for all kappa-presentable X (which form a strong generator / dense
subcategory), then G itself preserves kappa'-filtered colimits.

The argument: a cocone map is an iso iff Hom(X, -) of it is iso for all X
in a strong generator. The kappa-presentable objects form a strong generator
(IsCardinalFilteredGenerator.isStrongGenerator). -/

/-- Detection of accessibility by a generating set: if G : D => C is such that
    for all X in a strong generating set, Hom(X, G(-)) preserves kappa'-filtered
    colimits, then G is kappa'-accessible.

    This is the key lemma and the most technically demanding part of the
    formalization. It uses:
    - The strong generators detect isomorphisms
    - A cocone is a colimit iff it is after applying Hom(X, -) for all
      generators X
    - The kappa-presentable objects form a strong generator -/
theorem isCardinalAccessible_of_coyoneda_comp_accessible
    {G : D ⥤ C}
    (κ κ' : Cardinal.{w}) [Fact κ.IsRegular] [Fact κ'.IsRegular]
    [IsCardinalLocallyPresentable C κ]
    (hle : κ ≤ κ')
    (h : ∀ (X : C), IsCardinalPresentable X κ →
      (G ⋙ coyoneda.obj (op X)).IsCardinalAccessible κ') :
    G.IsCardinalAccessible κ' := by
  -- Strategy: For κ'-filtered J, K : J ⥤ D with colimit c, show G.mapCocone c
  -- is a colimit in C. Since C is cocomplete, the colimit d of K ⋙ G exists.
  -- The comparison map σ : d.pt → G(c.pt) is an iso because:
  -- (1) σ is mono (detected by the separating family of κ-presentable objects)
  -- (2) Hom(Xi, σ) is surjective for all κ-presentable Xi
  -- (3) The strong generator gives: mono + surjective precomposition → iso
  constructor
  intro J _ hJ
  constructor
  intro K
  constructor
  intro c hc
  -- hc : IsColimit c (in D), need: Nonempty (IsColimit (G.mapCocone c)) (in C)
  -- The comparison map from the colimit of K ⋙ G to G(c.pt)
  let d := getColimitCocone (K ⋙ G)
  let σ : d.cocone.pt ⟶ G.obj c.pt := d.isColimit.desc (G.mapCocone c)
  -- If σ is iso, then G.mapCocone c is a colimit (isomorphic to d)
  suffices hσ : IsIso σ by
    exact ⟨IsColimit.ofIsoColimit d.isColimit
      (Cocones.ext (asIso σ) (fun j => d.isColimit.fac (G.mapCocone c) j))⟩
  -- To show σ is iso, use the strong generator of κ-presentable objects.
  have hgen := isCardinalFilteredGenerator_isCardinalPresentable C κ
  have hstrong := hgen.isStrongGenerator
  -- Key observation: for any κ-presentable Xi, Hom(Xi, σ) is bijective.
  -- This is because:
  -- (a) d is a κ'-filtered colimit in C. Xi is κ'-presentable (since κ ≤ κ').
  --     So Hom(Xi, d.pt) ≅ colim_j Hom(Xi, (K ⋙ G).obj j)
  -- (b) By hypothesis h, Hom(Xi, G(-)) preserves κ'-filtered colimits.
  --     So Hom(Xi, G(c.pt)) ≅ colim_j Hom(Xi, G(K.obj j))
  -- These two colimits are the same, and σ induces the canonical comparison.
  have key : ∀ (Xi : C), isCardinalPresentable C κ Xi →
      Function.Bijective (fun (f : Xi ⟶ d.cocone.pt) => f ≫ σ) := by
    intro Xi hXi
    -- Xi is κ-presentable, hence κ'-presentable
    have hXi_κ : IsCardinalPresentable Xi κ := (isCardinalPresentable_iff κ Xi).mp hXi
    have hXi' : IsCardinalPresentable Xi κ' := isCardinalPresentable_of_le Xi hle
    -- d.cocone is a κ'-filtered colimit in C, Xi is κ'-presentable
    have : PreservesColimitsOfShape J (coyoneda.obj (op Xi)) :=
      preservesColimitsOfShape_of_isCardinalPresentable Xi κ' J
    have hd_colim : IsColimit ((coyoneda.obj (op Xi)).mapCocone d.cocone) :=
      (PreservesColimit.preserves d.isColimit).some
    -- From hypothesis h, Hom(Xi, G(-)) preserves κ'-filtered colimits
    have hpres_G : (G ⋙ coyoneda.obj (op Xi)).IsCardinalAccessible κ' := h Xi hXi_κ
    have : PreservesColimitsOfShape J (G ⋙ coyoneda.obj (op Xi)) :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible (G ⋙ coyoneda.obj (op Xi)) κ' J
    have hG_colim : IsColimit ((G ⋙ coyoneda.obj (op Xi)).mapCocone c) :=
      (PreservesColimit.preserves hc).some
    -- The map (fun f => f ≫ σ) is the colimit comparison from hd_colim to hG_colim.
    -- Both are colimits of the same diagram, so this map is an iso, hence bijective.
    -- Note: K ⋙ G ⋙ coyoneda.obj (op Xi) = K ⋙ (G ⋙ coyoneda.obj (op Xi)) definitionally.
    -- Step 1: Show (fun f => f ≫ σ) = hd_colim.desc (target cocone)
    suffices hφ : hd_colim.desc ((G ⋙ coyoneda.obj (op Xi)).mapCocone c) = fun f => f ≫ σ by
      rw [← hφ]
      -- The desc from one colimit to another is an iso
      rw [← isIso_iff_bijective]
      change IsIso (hd_colim.coconePointUniqueUpToIso hG_colim).hom
      infer_instance
    -- Verify the desc equals (fun f => f ≫ σ) using uniqueness
    apply hd_colim.hom_ext
    intro j
    simp only [IsColimit.fac]
    -- Goal: (coyoneda.obj (op Xi)).mapCocone d.cocone).ι.app j ≫ (fun f => f ≫ σ) =
    --        ((G ⋙ coyoneda.obj (op Xi)).mapCocone c).ι.app j
    ext f
    simp only [Functor.mapCocone_ι_app, types_comp_apply, Functor.comp_map]
    -- Goal: coyoneda.obj (op Xi)).map (G.map (c.ι.app j)) f =
    --       coyoneda.obj (op Xi)).map (d.cocone.ι.app j) f ≫ σ
    -- i.e.: f ≫ G.map (c.ι.app j) = (f ≫ d.cocone.ι.app j) ≫ σ
    change f ≫ G.map (c.ι.app j) = (f ≫ d.cocone.ι.app j) ≫ σ
    rw [Category.assoc, d.isColimit.fac (G.mapCocone c) j]
    rfl
  -- σ is mono (from injectivity of Hom(Xi, σ) for all generators Xi)
  have hmono : Mono σ := by
    rw [hstrong.isSeparating.mono_iff σ]
    intro Xi hXi g₁ g₂ hg
    exact (key Xi hXi).injective hg
  -- σ is iso (strong generator: mono + surjective precomposition → iso)
  exact hstrong.isIso_of_mono σ (fun Xi hXi => (key Xi hXi).surjective)

/-! ## Subtask 5: Assembly -- Adamek-Rosicky Theorem 2.23

Combine all subtasks into the main result. -/

/-- **Adamek-Rosicky Theorem 2.23**: A right adjoint between locally
    presentable categories is accessible.

    Given an adjunction F -| G where C and D are both locally
    kappa-presentable, G is kappa'-accessible for some regular
    cardinal kappa' >= kappa.

    Proof outline:
    1. The kappa-presentable objects in C are essentially small
       (from HasCardinalFilteredGenerator).
    2. For each kappa-presentable X, F(X) is presentable in D
       (locally presentable => all presentable).
    3. Find uniform kappa' such that F(X) is kappa'-presentable
       for all kappa-presentable X.
    4. By adjunction, Hom(X, G(-)) ~= Hom(FX, -) preserves
       kappa'-filtered colimits.
    5. By detection on generators, G preserves kappa'-filtered
       colimits. -/
theorem rightAdjoint_isAccessible
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ]
    [IsCardinalLocallyPresentable D κ] :
    Functor.IsAccessible.{w} G := by
  -- Step 1-3: Get uniform κ₁ for F on generators
  obtain ⟨κ₁, hκ₁, hpres⟩ := exists_uniform_presentable_left_adjoint (F := F) κ
    (P := isCardinalPresentable C κ)
  -- Raise to κ' ≥ κ: take κ' = succ(κ ⊔ κ₁)
  let κ' := Order.succ (κ ⊔ κ₁)
  have hκ'_reg : Fact κ'.IsRegular :=
    ⟨isRegular_succ (le_sup_of_le_right (Fact.out : κ₁.IsRegular).aleph0_le)⟩
  have hle : κ ≤ κ' := le_trans le_sup_left (Order.le_succ _)
  have hle₁ : κ₁ ≤ κ' := le_trans le_sup_right (Order.le_succ _)
  haveI := hκ'_reg; haveI := hκ₁
  -- Step 4-5: Assemble via adjunction iso + detection by generators
  haveI : G.IsCardinalAccessible κ' :=
    isCardinalAccessible_of_coyoneda_comp_accessible κ κ' hle (fun X hX => by
      haveI : IsCardinalPresentable (F.obj X) κ₁ := hpres X hX
      haveI : IsCardinalPresentable (F.obj X) κ' := isCardinalPresentable_of_le (F.obj X) hle₁
      exact isCardinalAccessible_coyoneda_comp_rightAdj adj κ' X)
  exact Functor.isAccessible_of_isCardinalAccessible G κ'

/-- Corollary: the right adjoint is kappa'-accessible at a specific
    cardinal. -/
theorem rightAdjoint_isCardinalAccessible
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable C κ]
    [IsCardinalLocallyPresentable D κ] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular),
      Functor.IsCardinalAccessible G κ' :=
  (rightAdjoint_isAccessible adj κ).exists_cardinal

/-! ## Application: Eliminating the PreservesColimit hypothesis

These results connect AR 2.23 back to the fixed-point construction. -/

/-- In a locally presentable monoidal closed category, the internal hom
    endofunctor ihom(A) is accessible (as a right adjoint of
    tensorLeft A). -/
theorem ihom_isAccessible
    {C : Type u₁} [Category.{v₁} C]
    [MonoidalCategory C] [MonoidalClosed C]
    [IsLocallyPresentable.{w} C] (A : C) [Closed A] :
    Functor.IsAccessible.{w} (ihom A) := by
  have ⟨κ, hκ, hLP⟩ := IsLocallyPresentable.exists_cardinal C
  haveI := hκ
  haveI := hLP
  exact rightAdjoint_isAccessible (ihom.adjunction A) κ

/-- In a locally **finitely** presentable monoidal closed category, if `tensorLeft A`
    sends finitely presentable objects to finitely presentable objects, then `ihom(A)`
    preserves all colimits of shape ℕ.

    **Proof** (LFP route, closing the gap noted in SubstrateIndependent.lean):
    1. Apply AR 2.23 at κ = κ' = aleph_0:
       - For each aleph_0-presentable X, the adjunction iso gives
         `Hom(X, ihom(A)(-)) ≅ Hom(A ⊗ X, -)`.
       - Since A ⊗ X is aleph_0-presentable (hypothesis), `Hom(A ⊗ X, -)` preserves
         aleph_0-filtered = filtered colimits.
       - The aleph_0-presentable objects form a strong generator (IsLocallyFinitelyPresentable).
       - Hence `ihom(A)` preserves aleph_0-filtered = filtered colimits.
    2. ℕ is filtered (= aleph_0-filtered), so `ihom(A)` preserves ℕ-shaped colimits.

    The hypothesis `hA` says `tensorLeft A` (the functor X ↦ A ⊗ X) preserves finite
    presentability. This holds, for example, when A is finitely presentable and the
    monoidal structure is closed and compatible with filtered colimits (e.g. in module
    categories, presheaf categories, etc.). -/
theorem ihom_preservesColimitsOfShape_nat
    {C : Type u₁} [Category.{v₁} C]
    [MonoidalCategory C] [MonoidalClosed C]
    [IsLocallyFinitelyPresentable.{0} C]
    (A : C) [Closed A]
    (hA : ∀ (X : C), IsFinitelyPresentable.{0} X →
        IsFinitelyPresentable.{0} ((MonoidalCategory.tensorLeft A).obj X)) :
    PreservesColimitsOfShape ℕ (ihom A) := by
  -- Aleph0 is a regular cardinal (needed for instance resolution)
  haveI : Fact (Cardinal.aleph0 : Cardinal.{0}).IsRegular := Cardinal.fact_isRegular_aleph0
  -- Step 1: ihom A is aleph0-accessible (AR 2.23 at κ = κ' = aleph0)
  have hAcc : (ihom A).IsCardinalAccessible (Cardinal.aleph0 : Cardinal.{0}) :=
    isCardinalAccessible_of_coyoneda_comp_accessible Cardinal.aleph0 Cardinal.aleph0
      (le_refl Cardinal.aleph0)
      (fun X hX => by
        haveI : IsFinitelyPresentable.{0} X := hX
        haveI : IsCardinalPresentable ((MonoidalCategory.tensorLeft A).obj X) Cardinal.aleph0 :=
          hA X hX
        exact isCardinalAccessible_coyoneda_comp_rightAdj (ihom.adjunction A) Cardinal.aleph0 X)
  -- Step 2: ℕ is aleph0-filtered (= filtered)
  have hfilt : IsCardinalFiltered (ℕ : Type 0) (Cardinal.aleph0 : Cardinal.{0}) := by
    rw [isCardinalFiltered_aleph0_iff]
    infer_instance
  -- Step 3: aleph0-accessible functor preserves colimits of aleph0-filtered shapes
  exact @Functor.preservesColimitsOfShape_of_isCardinalAccessible
    C _ C _ (ihom A) (Cardinal.aleph0 : Cardinal.{0}) _ hAcc (ℕ : Type 0) inferInstance hfilt

/-- The key application: ihom(A) preserves the colimit of any Nat-indexed diagram.
    Follows from `ihom_preservesColimitsOfShape_nat` under the LFP hypothesis. -/
theorem ihom_preservesColimit_nat_diagram
    {C : Type u₁} [Category.{v₁} C]
    [MonoidalCategory C] [MonoidalClosed C]
    [IsLocallyFinitelyPresentable.{0} C]
    (A : C) [Closed A]
    (hA : ∀ (X : C), IsFinitelyPresentable.{0} X →
        IsFinitelyPresentable.{0} ((MonoidalCategory.tensorLeft A).obj X))
    (K : ℕ ⥤ C) :
    PreservesColimit K (ihom A) := by
  have : PreservesColimitsOfShape ℕ (ihom A) :=
    ihom_preservesColimitsOfShape_nat A hA
  infer_instance

end FixedPoint.Accessibility
