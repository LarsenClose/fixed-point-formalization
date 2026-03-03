/-
  RightAdjointUnique.lean

  The uniqueness argument from the paper series: the fixed-point endofunctor
  is forced because it is the right adjoint of a monoidal tensor, and right
  adjoints are unique up to natural isomorphism.

  In a monoidal closed category C:
    tensorLeft A ⊣ ihom A
  Any other right adjoint G to tensorLeft A satisfies G ≅ ihom A
  (by Mathlib's `Adjunction.rightAdjointUniq`). Therefore the endofunctor
  whose initial algebra yields the fixed point is not a free choice — it
  is determined by the monoidal structure.

  STATUS: Tier 1 — fully verified from Mathlib, no sorry.
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Adjunction.Unique

universe v u

open CategoryTheory

namespace FixedPoint.Uniqueness

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The canonical adjunction: tensorLeft A ⊣ ihom A.
    This is the defining property of a monoidal closed category. -/
noncomputable def closedAdjunction (A : C) [Closed A] :
    MonoidalCategory.tensorLeft A ⊣ ihom A :=
  ihom.adjunction A

/-- Core uniqueness theorem: any right adjoint to tensorLeft A is naturally
    isomorphic to ihom A. This is a direct application of Mathlib's
    `Adjunction.rightAdjointUniq`.

    Paper series consequence: the endofunctor F in F(X) ≅ X is not chosen
    but forced by the monoidal structure. -/
noncomputable def rightAdjointForcedToIHom (A : C) [Closed A]
    {G : C ⥤ C} (adj : MonoidalCategory.tensorLeft A ⊣ G) :
    G ≅ ihom A :=
  adj.rightAdjointUniq (ihom.adjunction A)

/-- The endofunctor is unique: if G and G' are both right adjoint to
    tensorLeft A, then G ≅ G'. -/
noncomputable def endofunctorUnique (A : C) [Closed A]
    {G G' : C ⥤ C}
    (adj₁ : MonoidalCategory.tensorLeft A ⊣ G)
    (adj₂ : MonoidalCategory.tensorLeft A ⊣ G') :
    G ≅ G' :=
  adj₁.rightAdjointUniq adj₂

omit [MonoidalClosed C] in
/-- The uniqueness is coherent with units: if adj₁ and adj₂ are two
    adjunctions for the same left adjoint, the isomorphism between
    right adjoints intertwines the units. -/
theorem unit_coherence (A : C) [Closed A]
    {G G' : C ⥤ C}
    (adj₁ : MonoidalCategory.tensorLeft A ⊣ G)
    (adj₂ : MonoidalCategory.tensorLeft A ⊣ G') :
    adj₁.unit ≫
      (MonoidalCategory.tensorLeft A).whiskerLeft (adj₁.rightAdjointUniq adj₂).hom =
    adj₂.unit :=
  Adjunction.unit_rightAdjointUniq_hom adj₁ adj₂

end FixedPoint.Uniqueness
