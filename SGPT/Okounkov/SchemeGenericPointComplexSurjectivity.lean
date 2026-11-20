import SGPT.Foundations.Schemes.SchemeComplexPointOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Surjectivity on complex points detects the image of the generic point. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace

/-- A morphism of integral complex schemes that is surjective on complex points sends the
generic point to the generic point when the target is locally of finite type over `ℂ`. -/
theorem genericPoint_eq_of_surjective_complexPoints {V X : Scheme.{0}}
    [IsIntegral V] [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (p : V ⟶ X)
    [LocallyOfFiniteType f]
    (hsurj : Function.Surjective (schemeComplexPointMap (p ≫ f) f p rfl)) :
    p (genericPoint V) = genericPoint X := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hpoints : closedPoints X ⊆ range p := by
    intro x hx
    let q : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩
    obtain ⟨v, hv⟩ := hsurj q
    refine ⟨schemeComplexPointImage (p ≫ f) v, ?_⟩
    have hq : schemeComplexPointImage f q = x := pointOfClosedPoint_apply f x hx _
    exact (congrArg (schemeComplexPointImage f) hv).trans hq
  have hdense : DenseRange p := by
    intro x
    apply closure_mono hpoints
    rw [closure_closedPoints]
    exact mem_univ x
  apply ((genericPoint_spec X).eq _).symm
  simpa only [image_univ, hdense.closure_range] using
    (genericPoint_spec V).image p.continuous

end SGPT.Okounkov
