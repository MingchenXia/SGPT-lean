import SGPT.Projective.AlgebraicStalkCotangentRank
import SGPT.Foundations.Schemes.SchemeComplexPointOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Prescribed relative dimension from genuine original stalk ranks at
actual complex points. Blueprint: algebraic-relative-dimension-criterion.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Module
open SGPT.Okounkov

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- Actual smoothness supplies an ORIGINAL affine chart of some genuine
constant relative dimension, retaining its original scalar ring map. -/
theorem exists_original_standardSmooth_dimension_chart [Smooth f] (x : X) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U), x ∈ U ∧ ∃ d : ℕ,
      RingHom.IsStandardSmoothOfRelativeDimension d
        ((schemeConstantPresheafMap f).app (.op U)).hom := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim y (f x)) ▸ e hx
  subst U
  have hs := hf.comp
    ((RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv).isStandardSmooth)
  let R := Γ(X, V)
  let := affineChartAlgebra f V
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  let : Nontrivial R := (algebraMap R (X.presheaf.stalk x)).domain_nontrivial
  let : Algebra.IsStandardSmooth ℂ R := hs
  let d := finrank R Ω[R⁄ℂ]
  have hrel : Algebra.IsStandardSmoothOfRelativeDimension d ℂ R :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth d).mpr
      (Module.finrank_eq_rank R Ω[R⁄ℂ]).symm
  exact ⟨V, hV, hx, d, hrel⟩

/-- Actual original complex-point cotangent ranks determine the actual
original smooth relative dimension, through genuine Jacobson points and
original standard-smooth charts. All components/empty schemes retained. -/
theorem smoothOfRelativeDimension_of_complexPoint_cotangent_finrank [Smooth f]
    (n : ℕ) (h : ∀ p : SchemeComplexPoint f,
      letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
      finrank (X.presheaf.stalk (schemeComplexPointImage f p))
        Ω[X.presheaf.stalk (schemeComplexPointImage f p)⁄ℂ] = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  constructor
  intro x
  obtain ⟨V, hV, hx, d, hs⟩ := exists_original_standardSmooth_dimension_chart f x
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ V.isOpen.isLocallyClosed
  let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f y hyc, pointOfClosedPoint_comp f y hyc⟩
  have himage : schemeComplexPointImage f p = y := pointOfClosedPoint_apply f y hyc _
  have hpd := originalStalk_cotangent_finrank_of_chart f V hV (schemeComplexPointImage f p)
    (himage.symm ▸ hy) d hs
  have hdn : d = n := hpd.symm.trans (h p)
  have hs' : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op V)).hom := hdn ▸ hs
  let e : V ≤ f ⁻¹ᵁ ⊤ := by simp
  refine ⟨⊤, isAffineOpen_top _, V, hV, hx, e, ?_⟩
  apply (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of ℂ)).inv (f.appLE ⊤ V e) |>.mp
  exact hs'

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
