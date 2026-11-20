import SGPT.Projective.OriginalNormalizationCurveSmooth
import SGPT.NAPotential.SmoothAffineDimension

/-! TRUE relative dimension of the actual original normalization, computed
from its SAME actual inverse-affine algebra; no normalized dimension input.
Blueprint: original-normalization-curve-dimension.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Algebra
open scoped nonZeroDivisors

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include E hcurve in
/-- The ACTUAL normalized function field has TRUE transcendence degree
one over the SAME original structural complex algebra, derived from actual
normalization inverse-affine geometry, not a supplied field comparison. -/
theorem originalNormalizationCurve_functionField_trdeg :
    letI := schemeFunctionFieldAlgebra (originalNormalizationMap X ≫ f)
    Algebra.trdeg ℂ (originalNormalizationScheme X).functionField = 1 := by
  let := originalNormalizationMap_finite X f E
  let := E.locallyOfFiniteType
  let g := originalNormalizationMap X ≫ f
  let : LocallyOfFiniteType g := inferInstance
  let := schemeFunctionFieldAlgebra g
  obtain ⟨z⟩ := (inferInstance : Nonempty (originalNormalizationScheme X))
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (originalNormalizationMap X z)) isOpen_univ
  let : Nonempty U := ⟨⟨originalNormalizationMap X z,hxU⟩⟩
  let V := originalNormalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (originalNormalizationMap X)
  let : Nonempty V := ⟨⟨z,hxU⟩⟩
  let := affineChartAlgebra g V
  let : Algebra.FiniteType ℂ Γ(originalNormalizationScheme X, V) := affineChartAlgebra_finiteType g hV
  obtain ⟨d,hd,htr⟩ := finiteTypeDomain_dimension_exists ℂ Γ(originalNormalizationScheme X, V)
  have hd1 : d = 1 := by
    have h := hd.symm.trans (originalNormalizationCurve_affine_ringKrullDim_one f E hcurve hU)
    exact_mod_cast h
  have htr1 : Algebra.trdeg ℂ Γ(originalNormalizationScheme X, V) = 1 := by simpa [hd1] using htr
  let : IsScalarTower ℂ Γ(originalNormalizationScheme X, V) (originalNormalizationScheme X).functionField :=
    schemeFunctionField_affineChartScalarTower g V
  let : IsFractionRing Γ(originalNormalizationScheme X, V) (originalNormalizationScheme X).functionField :=
    functionField_isFractionRing_of_isAffineOpen (originalNormalizationScheme X) V hV
  let : Algebra.IsAlgebraic Γ(originalNormalizationScheme X, V) (originalNormalizationScheme X).functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(originalNormalizationScheme X, V))
  have h := trdeg_add_eq ℂ Γ(originalNormalizationScheme X, V)
    (A := (originalNormalizationScheme X).functionField)
  rw [trdeg_eq_zero (R := Γ(originalNormalizationScheme X, V))
    (A := (originalNormalizationScheme X).functionField),add_zero,htr1] at h
  exact h.symm

include E hcurve in
/-- The SAME actual normalization is a genuine smooth relative-dimension
one curve over the SAME original complex base. All branches are retained. -/
theorem originalNormalizationCurve_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (originalNormalizationMap X ≫ f) := by
  let := originalNormalizationCurve_smooth f E hcurve
  exact SGPT.NAPotential.SmoothAffineDimension.smoothOfRelativeDimension_of_functionField_trdeg
    (originalNormalizationMap X ≫ f) 1 (originalNormalizationCurve_functionField_trdeg f E hcurve)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
