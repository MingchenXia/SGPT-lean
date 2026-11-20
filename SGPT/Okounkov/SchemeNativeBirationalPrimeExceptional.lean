import SGPT.Okounkov.SchemeNativeBirationalPrimeCycleClassification
import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder

/-! A prime carrier inside the exceptional locus cannot have a codimension-one image. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy
open SGPT.NAPotential.SmoothDivisorNormalOrder
open SGPT.Projective.BDivNov16 SGPT.Projective.NumEq.AlgebraicCurveDegree
open scoped Topology Manifold ContDiff

local instance pointTopology {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f

local instance pointCharts {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n

local instance pointManifold {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The actual image trace of an analytically exceptional carrier cannot be the
trace of an algebraic codimension-one point. -/
theorem coheight_ne_one_of_complexCarrier_subset_exceptional
    {V X : Scheme.{0}} [IsIntegral X] (p : V ⟶ X) [IsProper p]
    (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [SmoothOfRelativeDimension (m + 1) (p ≫ f)]
    [IsSeparated f] [QuasiCompact f] [IsSeparated (p ≫ f)] [QuasiCompact (p ≫ f)]
    (v : V)
    (hπ : IsAnalyticModification (n := m + 1) (schemeComplexPointMap (p ≫ f) f p rfl))
    (hExc : schemeNativeAlgebraicTrace (p ≫ f) (closure ({v} : Set V)) ⊆
      exceptionalLocus (m + 1) (schemeComplexPointMap (p ≫ f) f p rfl)) :
    Order.coheight (p v) ≠ 1 := by
  intro hz
  let : Smooth (p ≫ f) := SmoothOfRelativeDimension.smooth (m + 1) (p ≫ f)
  have hsub : schemeNativeAlgebraicTrace f (closure ({p v} : Set X)) ⊆
      schemeComplexPointMap (p ≫ f) f p rfl ''
        exceptionalLocus (m + 1) (schemeComplexPointMap (p ≫ f) f p rfl) := by
    unfold schemeNativeAlgebraicTrace at hExc ⊢
    rw [← schemeComplexPointMap_image_pointClosure f p v]
    exact image_mono hExc
  obtain ⟨y, _, Φ, _⟩ := exists_nativeNormalOrder f m hz
  have hreg := IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Φ
  obtain ⟨z, _, d, hd, hz'⟩ := DimensionMonotone.locDimGE_of_regularAtDim_subset
    (AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hπ)
    hsub hreg univ univ_mem
  have hbound := AnalyticModificationExceptionalImageCodimension.add_one_le_pred_of_regularAtDim_image
    hπ hz'
  omega

/-- With the source prime dimension formula, geometric exceptionality forces the
strict dimension drop and the zero original cycle predicted by that formula. -/
theorem nativeBirational_primeCycle_eq_zero_of_complexCarrier_subset_exceptional
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X) [IsProper p]
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [SmoothOfRelativeDimension (m + 1) (p ≫ f)]
    [IsSeparated f] [QuasiCompact f] [IsSeparated (p ≫ f)] [QuasiCompact (p ≫ f)]
    (v : V)
    (hπ : IsAnalyticModification (n := m + 1) (schemeComplexPointMap (p ≫ f) f p rfl))
    (hExc : schemeNativeAlgebraicTrace (p ≫ f) (closure ({v} : Set V)) ⊆
      exceptionalLocus (m + 1) (schemeComplexPointMap (p ≫ f) f p rfl))
    (hsource : (↑(pointDimension V v + 1) : WithBot ℕ∞) =
      topologicalKrullDim V) :
    pointDimension X (p v) < pointDimension V v ∧
      AlgebraicCycle.map p (pointDimension V) (pointDimension X) (schemePointCycle v 1) = 0 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  let : Smooth (p ≫ f) := SmoothOfRelativeDimension.smooth (m + 1) (p ≫ f)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rcases nativeBirational_primeCycle_classification_of_source_dimension p hη v f (m + 1) hsource
    with hdrop | ⟨hz, _, _⟩
  · exact hdrop
  · exact (coheight_ne_one_of_complexCarrier_subset_exceptional p f m v hπ hExc hz).elim

end SGPT.Okounkov
