import SGPT.Projective.AlgebraicCurveWholeCurrent
import SGPT.Projective.NumEqDivisorMixedPeriod
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Hodge.SourceSmoothMixedCohomology

/-! Independent original actual algebraic zero-cycle degree equals the SAME
physical native Chern period, and original algebraic metric Chern period.
Blueprint: algebraic-curve-chern-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric HermitianHolomorphicLineBundle
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms StronglyPositiveForms
open ActualCompactGlobalPairingCalibration MixedMassClassInvariance ConstantFormProducts
open SGPT.Projective.NumEq
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open scoped Topology Manifold BigOperators Distributions
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
local instance chernPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance chernPointCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance chernPointMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance chernPointBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
local instance chernPointManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

/-- SAME independent original algebraic zero degree is the SAME physical native Chern period. -/
theorem sectionZeroCycleDegree_eq_nativeChernPeriod
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0)
    (b : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let B := positivePower (schemeHermitianLineBundle f 1 E a H) k
    let hB := sourceNativePositivePower_smooth (schemeHermitianLineBundle f 1 E a H)
      (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f 1 E a H) k
    ((sectionZeroCycleDegree f E (a.tensorPower (k + 1)) σ hσ b : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (sourceNativeFirstChernForm B hB)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
  dsimp only
  rw [sectionZeroCycleDegree_eq_fullCurrent f E a H k σ hσ b]
  exact pairing_nativeSectionDivisor_eq_slotIntegral κ _ _
    (nativeSectionOfAlgebraicPositivePower f 1 E a H k σ)
    (nativeSectionOfAlgebraicPositivePower_dense f 1 E a H k σ hσ)
    (fun i : Fin 0 => Fin.elim0 i)

/-- The SAME independent original degree equals power times SAME original algebraic
metric Chern period; neither native-own nor tensor Chern law is a supplied premise. -/
theorem sectionZeroCycleDegree_eq_originalChernPeriod
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0)
    (b : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ((sectionZeroCycleDegree f E (a.tensorPower (k + 1)) σ hσ b : ℤ) : ℝ) =
      ((k + 1 : ℕ) : ℝ) * slotIntegral κ
        (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  dsimp only
  let B := schemeHermitianLineBundle f 1 E a H
  let hB := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f 1 E a H
  let q := ((k + 1 : ℕ) : ℝ)
  have hbase := sourceNativeFirstChernForm_geometricallyEq B hB
    (isOwnFirstChernForm_schemeHermitianLineBundle f 1 E a H)
  have hgeo : (sourceNativeFirstChernForm (positivePower B k)
      (sourceNativePositivePower_smooth B hB k)).val.GeometricallyEq (q • H.curvature a).val := by
    intro c z hz
    change (sourceNativeFirstChernForm (positivePower B k)
      (sourceNativePositivePower_smooth B hB k)).val.coeff c z = q • (H.curvature a).val.coeff c z
    rw [sourceNativePositivePower_chern_coeff B hB c hz k, hbase c hz]
  have hrel := ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo
  have hslots : ∀ i : Fin 1, ClosedRealOneOneForm.BottChernRel
      ((Fin.snoc (fun j : Fin 0 => Fin.elim0 j)
        (sourceNativeFirstChernForm (positivePower B k) (sourceNativePositivePower_smooth B hB k)) :
          Fin 1 → ClosedRealOneOneForm 1 (SchemeComplexPoint f)) i)
      ((Fin.snoc (fun j : Fin 0 => Fin.elim0 j) (q • H.curvature a) :
          Fin 1 → ClosedRealOneOneForm 1 (SchemeComplexPoint f)) i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
    simpa only [Fin.snoc_last] using hrel
  rw [sectionZeroCycleDegree_eq_nativeChernPeriod f E a H k σ hσ b κ,
    slotIntegral_eq_of_bottChernRel κ _ _ hslots]
  simpa only [Fin.update_snoc_last, smul_eq_mul] using
    slotIntegral_update_smul κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a))
      (Fin.last 0) q (H.curvature a)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
