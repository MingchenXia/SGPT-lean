import SGPT.Trace.BertiniUniversalProduct
import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.Trace.BertiniSectionMultiplication

/-! Actual original global I(phi) representatives yield true finite mass in
manufactured universal q-product coordinates. Preferred Hodge Jacobian remains separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open scoped ProductComplexManifold
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {k n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  (i j : Fin (k + 1 + 1)) (m : Fin (k + 1))
  (B : HermitianHolomorphicLineBundle.{0,0} n X) (φ : X → EReal)

def localProductOriginalDensity
    (T : HolomorphicSections (n := n) B.Fiber) (u : ComplexModel k × localXOpen p i j m) : ℝ≥0∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  exact originalSectionDensity B.Fiber φ 1 T
    (nativeXMap p i ((localProductDiffeomorph p i j m).symm u).val)

theorem localProductOriginalDensity_eq_original
    (T : HolomorphicSections (n := n) B.Fiber) (u : ComplexModel k × localXOpen p i j m) :
    localProductOriginalDensity p i j m B φ T u = originalSectionDensity B.Fiber φ 1 T u.2.val := rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem localProduct_originalMultiplier_integral_lt_top
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (T : nativeMultiplierSections B φ) (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (b : ComplexModel k) (R : ℝ) :
    (∫⁻ u, localProductOriginalDensity p i j m B φ T.val u
      ∂((volume : Measure (ComplexModel k)).restrict (closedBall b R)).prod
        (μ.comap (Subtype.val : localXOpen p i j m → X))) < ⊤ := by
  let ν : Measure (localXOpen p i j m) := μ.comap Subtype.val
  let a : Measure (ComplexModel k) := volume.restrict (closedBall b R)
  let f := originalSectionDensity B.Fiber φ 1 T.val
  have hglobal : (∫⁻ x, f x ∂μ) < ⊤ := by
    simpa only [f,Nat.cast_one] using
      (fullHolomorphicDegreeIdealSections_iff_finite_integral B.Fiber 1 hφ T.val hμ).mp T.property
  have hlocal : (∫⁻ x : localXOpen p i j m, f x.val ∂ν) < ⊤ := by
    have heq := lintegral_subtype_comap (μ := μ) (s := (localXOpen p i j m : Set X))
      (localXOpen p i j m).isOpen.measurableSet f
    exact heq.trans_lt ((setLIntegral_le_lintegral _ f).trans_lt hglobal)
  have hball : a univ < ⊤ := by
    simpa only [a,Measure.restrict_apply_univ] using (measure_closedBall_lt_top (x := b) (r := R))
  change (∫⁻ u : ComplexModel k × localXOpen p i j m, f u.2.val ∂a.prod ν) < ⊤
  calc
    _ ≤ ∫⁻ _b : ComplexModel k, ∫⁻ x : localXOpen p i j m, f x.val ∂ν ∂a := lintegral_prod_le _
    _ = (∫⁻ x : localXOpen p i j m, f x.val ∂ν) * a univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top hlocal hball

end SGPT.Trace.BertiniUniversal
