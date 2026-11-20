import SGPT.Trace.BertiniUniversalSingularExtension
import SGPT.Trace.BertiniFixedNativeMemberLift

/-! Uniform original full native pullback H0 lifting, no connected member
or finite restricted-weight point; SAME original multiplier ideals. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeKodairaPullback SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.Bertini SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem exists_regular_original_native_multiplier_lift_threshold
    (ωb : KahlerBackground n X) (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    ∃ C bK : ℝ, 0 < C ∧ 0 ≤ bK ∧ ∀ b : ℝ, 0 ≤ b →
      ∀ (W : Set X) (m : ℕ) (_hclosed : IsClosed W) (hkn : m ≤ n)
        (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m), m < n →
      ∀ (R : X → ℝ), IsGlobalNormalPole ωb W R →
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v) →
      ∀ (V : HermitianHolomorphicLineBundle.{0,0} n X), IsSourceSmoothHermitianMetric V →
      ∀ (θV : ClosedRealOneOneForm n X), IsOwnFirstChernForm V θV →
      (θV - (regularNormalPoleThreshold n m bK b + C) • ωb.form).val.IsSemipositive →
      let hk : m ≤ n := hkn
      letI := chartedSpace hk hreg
      letI := isComplexManifold_chartedSpace hk hreg
      let ι : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ :=
        ⟨Subtype.val,contMDiff_val hk hreg⟩
      ∀ σ : nativeMultiplierSections (nativeHolomorphicPullbackBundle V ι) (fun y : W => φ y.val),
        ∃ s : nativeMultiplierSections V φ, sourceNativeHolomorphicSectionPullback V ι s.val = σ.val := by
  obtain ⟨C,bK,hC,hbK,hAll⟩ := exists_regular_original_multiplier_extension_threshold ωb φ hφ
  refine ⟨C,bK,hC,hbK,?_⟩
  intro b hb W m hclosed hkn hreg hmn R hR hbR V hV θV hθV hmargin hk
  let := chartedSpace hk hreg
  let := isComplexManifold_chartedSpace hk hreg
  intro ι σ
  have hσ := nativeRestrictedMultiplierSection_isAlong V (contMDiff_val hk hreg) φ hφ.1 σ
  obtain ⟨s,hseq⟩ := hAll b hb W m hclosed hkn hreg hmn R hR hbR V hV θV hθV hmargin
    (fun y => σ.val y) hσ
  refine ⟨s,?_⟩
  ext y
  exact hseq y

end SGPT.Trace.BertiniUniversal
