import SGPT.Trace.BertiniUniversalExplicitExtension
import SGPT.Okounkov.TranscendentalCoreGentleSum
import SGPT.Okounkov.TranscendentalCoreRepresentative

/-! Genuine smooth finite weights feed the actual explicit all-member
threshold; uniform curvature loss is allowed before the ample choice. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OTExt4 SGPT.Trace.OTExt5
open SGPT.Okounkov.TranscendentalCore
open SGPT.Foundations.Analysis.Pending.IdealWeightPowers
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def regularSmoothExtensionAt (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (N₀ : ℝ) : Prop :=
  let hk : m ≤ n := hkn
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hreg
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hreg
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hclosed.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ C : ℝ, 0 < C ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ u : X → ℝ, ChartSmooth (n := n) u →
    IsThetaPshPotential (θV - N₀ • ωb.form).val (fun x => (u x : EReal)) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => (u y : EReal)) f →
  ∃ s : HolomorphicSections (n := n) V.Fiber, (∀ y : W, s y = f y) ∧
    ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight 1 ((u x : EReal))
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤
      ENNReal.ofReal C * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 ((u y : EReal))
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem regularSmooth_weight_gentle (ωb : KahlerBackground n X)
    (u : X → ℝ) (hu : ChartSmooth (n := n) u)
    (hq : IsGlobalQuasiPshPotential (n := n) (fun x => (u x : EReal))) :
    HasGentleAnalyticSingularitiesOfType (n := n) (fun x => (u x : EReal)) 1 (unitIdeal n X) := by
  have hzero := hasGentleAnalyticSingularitiesOfType_zero (X := X) (n := n) ⟨ωb⟩
  have hneg : ChartSmooth (n := n) (fun x => -u x) := fun e => (hu e).neg
  have hq' : IsGlobalQuasiPshPotential (n := n) (fun x => (0 : EReal) - ((-u x : ℝ) : EReal)) := by
    simpa only [EReal.coe_neg,zero_sub,neg_neg] using hq
  have h := hasGentleAnalyticSingularitiesOfType_sub_smooth hzero hneg hq'
  simpa only [EReal.coe_neg,zero_sub,neg_neg] using h

omit [BorelSpace X] in
private theorem actualSmooth_extension_of_finiteGentle
    (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (N₀ : ℝ)
    (hExt : regularFiniteGentleExtensionAt ωb hclosed hkn hreg N₀) :
    regularSmoothExtensionAt ωb hclosed hkn hreg N₀ := by
  unfold regularSmoothExtensionAt
  intro hk
  let := chartedSpace hk hreg
  let := isComplexManifold_chartedSpace hk hreg
  let := isCompact_iff_compactSpace.mp hclosed.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  obtain ⟨C,hC,hE⟩ := hExt
  refine ⟨C,hC,?_⟩
  intro V hV θV hθV u hu hΦ f hf
  have hq : IsGlobalQuasiPshPotential (n := n) (fun x => (u x : EReal)) :=
    ⟨hΦ.1.quasiPlurisubharmonic,hΦ.2⟩
  exact hE V hV θV hθV (fun x => (u x : EReal)) hΦ
    ⟨1,unitIdeal n X,regularSmooth_weight_gentle ωb u hu hq⟩ (fun y => EReal.coe_ne_bot (u y.val)) f hf

theorem exists_regularSmooth_extension_threshold (ωb : KahlerBackground n X) :
    ∃ bK : ℝ, 0 ≤ bK ∧ ∀ b : ℝ, 0 ≤ b →
      ∀ (W : Set X) (m : ℕ) (hclosed : IsClosed W) (hkn : m ≤ n)
        (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m), m < n →
      ∀ (R : X → ℝ), IsGlobalNormalPole ωb W R →
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v) →
      regularSmoothExtensionAt ωb hclosed hkn hreg (regularNormalPoleThreshold n m bK b) := by
  obtain ⟨bK,hbK,hF⟩ := exists_regularFiniteGentle_extension_threshold ωb
  refine ⟨bK,hbK,?_⟩
  intro b hb W m hclosed hkn hreg hmn R hR hbR
  exact actualSmooth_extension_of_finiteGentle ωb hclosed hkn hreg _
    (hF b hb W m hclosed hkn hreg hmn R hR hbR)

end SGPT.Trace.BertiniUniversal
