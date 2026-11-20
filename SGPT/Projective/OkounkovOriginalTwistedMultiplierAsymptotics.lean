import SGPT.Projective.OkounkovOriginalTwistedMultiplierCount
import SGPT.Projective.OkounkovOriginalBookPartial

/-! SAME actual original multiplier count limits, arbitrary original valuations and twists.
Blueprint: okounkov-original-twisted-multiplier-asymptotics.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalMultiplierAsymptotics
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.ValGen SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance multiplierAsymptoticTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance multiplierAsymptoticCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance multiplierAsymptoticManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
  (hbig : SGPT.LineBundle.IsBig f L (m+1))
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v) (c : X)
include hbig hv

/-- Actual arbitrary-valuation twisted multiplier VALUE counts converge to SAME original I-volume/n!. -/
theorem tendsto_normalized_twistedMultiplierValues_card {T : X.Modules} (aT : LineBundleAtlas T)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (k:ℝ)⁻¹^(m+1) *
      (Nat.card (AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ):ℝ)) atTop
      (𝓝 ((iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
        ((m+1).factorial:ℝ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  have hfinite := OriginalBook.original_iVolume_ne_top_allDimensions f (m+1) E a H hφ
  have hdim := SGPT.GAGA.OkoClose.dxMain1TwistedHolds a H Y hY aT hφ
  have hreal := (ENNReal.tendsto_toReal hfinite).comp hdim
  have hdiv := hreal.div_const ((m+1).factorial:ℝ)
  apply hdiv.congr
  intro k
  change ((((m+1).factorial:ℝ≥0∞) *
      (SGPT.IGood.DXMain.twistedMultiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic T L k:ℝ≥0∞)) /
      (k:ℝ≥0∞)^(m+1)).toReal / ((m+1).factorial:ℝ) = _
  rw [(OriginalTwistedMultiplierCount.twistedMultiplierValues_finite_card f E a hbig v hv c k (r k)
    hφ.1.quasiPlurisubharmonic).2]
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_natCast]
  have hf : ((m+1).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
  calc
    _ = ((m+1).factorial:ℝ) *
        ((SGPT.IGood.DXMain.twistedMultiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic T L k:ℝ)/(k:ℝ)^(m+1)) /
        ((m+1).factorial:ℝ) := by ring
    _ = _ := by rw [mul_div_cancel_left₀ _ hf,div_eq_mul_inv,inv_pow,mul_comm]

/-- Actual original multiplier slices have SAME original I-volume/n! count limit; no source cone/flag supplied. -/
theorem tendsto_normalized_original_multiplier_slice_card
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (k:ℝ)⁻¹^(m+1) *
      (Nat.card (slice (AlgebraicValuation.multiplierSectionSet f (m+1) E v c a φ) (k:ℤ)):ℝ)) atTop
      (𝓝 ((iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
        ((m+1).factorial:ℝ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨C,hS,hG⟩ := OriginalBook.exists_original_admissibleCone_allDimensions f a (m+1) E hbig v hv c
  have hlim := ValGen.tendsto_normalized_multiplierH0 f E Y hY a H hφ
  rw [AlgPOB.volume_real_generalPartialBody f E Y hY a H hφ] at hlim
  apply hlim.congr
  intro k
  rw [ValGen.card_slice_multiplierSectionSet f E Y hY a c v hS hG hφ.1.quasiPlurisubharmonic k]

end SGPT.Okounkov.OriginalMultiplierAsymptotics
