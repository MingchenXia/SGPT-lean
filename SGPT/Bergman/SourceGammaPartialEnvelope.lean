import SGPT.Bergman.SourceGammaBergmanSingularity
import SGPT.Bergman.SourceSectionLogObstacle
import SGPT.Bergman.SourceNativeSectionKahlerBackground
import SGPT.Bergman.SourcePartialEnvelopes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.MultiplierSectionSingularity

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.BernsteinMarkov
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

/-- Literal source921: the actual original nonzero Gamma section, shifted
by the internally produced smooth C*k^n obstacle constant, is a genuine
candidate of the original partial envelope. ONE manufactured alpha,
ONE C and ONE degree threshold precede ALL literal original sections.
No PSH, singularity-order, point-bound or envelope certificate is supplied. -/
theorem exists_alpha_source_section_le_partialEnvelope
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (hφan : (ofFixedModel n X).HasRationalAnalyticChartType φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℕ → ℝ, StrictMono α ∧ (∀ k, 0 < α k ∧ α k < 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ s : LiteralTwistedMultiplierSections L T k φ, s ≠ 0 →
          weightedL2Norm (twistedPower L T k).Fiber k
            (wholeWeightedSubset (n := n) v).erealWeight
            ((SGPT.Foundations.Analysis.Pending.IntegrationCurrent.kahlerVolume omega).comap
              (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X))
            (literalTwistedMultiplierSectionEquiv L T k φ s).val ≤ 1 →
          ∀ x : X, (((k : ℝ)⁻¹ : ℝ) : EReal) *
              logNormSq ((literalTwistedMultiplierSectionEquiv L T k φ s).val x) +
            ((-((k : ℝ)⁻¹ * Real.log (C * (k : ℝ) ^ n)) : ℝ) : EReal) ≤
            partialEnvelope (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + ε • omega.form))
              (fun y => ((α k : ℝ) : EReal) * φ y) univ
              (fun y : ↥(univ : Set X) => (v y.val : EReal)) x := by
  obtain ⟨α, hmono, hα, hlim, Nα, hNα, horder⟩ :=
    exists_alpha_literalGamma_normalizedLogNormSq_singularityLE omega L T hφ hφan
  have hμ := SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  obtain ⟨C, hC, hobstacle⟩ := exists_source_smooth_weighted_section_obstacle
    L T hL hT v hv _ hμ
  obtain ⟨NP, hNP, hpsh⟩ := exists_sourceNormalizedSection_kahler_background L T hL hT omega hε
  refine ⟨α, hmono, hα, hlim, C, hC, max Nα NP, by omega, fun k hk s hs hunit => ?_⟩
  let t : twistedSections L T k := (literalTwistedMultiplierSectionEquiv L T k φ s).val
  have ht : t ≠ 0 := by
    intro hz
    apply hs
    apply (literalTwistedMultiplierSectionEquiv L T k φ).injective
    rw [map_zero]
    exact Subtype.ext hz
  have hkpos : 0 < k := lt_of_lt_of_le hNα (le_of_max_le_left hk)
  let A : ℝ := -((k : ℝ)⁻¹ * Real.log (C * (k : ℝ) ^ n))
  let u : X → EReal := fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (t x) + (A : EReal)
  have hup : IsThetaPshPotential
      (sourceNativeFirstChernForm L hL + ε • omega.form).val u :=
    (hpsh k (le_of_max_le_right hk) t ht).add_const A
  have hua : (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + ε • omega.form)) u :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr hup
  have hobs : partialObstacle (n := n) univ
      (fun y : ↥(univ : Set X) => (v y.val : EReal)) u :=
    partialObstacle_of_forall (fun x => hobstacle k hkpos t hunit x.val)
  have hshift : SGPT.PSH.SingularityLE u
      (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (t x)) :=
    ⟨A, fun _ _ => le_rfl⟩
  exact le_partialEnvelope hua hobs
    (SGPT.PSH.singularityLE_trans hshift (horder k (le_of_max_le_left hk) s))

end SGPT.Bergman.MultiplierSectionSingularity
