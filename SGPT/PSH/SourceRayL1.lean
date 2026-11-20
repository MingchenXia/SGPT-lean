import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open ChartwiseGlobalL1 IntegrationCurrent KahlerVolumeSmoothPositive
open scoped Topology ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [IsComplexManifold n M] in
/-- Eventual measurability suffices for the original global/chartwise L1 bridge.
No condition is added on curve values outside the source time interval. -/
theorem manifoldL1LocallyTendsto_iff_global_of_eventually_measurable
    {I : Type*} {l : Filter I} {u : I → M → EReal} {v : M → EReal}
    {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hu : ∀ᶠ i in l, Measurable (u i)) (hv : Measurable v) :
    ManifoldL1LocallyTendsto (n := n) u l v ↔
      Tendsto (fun i ↦ globalL1EDistance μ (u i) v) l (𝓝 0) := by
  classical
  let w : I → M → EReal := fun i ↦ if Measurable (u i) then u i else v
  have hw (i : I) : Measurable (w i) := by
    dsimp only [w]
    split_ifs with hi
    · exact hi
    · exact hv
  have heq : u =ᶠ[l] w := hu.mono fun i hi ↦ by simp only [w, if_pos hi]
  have hdist : (fun i ↦ globalL1EDistance μ (u i) v) =ᶠ[l]
      (fun i ↦ globalL1EDistance μ (w i) v) :=
    heq.mono fun i hi ↦ congrArg (fun f ↦ globalL1EDistance μ f v) hi
  have hbridge := manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance (l := l) hμ hw hv
  constructor
  · intro h
    exact (hbridge.mp (h.congr' heq)).congr' hdist.symm
  · intro h
    exact (hbridge.mpr (h.congr' hdist)).congr' heq.symm

/-- The original distance integrates the true canonical absolute difference,
retaining every one-sided pole and choosing zero only at a common negative pole. -/
def sourceGlobalL1Distance (omega : KahlerBackground n M) (u v : M → EReal) : ℝ≥0∞ :=
  globalL1EDistance (kahlerVolume omega) u v

/-- Actual chart AE finiteness is carried by the genuine Kähler density and
finite original chart cover to the same global volume. -/
theorem sourceThetaPSH_ae_finite_kahlerVolume
    (omega : KahlerBackground n M) {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    ∀ᵐ x ∂kahlerVolume omega, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  have hnative := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hm : Measurable u := hnative.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have ht : MeasurableSet {x : M | u x = ⊤} := hm (measurableSet_singleton _)
  have hb : MeasurableSet {x : M | u x = ⊥} := hm (measurableSet_singleton _)
  apply ChartHaarKahlerVolumeAE.ae_kahlerVolume_of_forall_chart_ae omega (ht.compl.inter hb.compl)
  intro e
  exact hnative.quasiPshPotential.ae_finite_chart e

/-- Only after genuine original AE finiteness and integrability have been
proved is the global extended distance read as an ordinary real L1 integral. -/
theorem sourceGlobalL1Distance_eq_real_integral
    (omega : KahlerBackground n M)
    {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceGlobalL1Distance omega u v =
      ENNReal.ofReal (∫ x, |(u x).toReal - (v x).toReal| ∂kahlerVolume omega) := by
  have hU := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hV := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  have hiU := GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh
    (kahlerVolume omega) (isSmoothPositiveVolume_kahlerVolume omega) _ _ hU
  have hiV := GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh
    (kahlerVolume omega) (isSmoothPositiveVolume_kahlerVolume omega) _ _ hV
  calc
    sourceGlobalL1Distance omega u v =
        ∫⁻ x, ENNReal.ofReal |(u x).toReal - (v x).toReal| ∂kahlerVolume omega := by
      apply lintegral_congr_ae
      filter_upwards [sourceThetaPSH_ae_finite_kahlerVolume omega hu,
        sourceThetaPSH_ae_finite_kahlerVolume omega hv] with x hxU hxV
      rw [← EReal.coe_toReal hxU.1 hxU.2, ← EReal.coe_toReal hxV.1 hxV.2]
      exact canonicalERealAbsDiff_coe_coe _ _
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (hiU.sub hiV).abs
      (Eventually.of_forall fun x ↦ abs_nonneg _)).symm

/-- Both original endpoint filters eventually stay in the original open interval. -/
theorem sourceRay_endpoint_filters :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1) ∧
      (∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1) := by
  constructor
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with t ht0 ht1
    exact ⟨ht0, ht1⟩
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with t ht1 ht0
    exact ⟨ht0, ht1⟩

/-- Full original L1 dictionary for any filter eventually in the source interval;
the source curve is genuinely theta-PSH only where the source requires it. -/
theorem sourceRayL1_iff_global
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    {v : M → EReal} {l : Filter ℝ}
    (hcurve : ∀ t ∈ Ioo (0 : ℝ) 1, (ofFixedModel n M).IsThetaPSH θ (curve t))
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hl : ∀ᶠ t in l, t ∈ Ioo (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) curve l v ↔
      Tendsto (fun t ↦ sourceGlobalL1Distance omega (curve t) v) l (𝓝 0) := by
  apply manifoldL1LocallyTendsto_iff_global_of_eventually_measurable
    (isSmoothPositiveVolume_kahlerVolume omega)
  · exact hl.mono fun t ht ↦ ((isThetaPSH_iff_nativeThetaPotential θ (curve t)).mp
      (hcurve t ht)).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  · exact ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv).1.quasiPlurisubharmonic.upperSemicontinuous.measurable

end SGPT.PSH.VariableComplexAtlas
