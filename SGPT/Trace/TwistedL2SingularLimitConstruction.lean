import SGPT.Trace.TwistedL2SingularFatou
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-!
# The singular weighted limit along an open exhaustion

Starting with actual sections on an increasing open cover and their actual weighted
estimates, construct the global holomorphic limit and prove its weighted bound.
The original singular multiplier is recovered almost everywhere because the
analytic pole set is null. The punctured-section version first removes the pole
set using the weighted estimates and the L² removable singularity theorem.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- A finite common singular-weight bound on an open exhaustion produces an
actual holomorphic limit section with the same global singular-weight bound. -/
theorem exists_singular_weighted_limit_section
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    (hAn : IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥})
    {a b : X → ℝ} (has : ChartSmooth (n := n) a) (hbs : ChartSmooth (n := n) b)
    (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {V : ℕ → Set X} (hVo : ∀ j, IsOpen (V j)) (hVm : Monotone V)
    (hcover : ∀ x : X, ∃ j, x ∈ V j)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) (V j))
    (hbound : ∀ j, (∫⁻ x in V j \ {x | ψ x = ⊥}, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) *
        multiplierWeight 1 (ψ x) ∂μ) ≤ I := by
  classical
  obtain ⟨D, σ, F, hcovD, hσ, hF⟩ := exists_frame_locally_uniform_subsequence
    hμ L hqpsh htop hcl hAn ha0 hb0 hM hG hVo hVm hcover hI T hT hbound
  have hF' : ∀ y : D,
      DifferentiableOn ℂ (F y)
        (chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val)) ∧
      ∀ z ∈ chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val),
        Tendsto (fun j => chartCoeff L (complexChartAt (n := n) y.val)
          (preferredAtlasFrame L y.val) (T (σ j)) z) atTop (𝓝 (F y z)) :=
    fun y => ⟨(hF y).1, (hF y).2.2⟩
  obtain ⟨S, hS, hcoef, hnorm⟩ :=
    exists_holomorphic_section_of_frame_limits L D hcovD (fun j => T (σ j)) F hF'
  let A : Set X := {x | ψ x = ⊥}
  have hA0 : μ A = 0 := measure_eq_zero_of_isLocallyAnalyticNull hμ hAn
  have hae : ∀ᵐ x ∂μ, x ∉ A := measure_eq_zero_iff_ae_notMem.mp hA0
  let U : ℕ → Set X := fun j => V (σ j) \ A
  have hUo : ∀ j, IsOpen (U j) := fun j => (hVo (σ j)).sdiff hcl
  have hUm : Monotone U := fun i j hij x hx =>
    ⟨hVm (hσ.monotone hij) hx.1, hx.2⟩
  have hcovU : ∀ᵐ x ∂μ, ∃ j, x ∈ U j := by
    filter_upwards [hae] with x hx
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨j, hVm (hσ.id_le j) hj, hx⟩
  let u : ℕ → X → ℝ := fun j x => ‖G x - T (σ j) x‖ ^ 2
  let v : X → ℝ := fun x => ‖G x - S x‖ ^ 2
  let w : X → ℝ := fun x => Real.exp (-(ψ x).toReal) / (a x + b x)
  have hu : ∀ j, ContinuousOn (u j) (U j) := fun j =>
    ((continuousOn_norm_sub_of_holomorphic L hG (hVo (σ j)) (hT (σ j))).mono
      (sdiff_subset : U j ⊆ V (σ j))).pow 2
  have hψm : Measurable (fun x => (ψ x).toReal) := hqpsh.upperSemicontinuous.measurable.ereal_toReal
  have hw : Measurable w :=
    ((Real.continuous_exp.measurable.comp hψm.neg).div
      ((continuous_of_chartSmooth' has).measurable.add (continuous_of_chartSmooth' hbs).measurable))
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun j => u j x) atTop (𝓝 (v x)) :=
    Filter.Eventually.of_forall fun x => (hnorm G x).pow 2
  have hbound' : ∀ j, (∫⁻ x in U j, ENNReal.ofReal (u j x * w x) ∂μ) ≤ I := by
    intro j
    refine (setLIntegral_congr_fun (hUo j).measurableSet fun x hx => ?_).trans_le (hbound (σ j))
    congr 1
    dsimp [u, w]
    ring
  have hfatou := lintegral_le_of_ae_tendsto_on_exhaustion hUo hUm hcovU u v w hu hw hconv hbound'
  refine ⟨S, hS, ?_⟩
  calc
    (∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) *
        multiplierWeight 1 (ψ x) ∂μ) = ∫⁻ x, ENNReal.ofReal (v x * w x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      rw [← ofReal_mul_exp_neg_toReal (‖G x - S x‖ ^ 2 / (a x + b x)) hx (htop x)]
      congr 1
      dsimp [v, w]
      ring
    _ ≤ I := hfatou


/-- Remove the analytic pole set from every actual exhaustion solution before
applying the global normal-family construction. The local square-integrability
needed for removal follows from the given weighted estimate. -/
theorem exists_singular_weighted_limit_section_of_punctured_sections
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    (hAn : IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥})
    {a b : X → ℝ} (has : ChartSmooth (n := n) a) (hbs : ChartSmooth (n := n) b)
    (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {V : ℕ → Set X} (hVo : ∀ j, IsOpen (V j)) (hVm : Monotone V)
    (hcover : ∀ x : X, ∃ j, x ∈ V j)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber
      (T j) (V j \ {x | ψ x = ⊥}))
    (hbound : ∀ j, (∫⁻ x in V j \ {x | ψ x = ⊥}, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) *
        multiplierWeight 1 (ψ x) ∂μ) ≤ I := by
  classical
  have hlocal : ∀ j (K : Set X), IsCompact K → K ⊆ V j →
      (∫⁻ x in K \ {x | ψ x = ⊥}, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) < ⊤ := by
    intro j K hK hKV
    apply locally_sq_integrable_of_weighted_difference hμ L hqpsh htop hcl ha0 hb0 hM hG
      (U := V j \ {x | ψ x = ⊥}) hK (fun x hx => ⟨hKV hx.1, hx.2⟩)
    exact (hbound j).trans_lt hI
  choose T' hT' heq using fun j => l2RemovableSingularityStatement n X μ hμ L
    (V j) {x | ψ x = ⊥} (hVo j) hcl hAn (T j) (hT j) (hlocal j)
  have hbound' : ∀ j, (∫⁻ x in V j \ {x | ψ x = ⊥}, ENNReal.ofReal
      (‖G x - T' j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I := by
    intro j
    refine (setLIntegral_congr_fun ((hVo j).sdiff hcl).measurableSet fun x hx => ?_).trans_le
      (hbound j)
    rw [heq j x hx]
  exact exists_singular_weighted_limit_section hμ L hqpsh htop hcl hAn has hbs ha0 hb0 hM
    hG hVo hVm hcover hI T' hT' hbound'

end SGPT.Trace.TwistedL2
