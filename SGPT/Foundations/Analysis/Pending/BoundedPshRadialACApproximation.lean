import SGPT.Foundations.Analysis.Pending.ExplicitRadialScalarDdcCalibration
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

set_option autoImplicit false

/-! The literal explicit radial bounded-PSH sequence is internally produced
with pointwise decreasing convergence AND recovery of the SAME original
current's entire AC form on ONE Lebesgue-full set. Full mathematical
statement and ENTIRE proof precede this source. There is no incoming
approximation, current positivity, coefficient limit or mass certificate. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators

namespace SGPT.Foundations.Analysis.Pending.BoundedPshRadialACApproximation
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentDensityMatrix LocalCurrentDeterminant LocalBedfordTaylorProducts
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing HolomorphicPullback
  ExplicitRadialCurrentACApproximation ExplicitRadialScalarDdcCalibration
  TopDegreeDensity

variable {m : ℕ} {U A : Opens (ComplexModel (m+1))}

/-- Natural bounded PSH data internally produce the literal fixed explicit
radial sequence, its full original current positivity, decreasing pointwise
limit, and simultaneous AC form/matrix/exterior-top-density recovery. -/
theorem exists_decreasing_radial_ac_approximation
    {p : ComplexModel (m+1) → ℝ} (hp : IsLocallyBoundedPshOn U p)
    (hA : RelativelyCompactIn A U) :
    let D := regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)
    let T := ddc (scalarTopCurrent D)
    ∃ (hT : IsPositive T) (R : ℝ) (hR : 0 < R) (K : Set (ComplexModel (m+1))),
      IsCompact K ∧ K ⊆ U ∧
      let f : ℕ → ComplexModel (m+1) → ℝ :=
        fun j => translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)
      IsDecreasingApproximation A p f ∧
      ∀ᵐ z ∂volume, z ∈ A →
        Tendsto (fun j => smoothDDC (f j) z) atTop (𝓝 (acForm hT z)) ∧
        Tendsto (fun j => normalizedHermitianMatrix (smoothDDC (f j) z)) atTop
          (𝓝 (acMatrix hT z)) ∧
        Tendsto (fun j => actualTopPowerDensity (smoothDDC (f j) z)) atTop
          (𝓝 (actualTopPowerDensity (acForm hT z))) := by
  classical
  let hpL := locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
  let D := regularDistribution volume p hpL
  let T := ddc (scalarTopCurrent D)
  have hpLevi : HasNonnegativeDistributionalLevi D :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1
  have hT : IsPositive T := isPositive_ddc_scalarTopCurrent hpLevi
  obtain ⟨R,hR,N,K,hN,hclAN,hNK,hK,hKU,hball⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 U.isOpen hA.2
  have hAN : (A : Set (ComplexModel (m+1))) ⊆ N := subset_closure.trans hclAN
  have hAU : (A : Set (ComplexModel (m+1))) ⊆ U := hAN.trans (hNK.trans hKU)
  obtain ⟨S,hSkernel⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
    hp hR hN (hNK.trans hKU) hK hKU hball
  have hkernel (j : ℕ) : S.kernel j = explicitRadialKernel R hR j := funext (hSkernel j)
  let f : ℕ → ComplexModel (m+1) → ℝ :=
    fun j => translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hK hKU).locallyIntegrable
  have hfSmooth (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f j) :=
    contDiff_translationPairing hg (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff R hR j)
  have hfPsh (j : ℕ) : PlurisubharmonicOn (fun z => (f j z : EReal)) A := by
    have hd := discPshOn_translationPairing_indicator hpL hpLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
      (S.kernel_nonneg j) hK hKU (S.translated_tsupport j)
    have hpn := hd.plurisubharmonicOn hN
    simp only [hkernel] at hpn
    exact hpn.mono hAN
  have hf (j : ℕ) : IsSmoothPshOn A (f j) :=
    isSmoothPshOn_of_psh (hfSmooth j).contDiffOn (hfPsh j)
  have hanti : ∀ z ∈ A, Antitone (fun j => f j z) := by
    intro z hz
    simpa only [hkernel] using S.antitone_pairing z (hAN hz)
  have hae : ∀ᵐ z ∂volume.restrict (A : Set (ComplexModel (m+1))),
      Tendsto (fun j => f j z) atTop (𝓝 (p z)) := by
    have hh := S.ae_tendsto_pairing
    change ∀ᵐ z ∂volume.restrict N,
      Tendsto (fun j => translationPairing volume (K.indicator p) (S.kernel j) z)
        atTop (𝓝 (p z)) at hh
    simp only [hkernel] at hh
    exact ae_mono (Measure.restrict_mono hAN le_rfl) hh
  have hpoint : ∀ z ∈ A, Tendsto (fun j => f j z) atTop (𝓝 (p z)) :=
    tendsto_everywhere_of_ae_of_antitone_psh (hp.1.mono hAU) hfPsh hanti hae
  have hclosed (j : ℕ) (z : ComplexModel (m+1)) (hz : z ∈ A) :
      closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR j).rOut ⊆ U :=
    ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j)).trans
      (hball z (hAN hz))).trans hKU
  have heq (j : ℕ) : Set.EqOn (radialMollifiedScalar D R hR j) (f j) A := by
    intro z hz
    unfold radialMollifiedScalar
    rw [dif_pos (hclosed j z hz),regularDistribution_apply]
    change (∫ y, explicitRadialKernel R hR j (z-y)*p y ∂volume) =
      ∫ y, K.indicator p y * explicitRadialKernel R hR j (y-z) ∂volume
    apply integral_congr_ae
    filter_upwards with y
    have heven : explicitRadialKernel R hR j (z-y) =
        explicitRadialKernel R hR j (y-z) := by
      rw [← neg_sub y z,explicitRadialKernel_neg]
    rw [heven]
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact mul_comm _ _
    · have hzero : explicitRadialKernel R hR j (y-z) = 0 := by
        by_contra hne
        have hsup : y ∈ tsupport (fun q => explicitRadialKernel R hR j (q-z)) :=
          subset_tsupport _ hne
        exact hy ((hball z (hAN hz))
          ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j))
            (tsupport_explicitRadialKernel_translate_subset R hR j z hsup)))
      rw [hzero,zero_mul,mul_zero]
  have heventual (z : ComplexModel (m+1)) (hz : z ∈ A) :
      (fun j => smoothDDC (f j) z) =ᶠ[atTop]
        (fun j => radialMollifiedForm T R hR j z) := by
    obtain ⟨V,hVU,hzV,Nz,hNz⟩ :=
      exists_buffered_radial_scalar_ddc_calibration (hAU hz) R hR
    filter_upwards [eventually_ge_atTop Nz] with j hj
    have hc := (hNz D j hj).2 z hzV
    rw [hc]
    exact (FirstPass.smoothDDC_congr ((heq j).eventuallyEq_of_mem
      (A.isOpen.mem_nhds hz))).symm
  refine ⟨hT,R,hR,K,hK,hKU,⟨hf,hanti,hpoint⟩,?_⟩
  have hfull := (positive_and_ae_tendsto_radial_form_matrix_density hT R hR).2
  filter_upwards [hfull] with z hz hzA
  have h := hz (hAU hzA)
  have he := heventual z hzA
  exact ⟨h.1.congr' he.symm,h.2.1.congr' (he.mono fun j hj => congrArg normalizedHermitianMatrix hj.symm),
    h.2.2.congr' (he.mono fun j hj => congrArg actualTopPowerDensity hj.symm)⟩

end SGPT.Foundations.Analysis.Pending.BoundedPshRadialACApproximation
