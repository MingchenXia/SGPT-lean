import SGPT.Foundations.Analysis.Pending.SingularModelEnergyChartIntegrals
import SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotIntegrableDefect
import SGPT.Foundations.Analysis.Pending.NonPluripolarGauge

set_option autoImplicit false

/-!
# Actual signed NP fibres identify the actual model-energy pairing

Xia SGPT PDF0171 (4.29)--(4.30)'s representative step. Genuine joint
PSH slots with actual local coordinate expressions recover the actual
global endpoint mixed measure on each fibre, including arbitrary real
time-only corrections. Actual signed NP slicing and the actual finite
base-chart energy sum identify the resulting time-test pairing.
No fibre measure identity or energy-affinity certificate is an input.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergySignedFibreIdentification

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  RelativeEnergy RelativeDarvasDistance RelativePreceqClasses GlobalSlotStokes
  FiniteGeodesicStripCharts BedfordTaylorStripCovariance BedfordTaylorFibreSlicing
  BedfordTaylorTimeSlot MixedDensityRankOneSlot BedfordTaylor
  NonPluripolarFibreSlicing MixedNonPluripolar NonPluripolarTimeSlotTruncationBalance
  NonPluripolarTimeSlotIntegrableDefect SingularModelEnergyChartIntegrals

noncomputable section

variable {n : ℕ}

/-- The actual singular joint endpoint tuple with the genuine final norm-square time slot. -/
def endpointTimeTuple (H Φ : ComplexModel (n + 1) → EReal) (k : Fin (n + 1)) :
    Fin (n + 1) → ComplexModel (n + 1) → EReal :=
  fun i => if i = Fin.last n then fun q => (lastNormSq n q : EReal)
    else if i.val < k.val then H else Φ

/-- Genuine joint PSH potentials produce genuine PSH membership of every actual endpoint/time slot. -/
theorem endpointTimeTuple_plurisubharmonicOn {Ω : Opens (ComplexModel (n + 1))}
    {H Φ : ComplexModel (n + 1) → EReal}
    (hH : PlurisubharmonicOn H Ω) (hΦ : PlurisubharmonicOn Φ Ω) (k : Fin (n + 1)) :
    ∀ i, PlurisubharmonicOn (endpointTimeTuple H Φ k i) Ω := by
  intro i
  unfold endpointTimeTuple
  split_ifs with hi hik
  · exact (isSmoothPsdOn_lastNormSq Ω).isLocallyBoundedPshOn.1
  · exact hH
  · exact hΦ

private theorem fibreOpens_stripLift_eq {A : Opens (ComplexModel n)}
    {S : Set ℂ} (hS : IsOpen S) {τ : ℂ} (hτ : τ ∈ S) :
    fibreOpens (stripLift A S hS) τ = A := by
  ext y
  change fibreMap n τ y ∈ stripLift A S hS ↔ y ∈ A
  rw [mem_stripLift, stripFst_fibreMap, stripModelEquiv_fibreMap]
  exact and_iff_left hτ

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Actual joint fibre coordinates and genuine NP gauge invariance produce the actual base endpoint coordinate measure. -/
theorem fibre_endpointTimeTuple_measure_eq_endpointChartMeasure
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (J : SlotChart (fun _ : Fin n => θ) θ) {S : Set ℂ} (hS : IsOpen S)
    {H Φ : ComplexModel (n + 1) → EReal}
    (hH : PlurisubharmonicOn H (stripLift J.domain S hS))
    (hΦ : PlurisubharmonicOn Φ (stripLift J.domain S hS)) (k : Fin (n + 1))
    {τ : ℂ} (hτ : τ ∈ S) (c : ℝ)
    (hHτ : ∀ y ∈ J.domain, H (fibreMap n τ y) =
      chartFunction u J.chart y + (J.kahler y : EReal) + (c : EReal))
    (hΦτ : ∀ y ∈ J.domain, Φ (fibreMap n τ y) =
      chartFunction φ J.chart y + (J.kahler y : EReal) + (c : EReal)) :
    mixedTruncationLimitMeasure (fibreOpens (stripLift J.domain S hS) τ)
      (fibrePotentials (endpointTimeTuple H Φ k) τ)
      (plurisubharmonicOn_fibrePotentials (endpointTimeTuple_plurisubharmonicOn hH hΦ k) τ) =
      endpointChartMeasure θ φ u hφ hu J k := by
  let v : Fin n → ComplexModel n → EReal := fun i y =>
    chartFunction (endpointMixedPotential k u φ i) J.chart y + (J.kahler y : EReal)
  have hv (i : Fin n) : PlurisubharmonicOn (v i) J.domain :=
    BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
      (endpointMixedPotential_thetaPlurisubharmonic θ k u φ hu hφ i) J.chart J.kahlerLocal
  have heq (i : Fin n) : EqOn (fibrePotentials (endpointTimeTuple H Φ k) τ i)
      (fun y => v i y + (c : EReal)) J.domain := by
    intro y hy
    simp only [fibrePotentials, endpointTimeTuple, Fin.castSucc_ne_last, ↓reduceIte,
      Fin.val_castSucc, v, endpointMixedPotential]
    by_cases hi : i.val < k.val
    · simpa only [hi, ↓reduceIte] using hHτ y hy
    · simpa only [hi, ↓reduceIte] using hΦτ y hy
  have hdom := fibreOpens_stripLift_eq hS hτ (A := J.domain)
  have hf (i : Fin n) : PlurisubharmonicOn
      (fibrePotentials (endpointTimeTuple H Φ k) τ i) J.domain := by
    rw [← hdom]
    exact plurisubharmonicOn_fibrePotentials (endpointTimeTuple_plurisubharmonicOn hH hΦ k) τ i
  have hvc (i : Fin n) : PlurisubharmonicOn (fun y => v i y + (c : EReal)) J.domain := by
    intro y hy
    apply (hf i y hy).congr
    filter_upwards [J.domain.isOpen.mem_nhds hy] with z hz
    exact heq i hz
  have hg := mixedTruncationLimitMeasure_add_pluriharmonic hv
    (fun _ => (show IsSmoothPluriharmonicOn J.domain (fun _ => c) from
      ⟨contDiffOn_const, fun z _ => complexHessian_const c z⟩)) hvc
  have hm := mixedTruncationLimitMeasure_congr hf hvc heq
  rw [hg] at hm
  have hsource : mixedTruncationLimitMeasure (fibreOpens (stripLift J.domain S hS) τ)
      (fibrePotentials (endpointTimeTuple H Φ k) τ)
      (plurisubharmonicOn_fibrePotentials (endpointTimeTuple_plurisubharmonicOn hH hΦ k) τ) =
      mixedTruncationLimitMeasure J.domain (fibrePotentials (endpointTimeTuple H Φ k) τ) hf := by
    have hchange {A B : Opens (ComplexModel n)} (hab : A = B)
        (w : Fin n → ComplexModel n → EReal)
        (ha : ∀ i, PlurisubharmonicOn (w i) A) (hb : ∀ i, PlurisubharmonicOn (w i) B) :
        mixedTruncationLimitMeasure A w ha = mixedTruncationLimitMeasure B w hb := by
      cases hab
      rfl
    exact hchange hdom _ _ hf
  rw [hsource, hm]
  rfl

/-- Actual fibre NP measure identification and canonical finite cancellation recover the actual global endpoint energy integral. -/
theorem integral_fibre_endpointTimeTuple_eq_global
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (J : SlotChart (fun _ : Fin n => θ) θ) {S : Set ℂ} (hS : IsOpen S)
    {H Φ : ComplexModel (n + 1) → EReal}
    (hH : PlurisubharmonicOn H (stripLift J.domain S hS))
    (hΦ : PlurisubharmonicOn Φ (stripLift J.domain S hS)) (k : Fin (n + 1))
    {τ : ℂ} (hτ : τ ∈ S) (c : ℝ)
    (hHτ : ∀ y ∈ J.domain, H (fibreMap n τ y) =
      chartFunction u J.chart y + (J.kahler y : EReal) + (c : EReal))
    (hΦτ : ∀ y ∈ J.domain, Φ (fibreMap n τ y) =
      chartFunction φ J.chart y + (J.kahler y : EReal) + (c : EReal))
    {f : M → ℝ} (hf : tsupport f ⊆ (J.source : Set M)) :
    (∫ y, chartRead J.chart f y *
      canonicalERealDiffToReal (H (fibreMap n τ y)) (Φ (fibreMap n τ y))
      ∂mixedTruncationLimitMeasure (fibreOpens (stripLift J.domain S hS) τ)
        (fibrePotentials (endpointTimeTuple H Φ k) τ)
        (plurisubharmonicOn_fibrePotentials (endpointTimeTuple_plurisubharmonicOn hH hΦ k) τ)) =
      ∫ x, f x * canonicalERealDiffToReal (u x) (φ x)
        ∂endpointMixedMeasure θ φ u hφ hu k := by
  rw [fibre_endpointTimeTuple_measure_eq_endpointChartMeasure hφ hu J hS hH hΦ k hτ c hHτ hΦτ]
  refine (integral_congr_ae ?_).trans (integral_chart_endpoint_eq_global hφ hu J k hf)
  have hae : ∀ᵐ y ∂endpointChartMeasure θ φ u hφ hu J k,
      y ∈ (J.domain : Set (ComplexModel n)) :=
    ae_iff.mpr (mixedTruncationLimitMeasure_compl _)
  filter_upwards [hae] with y hy
  rw [hHτ y hy, hΦτ y hy, canonicalDiff_add_common]

/-- The actual global endpoint mixed integral of a genuine complex-parameter family, extended by zero outside its true parameter domain. -/
def endpointCurveTerm (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (U : ℂ → M → EReal) (S : Set ℂ) (hφ : IsThetaPshPotential θ.val φ)
    (hU : ∀ τ ∈ S, IsThetaPshPotential θ.val (U τ)) (f : M → ℝ)
    (k : Fin (n + 1)) (τ : ℂ) : ℝ := by
  classical
  exact if hτ : τ ∈ S then ∫ x, f x * canonicalERealDiffToReal (U τ x) (φ x)
    ∂endpointMixedMeasure θ φ (U τ) hφ (hU τ hτ) k else 0

/-- Genuine signed NP time-slot slicing and actual fibre recovery identify one chart-slot defect with its actual global endpoint time pairing. -/
theorem integral_timeLift_sub_eq_global_endpoint_pairing
    (hφ : IsThetaPshPotential θ.val φ) (J : SlotChart (fun _ : Fin n => θ) θ)
    {S : Set ℂ} (hS : IsOpen S) (U : ℂ → M → EReal)
    (hU : ∀ τ ∈ S, IsThetaPshPotential θ.val (U τ))
    {H Φ : ComplexModel (n + 1) → EReal}
    (hH : PlurisubharmonicOn H (stripLift J.domain S hS))
    (hΦ : PlurisubharmonicOn Φ (stripLift J.domain S hS))
    (hHm : Measurable H) (hΦm : Measurable Φ) (c : ℂ → ℝ)
    (hHcoord : ∀ τ ∈ S, ∀ y ∈ J.domain, H (fibreMap n τ y) =
      chartFunction (U τ) J.chart y + (J.kahler y : EReal) + (c τ : EReal))
    (hΦcoord : ∀ τ ∈ S, ∀ y ∈ J.domain, Φ (fibreMap n τ y) =
      chartFunction φ J.chart y + (J.kahler y : EReal) + (c τ : EReal))
    (k : Fin (n + 1)) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hfc : HasCompactSupport f) (hfJ : tsupport f ⊆ (J.source : Set M))
    (hf0 : ∀ x, 0 ≤ f x) {ζ ψ : ℂ → ℝ}
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) (hζS : tsupport ζ ⊆ S)
    (hζ0 : ∀ τ, 0 ≤ ζ τ) (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn (stripLift J.domain S hS) p)
    (hψp : IsSmoothPsdOn (stripLift J.domain S hS) fun q => timeLift n ψ q + p q)
    (ha : Integrable (fun q => stripCutoff (chartRead J.chart f) ζ q *
        canonicalERealDiffToReal (H q) (Φ q))
      (mixedTruncationLimitMeasure (stripLift J.domain S hS)
        (Function.update (endpointTimeTuple H Φ k) (Fin.last n)
          fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) hψp)))
    (hb : Integrable (fun q => stripCutoff (chartRead J.chart f) ζ q *
        canonicalERealDiffToReal (H q) (Φ q))
      (mixedTruncationLimitMeasure (stripLift J.domain S hS)
        (Function.update (endpointTimeTuple H Φ k) (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) hp))) :
    Integrable (fun τ : ℂ => timeLaplacian ψ τ * ζ τ * endpointCurveTerm θ φ U S hφ hU f k τ) ∧
    (∫ q, stripCutoff (chartRead J.chart f) ζ q * canonicalERealDiffToReal (H q) (Φ q)
      ∂mixedTruncationLimitMeasure (stripLift J.domain S hS)
        (Function.update (endpointTimeTuple H Φ k) (Fin.last n)
          fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
        (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) hψp)) -
    (∫ q, stripCutoff (chartRead J.chart f) ζ q * canonicalERealDiffToReal (H q) (Φ q)
      ∂mixedTruncationLimitMeasure (stripLift J.domain S hS)
        (Function.update (endpointTimeTuple H Φ k) (Fin.last n) fun q => (p q : EReal))
        (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) hp)) =
    (∫ τ : ℂ, timeLaplacian ψ τ * ζ τ * endpointCurveTerm θ φ U S hφ hU f k τ) / Real.pi := by
  classical
  have hfs : tsupport f ⊆ J.chart.val.source := hfJ.trans inter_subset_left
  have hread := continuous_chartRead hf hfc hfs
  have hreadc := hasCompactSupport_chartRead hfc hfs
  have hreadJ : tsupport (chartRead J.chart f) ⊆ J.domain := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_chartRead_subset hfc hfs hy
    exact (hfJ hx).2
  have hread0 (y : ComplexModel n) : 0 ≤ chartRead J.chart f y := by
    by_cases hy : y ∈ J.chart.val.target
    · rw [chartRead_of_mem hy]
      exact hf0 _
    · rw [chartRead_of_notMem hy]
  have hlast : endpointTimeTuple H Φ k (Fin.last n) = fun q => (lastNormSq n q : EReal) := by
    simp only [endpointTimeTuple, ↓reduceIte]
  have hs := integral_timeLift_sub_eq_timeLaplacian_fibre
    (endpointTimeTuple_plurisubharmonicOn hH hΦ k) hlast hψ hp hψp
    (continuous_stripCutoff hread hζ) (hasCompactSupport_stripCutoff hreadc hζc)
    (tsupport_stripCutoff_subset_stripLift hreadc hζc hS hreadJ hζS)
    (fun q => mul_nonneg (hread0 _) (hζ0 _))
    (RelativeEnergyIntegrability.measurable_canonicalERealDiffToReal.comp (hHm.prodMk hΦm)) ha hb
  have hcoord (τ : ℂ) (y : ComplexModel n) : (fibreMap n τ y) (Fin.last n) = τ :=
    stripModelEquiv_symm_apply_last y τ
  have hfib (τ : ℂ) :
      (∫ y, stripCutoff (chartRead J.chart f) ζ (fibreMap n τ y) *
        canonicalERealDiffToReal (H (fibreMap n τ y)) (Φ (fibreMap n τ y))
        ∂mixedTruncationLimitMeasure (fibreOpens (stripLift J.domain S hS) τ)
          (fibrePotentials (endpointTimeTuple H Φ k) τ)
          (plurisubharmonicOn_fibrePotentials (endpointTimeTuple_plurisubharmonicOn hH hΦ k) τ)) =
        ζ τ * endpointCurveTerm θ φ U S hφ hU f k τ := by
    by_cases hτ : τ ∈ S
    · rw [endpointCurveTerm, dif_pos hτ]
      have heq (y : ComplexModel n) : stripCutoff (chartRead J.chart f) ζ (fibreMap n τ y) *
          canonicalERealDiffToReal (H (fibreMap n τ y)) (Φ (fibreMap n τ y)) =
          ζ τ * (chartRead J.chart f y *
            canonicalERealDiffToReal (H (fibreMap n τ y)) (Φ (fibreMap n τ y))) := by
        simp only [stripCutoff, stripFst_fibreMap, hcoord]
        ring
      simp_rw [heq, integral_const_mul]
      rw [integral_fibre_endpointTimeTuple_eq_global hφ (hU τ hτ) J hS hH hΦ k hτ
        (c τ) (hHcoord τ hτ) (hΦcoord τ hτ) hfJ]
    · have hζzero : ζ τ = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hτ (hζS ht))
      simp only [stripCutoff, hcoord, hζzero, mul_zero, zero_mul, integral_zero,
        endpointCurveTerm, dif_neg hτ]
  simpa only [Function.comp_apply, hfib, mul_assoc] using hs

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergySignedFibreIdentification
