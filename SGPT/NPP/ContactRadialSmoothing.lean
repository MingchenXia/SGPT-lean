import SGPT.NPP.DNTBigReduction
import SGPT.Analysis.CZContact
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

/-!
# Actual radial smoothing of the big-class envelope at contact points

Complete mathematics was written first in
`blueprint/src/dnt-big-contact-smoothing.tex`. The envelope is the actual
rooftop envelope of the actual continuous weak-Hessian obstacle. Its chart
representative is only locally integrable; no continuity or C² regularity of
that envelope is assumed. The actual explicit radial probability kernel gives
a quadratic upper mean bound at every contact point. Away from contact, the
estimate retains the explicit obstacle gap.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTC11
open SGPT.Analysis.CZ

/-! ### The obstacle curvature is its actual distributional density -/

theorem locallyBoundedComplexHessian_of_boundedDensity {n : ℕ}
    {q : ComplexModel n → ℝ} {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {Ω : Set (ComplexModel n)} (hq : IsBoundedHessianDensityOn q h Ω) :
    HasLocallyBoundedComplexHessianOn q Ω := by
  intro K hK hKΩ
  obtain ⟨C, _, hC⟩ := hq.exists_ae_abs_hermQuad_le hK hKΩ
  have hC' : ∀ᵐ z ∂volume, z ∈ K → ∀ v, |hermQuad (h z) v| ≤ C * ‖v‖ ^ 2 :=
    (ae_restrict_iff' hK.measurableSet).mp hC
  refine ⟨C, fun φ hφ hφK v => ?_⟩
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport _) hφK
  rw [hq.levi φ hφ hφc (hφK.trans hKΩ) v]
  have hbound : ∀ᵐ z ∂volume,
      ‖hermQuad (h z) v * φ z‖ ≤ C * ‖v‖ ^ 2 * |φ z| := by
    filter_upwards [hC'] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hzK : z ∈ K
    · exact mul_le_mul_of_nonneg_right (hz hzK v) (abs_nonneg _)
    · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzK (hφK h)
      simp only [hφz, abs_zero, mul_zero, le_refl]
  have hφi : Integrable (fun z => |φ z|) (volume : Measure (ComplexModel n)) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  have h := norm_integral_le_of_norm_le (hφi.const_mul (C * ‖v‖ ^ 2)) hbound
  rwa [Real.norm_eq_abs, integral_const_mul] at h

theorem locallyBoundedLeviTrace_of_boundedDensity {n : ℕ}
    {q : ComplexModel n → ℝ} {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {Ω : Set (ComplexModel n)} (hq : IsBoundedHessianDensityOn q h Ω) :
    HasLocallyBoundedLeviTraceOn q Ω :=
  hasLocallyBoundedLeviTraceOn_of_complexHessian hq.isOpen hq.continuousOn
    (locallyBoundedComplexHessian_of_boundedDensity hq)

section Envelope

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- A genuine chart-kernel estimate for the actual big-class envelope. The
only nonquadratic term is its actual obstacle gap. Both averages are honest
integrals, proved from chart L¹, rather than an assumed regularity output. -/
theorem rooftopEnvelope_chart_kernelMean_le_obstacle_gap (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {g : Y → ℝ} (hg : HasBoundedComplexHessian (n := m + 1) g)
    (e : ComplexChart (m + 1) Y) {c : ComplexModel (m + 1)} {a : ℝ} (_ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ ball c (2 * a), ∀ r : ℝ, ∀ hr : 0 < r, r < a →
      Integrable (fun z => envelopeReal θ g (e.val.symm z) *
        explicitRadialKernel r hr 0 (z - y)) ∧
      (∫ z, envelopeReal θ g (e.val.symm z) * explicitRadialKernel r hr 0 (z - y)) -
        envelopeReal θ g (e.val.symm y) ≤
      g (e.val.symm y) - envelopeReal θ g (e.val.symm y) + C * r ^ 2 := by
  obtain ⟨h, hh⟩ := hg.2 e
  have htrace := locallyBoundedLeviTrace_of_boundedDensity hh
  obtain ⟨M, hM0, _, hM⟩ := htrace.exists_ge_le
    (isCompact_closedBall c (4 * a)) hball (V := ball c (4 * a)) ball_subset_closedBall
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous w θ hg.1 hφ
  have hPg := rooftopEnvelope_le_of_isThetaPshPotential hg.1 hP
  have hfinite : ∀ᵐ z ∂volume.restrict e.val.target,
      chartFunction (rooftopEnvelope θ.val (fun x => (g x : EReal))) e z ≠ ⊤ ∧
      chartFunction (rooftopEnvelope θ.val (fun x => (g x : EReal))) e z ≠ ⊥ := by
    have h := GlobalCurrentPotentials.quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
      (Nat.succ_pos m) _ hP.quasiPshPotential e
    rw [addHaar_canonicalBasis] at h
    exact h
  have hfinite' := (ae_restrict_iff' e.val.open_target.measurableSet).mp hfinite
  refine ⟨M / (m + 1 : ℕ), div_nonneg hM0 (by positivity), ?_⟩
  intro y hy r hr hra
  have hsub : closedBall y r ⊆ ball c (4 * a) := by
    intro z hz
    have hzy : dist z y ≤ r := hz
    have hyc : dist y c < 2 * a := hy
    rw [mem_ball]
    calc
      dist z c ≤ dist z y + dist y c := dist_triangle z y c
      _ ≤ r + dist y c := add_le_add hzy le_rfl
      _ < 4 * a := by linarith [_ha]
  have hye : closedBall y r ⊆ e.val.target :=
    hsub.trans (ball_subset_closedBall.trans hball)
  let κ : ComplexModel (m + 1) → ℝ := fun z => explicitRadialKernel r hr 0 (z - y)
  have hκc : Continuous κ :=
    (explicitRadialKernel_contDiff r hr 0).continuous.comp (continuous_id.sub continuous_const)
  have hκs : HasCompactSupport κ :=
    (explicitRadialKernel_hasCompactSupport r hr 0).comp_homeomorph (Homeomorph.subRight y)
  have hκball : tsupport κ ⊆ closedBall y r := by
    simpa only [κ, shrinkingBump, Nat.cast_zero, zero_add, div_one] using
      tsupport_explicitRadialKernel_translate_subset r hr 0 y
  have hκe : tsupport κ ⊆ e.val.target := hκball.trans hye
  have huOn : IntegrableOn (fun z => envelopeReal θ g (e.val.symm z)) (tsupport κ) := by
    simpa only [chartFunction, envelopeReal] using
      hP.quasiPshPotential.integrableOn_chart_toReal e hκs hκe
  have huI : Integrable (fun z => envelopeReal θ g (e.val.symm z) * κ z) :=
    (huOn.mul_continuousOn hκc.continuousOn hκs).integrable_of_forall_notMem_eq_zero
      fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hgI : Integrable (fun z => g (e.val.symm z) * κ z) :=
    integrable_mul_of_continuousOn e.val.open_target hh.continuousOn hκc hκs hκe
  have hmean : (∫ z, envelopeReal θ g (e.val.symm z) * κ z) ≤
      ∫ z, g (e.val.symm z) * κ z := by
    refine integral_mono_ae huI hgI ?_
    filter_upwards [hfinite'] with z hz
    by_cases hze : z ∈ e.val.target
    · have hle : envelopeReal θ g (e.val.symm z) ≤ g (e.val.symm z) := by
        have h := EReal.toReal_le_toReal (hPg (e.val.symm z)) (hz hze).2
          (EReal.coe_ne_top _)
        simpa only [chartFunction, envelopeReal, EReal.toReal_coe] using h
      exact mul_le_mul_of_nonneg_right hle (explicitRadialKernel_nonneg r hr 0 _)
    · have hzκ : z ∉ tsupport κ := fun h => hze (hκe h)
      rw [image_eq_zero_of_notMem_tsupport hzκ, mul_zero, mul_zero]
  have hq := kernelAverage_sub_le (Nat.succ_pos m) isOpen_ball
    (hh.continuousOn.mono (ball_subset_closedBall.trans hball)) hM0 hM hr hsub
  refine ⟨huI, ?_⟩
  dsimp only [κ] at hmean
  linarith

/-- At the actual contact points, the obstacle gap vanishes and the real
radial smoothing of the actual envelope has a uniform quadratic upper bound. -/
theorem rooftopEnvelope_chart_kernelMean_le_of_contact (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {g : Y → ℝ} (hg : HasBoundedComplexHessian (n := m + 1) g)
    (e : ComplexChart (m + 1) Y) {c : ComplexModel (m + 1)} {a : ℝ} (ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ ball c (2 * a), ∀ r : ℝ, ∀ hr : 0 < r, r < a →
      rooftopEnvelope θ.val (fun x => (g x : EReal)) (e.val.symm y) =
        (g (e.val.symm y) : EReal) →
      Integrable (fun z => envelopeReal θ g (e.val.symm z) *
        explicitRadialKernel r hr 0 (z - y)) ∧
      (∫ z, envelopeReal θ g (e.val.symm z) * explicitRadialKernel r hr 0 (z - y)) -
        envelopeReal θ g (e.val.symm y) ≤ C * r ^ 2 := by
  obtain ⟨C, hC, hmean⟩ :=
    rooftopEnvelope_chart_kernelMean_le_obstacle_gap w θ hbig hg e ha hball
  refine ⟨C, hC, fun y hy r hr hra hcontact => ?_⟩
  obtain ⟨hi, hmean⟩ := hmean y hy r hr hra
  have hreal : envelopeReal θ g (e.val.symm y) = g (e.val.symm y) := by
    simp only [envelopeReal, hcontact, EReal.toReal_coe]
  exact ⟨hi, by simpa only [hreal, sub_self, zero_add] using hmean⟩

/-- Literal original source obstacle envelope, with the same actual native
chart kernel and actual contact equality. -/
theorem sourceObstacleEnvelope_chart_kernelMean_le_of_contact
    (w : KahlerBackground (m + 1) Y)
    (θ : SGPT.PSH.VariableComplexAtlas.AtlasClosedRealOneOneForm
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative
      (SGPT.PSH.VariableComplexAtlas.atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : HasBoundedComplexHessian (n := m + 1) g)
    (e : ComplexChart (m + 1) Y) {c : ComplexModel (m + 1)} {a : ℝ} (ha : 0 < a)
    (hball : closedBall c (4 * a) ⊆ e.val.target) :
    let P := SGPT.PSH.VariableComplexAtlas.sourceRelativeEnvelope θ (fun _ => ⊤)
      (fun x => (g x : EReal))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ ball c (2 * a), ∀ r : ℝ, ∀ hr : 0 < r, r < a →
      P (e.val.symm y) = (g (e.val.symm y) : EReal) →
      Integrable (fun z => (P (e.val.symm z)).toReal * explicitRadialKernel r hr 0 (z - y)) ∧
      (∫ z, (P (e.val.symm z)).toReal * explicitRadialKernel r hr 0 (z - y)) -
        (P (e.val.symm y)).toReal ≤ C * r ^ 2 := by
  dsimp only
  simpa only [SGPT.PSH.VariableComplexAtlas.sourceObstacleEnvelope_eq_native, envelopeReal] using
    rooftopEnvelope_chart_kernelMean_le_of_contact w
      (SGPT.PSH.VariableComplexAtlas.atlasClosedFormToNative θ) hbig hg e ha hball

end Envelope

end SGPT.NPP.DNTBig
