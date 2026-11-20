import SGPT.Okounkov.TranscendentalVolIdCurve
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.FirstPass.AnalyticPoleSet
import SGPT.Foundations.Analysis.Pending.GlobalTubeFunction
import SGPT.Okounkov.TranscendentalL2Corollaries

/-!
# The degree of a point on a curve, `A_1`, and the volume identity

Package VOL (blueprint `claude-tok-volid`, nodes `tok-volid:ddc-laplacian`,
`tok-volid:lelong-local`, `tok-volid:point-degree`; blueprint `claude-okounkov-transcendental`,
nodes `tok:ext-curve`, `tok:A1`, `tok:volume-identity`).

* `integral_laplacian_cutoff_log`, `integral_laplacian_cutoff_logNormSq` (in `ℂ`): if
  `G(w) a(w) = w - w₀` near `w₀` with `a` analytic and nonvanishing, `χ` a cutoff equal to `1`
  near `w₀` and `η` a cutoff equal to `1` near the support of `χ`, then
  `∫ Δ((1 - χ) log ‖G‖) η = 2π`; this is TN's one-variable Lelong--Poincaré formula
  (`LelongPoincareOneVariable`).
* `actualTopPowerDensity_smoothDDC_comp`: on `ℂ¹`, the top density of `dd^c (Φ ∘ ι)` is
  `ΔΦ / (4π)`.
* `pointDegreeStatement` (**`tok-volid:point-degree`**): for a unit metric `E` of the point
  `Y₁ = {q}` of a compact Kähler curve, `∫_X Θ_E = 1`.
* `exists_kahler_iff_curveDegree_pos` (**`tok:ext-curve`**): a class on a curve contains a
  Kähler form iff its degree is positive.
* `volumeIdentity_dimOne` (**`tok:A1`**, unconditional) and the volume identity in every
  dimension, `volumeIdentity_of_wnIntegrated_of_pushforward` (**`tok:volume-identity`**),
  conditional only on `WNIntegratedStatement` in dimensions `≥ 2` and RELGEN's
  `PushforwardAnalyticStatement` (variants with `ModificationL2GenerationStatement` and with the
  package statement `WNStatement`).
* `volumeIdentityStatement_of_wn`, `volumeIdentityStatement_of_wnIntegrated`: the same with RELGEN3's
  proved `TranscendentalL2.pushforwardAnalyticStatement` plugged in, so conditional **only** on WN
  in dimensions `≥ 2`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped Topology ContDiff Laplacian
open SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section Local

/-- The Laplacian of a function vanishes on an open set where the function is constant. -/
theorem laplacian_eq_zero_of_eventuallyEq_const {f : ℂ → ℝ} {c : ℝ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] fun _ => c) : Δ f z = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds h).self_of_nhds]
  simp

/-- The cutoff logarithm `(1 - χ) log ‖G‖` is smooth on `W`. -/
theorem contDiffOn_cutoff_log {w₀ : ℂ} {W : Set ℂ} (hW : IsOpen W)
    {a G : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a W) (ha0 : ∀ w ∈ W, a w ≠ 0)
    (hGa : ∀ w ∈ W, G w * a w = w - w₀)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ᶠ w in 𝓝 w₀, χ w = 1) :
    ContDiffOn ℝ ∞ (fun v => (1 - χ v) * Real.log ‖G v‖) W := by
  set Ψ : ℂ → ℝ := fun v => (1 - χ v) * Real.log ‖G v‖ with hΨ
  have hGeq : ∀ w ∈ W, G w = (w - w₀) / a w := fun w hw => by
    rw [← hGa w hw, mul_div_cancel_right₀ _ (ha0 w hw)]
  have hGan : AnalyticOnNhd ℂ (fun w => (w - w₀) / a w) W := fun w hw =>
    ((analyticAt_id.sub analyticAt_const).div (ha w hw) (ha0 w hw))
  intro w hw
  by_cases hw0 : w = w₀
  · subst hw0
    have hev : Ψ =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hχ1] with v hv
      simp [hΨ, hv]
    exact (contDiffAt_const.congr_of_eventuallyEq hev).contDiffWithinAt
  · have hWn : W \ {w₀} ∈ 𝓝 w := (hW.sdiff isClosed_singleton).mem_nhds ⟨hw, hw0⟩
    have hGev : (fun v => (v - w₀) / a v) =ᶠ[𝓝 w] G := by
      filter_upwards [hW.mem_nhds hw] with v hv
      exact (hGeq v hv).symm
    have hne : (w - w₀) / a w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hw0) (ha0 w hw)
    have hlog : ContDiffAt ℝ ∞ (fun v => Real.log ‖(v - w₀) / a v‖) w := by
      have hgz : ContDiffAt ℝ ∞ (fun v => (v - w₀) / a v) w :=
        ((hGan w hw).contDiffAt (n := ∞)).restrict_scalars ℝ
      exact (hgz.norm ℝ hne).log (norm_ne_zero_iff.mpr hne)
    have hlog' : ContDiffAt ℝ ∞ (fun v => Real.log ‖G v‖) w :=
      hlog.congr_of_eventuallyEq (hGev.mono fun v hv => by simp [hv])
    exact ((contDiffAt_const.sub hχ.contDiffAt).mul hlog').contDiffWithinAt

/-- **The local computation.** -/
theorem integral_laplacian_cutoff_log {w₀ : ℂ} {W : Set ℂ} (hW : IsOpen W)
    {a G : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a W) (ha0 : ∀ w ∈ W, a w ≠ 0)
    (hGa : ∀ w ∈ W, G w * a w = w - w₀)
    {χ η : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηW : tsupport η ⊆ W) (hχ1 : ∀ᶠ w in 𝓝 w₀, χ w = 1)
    (hη1 : ∀ᶠ w in 𝓝ˢ (tsupport χ), η w = 1) (hηw₀ : η w₀ = 1) :
    ∫ w, Δ (fun v => (1 - χ v) * Real.log ‖G v‖) w * η w = 2 * Real.pi := by
  set Ψ : ℂ → ℝ := fun v => (1 - χ v) * Real.log ‖G v‖ with hΨ
  -- `G` is analytic and nonzero on `W \ {w₀}`
  have hGeq : ∀ w ∈ W, G w = (w - w₀) / a w := fun w hw => by
    rw [← hGa w hw, mul_div_cancel_right₀ _ (ha0 w hw)]
  have hGan : AnalyticOnNhd ℂ (fun w => (w - w₀) / a w) W := fun w hw =>
    ((analyticAt_id.sub analyticAt_const).div (ha w hw) (ha0 w hw))
  have hΨs : ContDiffOn ℝ ∞ Ψ W := contDiffOn_cutoff_log hW ha ha0 hGa hχ hχ1
  -- integration by parts
  have hibp := integral_mul_laplacian_eq hW hη hηc hηW hΨs
  rw [← hibp]
  -- `(1 - χ) Δη = Δη`
  have hΔη : ∀ w, (1 - χ w) * Δ η w = Δ η w := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · have hev : η =ᶠ[𝓝 w] fun _ => 1 := hη1.filter_mono (nhds_le_nhdsSet hw)
      rw [laplacian_eq_zero_of_eventuallyEq_const hev, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hw, sub_zero, one_mul]
  have h1 : (fun w => Ψ w * Δ η w) = fun w => Real.log ‖G w‖ * Δ η w := by
    funext w
    simp only [hΨ]
    rw [mul_comm (1 - χ w), mul_assoc, hΔη w]
  rw [h1]
  -- `log ‖G‖ = log ‖w - w₀‖ - log ‖a‖` on the support of `Δη`, off `w₀`
  have h2 : (fun w => Real.log ‖G w‖ * Δ η w) =ᵐ[volume]
      fun w => Real.log ‖w - w₀‖ * Δ η w - Real.log ‖a w‖ * Δ η w := by
    have hnull : (volume : Measure ℂ) {w₀} = 0 := measure_singleton w₀
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hw
    by_cases hwW : w ∈ W
    · have hw0 : w ≠ w₀ := hw
      rw [← sub_mul, hGeq w hwW, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw0))
        (norm_ne_zero_iff.mpr (ha0 w hwW))]
    · have hws : w ∉ tsupport η := fun h => hwW (hηW h)
      have : Δ η w = 0 := by
        have hev : η =ᶠ[𝓝 w] fun _ => 0 := by
          have : (tsupport η)ᶜ ∈ 𝓝 w := (isClosed_tsupport η).isOpen_compl.mem_nhds hws
          filter_upwards [this] with v hv
          exact image_eq_zero_of_notMem_tsupport hv
        exact laplacian_eq_zero_of_eventuallyEq_const hev
      simp [this]
  rw [integral_congr_ae h2]
  have hΔηc : HasCompactSupport (Δ η) := hasCompactSupport_laplacian hηc
  have hint1 : Integrable fun w => Real.log ‖w - w₀‖ * Δ η w :=
    integrable_log_norm_sub_mul (continuous_laplacian hη) hΔηc w₀
  have hint2 : Integrable fun w => Real.log ‖a w‖ * Δ η w := by
    have hcont : Continuous fun w => Real.log ‖a w‖ * Δ η w := by
      refine continuous_iff_continuousAt.mpr fun w => ?_
      by_cases hw : w ∈ W
      · have hac : ContinuousAt (fun v => Real.log ‖a v‖) w :=
          ((ha w hw).continuousAt.norm).log (norm_ne_zero_iff.mpr (ha0 w hw))
        exact hac.mul (continuous_laplacian hη).continuousAt
      · have hws : w ∉ tsupport η := fun h => hw (hηW h)
        have hev : (fun v => Real.log ‖a v‖ * Δ η v) =ᶠ[𝓝 w] fun _ => 0 := by
          have : (tsupport η)ᶜ ∈ 𝓝 w := (isClosed_tsupport η).isOpen_compl.mem_nhds hws
          filter_upwards [this] with v hv
          have hev' : η =ᶠ[𝓝 v] fun _ => 0 := by
            filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hv] with u hu
            exact image_eq_zero_of_notMem_tsupport hu
          rw [laplacian_eq_zero_of_eventuallyEq_const hev', mul_zero]
        exact continuousAt_const.congr hev.symm
    exact hcont.integrable_of_hasCompactSupport hΔηc.mul_left
  rw [integral_sub hint1 hint2, integral_log_norm_sub_mul_laplacian hη hηc w₀, hηw₀,
    integral_log_norm_mul_laplacian_eq_zero hW ha ha0 hη hηc hηW]
  ring

/-- **The local computation**, with `log |G|² = 2 log ‖G‖`. -/
theorem integral_laplacian_cutoff_logNormSq {w₀ : ℂ} {W : Set ℂ} (hW : IsOpen W)
    {a G : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a W) (ha0 : ∀ w ∈ W, a w ≠ 0)
    (hGa : ∀ w ∈ W, G w * a w = w - w₀)
    {χ η : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηW : tsupport η ⊆ W) (hχ1 : ∀ᶠ w in 𝓝 w₀, χ w = 1)
    (hη1 : ∀ᶠ w in 𝓝ˢ (tsupport χ), η w = 1) (hηw₀ : η w₀ = 1) :
    ∫ w, Δ (fun v => (1 - χ v) * Real.log (Complex.normSq (G v))) w * η w = 4 * Real.pi := by
  have hfun : (fun v => (1 - χ v) * Real.log (Complex.normSq (G v))) =
      (2 : ℝ) • fun v => (1 - χ v) * Real.log ‖G v‖ := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  have hs := contDiffOn_cutoff_log hW ha ha0 hGa hχ hχ1
  have hpt : ∀ w, Δ (fun v => (1 - χ v) * Real.log (Complex.normSq (G v))) w * η w =
      2 * (Δ (fun v => (1 - χ v) * Real.log ‖G v‖) w * η w) := by
    intro w
    by_cases hw : w ∈ W
    · rw [hfun, InnerProductSpace.laplacian_smul _
        ((hs.contDiffAt (hW.mem_nhds hw)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), smul_eq_mul, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hw (hηW h)), mul_zero, mul_zero, mul_zero]
  simp_rw [hpt]
  rw [integral_const_mul, integral_laplacian_cutoff_log hW ha ha0 hGa hχ hη hηc hηW hχ1 hη1 hηw₀]
  ring

end Local

/-! ### The complex coordinate of `ℂ¹` -/

/-- `ℂ¹ ≅ ℂ`, `z ↦ z 0`. -/
def complexCoordinate : ComplexModel 1 ≃ₗᵢ[ℂ] ℂ :=
  (EuclideanSpace.equiv (Fin 1) ℂ).toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
    |>.isometryOfInner (by
      intro x y
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, LinearEquiv.funUnique])

/-- The same map as a real linear isometry (it preserves Lebesgue measure). -/
def complexCoordinateR : ComplexModel 1 ≃ₗᵢ[ℝ] ℂ :=
  { complexCoordinate.toLinearEquiv.restrictScalars ℝ with norm_map' := complexCoordinate.norm_map }

theorem complexCoordinateR_apply (z : ComplexModel 1) :
    complexCoordinateR z = complexCoordinate z := rfl

theorem measurePreserving_complexCoordinate :
    MeasurePreserving (complexCoordinate : ComplexModel 1 → ℂ) :=
  complexCoordinateR.measurePreserving

/-! ### `dd^c` in dimension one is `Δ/(4π)` -/

section ChartCalculus

open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

theorem complexCoordinate_coordinateVector :
    complexCoordinate (coordinateVector (0 : Fin 1) : ComplexModel 1) = 1 := by
  simp [complexCoordinate, coordinateVector, LinearEquiv.funUnique]

theorem complexCoordinate_I_coordinateVector :
    complexCoordinate (Complex.I • (coordinateVector (0 : Fin 1) : ComplexModel 1)) = Complex.I := by
  rw [map_smul, complexCoordinate_coordinateVector, smul_eq_mul, mul_one]

/-- The second derivative of `Φ ∘ ι` along `(v, w)` is that of `Φ` along `(ι v, ι w)`. -/
theorem iteratedFDeriv_two_comp_complexCoordinate (Φ : ℂ → ℝ) (z v w : ComplexModel 1) :
    iteratedFDeriv ℝ 2 (fun y => Φ (complexCoordinate y)) z ![v, w] =
      iteratedFDeriv ℝ 2 Φ (complexCoordinate z) ![complexCoordinate v, complexCoordinate w] := by
  set g := complexCoordinateR.toContinuousLinearEquiv with hg
  have h := g.iteratedFDerivWithin_comp_right Φ uniqueDiffOn_univ (x := z) (mem_univ _) 2
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have hfun : (fun y => Φ (complexCoordinate y)) = Φ ∘ g := rfl
  rw [hfun, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`dd^c` on `ℂ¹`**: the top density of `dd^c (Φ ∘ ι)` at `z` is `ΔΦ(ι z)/(4π)`. -/
theorem actualTopPowerDensity_smoothDDC_comp {Φ : ℂ → ℝ} {z : ComplexModel 1}
    (hΦ : ContDiffAt ℝ 2 Φ (complexCoordinate z)) :
    actualTopPowerDensity (smoothDDC (fun y => Φ (complexCoordinate y)) z) =
      Δ Φ (complexCoordinate z) / (4 * Real.pi) := by
  have hc : ContDiffAt ℝ 2 (fun y => Φ (complexCoordinate y)) z :=
    hΦ.comp z (complexCoordinateR.toContinuousLinearEquiv.contDiff.contDiffAt)
  have hframe : (coordinateRealFrame (n := 1) : Fin (1 * 2) → ComplexModel 1) =
      ![coordinateVector (0 : Fin 1), Complex.I • coordinateVector (0 : Fin 1)] := by
    funext i
    fin_cases i
    · exact coordinateRealFrame_one_zero
    · exact coordinateRealFrame_one_one
  rw [actualTopPowerDensity_one, hframe,
    smoothDDC_complexDiagonal_eq_leviForm hc (coordinateVector (0 : Fin 1))]
  unfold leviForm realHessian
  rw [iteratedFDeriv_two_comp_complexCoordinate, iteratedFDeriv_two_comp_complexCoordinate,
    complexCoordinate_coordinateVector, complexCoordinate_I_coordinateVector,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  ring

end ChartCalculus

/-! ### The degree of a point -/

section Curve

universe u

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalMain

variable {F : OriginalFlagGeometry.{u} 1}

/-- The flag `X ⊇ Y₁` of a curve: `Y₁` is a point. -/
theorem exists_flag_one_eq_singleton (F : OriginalFlagGeometry.{u} 1) :
    ∃ q : F.carrier, F.flag (1 : Fin 2) = {q} := by
  obtain ⟨q, hq⟩ := F.firstDivisor.2.1.nonempty
  have hdisc := (ZeroDimensionalGlobalMixedMass.compact_zero_dim_finite_discrete
    (M := F.tail.carrier)).1
  have hsub : Subsingleton F.tail.carrier :=
    ⟨fun a b => isPreconnected_univ.subsingleton (mem_univ a) (mem_univ b)⟩
  refine ⟨q, Set.eq_singleton_iff_unique_mem.mpr ⟨hq, fun y hy => ?_⟩⟩
  have : (⟨y, hy⟩ : F.tail.carrier) = ⟨q, hq⟩ := @Subsingleton.elim _ hsub _ _
  exact congrArg Subtype.val this

/-- The Kähler measure on a chart (as in TN `kahlerVolume_restrict_chart`). -/
theorem kahlerVolume_restrict_chart' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] (w : KahlerBackground n M) (e : ComplexChart n M) :
    (IntegrationCurrent.kahlerVolume w).restrict e.val.source =
      Measure.map e.val.symm
        ((volume.restrict e.val.target).withDensity
          (SmoothMixedMeasureDensity.chartDensity (fun _ => w.form) e)) := by
  have h0 : IsThetaPshPotential w.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  rw [← himage, IntegrationCurrent.kahlerVolume, DiagonalMass.diagonalPotentialMeasure]
  exact SmoothMixedMeasureDensity.restrict_image_eq_map (fun _ => h0.1) e
    e.val.open_target.measurableSet (Subset.refl _)

section PointDegreeProof

open SGPT.Foundations.Analysis.Pending.GlobalTubeFunction SGPT.Foundations.Analysis.Pending.ChartPartition
open SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
open SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open Metric
open scoped Manifold

/-- The weight of a metered divisor is chart-smooth off its support. -/
theorem chartSmoothOn_weight_toReal (E : MeteredEffectiveQDivisor 1 F.carrier) :
    ChartSmoothOn 1 (fun x => (E.weight x).toReal) E.supportᶜ := by
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  obtain ⟨W, hzW, hW⟩ :=
    exists_isSmoothLocalPotential_neg_curvature E hz.2 e (e.val.map_target hz.1)
  rw [e.val.right_inv hz.1] at hzW
  exact ⟨W, hW.1, hzW, hW.2.2.1.mono inter_subset_right⟩

/-- Off the support, `Θ_E = -dd^c ψ_E` in every chart. -/
theorem curvature_coeff_eq_neg_smoothDDC (E : MeteredEffectiveQDivisor 1 F.carrier)
    {e : ComplexChart 1 F.carrier} {z : ComplexModel 1} (hz : z ∈ e.val.target)
    (hx : e.val.symm z ∉ E.support) :
    E.curvature.val.coeff e z = -smoothDDC (fun ζ => (E.weight (e.val.symm ζ)).toReal) z := by
  obtain ⟨W, hzW, hW⟩ := exists_isSmoothLocalPotential_neg_curvature E hx e (e.val.map_target hz)
  rw [e.val.right_inv hz] at hzW
  rw [hW.2.2.2 hzW, ClosedRealOneOneForm.coeff_neg, neg_neg]

/-- The integrand of the degree, read in any chart. -/
theorem topRatio_formPow_one_chart (θ : ClosedRealOneOneForm 1 F.carrier)
    {e : ComplexChart 1 F.carrier} {x : F.carrier} (hx : x ∈ e.val.source) :
    topRatio F.omega.form.val (formPow θ.val 1) x =
      actualTopPowerDensity (θ.val.coeff e (e.val x)) /
        actualTopPowerDensity (F.omega.form.val.coeff e (e.val x)) := by
  rw [topRatio_eq_chartRatio F.omega.isKahler.1 _ hx]
  unfold chartRatio
  rw [formPow_coeff, formPow_coeff, topDensity_formPower, topDensity_formPower]

theorem actualTopPowerDensity_omega_pos {e : ComplexChart 1 F.carrier} {z : ComplexModel 1}
    (hz : z ∈ e.val.target) : 0 < actualTopPowerDensity (F.omega.form.val.coeff e z) := by
  have := topDensity_formPow_pos F.omega.isKahler.1 hz
  rwa [formPow_coeff, topDensity_formPower] at this

theorem actualTopPowerDensity_zero_one :
    actualTopPowerDensity (0 : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ) = 0 := by
  rw [actualTopPowerDensity_one]
  rfl

/-- A Kähler form has positive degree. -/
theorem curveDegree_pos_of_kahler (κ : KahlerBackground 1 F.carrier) : 0 < curveDegree F κ.form := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := ConnectedSpace.toNonempty
  have hpos : ∀ x, 0 < topRatio F.omega.form.val (formPow κ.form.val 1) x := fun x => by
    have hxs := mem_complexChartAt_source (n := 1) x
    have hz := (complexChartAt (n := 1) x).val.map_source hxs
    rw [topRatio_formPow_one_chart κ.form hxs]
    have hκ := topDensity_formPow_pos κ.isKahler.1 hz
    rw [formPow_coeff, topDensity_formPower] at hκ
    exact div_pos hκ (actualTopPowerDensity_omega_pos hz)
  unfold curveDegree
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) (integrable_topRatio F.omega _)]
  have hsupp : Function.support (topRatio F.omega.form.val (formPow κ.form.val 1)) = univ :=
    eq_univ_of_forall fun x => (hpos x).ne'
  rw [hsupp]
  have := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos F.omega
  exact pos_iff_ne_zero.mpr fun h => by simp [Measure.real, h] at this

/-- **`tok:ext-curve`**: on a compact Kähler curve, a class contains a Kähler form if and only
if its degree is positive. -/
theorem exists_kahler_iff_curveDegree_pos (θ : ClosedRealOneOneForm 1 F.carrier) :
    (∃ κ : KahlerBackground 1 F.carrier,
      RealBottChern.ofRepresentative κ.form = RealBottChern.ofRepresentative θ) ↔
      0 < curveDegree F θ := by
  refine ⟨fun ⟨κ, hκ⟩ => ?_, exists_kahler_of_curveDegree_pos⟩
  rw [← curveDegree_eq_of_class_eq hκ]
  exact curveDegree_pos_of_kahler κ

/-- A holomorphic function on the manifold, read in an atlas chart. -/
theorem differentiableAt_comp_chart_symm {e : ComplexChart 1 F.carrier} {ψ : F.carrier → ℂ}
    {z : ComplexModel 1} (hz : z ∈ e.val.target)
    (hψ : MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ψ (e.val.symm z)) :
    DifferentiableAt ℂ (fun w => ψ (e.val.symm w)) z := by
  have h2 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 1)) e.2 hz
  have h3 := hψ.comp z h2
  rwa [mdifferentiableAt_iff_differentiableAt] at h3

/-- The same, in the complex coordinate. -/
theorem differentiableAt_comp_chart_symm_coord {e : ComplexChart 1 F.carrier} {ψ : F.carrier → ℂ}
    {w : ℂ} (hw : complexCoordinate.symm w ∈ e.val.target)
    (hψ : MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ψ
      (e.val.symm (complexCoordinate.symm w))) :
    DifferentiableAt ℂ (fun v => ψ (e.val.symm (complexCoordinate.symm v))) w :=
  (differentiableAt_comp_chart_symm hw hψ).comp w
    complexCoordinate.symm.toContinuousLinearEquiv.differentiableAt

/-- **The degree of a point** (`tok-volid:point-degree`): for a unit metric `E` of the point
`Y₁ = {q}` of the curve `X`, `∫_X Θ_E = 1`.  In a chart `w` centred at `q`, with `g` the local
generator of `𝒪(-q)` and `ψ_E = log |g|² + h`, the form `σ = Θ_E + dd^c((1 - ρ) ψ_E + ρ h)`
(`ρ` a bump equal to `1` near `q`) has the same degree, vanishes off the annulus where `ρ` is not
locally constant, and equals `dd^c ((1 - ρ) log |g|²)` near `q`; its degree is
`(1/4π) ∫ Δ((1 - ρ) log |g|²) = 1` by the one-variable Lelong--Poincaré formula. -/
theorem pointDegreeStatement (F : OriginalFlagGeometry.{u} 1) : PointDegreeStatement F := by
  intro E hE
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  obtain ⟨D, hDideal, hEsupp, hmetric⟩ := hE
  obtain ⟨q, hq⟩ := exists_flag_one_eq_singleton F
  rw [hq] at hDideal hEsupp
  obtain ⟨V, hVo, hqV, g, hgd, hgen, h', hh', hw⟩ := hmetric q
  set e : ComplexChart 1 F.carrier := complexChartAt (n := 1) q with he
  have hqe : q ∈ e.val.source := mem_complexChartAt_source q
  set w₀ : ℂ := complexCoordinate (e.val q) with hw₀def
  have hsymm0 : complexCoordinate.symm w₀ = e.val q := by
    rw [hw₀def, LinearIsometryEquiv.symm_apply_apply]
  have hgM : ∀ y ∈ V, MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) g y :=
    fun y hy => hgd.mdifferentiableAt (hVo.mem_nhds hy)
  -- `g` vanishes at `q`
  have hgq : g q = 0 := by
    have hmem : D.ideal.mem q g := (hgen q hqV g).mpr
      ⟨Filter.eventually_of_mem (hVo.mem_nhds hqV) hgM, 1, fun _ => g, fun _ => 1,
        fun _ => rfl, fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const,
        Eventually.of_forall fun y => by simp⟩
    rw [hDideal] at hmem
    obtain ⟨-, hvan⟩ := hmem
    exact hvan.self_of_nhds rfl
  -- the coordinate `κ = w - w₀` is a multiple of the generator
  set κ : F.carrier → ℂ := fun x => complexCoordinate (e.val x) - w₀ with hκ
  have hκd : ∀ y ∈ e.val.source, MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) κ y :=
    fun y hy => by
      have h1 := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel 1)) e.2 hy
      have h2 : DifferentiableAt ℂ (fun z : ComplexModel 1 => complexCoordinate z - w₀) (e.val y) :=
        (complexCoordinate.toContinuousLinearEquiv.differentiableAt).sub_const w₀
      exact h2.comp_mdifferentiableAt h1
  have hmemκ : D.ideal.mem q κ := by
    rw [hDideal]
    show _ ∧ _
    exact ⟨Filter.eventually_of_mem (e.val.open_source.mem_nhds hqe) hκd,
      Eventually.of_forall fun y hy => by rw [mem_singleton_iff.mp hy]; simp [hκ, hw₀def]⟩
  obtain ⟨-, N, s, a, hs, ha, hκeq⟩ := (hgen q hqV κ).mp hmemκ
  obtain ⟨Ah, hAh⟩ : ∃ Ah : ℂ → ℂ,
      Ah = fun w => ∑ i, a i (e.val.symm (complexCoordinate.symm w)) := ⟨_, rfl⟩
  obtain ⟨Gh, hGh⟩ : ∃ Gh : ℂ → ℂ,
      Gh = fun w => g (e.val.symm (complexCoordinate.symm w)) := ⟨_, rfl⟩
  have hP : ∀ᶠ y in 𝓝 q, (κ y = (∑ i, a i y) * g y ∧
      ∀ i, MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) (a i) y) ∧ y ∈ V := by
    filter_upwards [hκeq, eventually_all.mpr ha, hVo.mem_nhds hqV] with y h1 h2 h3
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [h1, Finset.sum_mul]
    simp only [hs]
  have hφt : Tendsto (fun w => e.val.symm (complexCoordinate.symm w)) (𝓝 w₀) (𝓝 q) := by
    have h1 : Tendsto (fun w => complexCoordinate.symm w) (𝓝 w₀) (𝓝 (e.val q)) := by
      rw [← hsymm0]; exact complexCoordinate.symm.continuous.continuousAt
    have h2 : Tendsto e.val.symm (𝓝 (e.val q)) (𝓝 q) := by
      have := e.val.continuousAt_symm (e.val.map_source hqe)
      rwa [ContinuousAt, e.val.left_inv hqe] at this
    exact h2.comp h1
  have ht : ∀ᶠ w in 𝓝 w₀, complexCoordinate.symm w ∈ e.val.target := by
    have h1 : Tendsto (fun w => complexCoordinate.symm w) (𝓝 w₀) (𝓝 (e.val q)) := by
      rw [← hsymm0]; exact complexCoordinate.symm.continuous.continuousAt
    exact h1.eventually_mem (e.val.open_target.mem_nhds (e.val.map_source hqe))
  -- the factorisation in the coordinate
  have hQ0 : ∀ᶠ w in 𝓝 w₀, complexCoordinate.symm w ∈ e.val.target ∧
      e.val.symm (complexCoordinate.symm w) ∈ V ∧ w - w₀ = Ah w * Gh w ∧
      DifferentiableAt ℂ Ah w ∧ DifferentiableAt ℂ Gh w := by
    filter_upwards [ht, hφt.eventually hP] with w h1 h2
    obtain ⟨⟨h21, h22⟩, h23⟩ := h2
    refine ⟨h1, h23, ?_, ?_, ?_⟩
    · have : κ (e.val.symm (complexCoordinate.symm w)) = w - w₀ := by
        simp only [hκ, e.val.right_inv h1, LinearIsometryEquiv.apply_symm_apply]
      rw [← this, h21, hAh, hGh]
    · rw [hAh]
      exact DifferentiableAt.fun_sum fun i _ => differentiableAt_comp_chart_symm_coord h1 (h22 i)
    · rw [hGh]
      exact differentiableAt_comp_chart_symm_coord h1 (hgM _ h23)
  obtain ⟨-, -, -, hAd0, hGd0⟩ := hQ0.self_of_nhds
  have hGw₀ : Gh w₀ = 0 := by
    rw [hGh]
    simp only [hsymm0, e.val.left_inv hqe, hgq]
  have hAw₀ : Ah w₀ ≠ 0 := by
    intro h0
    have hprod := hAd0.hasDerivAt.mul hGd0.hasDerivAt
    have hlin : HasDerivAt (fun w => Ah w * Gh w) 1 w₀ := by
      refine ((hasDerivAt_id w₀).sub_const w₀).congr_of_eventuallyEq ?_
      filter_upwards [hQ0] with w hw
      exact hw.2.2.1.symm
    have := hprod.unique hlin
    rw [h0, hGw₀] at this
    simp at this
  have hQev : ∀ᶠ w in 𝓝 w₀, (complexCoordinate.symm w ∈ e.val.target ∧
      e.val.symm (complexCoordinate.symm w) ∈ V ∧ w - w₀ = Ah w * Gh w ∧
      DifferentiableAt ℂ Ah w ∧ DifferentiableAt ℂ Gh w) ∧ Ah w ≠ 0 :=
    hQ0.and (hAd0.continuousAt.eventually_ne hAw₀)
  obtain ⟨r, hr, hQ⟩ := Metric.eventually_nhds_iff_ball.mp hQev
  -- consequences on the ball `W = B(w₀, r)`
  have hGhan : AnalyticOnNhd ℂ Gh (ball w₀ r) :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hQ w hw).1.2.2.2.2.differentiableWithinAt)
      isOpen_ball
  have hAhan : AnalyticOnNhd ℂ Ah (ball w₀ r) :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hQ w hw).1.2.2.2.1.differentiableWithinAt)
      isOpen_ball
  have hGa : ∀ w ∈ ball w₀ r, Gh w * Ah w = w - w₀ := fun w hw => by
    rw [mul_comm]; exact (hQ w hw).1.2.2.1.symm
  have hGne : ∀ w ∈ ball w₀ r, w ≠ w₀ → Gh w ≠ 0 := fun w hw hw0 h => by
    have := (hQ w hw).1.2.2.1
    rw [h, mul_zero, sub_eq_zero] at this
    exact hw0 this
  have hLs : ∀ w ∈ ball w₀ r, w ≠ w₀ →
      ContDiffAt ℝ ∞ (fun v => Real.log (Complex.normSq (Gh v))) w := by
    intro w hw hw0
    have hgz : ContDiffAt ℝ ∞ Gh w := ((hGhan w hw).contDiffAt (n := ∞)).restrict_scalars ℝ
    have hne := hGne w hw hw0
    have h := ((hgz.norm ℝ hne).pow 2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
    simp [Complex.normSq_eq_norm_sq]
  -- the cutoffs
  let χb : ContDiffBump w₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let ηb : ContDiffBump w₀ := ⟨2 * r / 3, 5 * r / 6, by positivity, by linarith⟩
  have hχt : tsupport χb = closedBall w₀ (r / 2) := χb.tsupport_eq
  have hηW : tsupport ηb ⊆ ball w₀ r := by
    rw [ηb.tsupport_eq]; exact closedBall_subset_ball (by show 5 * r / 6 < r; linarith)
  have hχ1 : ∀ᶠ w in 𝓝 w₀, χb w = 1 :=
    Filter.eventually_of_mem (closedBall_mem_nhds w₀ (show 0 < r / 4 by positivity))
      fun w hw => χb.one_of_mem_closedBall hw
  have hη1 : ∀ᶠ w in 𝓝ˢ (tsupport χb), ηb w = 1 := by
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhdsSet.mpr
      (hχt.trans_subset (closedBall_subset_ball (show r / 2 < 2 * r / 3 by linarith))))
      fun w hw => ηb.one_of_mem_closedBall (ball_subset_closedBall hw)
  set Φ : ℂ → ℝ := fun v => (1 - χb v) * Real.log (Complex.normSq (Gh v)) with hΦ
  have hloc : ∫ w, Δ Φ w * ηb w = 4 * Real.pi :=
    integral_laplacian_cutoff_logNormSq isOpen_ball hAhan (fun w hw => (hQ w hw).2) hGa
      χb.contDiff ηb.contDiff ηb.hasCompactSupport hηW hχ1 hη1
      (ηb.one_of_mem_closedBall (mem_closedBall_self (by positivity)))
  have hΦs : ∀ w ∈ ball w₀ r, w ≠ w₀ → ContDiffAt ℝ ∞ Φ w := fun w hw hw0 =>
    (contDiffAt_const.sub χb.contDiff.contDiffAt).mul (hLs w hw hw0)
  -- the bump on the manifold
  set β : ComplexModel 1 → ℝ := fun z => χb (complexCoordinate z) with hβ
  have hβs : ContDiff ℝ ∞ β := χb.contDiff.comp complexCoordinateR.contDiff
  have hβsupp : tsupport β ⊆ complexCoordinate ⁻¹' closedBall w₀ (r / 2) := by
    refine closure_minimal (fun z hz => ?_)
      (isClosed_closedBall.preimage complexCoordinate.continuous)
    rw [← hχt]
    exact subset_tsupport _ hz
  have hβc : IsCompact (tsupport β) :=
    ((complexCoordinateR.toHomeomorph.isCompact_preimage).mpr
      (isCompact_closedBall w₀ (r / 2))).of_isClosed_subset (isClosed_tsupport _) hβsupp
  have hβt : tsupport β ⊆ e.val.target := fun z hz => by
    have hzW : complexCoordinate z ∈ ball w₀ r :=
      closedBall_subset_ball (show r / 2 < r by linarith) (hβsupp hz)
    have := (hQ _ hzW).1.1
    rwa [LinearIsometryEquiv.symm_apply_apply] at this
  set ρ : F.carrier → ℝ := chartExtend e β with hρdef
  have hρs : ChartSmooth (n := 1) ρ := chartSmooth_chartExtend e hβs hβc hβt
  set K : Set F.carrier := e.val.symm '' tsupport β with hKdef
  have hK : tsupport ρ ⊆ K := by
    have hKc : IsCompact K := hβc.image_of_continuousOn (e.val.continuousOn_symm.mono hβt)
    have := support_chartExtend_subset e (β := β)
    rwa [hKc.isClosed.closure_eq] at this
  have hKV : K ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    have hzW : complexCoordinate z ∈ ball w₀ r :=
      closedBall_subset_ball (show r / 2 < r by linarith) (hβsupp hz)
    have := (hQ _ hzW).1.2.1
    rwa [LinearIsometryEquiv.symm_apply_apply] at this
  have hKsrc : K ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.val.map_target (hβt hz)
  have hF1 : ∀ z ∈ e.val.target, complexCoordinate z ∉ closedBall w₀ (r / 2) →
      e.val.symm z ∉ tsupport ρ := by
    intro z hz hzb hmem
    obtain ⟨z', hz', hzz'⟩ := hK hmem
    have h1 := congrArg e.val hzz'
    rw [e.val.right_inv (hβt hz'), e.val.right_inv hz] at h1
    subst h1
    exact hzb (hβsupp hz')
  have hF2 : ∀ z ∈ e.val.target, e.val.symm z = q → complexCoordinate z = w₀ := by
    intro z hz h
    have h1 := congrArg e.val h
    rw [e.val.right_inv hz] at h1
    rw [h1]
  have hρ1 : ∀ᶠ x in 𝓝 q, ρ x = 1 := by
    have hc : ContinuousAt (fun x => complexCoordinate (e.val x)) q :=
      complexCoordinate.continuous.continuousAt.comp (e.val.continuousAt hqe)
    have h2 : ∀ᶠ x in 𝓝 q, complexCoordinate (e.val x) ∈ closedBall w₀ (r / 4) :=
      hc.eventually_mem (closedBall_mem_nhds w₀ (show 0 < r / 4 by positivity))
    filter_upwards [h2, e.val.open_source.mem_nhds hqe] with x hx hxs
    rw [hρdef, chartExtend_of_mem hxs]
    exact χb.one_of_mem_closedBall hx
  -- the global potential
  obtain ⟨f, hfdef⟩ : ∃ f : F.carrier → ℝ, f = fun x =>
      bumpExtend ({q}ᶜ) (fun y => 1 - ρ y) (fun y => (E.weight y).toReal) x +
        bumpExtend V ρ h' x := ⟨_, rfl⟩
  have hf : ChartSmooth (n := 1) f := by
    have hwR : ChartSmoothOn 1 (fun x => (E.weight x).toReal) ({q}ᶜ) := by
      have := chartSmoothOn_weight_toReal E
      rwa [hEsupp] at this
    have hsupp1 : tsupport (fun y => 1 - ρ y) ⊆ ({q}ᶜ) := by
      intro x hx hxq
      rw [mem_singleton_iff] at hxq
      subst hxq
      refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
      filter_upwards [hρ1] with y hy
      simp [hy]
    have hρ' : ChartSmooth (n := 1) (fun y => 1 - ρ y) := fun e' => contDiffOn_const.sub (hρs e')
    have h1 := chartSmooth_bumpExtend (M := F.carrier) (S := ({q}ᶜ : Set F.carrier))
      isOpen_compl_singleton hρ' hwR hsupp1
    have h2 := chartSmooth_bumpExtend hVo hρs hh' (hK.trans hKV)
    rw [hfdef]
    exact fun e' => (h1 e').add (h2 e')
  set σ : ClosedRealOneOneForm 1 F.carrier := E.curvature + ddcClosedForm f hf with hσ
  have hdeg : curveDegree F E.curvature = curveDegree F σ := by
    rw [hσ, curveDegree_add, curveDegree_ddc, add_zero]
  -- off the transported support of the bump, `σ` vanishes
  have hcase1 : ∀ (e' : ComplexChart 1 F.carrier) (z : ComplexModel 1), z ∈ e'.val.target →
      e'.val.symm z ∉ tsupport ρ → e'.val.symm z ≠ q → σ.val.coeff e' z = 0 := by
    intro e' z hz hρz hqz
    have hsupp : e'.val.symm z ∉ E.support := by rw [hEsupp]; exact hqz
    rw [hσ, ClosedRealOneOneForm.coeff_add, curvature_coeff_eq_neg_smoothDDC E hz hsupp,
      ddcClosedForm_coeff]
    have hev : (fun ζ => f (e'.val.symm ζ)) =ᶠ[𝓝 z]
        fun ζ => (E.weight (e'.val.symm ζ)).toReal := by
      have hcont : ContinuousAt e'.val.symm z := e'.val.continuousAt_symm hz
      have h1 : (tsupport ρ)ᶜ ∩ {q}ᶜ ∈ 𝓝 (e'.val.symm z) :=
        inter_mem ((isClosed_tsupport ρ).isOpen_compl.mem_nhds hρz)
          (isOpen_compl_singleton.mem_nhds hqz)
      filter_upwards [hcont.preimage_mem_nhds h1] with ζ hζ
      obtain ⟨hζ1, hζ2⟩ := hζ
      simp only [hfdef]
      rw [bumpExtend_of_mem hζ2, bumpExtend_eq_zero_of_notMem_tsupport hζ1,
        image_eq_zero_of_notMem_tsupport hζ1]
      ring
    rw [smoothDDC_congr hev, neg_add_cancel]
  -- near `q`, `σ = dd^c ((1 - ρ) log |g|²)`
  have hcaseA : ∀ z ∈ e.val.target, complexCoordinate z ∈ ball w₀ r →
      complexCoordinate z ≠ w₀ → σ.val.coeff e z = smoothDDC (fun y => Φ (complexCoordinate y)) z := by
    intro z hz hzW hzw₀
    have hx : e.val.symm z ≠ q := fun h => hzw₀ (hF2 z hz h)
    have hsupp : e.val.symm z ∉ E.support := by rw [hEsupp]; exact hx
    obtain ⟨Wp, hzWp, hWp⟩ :=
      exists_isSmoothLocalPotential_neg_curvature E hsupp e (e.val.map_target hz)
    rw [e.val.right_inv hz] at hzWp
    set U : Set (ComplexModel 1) :=
      Wp ∩ complexCoordinate ⁻¹' (ball w₀ r \ {w₀}) with hU
    have hUo : IsOpen U := hWp.1.inter
      ((isOpen_ball.sdiff isClosed_singleton).preimage complexCoordinate.continuous)
    have hzU : z ∈ U := ⟨hzWp, hzW, hzw₀⟩
    have hUt : ∀ y ∈ U, y ∈ e.val.target := fun y hy => hWp.2.1 hy.1
    set L : ComplexModel 1 → ℝ := fun y => Real.log (Complex.normSq (Gh (complexCoordinate y)))
      with hL
    have hLs : ContDiffOn ℝ ∞ L U := fun y hy =>
      ((hLs _ hy.2.1 hy.2.2).comp y complexCoordinateR.contDiff.contDiffAt).contDiffWithinAt
    have hGd : ∀ y ∈ U, DifferentiableAt ℂ (fun y => Gh (complexCoordinate y)) y := fun y hy =>
      ((hGhan _ hy.2.1).differentiableAt).comp y
        complexCoordinate.toContinuousLinearEquiv.differentiableAt
    have hgy : ∀ y ∈ U, g (e.val.symm y) ≠ 0 := fun y hy => by
      have := hGne _ hy.2.1 hy.2.2
      simpa only [hGh, LinearIsometryEquiv.symm_apply_apply] using this
    have hfeq : ∀ y ∈ U, f (e.val.symm y) =
        (E.weight (e.val.symm y)).toReal + ((1 - β y) * L y - L y) := by
      intro y hy
      have hyt := hUt y hy
      have hyV : e.val.symm y ∈ V := by
        have := (hQ _ hy.2.1).1.2.1
        rwa [LinearIsometryEquiv.symm_apply_apply] at this
      have hyq : e.val.symm y ≠ q := fun h => hy.2.2 (hF2 y hyt h)
      have hρy : ρ (e.val.symm y) = β y := by
        rw [hρdef, chartExtend_of_mem (e.val.map_target hyt), e.val.right_inv hyt]
      have hLy : L y = Real.log (‖g (e.val.symm y)‖ ^ 2) := by
        simp only [hL, hGh, LinearIsometryEquiv.symm_apply_apply, Complex.normSq_eq_norm_sq]
      have hwy : (E.weight (e.val.symm y)).toReal = L y + h' (e.val.symm y) := by
        rw [hw _ hyV, generatorLog_single_eq_coe (hgy y hy), ← EReal.coe_add, EReal.toReal_coe,
          hLy]
      simp only [hfdef]
      rw [bumpExtend_of_mem (show e.val.symm y ∈ ({q}ᶜ : Set F.carrier) from hyq),
        bumpExtend_of_mem hyV, hρy, hwy]
      ring
    have hβU : ContDiffOn ℝ ∞ (fun y => (1 - β y) * L y) U :=
      (contDiffOn_const.sub hβs.contDiffOn).mul hLs
    have hpot : ContDiffOn ℝ ∞ (fun ζ => (E.weight (e.val.symm ζ)).toReal) U :=
      hWp.2.2.1.mono inter_subset_left
    rw [hσ, ClosedRealOneOneForm.coeff_add, curvature_coeff_eq_neg_smoothDDC E hz hsupp,
      ddcClosedForm_coeff]
    have hev : (fun ζ => f (e.val.symm ζ)) =ᶠ[𝓝 z]
        fun ζ => (E.weight (e.val.symm ζ)).toReal + ((1 - β ζ) * L ζ - L ζ) :=
      Filter.eventually_of_mem (hUo.mem_nhds hzU) hfeq
    rw [smoothDDC_congr hev, smoothDDC_add hUo hpot (hβU.sub hLs) hzU,
      smoothDDC_sub hUo hβU hLs hzU,
      smoothDDC_log_normSq_eq_zero (Filter.eventually_of_mem (hUo.mem_nhds hzU) hGd)
        (hGne _ hzU.2.1 hzU.2.2)]
    simp only [sub_zero, neg_add_cancel_left]
    rfl
  -- the degree of `σ` is the chart integral of its density
  have hT0 : ∀ x, x ∉ e.val.source → topRatio F.omega.form.val (formPow σ.val 1) x = 0 := by
    intro x hx
    have hxs := mem_complexChartAt_source (n := 1) x
    rw [topRatio_formPow_one_chart σ hxs,
      hcase1 _ _ ((complexChartAt (n := 1) x).val.map_source hxs) ?_ ?_,
      actualTopPowerDensity_zero_one, zero_div]
    · rw [(complexChartAt (n := 1) x).val.left_inv hxs]
      exact fun h => hx (hKsrc (hK h))
    · rw [(complexChartAt (n := 1) x).val.left_inv hxs]
      rintro rfl
      exact hx hqe
  have hdegσ : curveDegree F σ =
      ∫ z in e.val.target, actualTopPowerDensity (σ.val.coeff e z) := by
    unfold curveDegree
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hT0, kahlerVolume_restrict_chart' F.omega e]
    have hφm : AEMeasurable e.val.symm
        ((volume.restrict e.val.target).withDensity
          (SmoothMixedMeasureDensity.chartDensity (fun _ => F.omega.form) e)) :=
      (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [integral_map hφm (continuous_topRatio F.omega.isKahler.1 _).aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀
        ((SmoothMixedMeasureDensity.continuousOn_chartDensity _ e).aemeasurable
          e.val.open_target.measurableSet)
        (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun e.val.open_target.measurableSet fun z hz => ?_
    rw [topRatio_formPow_one_chart σ (e.val.map_target hz), e.val.right_inv hz,
      SmoothMixedMeasureDensity.chartDensity, actualMixedTopDensity_const,
      ENNReal.toReal_ofReal (actualTopPowerDensity_omega_pos hz).le, smul_eq_mul,
      mul_div_cancel₀ _ (actualTopPowerDensity_omega_pos hz).ne']
  -- the density, read in the complex coordinate
  set Dσ : ComplexModel 1 → ℝ := fun z => actualTopPowerDensity (σ.val.coeff e z) with hDσ
  have hpt : ∀ w : ℂ, w ≠ w₀ → e.val.target.indicator Dσ (complexCoordinate.symm w) =
      Δ Φ w * ηb w / (4 * Real.pi) := by
    intro w hw
    by_cases htw : complexCoordinate.symm w ∈ e.val.target
    · rw [indicator_of_mem htw]
      set z := complexCoordinate.symm w with hz
      have hιz : complexCoordinate z = w := by rw [hz, LinearIsometryEquiv.apply_symm_apply]
      by_cases hwb : w ∈ closedBall w₀ (r / 2)
      · have hwW : w ∈ ball w₀ r := closedBall_subset_ball (show r / 2 < r by linarith) hwb
        have hA := hcaseA z htw (by rw [hιz]; exact hwW) (by rw [hιz]; exact hw)
        have hΦz : ContDiffAt ℝ 2 Φ (complexCoordinate z) := by
          rw [hιz]
          exact (hΦs w hwW hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
        simp only [hDσ]
        rw [hA, actualTopPowerDensity_smoothDDC_comp hΦz, hιz,
          ηb.one_of_mem_closedBall (closedBall_subset_closedBall
            (show r / 2 ≤ 2 * r / 3 by linarith) hwb), mul_one]
      · have hρz := hF1 z htw (by rw [hιz]; exact hwb)
        have hqz : e.val.symm z ≠ q := fun h => hw (by rw [← hιz]; exact hF2 z htw h)
        have hD0 : Dσ z = 0 := by
          simp only [hDσ]
          rw [hcase1 e z htw hρz hqz, actualTopPowerDensity_zero_one]
        rw [hD0]
        by_cases hwW : w ∈ ball w₀ r
        · have hA := hcaseA z htw (by rw [hιz]; exact hwW) (by rw [hιz]; exact hw)
          rw [hcase1 e z htw hρz hqz] at hA
          have hΦz : ContDiffAt ℝ 2 Φ (complexCoordinate z) := by
            rw [hιz]
            exact (hΦs w hwW hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
          have h2 := actualTopPowerDensity_smoothDDC_comp hΦz
          rw [← hA, actualTopPowerDensity_zero_one, hιz] at h2
          have hπ : (0 : ℝ) < 4 * Real.pi := by positivity
          have h3 : Δ Φ w = 0 := by
            have := (div_eq_zero_iff.mp h2.symm).resolve_right hπ.ne'
            exact this
          rw [h3]
          ring
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hwW (hηW h))]
          ring
    · rw [indicator_of_notMem htw]
      have hwW : w ∉ ball w₀ r := fun h => htw (hQ w h).1.1
      rw [image_eq_zero_of_notMem_tsupport (fun h => hwW (hηW h))]
      ring
  have hemb : MeasurableEmbedding (complexCoordinate : ComplexModel 1 → ℂ) :=
    complexCoordinateR.toHomeomorph.measurableEmbedding
  have htrans := measurePreserving_complexCoordinate.integral_comp hemb
    (fun w => e.val.target.indicator Dσ (complexCoordinate.symm w))
  simp only [LinearIsometryEquiv.symm_apply_apply] at htrans
  have hae : (fun w => e.val.target.indicator Dσ (complexCoordinate.symm w)) =ᵐ[volume]
      fun w => Δ Φ w * ηb w / (4 * Real.pi) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton w₀)] with w hw
    exact hpt w hw
  rw [hdeg, hdegσ, ← integral_indicator e.val.open_target.measurableSet, htrans,
    integral_congr_ae hae, integral_div, hloc]
  have hπ : (0 : ℝ) < 4 * Real.pi := by positivity
  field_simp

end PointDegreeProof

/-! ### `A_1` and the volume identity -/

section Final

open SGPT.Okounkov.TranscendentalWN SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.TranscendentalRelGen

/-- **`tok:A1`** (DRWNXZ Lemma 3.6), unconditional: on a compact Kähler curve with flag
`X ⊇ {q}`, `vol Δ_{Y•}(α) = vol(α)` for every big class `α`. -/
theorem volumeIdentity_dimOne (F : OriginalFlagGeometry.{u} 1) : VolumeIdentityStatement F :=
  volumeIdentity_dimOne_of_pointDegree (pointDegreeStatement F)

/-- `A_1` for all curves. -/
theorem volumeIdentityAll_zero : VolumeIdentityAllStatement.{u} 0 :=
  fun F => volumeIdentity_dimOne F

/-- **`tok:volume-identity`** (DRWNXZ Theorem 7.6; the book's `thm:Okounkovtranmain` (1)):
`vol Δ_{Y•}(α) = vol(α)/n!` for every flag geometry of every dimension `n ≥ 1` and every big
class, **conditional on** Witt Nyström's integrated formula in dimensions `≥ 2`
(`WNIntegratedStatement`, package WN) and RELGEN's `PushforwardAnalyticStatement`. -/
theorem volumeIdentity_of_wnIntegrated_of_pushforward
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNIntegratedStatement F)
    (hP : PushforwardAnalyticStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wn_of_pushforward_of_pointDegree hWN hP pointDegreeStatement

/-- The volume identity, conditional on WN in dimensions `≥ 2` and RELGEN2's
`ModificationL2GenerationStatement`. -/
theorem volumeIdentity_of_wnIntegrated_of_modificationL2
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNIntegratedStatement F)
    (hM : SGPT.Okounkov.TranscendentalL2.ModificationL2GenerationStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wnIntegrated_of_pushforward hWN
    (SGPT.Okounkov.TranscendentalL2.pushforwardAnalyticStatement_of_modificationL2Generation hM)

/-- The volume identity in the form consumed by the final assembly: from the package statement
`WNStatement` (integrated formula and continuity) in dimensions `≥ 2` and
`PushforwardAnalyticStatement`; only the integrated formula is used. -/
theorem volumeIdentity_of_wnStatement_of_pushforward
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNStatement F)
    (hP : PushforwardAnalyticStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wnIntegrated_of_pushforward (fun m F => (hWN m F).1) hP

/-- The same with `ModificationL2GenerationStatement`. -/
theorem volumeIdentity_of_wnStatement_of_modificationL2
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNStatement F)
    (hM : SGPT.Okounkov.TranscendentalL2.ModificationL2GenerationStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wnIntegrated_of_modificationL2 (fun m F => (hWN m F).1) hM

/-- **`tok:volume-identity`, with the `L²` input discharged** (RELGEN3's
`TranscendentalL2.pushforwardAnalyticStatement`): `vol Δ_{Y•}(α) = vol(α)/n!` for every flag
geometry of every dimension and every big class, **conditional only on** Witt Nyström's integrated
formula in dimensions `≥ 2` (`WNIntegratedStatement`, package WN). -/
theorem volumeIdentityStatement_of_wnIntegrated
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNIntegratedStatement F) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wnIntegrated_of_pushforward hWN
    SGPT.Okounkov.TranscendentalL2.pushforwardAnalyticStatement

/-- **`tok:volume-identity`** in the form for the final assembly: conditional only on the WN
package statement `WNStatement F` for the flag geometries of dimension `≥ 2` (only its
integrated half is used). -/
theorem volumeIdentityStatement_of_wn
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNStatement F) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentityStatement_of_wnIntegrated fun m F => (hWN m F).1

end Final

end Curve

end SGPT.Okounkov.TranscendentalVolId
