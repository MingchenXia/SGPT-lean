import SGPT.Envelopes.LapClassDef
import SGPT.Envelopes.DNTRegQuasiPsh
import SGPT.Foundations.Analysis.Pending.AubinYauEstimate

/-!
# Bounded complex Hessian implies bounded metric Laplacian

Lane LAP-CLASS (`claude-lap-class`, node `lap-class:bridge`).  The earlier lanes (DNT-C11,
NPP-DNT, C11-REAL) proved the DNT-chapter statements for obstacles with bounded complex Hessian
(`DNTC11.HasBoundedComplexHessian`, the quasi-psh `C^{1,1̄}`).  This class is contained in the
book's `C^{1,1̄}(X)` (bounded metric Laplacian, `HasBoundedMetricLaplacian`):

* `laplacian_le_of_ddc_line_le`: `ddᶜg ≤ S ω` on complex lines gives `Δ_ω g ≤ N S`.
* `laplacianLE_of_neg_psh`: if `-f` is `(Sω)`-psh, then `Δ_ω f ≤ N S` in the sense of
  distributions (smooth approximation of NPP-DNT, `exists_tendstoUniformly_chartSmooth_ddc_le`).
* `HasBoundedComplexHessian.hasBoundedMetricLaplacian`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open KahlerLaplacianChart IntegrationCurrent

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A one-sided bound `ddᶜg ≤ S ω` on complex lines bounds the Laplacian: `Δ_ω g ≤ N S`. -/
theorem laplacian_le_of_ddc_line_le (w : KahlerBackground N Y) {g : Y → ℝ}
    (hg : ChartSmooth (n := N) g) {S : ℝ}
    (hS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm g hg).val.coeff e z ![v, Complex.I • v] ≤
        S * w.form.val.coeff e z ![v, Complex.I • v]) (y : Y) :
    laplacian w.form.val g y ≤ N * S := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  obtain ⟨W, ρ, hzW, hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials w.form e
    (e.val y) hz
  have hρ2 : ContDiffAt ℝ 2 ρ (e.val y) :=
    AubinYauEstimate.contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hzW
  have hHρ : complexHessian ρ (e.val y) = normalizedHermitianMatrix (w.form.val.coeff e (e.val y)) := by
    rw [← normalizedHermitianMatrix_smoothDDC hρ2, hpot.2.2.2 hzW]
  have hg2 : ContDiffAt ℝ 2 (fun z => g (e.val.symm z)) (e.val y) :=
    SGPT.Okounkov.TranscendentalWNReg.contDiffAt_two_chart hg e hz
  have hH := posDef_coeff w.isKahler.1 hz
  obtain ⟨m, v, hv, -⟩ := exists_trace_eq_sum_leviForm hH.inv.posSemidef
  have hterm : ∀ x : ComplexModel N, leviForm (fun z => g (e.val.symm z)) (e.val y) x ≤
      S * leviForm ρ (e.val y) x := by
    intro x
    have h := hS e (e.val y) hz x
    rw [SGPT.Okounkov.TranscendentalWNReg.ddc_line_eq hg e hz x] at h
    have h2 := AubinYauEstimate.coeff_line_eq_leviForm w hpot hzW x
    change w.form.val.coeff e (e.val y) ![x, Complex.I • x] = leviForm ρ (e.val y) x / Real.pi
      at h2
    rw [h2] at h
    have hpi := Real.pi_pos
    rw [div_le_iff₀ hpi] at h
    have : S * (leviForm ρ (e.val y) x / Real.pi) * Real.pi = S * leviForm ρ (e.val y) x := by
      field_simp
    linarith
  have htrρ : ((normalizedHermitianMatrix (w.form.val.coeff e (e.val y)))⁻¹ *
      complexHessian ρ (e.val y)).trace.re = N := by
    rw [hHρ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.trace_one]
    simp
  rw [hv _ _ hρ2] at htrρ
  rw [laplacian_eq_trace, hv _ _ hg2]
  calc ∑ i, leviForm (fun z => g (e.val.symm z)) (e.val y) (v i)
      ≤ ∑ i, S * leviForm ρ (e.val y) (v i) := Finset.sum_le_sum fun i _ => hterm (v i)
    _ = N * S := by rw [← Finset.mul_sum, htrρ, mul_comm]

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- If `-f` is `(Sω)`-plurisubharmonic (i.e. `ddᶜf ≤ S ω`), then `Δ_ω f ≤ N S` in the sense of
distributions. -/
theorem laplacianLE_of_neg_psh [ConnectedSpace Y] (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : Continuous f) {S : ℝ} (hS : 0 < S)
    (hpsh : IsThetaPshPotential (S • w.form).val (fun x => ((-f x : ℝ) : EReal))) :
    LaplacianLE w f (N * S) := by
  obtain ⟨g, hg, hconv, hddc⟩ :=
    SGPT.Envelopes.DNTReg.exists_tendstoUniformly_chartSmooth_ddc_le w hf hS hpsh
  exact laplacianLE_of_tendstoUniformly w
    (fun k => YauUniformEstimate.continuous_of_chartSmooth (hg k)) hconv
    (Eventually.of_forall fun k =>
      laplacianLE_of_chartSmooth w (hg k) (laplacian_le_of_ddc_line_le w (hg k) (hddc k)))

omit [BorelSpace Y] in
/-- An upper bound for `Δ_ω(-f)` is a lower bound for `Δ_ω f`. -/
theorem laplacianGE_of_laplacianLE_neg (w : KahlerBackground N Y) {f : Y → ℝ} {M : ℝ}
    (h : LaplacianLE w (fun x => -f x) M) : LaplacianGE w f (-M) := by
  intro χ hχ hχ0
  have h1 := h χ hχ hχ0
  have h2 : ∫ y, -(f y * laplacian w.form.val χ y) ∂(kahlerVolume w) =
      -∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) := integral_neg _
  have h3 : ∫ y, -f y * laplacian w.form.val χ y ∂(kahlerVolume w) =
      ∫ y, -(f y * laplacian w.form.val χ y) ∂(kahlerVolume w) :=
    integral_congr_ae (Eventually.of_forall fun y => by
      show -f y * laplacian w.form.val χ y = -(f y * laplacian w.form.val χ y)
      ring)
  linarith

/-- **Bounded complex Hessian implies bounded metric Laplacian**: the class of the earlier proved
DNT clauses (`DNTC11.HasBoundedComplexHessian`, the quasi-psh `C^{1,1̄}`) is contained in the book's
`C^{1,1̄}(X)` for every Kähler form `ω`. -/
theorem HasBoundedComplexHessian.hasBoundedMetricLaplacian [ConnectedSpace Y]
    (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := N) f) :
    HasBoundedMetricLaplacian w f := by
  have hnf : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := N) (fun x => -f x) := by
    refine ⟨hf.1.neg, fun e => ?_⟩
    obtain ⟨h, hh⟩ := hf.2 e
    refine ⟨_, (hh.smul (-1)).congr_fun ?_⟩
    funext z
    ring
  obtain ⟨S, hS, hpsh⟩ := SGPT.Envelopes.DNTReg.HasBoundedComplexHessian.exists_neg_psh w hf
  obtain ⟨T, hT, hpshT⟩ := SGPT.Envelopes.DNTReg.HasBoundedComplexHessian.exists_neg_psh w hnf
  have hle := laplacianLE_of_neg_psh w hf.1 hS hpsh
  have hge : LaplacianLE w (fun x => -f x) (N * T) := by
    refine laplacianLE_of_neg_psh w hf.1.neg hT ?_
    simpa using hpshT
  refine ⟨hf.1, max (N * S) (N * T), fun χ hχ hχ0 => ?_, fun χ hχ hχ0 => ?_⟩
  · exact (hle χ hχ hχ0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg hχ0))
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg hχ0))
      (laplacianGE_of_laplacianLE_neg w hge χ hχ hχ0)
    linarith [le_max_right (N * S) (N * T)]

end SGPT.Envelopes.LapClass
