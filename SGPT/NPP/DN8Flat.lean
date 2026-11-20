import SGPT.Analysis.CZHessianDensity
import SGPT.Envelopes.LapClass3Hessian

/-!
# Bounded metric Laplacian of a plurisubharmonic function in a chart: uniform Levi bounds

Lane DN8, `thm:DNT23_C11bar` (transfer step of FPT `thm:big-metric-laplacian-rooftop`,
`chapters/inputs/q10-big-envelope-regularity.tex`: "return through the isomorphism over `X ∖ Z`").

Let `v` be a continuous plurisubharmonic function on an open set `Ω ⊆ ℂⁿ`, `N` a continuous field
of positive definite Hermitian matrices and `V > 0` a continuous density on `Ω`, and write
`L φ = Re tr(N⁻¹ ∂∂̄φ)` (`pairLap`).  Assume that `V L` is symmetric for test functions on a ball
(Green's identity of a Kähler metric read in a chart) and that `v` has `V L`-Laplacian bounded above
in the sense of distributions on the ball `B̄(z₀, 3R)`:
`∫ v V Lφ ≤ M ∫ V φ` for smooth `φ ≥ 0`.  Then:

* `integral_mul_leviForm_le`: the flat directional Levi forms of `v` are bounded,
  `∫ v ∂_ξ∂̄_ξ φ ≤ C |ξ|² ∫ φ` for smooth `φ ≥ 0` supported in `B̄(z₀, 3R)` (mollify, integrate by
  parts, and use `⟨Pξ, ξ⟩ ≤ tr P |ξ|² ≤ tr N · tr(N⁻¹P) |ξ|²` for semipositive `P`);
* `leviForm_mollified_le`: hence the radial mollifications `v_j` of `v` (TN's explicit kernels) are
  smooth plurisubharmonic with `0 ≤ ∂_ξ∂̄_ξ v_j ≤ C |ξ|²` on `B(z₀, 2R)`, uniformly in `j`, and
  converge uniformly to `v` on `B̄(z₀, R)` (Dini).

This is the metric-independent content of a bounded metric Laplacian for a quasi-psh function:
the positive current `ddᶜv` has bounded coefficients.  It is used to pass the Laplacian bound of
the envelope from the modification `Y` to `X` (`DN8Transfer`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal ComplexOrder

namespace SGPT.NPP.DN8

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11 SGPT.Analysis.CZLp

variable {n : ℕ}

/-- The chart operator `L_N φ(z) = Re tr(N(z)⁻¹ ∂∂̄φ(z))` (the chart Laplacian of a Hermitian
metric with coefficient matrix `N`). -/
def pairLap (N : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (φ : ComplexModel n → ℝ)
    (z : ComplexModel n) : ℝ :=
  ((N z)⁻¹ * complexHessian φ z).trace.re

/-! ### Integration by parts and pointwise algebra -/

theorem contDiff_two_of_contDiff {g : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ 2 g :=
  hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- **Two integrations by parts in a complex direction**: `∫ g ∂_ξ∂̄_ξ φ = ∫ (∂_ξ∂̄_ξ g) φ`. -/
theorem integral_mul_leviForm_eq {g φ : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (ξ : ComplexModel n) :
    ∫ x, g x * leviForm φ x ξ = ∫ x, leviForm g x ξ * φ x := by
  have hφ2 := contDiff_two_of_contDiff hφ
  have hg2 := contDiff_two_of_contDiff hg
  have hcs : ∀ a, HasCompactSupport (fun x => realHessian φ x a a) := fun a => by
    refine hφc.mono' fun x hx => ?_
    by_contra hxt
    exact hx (ContactLocal.realHessian_eq_zero_of_notMem_tsupport hxt a a)
  have hA : ∀ a, Integrable (fun x => g x * realHessian φ x a a) := fun a =>
    (hg.continuous.mul (continuous_realHessian hφ2 a a)).integrable_of_hasCompactSupport
      (hcs a).mul_left
  have hB : ∀ a, Integrable (fun x => realHessian g x a a * φ x) := fun a =>
    ((continuous_realHessian hg2 a a).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left
  have e1 := ContactLocal.integral_mul_realHessian_eq_of_contDiffOn isOpen_univ hg.contDiffOn hφ
    hφc (subset_univ _) ξ ξ
  have e2 := ContactLocal.integral_mul_realHessian_eq_of_contDiffOn isOpen_univ hg.contDiffOn hφ
    hφc (subset_univ _) (Complex.I • ξ) (Complex.I • ξ)
  calc ∫ x, g x * leviForm φ x ξ
      = ∫ x, (g x * realHessian φ x ξ ξ +
          g x * realHessian φ x (Complex.I • ξ) (Complex.I • ξ)) / 4 := by
        congr 1; funext x; simp only [leviForm]; ring
    _ = ((∫ x, g x * realHessian φ x ξ ξ) +
          ∫ x, g x * realHessian φ x (Complex.I • ξ) (Complex.I • ξ)) / 4 := by
        rw [integral_div, integral_add (hA _) (hA _)]
    _ = ((∫ x, realHessian g x ξ ξ * φ x) +
          ∫ x, realHessian g x (Complex.I • ξ) (Complex.I • ξ) * φ x) / 4 := by rw [e1, e2]
    _ = ∫ x, leviForm g x ξ * φ x := by
        rw [← integral_add (hB _) (hB _), ← integral_div]
        congr 1; funext x; simp only [leviForm]; ring

/-- For `P` semipositive and `N` positive definite, `⟨Pξ, ξ⟩ ≤ tr N · Re tr(N⁻¹P) · |ξ|²`, and
`Re tr(N⁻¹P) ≥ 0`.  Stated for complex Hessians of `C²` functions. -/
theorem leviForm_le_trace_mul {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hP : (complexHessian u z).PosSemidef)
    {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (ξ : ComplexModel n) :
    leviForm u z ξ ≤ N.trace.re * (N⁻¹ * complexHessian u z).trace.re * ‖ξ‖ ^ 2 ∧
      0 ≤ (N⁻¹ * complexHessian u z).trace.re := by
  have hq : ∀ v, 0 ≤ hermQuad (complexHessian u z) v := fun v => by
    have h := hP.dotProduct_mulVec_nonneg (fun i => star (v i))
    rw [hermQuad, SGPT.Envelopes.LapClass3.sesqForm_eq_dotProduct]
    exact (Complex.nonneg_iff.mp h).1
  have h1 := SGPT.Envelopes.LapClass3.hermQuad_le_trace_mul hP.1 hq ξ
  rw [hermQuad_complexHessian hu] at h1
  have h2 := re_trace_le_re_trace_mul hN hP
  obtain ⟨m, w, hw, -⟩ := SGPT.Envelopes.LapClass.exists_trace_eq_sum_leviForm hN.inv.posSemidef
  have h3 : 0 ≤ (N⁻¹ * complexHessian u z).trace.re := by
    rw [hw u z hu]
    exact Finset.sum_nonneg fun i _ => by
      rw [← hermQuad_complexHessian hu]
      exact hq _
  refine ⟨h1.trans ?_, h3⟩
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-! ### Uniform bounds on compact sets -/

theorem exists_le_of_continuousOn {K : Set (ComplexModel n)} (hK : IsCompact K)
    {f : ComplexModel n → ℝ} (hf : ContinuousOn f K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, |f z| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨|C|, abs_nonneg _, fun z hz => by
    have := hC z hz; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)⟩

theorem continuous_of_continuousOn_of_eq_zero {E : Type*} [TopologicalSpace E] {F : E → ℝ}
    {U T : Set E} (hU : IsOpen U) (hT : IsClosed T) (hTU : T ⊆ U) (hF : ContinuousOn F U)
    (h0 : ∀ x ∉ T, F x = 0) : Continuous F := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact hF.continuousAt (hU.mem_nhds hx)
  · have hxT : x ∉ T := fun h => hx (hTU h)
    have h : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] F :=
      Filter.eventually_of_mem (hT.isOpen_compl.mem_nhds hxT) fun y hy => (h0 y hy).symm
    exact continuousAt_const.congr h

/-- `V · L_N g · φ` is continuous for `V`, `N⁻¹` continuous on an open set containing the support
of `φ` and `g` smooth. -/
theorem continuous_mul_pairLap {U : Set (ComplexModel n)} (hU : IsOpen U)
    {N : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {V : ComplexModel n → ℝ}
    (hNi : ContinuousOn (fun z => (N z)⁻¹) U) (hVc : ContinuousOn V U)
    {g φ : ComplexModel n → ℝ} (hg : ContDiff ℝ ∞ g) (hφ : Continuous φ)
    (hφU : tsupport φ ⊆ U) :
    Continuous fun z => φ z * (V z * pairLap N g z) := by
  refine continuous_of_continuousOn_of_eq_zero hU (isClosed_tsupport φ) hφU ?_ fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hH := SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_complexHessian hU
    hg.contDiffOn
  exact hφ.continuousOn.mul (hVc.mul (Complex.continuous_re.comp_continuousOn
    ((continuous_id.matrix_trace).comp_continuousOn (hNi.mul hH))))

/-- The same with `φ`'s Hessian: `V · L_N φ` for a test function `φ`. -/
theorem continuous_mul_pairLap_self {U : Set (ComplexModel n)} (hU : IsOpen U)
    {N : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {V : ComplexModel n → ℝ}
    (hNi : ContinuousOn (fun z => (N z)⁻¹) U) (hVc : ContinuousOn V U)
    {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U) :
    Continuous fun z => V z * pairLap N φ z := by
  refine continuous_of_continuousOn_of_eq_zero hU (isClosed_tsupport φ) hφU ?_ fun x hx => by
    rw [pairLap, SGPT.Foundations.Analysis.Pending.MixedHessian.complexHessian_eq_zero_of_notMem_tsupport
      hx, Matrix.mul_zero]
    simp
  have hH := SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_complexHessian hU
    hφ.contDiffOn
  exact hVc.mul (Complex.continuous_re.comp_continuousOn
    ((continuous_id.matrix_trace).comp_continuousOn (hNi.mul hH)))

/-! ### The flat Levi bound -/

section Flat

variable {Ω : Opens (ComplexModel n)} {v : ComplexModel n → ℝ} {z₀ : ComplexModel n} {R : ℝ}
  {N : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {V : ComplexModel n → ℝ}

/-- Dominated convergence for the mollifications of a continuous psh function, paired with a
continuous function supported in the ball where they decrease to it. -/
theorem tendsto_integral_mollified_mul (hv : IsLocallyBoundedPshOn Ω v) (hvc : ContinuousOn v Ω)
    {S : ℝ} (hS : 0 < S) (hball : closedBall z₀ (4 * S) ⊆ Ω) {G : ComplexModel n → ℝ}
    (hG : Continuous G) (hGs : HasCompactSupport G) (hGK : tsupport G ⊆ ball z₀ (2 * S)) :
    Tendsto (fun j => ∫ x, ContactLocal.mollified v z₀ S hS j x * G x) atTop
      (𝓝 (∫ x, v x * G x)) := by
  have happ := ContactLocal.isDecreasingApproximation_mollified hv hS hball
  have hcd : ∀ j, Continuous (ContactLocal.mollified v z₀ S hS j) := fun j =>
    (ContactLocal.contDiff_mollified hv hball hS j).continuous
  set K := tsupport G with hKdef
  have hKc : IsCompact K := hGs
  have hKΩ : K ⊆ Ω :=
    hGK.trans (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hball))
  obtain ⟨Bv, -, hBv⟩ := exists_le_of_continuousOn hKc (hvc.mono hKΩ)
  obtain ⟨B0, -, hB0⟩ := exists_le_of_continuousOn hKc (hcd 0).continuousOn
  have hin : ∀ x ∈ K, x ∈ (ContactLocal.innerBall z₀ S : Set (ComplexModel n)) := fun x hx =>
    hGK hx
  have hbs : HasCompactSupport (fun x => (Bv + B0) * |G x|) :=
    hGs.mono' fun x hx => subset_tsupport _ fun h => hx (by simp [h])
  refine tendsto_integral_of_dominated_convergence (fun x => (Bv + B0) * |G x|)
    (fun j => ((hcd j).mul hG).aestronglyMeasurable)
    ((continuous_const.mul hG.abs).integrable_of_hasCompactSupport hbs)
    (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · by_cases hx : x ∈ K
    · have h1 : v x ≤ ContactLocal.mollified v z₀ S hS j x :=
        (happ.2.1 x (hin x hx)).le_of_tendsto (happ.2.2 x (hin x hx)) j
      have h2 : ContactLocal.mollified v z₀ S hS j x ≤ ContactLocal.mollified v z₀ S hS 0 x :=
        happ.2.1 x (hin x hx) (Nat.zero_le j)
      have hb1 := abs_le.mp (hBv x hx)
      have hb2 := abs_le.mp (hB0 x hx)
      have : |ContactLocal.mollified v z₀ S hS j x| ≤ Bv + B0 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · by_cases hx : x ∈ K
    · exact (happ.2.2 x (hin x hx)).mul_const _
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **The flat directional Levi bound.**  If the continuous psh function `v` has `V L_N`-Laplacian
bounded above by `M` on `B̄(z₀, 3R)` in the sense of distributions, and `V L_N` is symmetric there,
then `∫ v ∂_ξ∂̄_ξ φ ≤ C |ξ|² ∫ φ` for every smooth `φ ≥ 0` supported in `B̄(z₀, 3R)`. -/
theorem integral_mul_leviForm_le (hv : IsLocallyBoundedPshOn Ω v) (hvc : ContinuousOn v Ω)
    (hR : 0 < R) (hball : closedBall z₀ (8 * R) ⊆ Ω) (hNpd : ∀ z ∈ Ω, (N z).PosDef)
    (hNc : ContinuousOn (fun z => (N z).trace.re) Ω)
    (hNi : ContinuousOn (fun z => (N z)⁻¹) Ω) (hVc : ContinuousOn V Ω)
    (hVpos : ∀ z ∈ Ω, 0 < V z)
    (hsym : ∀ f : ComplexModel n → ℝ, ContDiff ℝ ∞ f → ∀ φ : ComplexModel n → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ closedBall z₀ (3 * R) →
        ∫ z, f z * (V z * pairLap N φ z) = ∫ z, φ z * (V z * pairLap N f z))
    {M : ℝ} (hbd : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall z₀ (3 * R) → (∀ z, 0 ≤ φ z) →
        ∫ z, v z * (V z * pairLap N φ z) ≤ M * ∫ z, V z * φ z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall z₀ (3 * R) → (∀ z, 0 ≤ φ z) → ∀ ξ : ComplexModel n,
        ∫ z, v z * leviForm φ z ξ ≤ C * ‖ξ‖ ^ 2 * ∫ z, φ z := by
  set K := closedBall z₀ (3 * R) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hΩo : IsOpen (Ω : Set (ComplexModel n)) := Ω.isOpen
  -- constants
  obtain ⟨Tb, hTb0, hTb⟩ := exists_le_of_continuousOn hKc
    ((hNc.div hVc fun z hz => (hVpos z hz).ne').mono hKΩ)
  obtain ⟨Vb, hVb0, hVb⟩ := exists_le_of_continuousOn hKc (hVc.mono hKΩ)
  refine ⟨Tb * (max M 0 * Vb), by positivity, fun φ hφ hφc hφK hφ0 ξ => ?_⟩
  -- the mollifications at scale `2R`
  have hS : (0 : ℝ) < 2 * R := by linarith
  have hballS : closedBall z₀ (4 * (2 * R)) ⊆ Ω := by
    rw [show 4 * (2 * R) = 8 * R by ring]; exact hball
  set w : ℕ → ComplexModel n → ℝ := ContactLocal.mollified v z₀ (2 * R) hS with hwdef
  have happ := ContactLocal.isDecreasingApproximation_mollified hv hS hballS
  have hcd : ∀ j, ContDiff ℝ ∞ (w j) := fun j => ContactLocal.contDiff_mollified hv hballS hS j
  have hKin : K ⊆ ball z₀ (2 * (2 * R)) := closedBall_subset_ball (by linarith)
  have hφin : tsupport φ ⊆ ball z₀ (2 * (2 * R)) := hφK.trans hKin
  have hφ2 := contDiff_two_of_contDiff hφ
  -- the two pairings
  have hG1 : Continuous fun x => leviForm φ x ξ := continuous_leviForm hφ2 ξ
  have hG1s : HasCompactSupport fun x => leviForm φ x ξ := by
    refine hφc.mono' fun x hx => ?_
    by_contra hxt
    exact hx (by
      simp only [leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hxt, add_zero,
        zero_div])
  have hG1K : tsupport (fun x => leviForm φ x ξ) ⊆ ball z₀ (2 * (2 * R)) := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)).trans hφin
    by_contra hxt
    exact hx (by
      simp only [leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hxt, add_zero,
        zero_div])
  have hG2 : Continuous fun x => V x * pairLap N φ x :=
    continuous_mul_pairLap_self hΩo hNi hVc hφ (hφK.trans hKΩ)
  have hG2z : ∀ x ∉ tsupport φ, V x * pairLap N φ x = 0 := fun x hx => by
    rw [pairLap, SGPT.Foundations.Analysis.Pending.MixedHessian.complexHessian_eq_zero_of_notMem_tsupport
      hx, Matrix.mul_zero]
    simp
  have hG2s : HasCompactSupport fun x => V x * pairLap N φ x :=
    hφc.mono' fun x hx => by
      by_contra hxt
      exact hx (hG2z x hxt)
  have hG2K : tsupport (fun x => V x * pairLap N φ x) ⊆ ball z₀ (2 * (2 * R)) := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)).trans hφin
    by_contra hxt
    exact hx (hG2z x hxt)
  have lim1 := tendsto_integral_mollified_mul hv hvc hS hballS hG1 hG1s hG1K
  have lim2 := tendsto_integral_mollified_mul hv hvc hS hballS hG2 hG2s hG2K
  -- the inequality for each mollification
  have hstep : ∀ j, ∫ x, w j x * leviForm φ x ξ ≤
      Tb * ‖ξ‖ ^ 2 * ∫ x, w j x * (V x * pairLap N φ x) := by
    intro j
    rw [integral_mul_leviForm_eq (hcd j) hφ hφc ξ,
      hsym (w j) (hcd j) φ hφ hφc hφK, ← integral_const_mul]
    have hcont := continuous_mul_pairLap hΩo hNi hVc (hcd j) hφ.continuous (hφK.trans hKΩ)
    refine integral_mono
      (((continuous_leviForm (contDiff_two_of_contDiff (hcd j)) ξ).mul
        hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      ((continuous_const.mul hcont).integrable_of_hasCompactSupport
        (hφc.mul_right.mul_left)) fun x => ?_
    by_cases hx : x ∈ tsupport φ
    · have hxK : x ∈ K := hφK hx
      have hxΩ : x ∈ Ω := hKΩ hxK
      have hpsd : (complexHessian (w j) x).PosSemidef := (happ.1 j).2.2 x (hKin hxK)
      obtain ⟨h1, h2⟩ := leviForm_le_trace_mul
        ((contDiff_two_of_contDiff (hcd j)).contDiffAt) hpsd (hNpd x hxΩ) ξ
      have hVx := hVpos x hxΩ
      have hT : (N x).trace.re ≤ Tb * V x := by
        have := (abs_le.mp (hTb x hxK)).2
        simp only [Pi.div_apply] at this
        rwa [div_le_iff₀ hVx] at this
      have hφx := hφ0 x
      change leviForm (w j) x ξ * φ x ≤ Tb * ‖ξ‖ ^ 2 * (φ x * (V x * pairLap N (w j) x))
      rw [pairLap]
      have hA : leviForm (w j) x ξ ≤
          Tb * ‖ξ‖ ^ 2 * (V x * ((N x)⁻¹ * complexHessian (w j) x).trace.re) := by
        refine h1.trans ?_
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hT h2) (sq_nonneg ‖ξ‖)
        linarith
      have := mul_le_mul_of_nonneg_right hA hφx
      linarith
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- pass to the limit
  have hlim : ∫ x, v x * leviForm φ x ξ ≤ Tb * ‖ξ‖ ^ 2 * ∫ x, v x * (V x * pairLap N φ x) :=
    le_of_tendsto_of_tendsto' lim1 (lim2.const_mul _) hstep
  have hVφ : ∫ z, V z * φ z ≤ Vb * ∫ z, φ z := by
    rw [← integral_const_mul]
    have hc : Continuous fun z => V z * φ z :=
      continuous_mul_of_continuousOn_of_tsupport hΩo hVc hφ.continuous (hφK.trans hKΩ)
    refine integral_mono (hc.integrable_of_hasCompactSupport hφc.mul_left)
      ((continuous_const.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      fun z => ?_
    by_cases hz : z ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hVb z (hφK hz))) (hφ0 z)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hφint : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
  have hVφ0 : 0 ≤ ∫ z, V z * φ z := by
    refine integral_nonneg fun z => ?_
    by_cases hz : z ∈ tsupport φ
    · exact mul_nonneg (hVpos z (hKΩ (hφK hz))).le (hφ0 z)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hb := hbd φ hφ hφc hφK hφ0
  have hM : ∫ x, v x * (V x * pairLap N φ x) ≤ max M 0 * (Vb * ∫ z, φ z) :=
    hb.trans ((mul_le_mul_of_nonneg_right (le_max_left M 0) hVφ0).trans
      (mul_le_mul_of_nonneg_left hVφ (le_max_right M 0)))
  have hTξ : 0 ≤ Tb * ‖ξ‖ ^ 2 := by positivity
  calc ∫ x, v x * leviForm φ x ξ ≤ Tb * ‖ξ‖ ^ 2 * ∫ x, v x * (V x * pairLap N φ x) := hlim
    _ ≤ Tb * ‖ξ‖ ^ 2 * (max M 0 * (Vb * ∫ z, φ z)) := mul_le_mul_of_nonneg_left hM hTξ
    _ = Tb * (max M 0 * Vb) * ‖ξ‖ ^ 2 * ∫ z, φ z := by ring

/-- **The Levi forms of the mollifications are bounded**: under the flat directional Levi bound on
`B̄(z₀, 3R)`, the mollifications `v_j` (scale `R`) satisfy `0 ≤ ∂_ξ∂̄_ξ v_j ≤ C |ξ|²` on
`B(z₀, 2R)`. -/
theorem leviForm_mollified_le (hv : IsLocallyBoundedPshOn Ω v) (hR : 0 < R)
    (hball : closedBall z₀ (4 * R) ⊆ Ω) {C : ℝ}
    (hflat : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall z₀ (3 * R) → (∀ z, 0 ≤ φ z) → ∀ ξ : ComplexModel n,
        ∫ z, v z * leviForm φ z ξ ≤ C * ‖ξ‖ ^ 2 * ∫ z, φ z)
    (j : ℕ) {z : ComplexModel n} (hz : z ∈ ball z₀ (2 * R)) (ξ : ComplexModel n) :
    0 ≤ leviForm (ContactLocal.mollified v z₀ R hR j) z ξ ∧
      leviForm (ContactLocal.mollified v z₀ R hR j) z ξ ≤ C * ‖ξ‖ ^ 2 := by
  have happ := ContactLocal.isDecreasingApproximation_mollified hv hR hball
  have hcd := ContactLocal.contDiff_mollified hv hball hR j
  refine ⟨?_, ?_⟩
  · have hpsd : (complexHessian (ContactLocal.mollified v z₀ R hR j) z).PosSemidef :=
      (happ.1 j).2.2 z hz
    rw [← hermQuad_complexHessian (contDiff_two_of_contDiff hcd).contDiffAt]
    have h := hpsd.dotProduct_mulVec_nonneg (fun i => star (ξ i))
    rw [hermQuad, SGPT.Envelopes.LapClass3.sesqForm_eq_dotProduct]
    exact (Complex.nonneg_iff.mp h).1
  · set K := closedBall z₀ (3 * R) with hKdef
    have hloc := ContactLocal.locallyIntegrable_indicator hv hball hR
    have hzK : closedBall z R ⊆ K := ContactLocal.closedBall_subset_of_mem_innerBall hz
    set φ : ComplexModel n → ℝ := fun x => explicitRadialKernel (n := n) R hR j (x - z) with hφdef
    have hφ : ContDiff ℝ ∞ φ :=
      (explicitRadialKernel_contDiff R hR j).comp (contDiff_id.sub contDiff_const)
    have hφc : HasCompactSupport φ :=
      (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph (Homeomorph.subRight z)
    have hφK : tsupport φ ⊆ K :=
      (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
        ((closedBall_subset_closedBall
          (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans hzK)
    have heq : leviForm (ContactLocal.mollified v z₀ R hR j) z ξ =
        ∫ x, v x * leviForm φ x ξ := by
      rw [ContactLocal.mollified, leviForm_translationPairing hloc
        (explicitRadialKernel_hasCompactSupport R hR j)
        (ContactLocal.explicitRadialKernel_contDiff_two R hR j)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hφdef]
      rw [SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.leviForm_comp_sub]
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
      · have hxr := dist_lt_of_notMem_closedBall hz hx j
        have h0 : leviForm (explicitRadialKernel (n := n) R hR j) (x - z) ξ = 0 := by
          simp only [leviForm, ContactLocal.realHessian_explicitRadialKernel_sub_eq_zero R hR j hxr,
            add_zero, zero_div]
        rw [indicator_of_notMem hx, h0, mul_zero, mul_zero]
    rw [heq]
    have h1 := hflat φ hφ hφc hφK (fun x => explicitRadialKernel_nonneg R hR j _) ξ
    rwa [hφdef, ContactLocal.integral_explicitRadialKernel_sub R hR j z, mul_one] at h1

/-- **Dini**: the mollifications of a continuous psh function converge uniformly on `B̄(z₀, R)`. -/
theorem tendstoUniformlyOn_mollified (hv : IsLocallyBoundedPshOn Ω v) (hvc : ContinuousOn v Ω)
    (hR : 0 < R) (hball : closedBall z₀ (4 * R) ⊆ Ω) :
    TendstoUniformlyOn (ContactLocal.mollified v z₀ R hR) v atTop (closedBall z₀ R) := by
  have happ := ContactLocal.isDecreasingApproximation_mollified hv hR hball
  have hin : closedBall z₀ R ⊆ (ContactLocal.innerBall z₀ R : Set (ComplexModel n)) :=
    closedBall_subset_ball (by linarith)
  have hΩ : closedBall z₀ R ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto (isCompact_closedBall _ _)
    (fun j => (ContactLocal.contDiff_mollified hv hball hR j).continuous.continuousOn)
    (fun x hx => happ.2.1 x (hin hx)) (hvc.mono hΩ) (fun x hx => happ.2.2 x (hin hx))

end Flat

end SGPT.NPP.DN8
