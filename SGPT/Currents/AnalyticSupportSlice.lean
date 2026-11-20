import SGPT.Foundations.Analysis.Pending.PshRepresentative
import SGPT.Foundations.Analysis.TestLeviPairing
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
import SGPT.Foundations.Analysis.PshAddition
import SGPT.Foundations.Analysis.LocalPshDiscControl
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.Pending.DistributionRegularization

/-!
# The one-variable step of the support theorem

This file proves the one-dimensional analytic input of the support theorem for closed positive
`(1,1)`-currents carried by a hypersurface (`SGPT.Currents.AnalyticSupport`): Xia,
*Foundations of pluripotential theory*, `thm:analytic-order-zero-support`, Step 2, read on the
complex lines transverse to the hypersurface.

Let `φ₁, φ₂` be subharmonic on a disc `D = D(0, ρ) ⊆ ℂ` (plurisubharmonic in the sense of
`SGPT.Foundations.Analysis.PlurisubharmonicOn`, locally integrable), and let `ψ` be harmonic on the
punctured disc (`ψ` and `-ψ` subharmonic there) with `φ₁ = φ₂ + ψ` off the centre.  Then

`ψ = c log |t| + H` on `D \ {0}`, with `H` harmonic on all of `D` and
`c = (2π)⁻¹ ∫ ψ Δχ`

for every cut-off `χ` equal to `1` near `0` (`exists_harmonic_of_eq_add`).

The proof is distributional.  The Levi (one quarter of the Laplacian) distribution of `ψ` is the
difference of the positive Levi distributions of `φ₁` and `φ₂`; it vanishes on test functions
supported off `0`, because `ψ` is harmonic there.  A difference of positive distributions
supported at a point is a multiple of the Dirac mass (`eq_mul_apply_of_support_zero`), and the
Levi distribution of `log |t|` is `π/2` times the Dirac mass (Lelong–Poincaré in one variable,
`LelongPoincareOneVariable.integral_log_norm_mul_laplacian_zero`).  Hence `ψ - c log |t|` has
vanishing Levi distribution, and Weyl's lemma in the form
`hasNonnegativeDistributionalLevi_iff_exists_pshRepresentative`, applied to it and to its
negative, gives the harmonic representative `H`.

The maximum principle then bounds `ψ - c log |t|` on a closed disc by its values on the boundary
circle (`abs_sub_le_of_eq_add`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian

namespace SGPT.Currents.AnalyticSupport

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending

/-! ### Levi distributions on the complex line -/

section Levi

/-- The real Hessian of a function on `ℂ` on the diagonal, in the real basis `1, i`. -/
theorem realHessian_complex_diag (u : ℂ → ℝ) (x w : ℂ) :
    realHessian u x w w = w.re * w.re * realHessian u x 1 1 +
      w.re * w.im * (realHessian u x 1 Complex.I + realHessian u x Complex.I 1) +
      w.im * w.im * realHessian u x Complex.I Complex.I := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have key : realHessian u x ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I)
      ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I) =
      w.re * w.re * realHessian u x 1 1 +
      w.re * w.im * (realHessian u x 1 Complex.I + realHessian u x Complex.I 1) +
      w.im * w.im * realHessian u x Complex.I Complex.I := by
    simp only [realHessian_eq_fderiv, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [← hw] at key
  exact key

/-- On `ℂ`, the Levi form in a direction `v` is `‖v‖²` times the Levi form in the direction `1`. -/
theorem leviForm_complex (u : ℂ → ℝ) (x v : ℂ) :
    leviForm u x v = ‖v‖ ^ 2 * leviForm u x 1 := by
  unfold leviForm
  rw [realHessian_complex_diag u x v, realHessian_complex_diag u x (Complex.I • v),
    realHessian_complex_diag u x 1, realHessian_complex_diag u x (Complex.I • 1)]
  have hn : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

/-- On `ℂ`, the Levi form in the direction `1` is a quarter of the Laplacian. -/
theorem leviForm_one_eq_laplacian {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (x : ℂ) :
    leviForm u x 1 = Δ u x / 4 := by
  have h := laplacian_complexLine hu (0 : ℂ) (1 : ℂ) x
  simp only [smul_eq_mul, mul_one, zero_add] at h
  have hfun : (fun t : ℂ => u t) = u := rfl
  rw [hfun] at h
  linarith

variable {Ω : Opens ℂ}

/-- The Levi distribution of a regular distribution on `ℂ`, read on a test function, is a quarter
of the integral against the Laplacian. -/
theorem levi_one_regular_apply {u : ℂ → ℝ} (hu : LocallyIntegrableOn u Ω volume) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM (1 : ℂ) (regularDistribution volume u hu) φ =
      (1 / 4 : ℝ) * ∫ x, u x * Δ (φ : ℂ → ℝ) x := by
  rw [distributionalLeviCLM_regularDistribution_apply, ← integral_const_mul]
  congr 1
  funext x
  rw [leviForm_one_eq_laplacian ((φ.contDiff).of_le (WithTop.coe_le_coe.mpr le_top))]
  ring

/-- On `ℂ`, the Levi distribution in a direction `v` is `‖v‖²` times the one in direction `1`. -/
theorem levi_regular_apply {u : ℂ → ℝ} (hu : LocallyIntegrableOn u Ω volume) (v : ℂ)
    (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM v (regularDistribution volume u hu) φ =
      ‖v‖ ^ 2 * distributionalLeviCLM (1 : ℂ) (regularDistribution volume u hu) φ := by
  rw [distributionalLeviCLM_regularDistribution_apply,
    distributionalLeviCLM_regularDistribution_apply, ← integral_const_mul]
  congr 1
  funext x
  rw [leviForm_complex]
  ring

/-- A regular distribution on `ℂ` whose Levi distribution in the direction `1` is positive has
nonnegative distributional Levi derivatives in every direction. -/
theorem hasNonnegativeDistributionalLevi_of_levi_one {u : ℂ → ℝ}
    (hu : LocallyIntegrableOn u Ω volume)
    (h : PositiveDistribution (distributionalLeviCLM (1 : ℂ) (regularDistribution volume u hu))) :
    HasNonnegativeDistributionalLevi (regularDistribution volume u hu) := by
  intro v φ hφ
  rw [levi_regular_apply hu v φ]
  exact mul_nonneg (sq_nonneg _) (h φ hφ)

/-- The Levi distribution of `log |t|` is `π / 2` times the Dirac mass at `0`. -/
theorem levi_one_log_apply (hl : LocallyIntegrableOn (fun t : ℂ => Real.log ‖t‖) Ω volume)
    (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM (1 : ℂ) (regularDistribution volume (fun t : ℂ => Real.log ‖t‖) hl) φ =
      Real.pi / 2 * φ 0 := by
  rw [levi_one_regular_apply,
    LelongPoincareOneVariable.integral_log_norm_mul_laplacian_zero φ.contDiff φ.hasCompactSupport]
  ring

theorem locallyIntegrableOn_log_norm : LocallyIntegrableOn (fun t : ℂ => Real.log ‖t‖) Ω volume :=
  LelongPoincareOneVariable.locallyIntegrable_log_norm.locallyIntegrableOn _

end Levi

/-! ### Differences of positive distributions supported at a point -/

section PointSupport

variable {Ω : Opens ℂ}

/-- The product of a test function with a smooth function. -/
def mulTest (b : ℂ → ℝ) (hb : ContDiff ℝ ∞ b) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun x => b x * φ x, hb.mul φ.contDiff, φ.hasCompactSupport.mul_left,
    (tsupport_mul_subset_right).trans φ.tsupport_subset⟩

@[simp] theorem mulTest_apply (b : ℂ → ℝ) (hb : ContDiff ℝ ∞ b) (φ : 𝓓(Ω, ℝ)) (x : ℂ) :
    mulTest b hb φ x = b x * φ x := rfl

/-- The test function of a smooth function with compact support in `Ω`. -/
def ofSmooth (b : ℂ → ℝ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ Ω) : 𝓓(Ω, ℝ) := ⟨b, hb, hbc, hbs⟩

@[simp] theorem ofSmooth_apply (b : ℂ → ℝ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ Ω) (x : ℂ) : ofSmooth b hb hbc hbs x = b x := rfl

/-- A distribution that is positive together with its negative is zero (after
`SGPT.Currents.eq_zero_of_positiveDistribution_of_neg`). -/
theorem eq_zero_of_positive_of_neg {D : 𝓓'(Ω, ℝ)} (hD : PositiveDistribution D)
    (hD' : PositiveDistribution (-D)) : D = 0 := by
  have hzero : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → D ψ = 0 := fun ψ hψ =>
    le_antisymm (by simpa using hD' ψ hψ) (hD ψ hψ)
  ext φ
  obtain ⟨χ, hχ1, hχ⟩ := exists_testFunction_eq_one_nhds_compact φ.hasCompactSupport
    φ.tsupport_subset
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 : ∀ x, 0 ≤ (C • χ) x := fun x => by
    simpa using mul_nonneg hC0 (hχ x).1
  have h2 : ∀ x, 0 ≤ (C • χ + φ) x := by
    intro x
    change 0 ≤ C * χ x + φ x
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1.self_of_nhdsSet x hx), mul_one]
      have := hC x
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (φ x)]
    · rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
      exact mul_nonneg hC0 (hχ x).1
  have e := hzero _ h2
  rw [map_add, hzero _ h1, zero_add] at e
  simpa using e

theorem positiveDistribution_mono {P : 𝓓'(Ω, ℝ)} (hP : PositiveDistribution P) {φ ψ : 𝓓(Ω, ℝ)}
    (h : ∀ x, φ x ≤ ψ x) : P φ ≤ P ψ := by
  have := hP (ψ - φ) (fun x => by simp [h x])
  rw [map_sub] at this
  linarith

/-- **A difference of positive distributions supported at the origin is a multiple of the Dirac
mass.**  If `Λ = P - Q` with `P, Q` positive and `Λ` vanishes on test functions supported off `0`,
then `Λ φ = φ 0 · Λ χ` for every test function `φ`, where `χ ≥ 0` is any test function equal to
`1` near `0`. -/
theorem eq_mul_apply_of_support_zero {Λ P Q : 𝓓'(Ω, ℝ)} (hP : PositiveDistribution P)
    (hQ : PositiveDistribution Q) (hΛ : Λ = P - Q)
    (hsupp : ∀ φ : 𝓓(Ω, ℝ), (0 : ℂ) ∉ tsupport (φ : ℂ → ℝ) → Λ φ = 0)
    (χ : 𝓓(Ω, ℝ)) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ᶠ x in 𝓝 (0 : ℂ), χ x = 1) (φ : 𝓓(Ω, ℝ)) :
    Λ φ = φ 0 * Λ χ := by
  -- a radius on which `χ = 1`
  obtain ⟨r0, hr0, hr0χ⟩ := Metric.eventually_nhds_iff_ball.mp hχ1
  set K : ℝ := P χ + Q χ with hKdef
  have hK : 0 ≤ K := add_nonneg (hP χ hχ0) (hQ χ hχ0)
  apply eq_of_abs_sub_le_all
  intro η hη
  set ε : ℝ := η / (K + 1) with hεdef
  have hε : 0 < ε := by positivity
  -- a radius on which `φ` is close to `φ 0`
  have hφc : ContinuousAt (φ : ℂ → ℝ) 0 := φ.continuous.continuousAt
  obtain ⟨r1, hr1, hr1φ⟩ := Metric.continuousAt_iff.mp hφc ε hε
  set r : ℝ := min r0 r1 with hrdef
  have hr : 0 < r := lt_min hr0 hr1
  -- a bump equal to `1` near `0`, supported in `ball 0 r`
  let bump : ContDiffBump (0 : ℂ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set b : ℂ → ℝ := (bump : ℂ → ℝ) with hbdef
  have hbsmooth : ContDiff ℝ ∞ b := bump.contDiff
  have hb0 : ∀ x, 0 ≤ b x := fun x => bump.nonneg
  have hb1 : ∀ x, b x ≤ 1 := fun x => bump.le_one
  have hbsupp : tsupport b ⊆ ball (0 : ℂ) r := by
    rw [hbdef, bump.tsupport_eq]
    exact closedBall_subset_ball (by simp [bump]; linarith)
  have hbzero : ∀ x, x ∉ ball (0 : ℂ) r → b x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hbsupp h))
  have hbone : ∀ x ∈ ball (0 : ℂ) (r / 4), b x = 1 := fun x hx =>
    bump.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hrr0 : ball (0 : ℂ) r ⊆ ball (0 : ℂ) r0 := ball_subset_ball (min_le_left _ _)
  have hrr1 : ball (0 : ℂ) r ⊆ ball (0 : ℂ) r1 := ball_subset_ball (min_le_right _ _)
  have hrΩ : ball (0 : ℂ) r ⊆ Ω := by
    intro x hx
    have hχx : χ x = 1 := hr0χ x (hrr0 hx)
    by_contra hxΩ
    have : χ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hxΩ (χ.tsupport_subset h)
    linarith
  have hbcs : HasCompactSupport b := bump.hasCompactSupport
  set B : 𝓓(Ω, ℝ) := ofSmooth b hbsmooth hbcs (hbsupp.trans hrΩ) with hBdef
  have hball4 : ball (0 : ℂ) (r / 4) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ (by positivity)
  have hball4r : ball (0 : ℂ) (r / 4) ⊆ ball (0 : ℂ) r := ball_subset_ball (by linarith)
  -- `(1 - b) φ` and `χ - b` vanish near `0`
  have h1 : Λ (φ - mulTest b hbsmooth φ) = 0 := by
    apply hsupp
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hball4] with x hx
    simp [hbone x hx]
  have h2 : Λ (χ - B) = 0 := by
    apply hsupp
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hball4] with x hx
    simp [hBdef, hbone x hx, hr0χ x (hrr0 (hball4r hx))]
  -- the remainder `G = b (φ - φ 0)`
  set G : 𝓓(Ω, ℝ) := mulTest b hbsmooth φ - φ 0 • B with hGdef
  have hGx : ∀ x, G x = b x * (φ x - φ 0) := by
    intro x; simp [hGdef, hBdef]; ring
  have hGle : ∀ x, |G x| ≤ ε * B x := by
    intro x
    rw [hGx]
    by_cases hx : x ∈ ball (0 : ℂ) r
    · have hd : dist x 0 < r1 := by rw [← mem_ball]; exact hrr1 hx
      have hφx : |φ x - φ 0| < ε := by
        have := hr1φ hd; rwa [Real.dist_eq] at this
      rw [abs_mul, abs_of_nonneg (hb0 x)]
      simp only [hBdef, ofSmooth_apply]
      nlinarith [hb0 x]
    · simp [hbzero x hx, hBdef]
  have hBχ : ∀ x, B x ≤ χ x := by
    intro x
    simp only [hBdef, ofSmooth_apply]
    by_cases hx : x ∈ ball (0 : ℂ) r
    · rw [hr0χ x (hrr0 hx)]; exact hb1 x
    · rw [hbzero x hx]; exact hχ0 x
  have hbound : ∀ R : 𝓓'(Ω, ℝ), PositiveDistribution R → |R G| ≤ ε * R χ := by
    intro R hR
    have hup : R G ≤ R (ε • B) :=
      positiveDistribution_mono hR (fun x => by
        have := hGle x; simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact (le_abs_self _).trans this)
    have hlo : R (-G) ≤ R (ε • B) :=
      positiveDistribution_mono hR (fun x => by
        have := hGle x; simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
          FunLike.coe_neg, Pi.neg_apply]
        exact (neg_le_abs _).trans this)
    rw [map_smul, smul_eq_mul] at hup hlo
    rw [map_neg] at hlo
    have hBR : R B ≤ R χ := positiveDistribution_mono hR hBχ
    rw [abs_le]
    constructor <;> nlinarith
  have hsplit : Λ φ - φ 0 * Λ χ = Λ G := by
    have e1 : φ = (φ - mulTest b hbsmooth φ) + (G + φ 0 • B) := by
      rw [hGdef]; abel
    have e2 : Λ χ = Λ (χ - B) + Λ B := by rw [← map_add]; congr 1; abel
    have e3 : Λ φ = Λ (φ - mulTest b hbsmooth φ) + Λ G + φ 0 * Λ B := by
      conv_lhs => rw [e1]
      rw [map_add, map_add, map_smul, smul_eq_mul]
      ring
    rw [e3, e2, h1, h2]
    ring
  rw [hsplit, hΛ]
  simp only [sub_apply]
  have hPb := hbound P hP
  have hQb := hbound Q hQ
  have hPχ := hP χ hχ0
  have hQχ := hQ χ hχ0
  calc |P G - Q G| ≤ |P G| + |Q G| := abs_sub _ _
    _ ≤ ε * P χ + ε * Q χ := add_le_add hPb hQb
    _ = ε * K := by ring
    _ ≤ η := by
        rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

end PointSupport

/-! ### The one-variable decomposition -/

section Decomposition

variable {Ω : Opens ℂ}

theorem integrable_test_mul {f : ℂ → ℝ} (hf : LocallyIntegrableOn f Ω volume) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x => φ x * f x) volume := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hint : IntegrableOn f (tsupport φ) volume :=
    hf.integrableOn_compact_subset φ.tsupport_subset hK
  have h2 : IntegrableOn (fun x => φ x * f x) (tsupport φ) volume :=
    hint.continuousOn_mul φ.continuous.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]

theorem regularDistribution_sub_complex {f g : ℂ → ℝ} (hf : LocallyIntegrableOn f Ω volume)
    (hg : LocallyIntegrableOn g Ω volume) :
    regularDistribution volume (fun x => f x - g x) (hf.sub hg) =
      regularDistribution volume f hf - regularDistribution volume g hg := by
  ext φ
  change _ = regularDistribution volume f hf φ - regularDistribution volume g hg φ
  simp only [regularDistribution_apply, mul_sub]
  exact integral_sub (integrable_test_mul hf φ) (integrable_test_mul hg φ)

theorem regularDistribution_smul_complex (c : ℝ) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f Ω volume) :
    regularDistribution volume (c • f) (hf.smul c) = c • regularDistribution volume f hf := by
  ext φ
  change _ = c * regularDistribution volume f hf φ
  simp only [regularDistribution_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem upperSemicontinuousWithinAt_of_coe {f : ℂ → ℝ} {s : Set ℂ} {x : ℂ}
    (h : UpperSemicontinuousWithinAt (fun t => (f t : EReal)) s x) :
    UpperSemicontinuousWithinAt f s x := by
  intro y hy
  have := h (y : EReal) (EReal.coe_lt_coe_iff.mpr hy)
  filter_upwards [this] with t ht
  exact EReal.coe_lt_coe_iff.mp ht

/-- The coefficient of the logarithmic pole of a harmonic function on a punctured disc, read
against a cut-off `χ`: `(2π)⁻¹ ∫ ψ Δχ`. -/
def sliceCoeff (ψ χ : ℂ → ℝ) : ℝ := (2 * Real.pi)⁻¹ * ∫ t, ψ t * Δ χ t

/-- **The one-variable decomposition.**  Let `φ₁, φ₂` be locally integrable subharmonic functions
on the disc `D(0, ρ)`, and let `ψ` be harmonic on the punctured disc (`ψ` and `-ψ`
plurisubharmonic there, `ψ` continuous) with `φ₁ = φ₂ + ψ` off `0`.  Then
`ψ = c log |t| + H` off `0` with `H` continuous and harmonic (`H` and `-H` plurisubharmonic) on
the whole disc, where `c = (2π)⁻¹ ∫ ψ Δχ` for any cut-off `χ ≥ 0` equal to `1` near `0` with
support in the disc. -/
theorem exists_harmonic_of_eq_add {ρ : ℝ} {φ₁ φ₂ : ℂ → EReal}
    (hφ₁ : PlurisubharmonicOn φ₁ (ball 0 ρ)) (hφ₂ : PlurisubharmonicOn φ₂ (ball 0 ρ))
    (hi₁ : LocallyIntegrableOn (fun t => (φ₁ t).toReal) (ball 0 ρ) volume)
    (hi₂ : LocallyIntegrableOn (fun t => (φ₂ t).toReal) (ball 0 ρ) volume)
    (hf₁ : ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), φ₁ t ≠ ⊥)
    (hf₂ : ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), φ₂ t ≠ ⊥)
    {ψ : ℂ → ℝ} (hψc : ContinuousOn ψ (ball 0 ρ \ {0}))
    (hψp : PlurisubharmonicOn (fun t => (ψ t : EReal)) (ball 0 ρ \ {0}))
    (hψn : PlurisubharmonicOn (fun t => ((-ψ t : ℝ) : EReal)) (ball 0 ρ \ {0}))
    (heq : ∀ t ∈ ball (0 : ℂ) ρ \ {0}, φ₁ t = φ₂ t + (ψ t : EReal))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball 0 ρ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ᶠ t in 𝓝 (0 : ℂ), χ t = 1) :
    ∃ H : ℂ → ℝ, ContinuousOn H (ball 0 ρ) ∧
      PlurisubharmonicOn (fun t => (H t : EReal)) (ball 0 ρ) ∧
      PlurisubharmonicOn (fun t => ((-H t : ℝ) : EReal)) (ball 0 ρ) ∧
      ∀ t ∈ ball (0 : ℂ) ρ \ {0}, ψ t = sliceCoeff ψ χ * Real.log ‖t‖ + H t := by
  classical
  set Ω : Opens ℂ := ⟨ball 0 ρ, isOpen_ball⟩ with hΩdef
  have hΩc : ((Ω : Set ℂ)) = ball 0 ρ := rfl
  set c : ℝ := sliceCoeff ψ χ with hcdef
  -- `ψ` is almost everywhere the difference of the two potentials
  have hne0 : ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), t ≠ 0 := by
    apply ae_restrict_of_ae
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
  have hψae : (fun t => (φ₁ t).toReal - (φ₂ t).toReal) =ᵐ[volume.restrict (ball (0 : ℂ) ρ)] ψ := by
    filter_upwards [hf₂, hne0, ae_restrict_mem measurableSet_ball] with t h2 h0 hb
    have htop : φ₂ t ≠ ⊤ := (hφ₂ t hb).ne_top
    rw [heq t ⟨hb, h0⟩, ← EReal.coe_toReal htop h2, ← EReal.coe_add, EReal.toReal_coe,
      EReal.toReal_coe]
    ring
  have hψi : LocallyIntegrableOn ψ Ω volume := LocallyIntegrableOn.congr hψae (hi₁.sub hi₂)
  -- the positive Levi distributions of the two potentials
  have hrep : ∀ {φ : ℂ → EReal}, PlurisubharmonicOn φ (ball 0 ρ) →
      ∀ hi : LocallyIntegrableOn (fun t => (φ t).toReal) (ball 0 ρ) volume,
      (∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), φ t ≠ ⊥) →
      PositiveDistribution (distributionalLeviCLM (1 : ℂ)
        (regularDistribution (Ω := Ω) volume (fun t => (φ t).toReal) hi)) := by
    intro φ hφ hi hf
    have hR : IsPshRepresentative volume
        (regularDistribution (Ω := Ω) volume (fun t => (φ t).toReal) hi) φ := by
      refine ⟨hφ, ?_, hi, rfl⟩
      filter_upwards [hf, ae_restrict_mem measurableSet_ball] with t ht hb
      exact ⟨(hφ t hb).ne_top, ht⟩
    exact hR.hasNonnegativeDistributionalLevi 1
  have hP₁ := hrep hφ₁ hi₁ hf₁
  have hP₂ := hrep hφ₂ hi₂ hf₂
  have hψdiff : regularDistribution (Ω := Ω) volume ψ hψi =
      regularDistribution volume (fun t => (φ₁ t).toReal) hi₁ -
        regularDistribution volume (fun t => (φ₂ t).toReal) hi₂ := by
    rw [← regularDistribution_sub_complex]
    exact regularDistribution_congr_ae_on _ _ hψae.symm
  -- the Levi distribution of `ψ` is supported at `0`
  set Ω' : Opens ℂ := ⟨ball 0 ρ \ {0}, isOpen_ball.sdiff isClosed_singleton⟩ with hΩ'def
  have hψi' : LocallyIntegrableOn ψ Ω' volume :=
    hψc.locallyIntegrableOn (isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hψsupp : ∀ φ : 𝓓(Ω, ℝ), (0 : ℂ) ∉ tsupport (φ : ℂ → ℝ) →
      ∫ x, ψ x * Δ (φ : ℂ → ℝ) x = 0 := by
    intro φ hφ0
    have hsub : tsupport (φ : ℂ → ℝ) ⊆ Ω' := fun x hx =>
      ⟨φ.tsupport_subset hx, fun h => hφ0 (by rw [mem_singleton_iff.mp h] at hx; exact hx)⟩
    set φ' : 𝓓(Ω', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hsub⟩ with hφ'def
    have hrep' : ∀ {f : ℂ → ℝ},
        PlurisubharmonicOn (fun t => (f t : EReal)) (ball 0 ρ \ {0}) →
        ∀ hf : LocallyIntegrableOn f Ω' volume,
        PositiveDistribution (distributionalLeviCLM (1 : ℂ)
          (regularDistribution (Ω := Ω') volume f hf)) := by
      intro f hfp hf
      have hR : IsPshRepresentative volume (regularDistribution (Ω := Ω') volume f hf)
          (fun t => (f t : EReal)) := by
        refine ⟨hfp, Eventually.of_forall fun t => ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩,
          ?_, ?_⟩
        · simpa only [EReal.toReal_coe] using hf
        · simp only [EReal.toReal_coe]
      exact hR.hasNonnegativeDistributionalLevi 1
    have hpos := hrep' hψp hψi'
    have hneg := hrep' hψn hψi'.neg
    set D := distributionalLeviCLM (1 : ℂ) (regularDistribution (Ω := Ω') volume ψ hψi')
    have hnegD : PositiveDistribution (-D) := by
      intro θ hθ
      have h := hneg θ hθ
      rw [levi_one_regular_apply] at h
      simp only [D, neg_apply, levi_one_regular_apply]
      have : ∫ x, -ψ x * Δ (θ : ℂ → ℝ) x = -∫ x, ψ x * Δ (θ : ℂ → ℝ) x := by
        rw [← integral_neg]; congr 1; funext x; ring
      rw [this] at h
      linarith
    have hD0 := eq_zero_of_positive_of_neg hpos hnegD
    have h := congrArg (fun T => T φ') hD0
    simp only [D, levi_one_regular_apply, zero_apply] at h
    have hfun : ((φ' : ℂ → ℝ)) = (φ : ℂ → ℝ) := rfl
    rw [hfun] at h
    linarith
  -- the Levi distribution of `log |t|`
  have hlog : LocallyIntegrableOn (fun t : ℂ => Real.log ‖t‖) Ω volume :=
    locallyIntegrableOn_log_norm
  set L₀ := distributionalLeviCLM (1 : ℂ)
    (regularDistribution (Ω := Ω) volume (fun t : ℂ => Real.log ‖t‖) hlog) with hL₀def
  have hL₀ : ∀ φ : 𝓓(Ω, ℝ), L₀ φ = Real.pi / 2 * φ 0 := levi_one_log_apply hlog
  have hL₀pos : PositiveDistribution L₀ := fun φ hφ => by
    rw [hL₀]; exact mul_nonneg (by positivity) (hφ 0)
  set P₁ := distributionalLeviCLM (1 : ℂ)
    (regularDistribution (Ω := Ω) volume (fun t => (φ₁ t).toReal) hi₁) with hP₁def
  set P₂ := distributionalLeviCLM (1 : ℂ)
    (regularDistribution (Ω := Ω) volume (fun t => (φ₂ t).toReal) hi₂) with hP₂def
  set Lψ := distributionalLeviCLM (1 : ℂ) (regularDistribution (Ω := Ω) volume ψ hψi)
    with hLψdef
  have hLψ : Lψ = P₁ - P₂ := by rw [hLψdef, hψdiff, map_sub]
  set Λ : 𝓓'(Ω, ℝ) := Lψ - c • L₀ with hΛdef
  have hΛPQ : Λ = (P₁ + max (-c) 0 • L₀) - (P₂ + max c 0 • L₀) := by
    rw [hΛdef, hLψ]
    ext φ
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    linear_combination (L₀ φ) * max_zero_sub_eq_self c
  have hPpos : PositiveDistribution (P₁ + max (-c) 0 • L₀) := fun φ hφ => by
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_nonneg (hP₁ φ hφ) (mul_nonneg (le_max_right _ _) (hL₀pos φ hφ))
  have hQpos : PositiveDistribution (P₂ + max c 0 • L₀) := fun φ hφ => by
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_nonneg (hP₂ φ hφ) (mul_nonneg (le_max_right _ _) (hL₀pos φ hφ))
  have hΛsupp : ∀ φ : 𝓓(Ω, ℝ), (0 : ℂ) ∉ tsupport (φ : ℂ → ℝ) → Λ φ = 0 := by
    intro φ hφ0
    have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ0
    simp only [hΛdef, sub_apply, smul_apply, smul_eq_mul, hL₀, h0, mul_zero, sub_zero, hLψdef,
      levi_one_regular_apply, hψsupp φ hφ0]
  -- the cut-off as a test function
  set X : 𝓓(Ω, ℝ) := ofSmooth χ hχ hχc hχs with hXdef
  have hX0 : ∀ x, 0 ≤ X x := fun x => hχ0 x
  have hX1 : ∀ᶠ x in 𝓝 (0 : ℂ), X x = 1 := hχ1
  have hχ00 : χ 0 = 1 := hχ1.self_of_nhds
  have hint : ∫ t, ψ t * Δ χ t = 2 * Real.pi * c := by
    rw [hcdef, sliceCoeff]; field_simp
  have hΛX : Λ X = 0 := by
    simp only [hΛdef, sub_apply, smul_apply, smul_eq_mul, hL₀, hLψdef, levi_one_regular_apply]
    have h1 : ((X : ℂ → ℝ)) = χ := rfl
    rw [h1, hint]
    simp only [hχ00]
    ring
  have hΛ0 : Λ = 0 := by
    ext φ
    rw [eq_mul_apply_of_support_zero hPpos hQpos hΛPQ hΛsupp X hX0 hX1 φ, hΛX, mul_zero]
    rfl
  -- the harmonic remainder `F = ψ - c log |t|`
  have hlogc : LocallyIntegrableOn (c • fun t : ℂ => Real.log ‖t‖) Ω volume := hlog.smul c
  set F : ℂ → ℝ := fun t => ψ t - (c • fun t : ℂ => Real.log ‖t‖) t with hFdef
  have hFi : LocallyIntegrableOn F Ω volume := hψi.sub hlogc
  have hFdist : regularDistribution (Ω := Ω) volume F hFi =
      regularDistribution volume ψ hψi - c • regularDistribution volume
        (fun t : ℂ => Real.log ‖t‖) hlog := by
    have h := regularDistribution_sub_complex hψi hlogc
    rw [regularDistribution_smul_complex] at h
    exact h
  have hF0 : distributionalLeviCLM (1 : ℂ) (regularDistribution (Ω := Ω) volume F hFi) = 0 := by
    rw [hFdist, map_sub, map_smul]
    exact hΛ0
  have hFnn : HasNonnegativeDistributionalLevi (regularDistribution (Ω := Ω) volume F hFi) :=
    hasNonnegativeDistributionalLevi_of_levi_one hFi (by rw [hF0]; intro φ _; simp)
  set G : ℂ → ℝ := (-1 : ℝ) • F with hGdef
  have hGi : LocallyIntegrableOn G Ω volume := hFi.smul (-1 : ℝ)
  have hG0 : distributionalLeviCLM (1 : ℂ) (regularDistribution (Ω := Ω) volume G hGi) = 0 := by
    have h := regularDistribution_smul_complex (-1 : ℝ) hFi
    rw [show regularDistribution (Ω := Ω) volume G hGi = _ from h, map_smul, hF0, smul_zero]
  have hGnn : HasNonnegativeDistributionalLevi (regularDistribution (Ω := Ω) volume G hGi) :=
    hasNonnegativeDistributionalLevi_of_levi_one hGi (by rw [hG0]; intro φ _; simp)
  obtain ⟨H₁, hH₁p, hH₁f, hH₁i, hH₁e⟩ :=
    (hasNonnegativeDistributionalLevi_iff_exists_pshRepresentative volume _).mp hFnn
  obtain ⟨H₂, hH₂p, hH₂f, hH₂i, hH₂e⟩ :=
    (hasNonnegativeDistributionalLevi_iff_exists_pshRepresentative volume _).mp hGnn
  have hFae := ae_eq_of_regularDistribution_eq volume hFi hH₁i hH₁e
  have hGae := ae_eq_of_regularDistribution_eq volume hGi hH₂i hH₂e
  have hsumae : (fun t => H₁ t + H₂ t) =ᵐ[volume.restrict (Ω : Set ℂ)] fun _ => (0 : EReal) := by
    filter_upwards [hFae, hGae, hH₁f, hH₂f] with t h1 h2 hf1 hf2
    rw [← EReal.coe_toReal hf1.1 hf1.2, ← EReal.coe_toReal hf2.1 hf2.2, ← h1, ← h2,
      ← EReal.coe_add]
    simp [hGdef]
  have hsum : EqOn (fun t => H₁ t + H₂ t) (fun _ => (0 : EReal)) (Ω : Set ℂ) :=
    SGPT.Foundations.Analysis.PlurisubharmonicOn.eqOn_of_ae_eq (hH₁p.add hH₂p)
      (fun x _ => plurisubharmonicAt_const 0 EReal.zero_ne_top x) Ω.isOpen volume hsumae
  have hfin : ∀ t ∈ (Ω : Set ℂ), H₁ t ≠ ⊥ ∧ H₂ t ≠ ⊥ := by
    intro t ht
    have h := hsum ht
    simp only at h
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · rw [hb, EReal.bot_add] at h; exact EReal.bot_ne_zero h
    · rw [hb, EReal.add_bot] at h; exact EReal.bot_ne_zero h
  set H : ℂ → ℝ := fun t => (H₁ t).toReal with hHdef
  have hHcoe : ∀ t ∈ (Ω : Set ℂ), (H t : EReal) = H₁ t := fun t ht =>
    EReal.coe_toReal ((hH₁p t ht).ne_top) (hfin t ht).1
  have hHneg : ∀ t ∈ (Ω : Set ℂ), ((-H t : ℝ) : EReal) = H₂ t := by
    intro t ht
    have h := hsum ht
    simp only at h
    have h2 : H₂ t = ((H₂ t).toReal : EReal) :=
      (EReal.coe_toReal ((hH₂p t ht).ne_top) (hfin t ht).2).symm
    rw [← hHcoe t ht, h2, ← EReal.coe_add] at h
    have h' : H t + (H₂ t).toReal = 0 := by exact_mod_cast h
    rw [h2]
    congr 1
    linarith
  have hHp : PlurisubharmonicOn (fun t => (H t : EReal)) (ball 0 ρ) := fun x hx =>
    (hH₁p x hx).congr (by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hHcoe y hy).symm)
  have hHn : PlurisubharmonicOn (fun t => ((-H t : ℝ) : EReal)) (ball 0 ρ) := fun x hx =>
    (hH₂p x hx).congr (by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hHneg y hy).symm)
  have hHc : ContinuousOn H (ball 0 ρ) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    rw [continuousAt_iff_lower_upperSemicontinuousAt]
    constructor
    · intro y hy
      have hu := (hHn x hx).upperSemicontinuousAt ((-y : ℝ) : EReal)
        (EReal.coe_lt_coe_iff.mpr (by linarith))
      filter_upwards [hu] with t ht
      have := EReal.coe_lt_coe_iff.mp ht
      linarith
    · intro y hy
      have hu := (hHp x hx).upperSemicontinuousAt (y : EReal) (EReal.coe_lt_coe_iff.mpr hy)
      filter_upwards [hu] with t ht
      exact EReal.coe_lt_coe_iff.mp ht
  have hFc : ContinuousOn F (ball 0 ρ \ {0}) := by
    have hl : ContinuousOn (fun t : ℂ => c * Real.log ‖t‖) (ball 0 ρ \ {0}) := by
      refine continuousOn_const.mul (ContinuousOn.log continuous_norm.continuousOn ?_)
      intro t ht
      exact norm_ne_zero_iff.mpr ht.2
    exact hψc.sub hl
  have hFH : EqOn F H (ball 0 ρ \ {0}) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sdiff_subset hFae)
      (isOpen_ball.sdiff isClosed_singleton) hFc (hHc.mono sdiff_subset)
  refine ⟨H, hHc, hHp, hHn, fun t ht => ?_⟩
  have := hFH ht
  simp only [hFdef, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- **The bound on a closed disc.**  In the situation of `exists_harmonic_of_eq_add`, the
function `ψ - c log |t|` is bounded on a punctured closed disc by its bound on the boundary
circle. -/
theorem abs_sub_le_of_eq_add {ρ : ℝ} {φ₁ φ₂ : ℂ → EReal}
    (hφ₁ : PlurisubharmonicOn φ₁ (ball 0 ρ)) (hφ₂ : PlurisubharmonicOn φ₂ (ball 0 ρ))
    (hi₁ : LocallyIntegrableOn (fun t => (φ₁ t).toReal) (ball 0 ρ) volume)
    (hi₂ : LocallyIntegrableOn (fun t => (φ₂ t).toReal) (ball 0 ρ) volume)
    (hf₁ : ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), φ₁ t ≠ ⊥)
    (hf₂ : ∀ᵐ t ∂volume.restrict (ball (0 : ℂ) ρ), φ₂ t ≠ ⊥)
    {ψ : ℂ → ℝ} (hψc : ContinuousOn ψ (ball 0 ρ \ {0}))
    (hψp : PlurisubharmonicOn (fun t => (ψ t : EReal)) (ball 0 ρ \ {0}))
    (hψn : PlurisubharmonicOn (fun t => ((-ψ t : ℝ) : EReal)) (ball 0 ρ \ {0}))
    (heq : ∀ t ∈ ball (0 : ℂ) ρ \ {0}, φ₁ t = φ₂ t + (ψ t : EReal))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball 0 ρ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ᶠ t in 𝓝 (0 : ℂ), χ t = 1)
    {r C : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hC : ∀ t ∈ sphere (0 : ℂ) r, |ψ t - sliceCoeff ψ χ * Real.log ‖t‖| ≤ C) :
    ∀ t ∈ closedBall (0 : ℂ) r, t ≠ 0 → |ψ t - sliceCoeff ψ χ * Real.log ‖t‖| ≤ C := by
  obtain ⟨H, -, hHp, hHn, hψH⟩ := exists_harmonic_of_eq_add hφ₁ hφ₂ hi₁ hi₂ hf₁ hf₂ hψc hψp
    hψn heq hχ hχc hχs hχ0 hχ1
  have hD : closedBall (0 : ℂ) r ⊆ ball 0 ρ := closedBall_subset_ball hrρ
  have hsph : ∀ t ∈ sphere (0 : ℂ) r, t ∈ ball (0 : ℂ) ρ \ {0} := by
    intro t ht
    refine ⟨hD (sphere_subset_closedBall ht), fun h0 => ?_⟩
    rw [mem_singleton_iff.mp h0, mem_sphere, dist_self] at ht
    linarith
  have hup := SGPT.Foundations.Analysis.PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere
    hHp hr hD (C := C) (fun t ht => by
      have := hC t ht
      rw [hψH t (hsph t ht)] at this
      exact EReal.coe_le_coe_iff.mpr (by rw [abs_le] at this; linarith))
  have hlo := SGPT.Foundations.Analysis.PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere
    hHn hr hD (C := C) (fun t ht => by
      have := hC t ht
      rw [hψH t (hsph t ht)] at this
      exact EReal.coe_le_coe_iff.mpr (by rw [abs_le] at this; linarith))
  intro t ht ht0
  have h1 := EReal.coe_le_coe_iff.mp (hup t ht)
  have h2 := EReal.coe_le_coe_iff.mp (hlo t ht)
  rw [hψH t ⟨hD ht, ht0⟩]
  rw [abs_le]
  constructor <;> linarith

end Decomposition

end SGPT.Currents.AnalyticSupport
