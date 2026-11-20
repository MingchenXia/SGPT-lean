import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Laurent expansions on Reinhardt domains via Fourier series on the torus

Infrastructure of lane SERRE-PN2 (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), plan node PN6 of `claude-serre-pn.tex`: the
analytic part of the computation of `H^q(ℙᴺ, 𝒪(n))` by Laurent series.

The torus `T = (ℝ/ℤ)^d` acts on `ℂ^d` by `w ↦ w · e(x)`, `e(x)_k = exp(2πi x_k)` (`tpt`). For a
function `f` and a point `w`, `tcoeff f w α` is the `α`-th Fourier coefficient of
`x ↦ f(w · e(x))` (Mathlib's `mFourierCoeff`, Haar probability measure on the torus).

* `differentiableOn_tcoeff`: if `f` is holomorphic on `U` and the torus orbits of the points of
  an open `Ω` lie in `U`, then `w ↦ tcoeff f w α` is holomorphic on `Ω` (differentiation under
  the integral sign).
* `tcoeff_tpt`: `tcoeff f (w · e(y)) α = e(α · y) tcoeff f w α` (translation invariance of the
  Haar measure). Hence `H(w) = tcoeff f w α · w^{-α}` is invariant under the torus, so its
  derivative vanishes at points with nonzero coordinates (`fderiv_eq_zero_of_torus_invariant`),
  and it is constant on convex sets of radii (`eq_of_torus_invariant`): **the Laurent
  coefficient does not depend on the radius**.
* `laurent_core`: let `S` be an open convex set of positive radii such that every point `z`
  with `(|z_k|)_k ∈ S` lies in the domain `U` of the holomorphic function `f`. Then there are
  coefficients `C_α` with `‖C_α‖ r^α ≤ sup_{|z| = r} |f|` and `∑_α ‖C_α‖ r^α < ∞` for every
  `r ∈ S` (Cauchy estimates at the radii `r λ^{±1}`), and `f(z) = ∑_α C_α z^α` for every `z`
  with `(|z_k|)_k ∈ S` (Fourier inversion on the torus `|z| = r`, Mathlib's
  `hasSum_mFourier_series_apply_of_summable`).

Blueprint: `claude-serre-pn2.tex`, node `claude-serre-pn2:laurent-core`.
-/

set_option autoImplicit false

open MeasureTheory UnitAddTorus Set Filter Topology Metric Complex
open scoped Real

noncomputable section

namespace SGPT.GAGA.PN

/-! ### The torus and its action on `ℂ^d` -/

/-- The Haar probability measure on the torus `(ℝ/ℤ)^d` (the measure of `mFourierCoeff`). -/
abbrev torusMeasure (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi fun _ => AddCircle.haarAddCircle

theorem fourier_one_add (s t : UnitAddCircle) :
    fourier 1 (s + t) = fourier 1 s * fourier 1 t := by
  simp only [fourier_one, AddCircle.toCircle_add, Circle.coe_mul]

theorem norm_fourier_one (t : UnitAddCircle) : ‖fourier 1 t‖ = 1 := by
  rw [fourier_one]
  exact Circle.norm_coe _

theorem fourier_one_zpow (t : UnitAddCircle) (m : ℤ) : fourier 1 t ^ m = fourier m t := by
  rw [fourier_one, fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

theorem fourier_one_ne_zero (t : UnitAddCircle) : fourier 1 t ≠ 0 := by
  intro h
  have := norm_fourier_one t
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem fourier_one_coe (x : ℝ) : fourier 1 (x : UnitAddCircle) = exp (2 * π * I * x) := by
  rw [fourier_coe_apply]
  push_cast
  ring_nf

variable {d : ℕ}

/-- The action of the torus on `ℂ^d`: `tpt w x = (w_k e^{2πi x_k})_k`. -/
def tpt (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun k => w k * fourier 1 (x k)

@[simp] theorem tpt_apply (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) (k : Fin d) :
    tpt w x k = w k * fourier 1 (x k) :=
  rfl

theorem tpt_add (w : EuclideanSpace ℂ (Fin d)) (x y : UnitAddTorus (Fin d)) :
    tpt w (x + y) = tpt (tpt w x) y := by
  ext k
  simp only [tpt_apply, Pi.add_apply, fourier_one_add]
  ring

theorem norm_tpt_apply (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) (k : Fin d) :
    ‖tpt w x k‖ = ‖w k‖ := by
  rw [tpt_apply, norm_mul, norm_fourier_one, mul_one]

theorem norm_tpt (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) :
    ‖tpt w x‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_tpt_apply]

theorem tpt_smul (c : ℂ) (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) :
    tpt (c • w) x = c • tpt w x := by
  ext k
  simp only [tpt_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem continuous_tpt :
    Continuous fun p : EuclideanSpace ℂ (Fin d) × UnitAddTorus (Fin d) => tpt p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  exact ((EuclideanSpace.proj k).continuous.comp continuous_fst).mul
    ((fourier 1).continuous.comp ((continuous_apply k).comp continuous_snd))

theorem continuous_tpt_right (w : EuclideanSpace ℂ (Fin d)) : Continuous (tpt w) :=
  continuous_tpt.comp (continuous_const.prodMk continuous_id)

/-- `w ↦ tpt w x` as a continuous linear map. -/
def tptL (x : UnitAddTorus (Fin d)) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => tpt w x
      map_add' := fun w w' => by
        ext k
        simp only [tpt_apply, PiLp.add_apply]
        ring
      map_smul' := fun c w => tpt_smul c w x }

theorem tptL_apply (x : UnitAddTorus (Fin d)) (w : EuclideanSpace ℂ (Fin d)) :
    tptL x w = tpt w x :=
  rfl

theorem norm_tptL_le (x : UnitAddTorus (Fin d)) : ‖tptL x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [tptL_apply, norm_tpt, one_mul]

theorem continuous_tptL : Continuous (tptL (d := d)) :=
  continuous_clm_apply.2 fun _ => continuous_tpt.comp (continuous_const.prodMk continuous_id)

/-! ### Monomials and characters -/

/-- The Laurent monomial `z^α = ∏_k z_k^{α_k}`, `α ∈ ℤ^d`. -/
def mono (α : Fin d → ℤ) (z : EuclideanSpace ℂ (Fin d)) : ℂ :=
  ∏ k, z k ^ α k

/-- The real monomial `r^α = ∏_k r_k^{α_k}`. -/
def rmono (α : Fin d → ℤ) (r : Fin d → ℝ) : ℝ :=
  ∏ k, r k ^ α k

theorem mono_tpt (α : Fin d → ℤ) (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) :
    mono α (tpt w x) = mono α w * mFourier α x := by
  simp only [mono, tpt_apply, mul_zpow, Finset.prod_mul_distrib, fourier_one_zpow]
  rfl

theorem mono_neg_mul {α : Fin d → ℤ} {w : EuclideanSpace ℂ (Fin d)} (hw : ∀ k, w k ≠ 0) :
    mono (-α) w * mono α w = 1 := by
  simp only [mono, ← Finset.prod_mul_distrib, Pi.neg_apply]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← zpow_add₀ (hw k), neg_add_cancel, zpow_zero]

theorem mFourier_add_apply (α : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier α (x + y) = mFourier α x * mFourier α y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_neg_mul (α : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    mFourier (-α) x * mFourier α x = 1 := by
  rw [← mFourier_add, neg_add_cancel, mFourier_zero, ContinuousMap.one_apply]

theorem mFourier_neg_neg (α : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
    mFourier (-α) (-y) = mFourier α y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, neg_smul_neg]

theorem norm_mFourier_apply_le (α : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    ‖mFourier α x‖ ≤ 1 :=
  (ContinuousMap.norm_coe_le_norm _ x).trans mFourier_norm.le

/-! ### Fourier coefficients along torus orbits -/

/-- The `α`-th Fourier coefficient of `f` along the torus orbit of `w`. -/
def tcoeff (f : EuclideanSpace ℂ (Fin d) → ℂ) (w : EuclideanSpace ℂ (Fin d)) (α : Fin d → ℤ) :
    ℂ :=
  mFourierCoeff (fun x => f (tpt w x)) α

theorem tcoeff_eq (f : EuclideanSpace ℂ (Fin d) → ℂ) (w : EuclideanSpace ℂ (Fin d))
    (α : Fin d → ℤ) :
    tcoeff f w α = ∫ x, mFourier (-α) x • f (tpt w x) ∂torusMeasure d :=
  rfl

/-- **Translation**: `tcoeff f (w · e(y)) α = e(α y) · tcoeff f w α`. -/
theorem tcoeff_tpt (f : EuclideanSpace ℂ (Fin d) → ℂ) (w : EuclideanSpace ℂ (Fin d))
    (y : UnitAddTorus (Fin d)) (α : Fin d → ℤ) :
    tcoeff f (tpt w y) α = mFourier α y * tcoeff f w α := by
  set g : UnitAddTorus (Fin d) → ℂ := fun x => mFourier (-α) (x - y) • f (tpt w x) with hg
  have h1 : tcoeff f (tpt w y) α = ∫ x, g (x + y) ∂torusMeasure d := by
    rw [tcoeff_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hg, add_sub_cancel_right, ← tpt_add, add_comm y x]
  rw [h1, integral_add_right_eq_self g y, tcoeff_eq, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hg, sub_eq_add_neg, mFourier_add_apply, mFourier_neg_neg, smul_eq_mul]
  ring

theorem norm_tcoeff_le {f : EuclideanSpace ℂ (Fin d) → ℂ} {w : EuclideanSpace ℂ (Fin d)} {M : ℝ}
    (h : ∀ x, ‖f (tpt w x)‖ ≤ M) (α : Fin d → ℤ) : ‖tcoeff f w α‖ ≤ M := by
  rw [tcoeff_eq]
  have h' := norm_integral_le_of_norm_le_const (μ := torusMeasure d)
    (f := fun x => mFourier (-α) x • f (tpt w x)) (C := M) (ae_of_all _ fun x => by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_apply_le _ x)).trans (h x))
  simpa using h'

theorem tcoeff_smul_real (f : EuclideanSpace ℂ (Fin d) → ℂ) (w : EuclideanSpace ℂ (Fin d))
    (c b : ℂ) (hf : ∀ x, f (c • tpt w x) = b * f (tpt w x)) (α : Fin d → ℤ) :
    tcoeff f (c • w) α = b * tcoeff f w α := by
  rw [tcoeff_eq, tcoeff_eq, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [tpt_smul, hf, smul_eq_mul]
  ring

/-- **Differentiation under the integral sign**: the Fourier coefficients along torus orbits of
a holomorphic function are holomorphic in the base point. -/
theorem differentiableOn_tcoeff {f : EuclideanSpace ℂ (Fin d) → ℂ}
    {U Ω : Set (EuclideanSpace ℂ (Fin d))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hΩ : IsOpen Ω) (hΩU : ∀ w ∈ Ω, ∀ x, tpt w x ∈ U) (α : Fin d → ℤ) :
    DifferentiableOn ℂ (fun w => tcoeff f w α) Ω := by
  intro w₀ hw₀
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := Metric.isOpen_iff.1 hΩ w₀ hw₀
  set r : ℝ := r₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall w₀ r ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hr₀Ω
  set K := (fun p : EuclideanSpace ℂ (Fin d) × UnitAddTorus (Fin d) => tpt p.1 p.2) ''
    (closedBall w₀ r ×ˢ univ)
  have hKc : IsCompact K :=
    ((isCompact_closedBall w₀ r).prod isCompact_univ).image continuous_tpt
  have hKU : K ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hΩU p.1 (hcb hp.1) p.2
  have hda : ContinuousOn (fderiv ℂ f) U :=
    (SGPT.Foundations.Analysis.FirstPass.contDiffOn_of_differentiableOn_complex hf hU
      ).continuousOn_fderiv_of_isOpen hU (by simp)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hda.mono hKU)
  set F : EuclideanSpace ℂ (Fin d) → UnitAddTorus (Fin d) → ℂ :=
    fun w x => mFourier (-α) x • f (tpt w x) with hFdef
  set F' : EuclideanSpace ℂ (Fin d) → UnitAddTorus (Fin d) →
      (EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ) :=
    fun w x => mFourier (-α) x • (fderiv ℂ f (tpt w x)).comp (tptL x) with hF'def
  have hFc : ∀ w ∈ Ω, Continuous (F w) := fun w hw =>
    (mFourier (-α)).continuous.smul (hf.continuousOn.comp_continuous (continuous_tpt_right w)
      fun x => hΩU w hw x)
  have hF'c : Continuous (F' w₀) :=
    (mFourier (-α)).continuous.smul ((hda.comp_continuous (continuous_tpt_right w₀)
      fun x => hΩU w₀ hw₀ x).clm_comp continuous_tptL)
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := torusMeasure d)
    (F := F) (F' := F') (x₀ := w₀) (s := ball w₀ r) (bound := fun _ => B)
    (ball_mem_nhds w₀ hr0)
    (eventually_of_mem (ball_mem_nhds w₀ hr0) fun w hw =>
      (hFc w (hcb (ball_subset_closedBall hw))).aestronglyMeasurable)
    ((hFc w₀ hw₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hF'c.aestronglyMeasurable
    (ae_of_all _ fun x w hw => by
      have hK : tpt w x ∈ K := ⟨(w, x), ⟨ball_subset_closedBall hw, mem_univ _⟩, rfl⟩
      simp only [hF'def, norm_smul]
      calc ‖mFourier (-α) x‖ * ‖(fderiv ℂ f (tpt w x)).comp (tptL x)‖
          ≤ 1 * (B * 1) := by
            refine mul_le_mul (norm_mFourier_apply_le _ x) ?_ (norm_nonneg _) zero_le_one
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul (hB _ hK) (norm_tptL_le x) (norm_nonneg _)
                ((norm_nonneg _).trans (hB _ hK)))
        _ = B := by ring)
    (integrable_const B)
    (ae_of_all _ fun x w hw => by
      have hwU : tpt w x ∈ U := hΩU w (hcb (ball_subset_closedBall hw)) x
      have hd := ((hf.differentiableAt (hU.mem_nhds hwU)).hasFDerivAt.comp w
        (tptL x).hasFDerivAt).const_smul (mFourier (-α) x)
      exact hd)
  exact hderiv.differentiableAt.differentiableWithinAt

/-! ### Torus-invariant functions are constant along radii -/

theorem tpt_single (w : EuclideanSpace ℂ (Fin d)) (k : Fin d) (t : ℝ) :
    tpt w (Pi.single k (t : UnitAddCircle)) =
      w + (w k * (exp (2 * π * I * t) - 1)) • EuclideanSpace.single k (1 : ℂ) := by
  ext j
  by_cases hj : j = k
  · subst hj
    simp only [tpt_apply, Pi.single_eq_same, fourier_one_coe, PiLp.add_apply, PiLp.smul_apply,
      PiLp.single_apply, if_true, smul_eq_mul, mul_one]
    ring
  · simp only [tpt_apply, Pi.single_eq_of_ne hj, fourier_eval_zero, PiLp.add_apply,
      PiLp.smul_apply, PiLp.single_apply, hj, if_false, smul_eq_mul, mul_zero,
      add_zero, mul_one]

theorem hasDerivAt_tpt_single (w : EuclideanSpace ℂ (Fin d)) (k : Fin d) :
    HasDerivAt
      (fun t : ℝ => w + (w k * (exp (2 * π * I * t) - 1)) • EuclideanSpace.single k (1 : ℂ))
      ((w k * (2 * π * I)) • EuclideanSpace.single k (1 : ℂ)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => exp (2 * π * I * t)) (2 * π * I) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (2 * π * I)).cexp
    simpa using this
  have h2 := ((h1.sub_const 1).const_mul (w k)).smul_const (EuclideanSpace.single k (1 : ℂ))
  exact h2.const_add w

/-- **A torus-invariant function has vanishing derivative** at points with nonzero
coordinates. -/
theorem fderiv_eq_zero_of_torus_invariant {H : EuclideanSpace ℂ (Fin d) → ℂ}
    {w : EuclideanSpace ℂ (Fin d)} (hH : DifferentiableAt ℂ H w) (hw : ∀ k, w k ≠ 0)
    (hinv : ∀ y, H (tpt w y) = H w) : fderiv ℂ H w = 0 := by
  have hk : ∀ k, fderiv ℂ H w (EuclideanSpace.single k 1) = 0 := by
    intro k
    have hγ := hasDerivAt_tpt_single w k
    have hc := (hH.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hγ
      (by simp)
    have hconst : (H ∘ fun t : ℝ =>
        w + (w k * (exp (2 * π * I * t) - 1)) • EuclideanSpace.single k (1 : ℂ)) =
        fun _ => H w := by
      funext t
      simp only [Function.comp_apply, ← tpt_single, hinv]
    rw [hconst] at hc
    have h0 := hc.unique (hasDerivAt_const (0 : ℝ) (H w))
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul] at h0
    have hne : w k * (2 * π * I) ≠ 0 :=
      mul_ne_zero (hw k) (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))
        I_ne_zero)
    exact (mul_eq_zero.1 h0).resolve_left hne
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ k, v k • EuclideanSpace.single k (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp [hk]

/-- The point with real coordinates `r_k`. -/
def rpt (r : Fin d → ℝ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun k => (r k : ℂ)

@[simp] theorem rpt_apply (r : Fin d → ℝ) (k : Fin d) : rpt r k = r k :=
  rfl

/-- `rpt` as a real linear map. -/
def rptL : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := rpt
      map_add' := fun r r' => by
        ext k
        simp
      map_smul' := fun c r => by
        ext k
        simp [Complex.real_smul] }

/-- **Constancy along radii.** A function which is holomorphic at the points `rpt r`, `r ∈ S`
(a convex set of positive radii), and invariant under the torus there, takes the same value at
all of them. -/
theorem eq_of_torus_invariant {H : EuclideanSpace ℂ (Fin d) → ℂ} {S : Set (Fin d → ℝ)}
    (hS : Convex ℝ S) (hpos : ∀ r ∈ S, ∀ k, 0 < r k)
    (hH : ∀ r ∈ S, DifferentiableAt ℂ H (rpt r))
    (hinv : ∀ r ∈ S, ∀ y, H (tpt (rpt r) y) = H (rpt r)) {r r' : Fin d → ℝ}
    (hr : r ∈ S) (hr' : r' ∈ S) : H (rpt r') = H (rpt r) := by
  have hd : ∀ x ∈ S, HasFDerivAt (fun x => H (rpt x)) (0 : (Fin d → ℝ) →L[ℝ] ℂ) x := by
    intro x hx
    have h0 : fderiv ℂ H (rpt x) = 0 :=
      fderiv_eq_zero_of_torus_invariant (hH x hx)
        (fun k => by simpa using (hpos x hx k).ne') (hinv x hx)
    have h1 := ((hH x hx).hasFDerivAt.restrictScalars ℝ).comp x rptL.hasFDerivAt
    rw [h0] at h1
    simp only [ContinuousLinearMap.restrictScalars_zero, ContinuousLinearMap.zero_comp] at h1
    exact h1
  have := hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => H (rpt x)) (C := 0)
    (fun x hx => (hd x hx).differentiableAt) (fun x hx => by rw [(hd x hx).fderiv]; simp)
    hr hr'
  have h2 : ‖H (rpt r') - H (rpt r)‖ ≤ 0 := by simpa using this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-! ### Laurent expansions on Reinhardt domains -/

/-- The radii `(|z_k|)_k` of a point. -/
def radii (z : EuclideanSpace ℂ (Fin d)) : Fin d → ℝ :=
  fun k => ‖z k‖

theorem continuous_radii : Continuous (radii (d := d)) :=
  continuous_pi fun k => (EuclideanSpace.proj k).continuous.norm

theorem radii_tpt (w : EuclideanSpace ℂ (Fin d)) (x : UnitAddTorus (Fin d)) :
    radii (tpt w x) = radii w :=
  funext fun k => norm_tpt_apply w x k

theorem radii_rpt {r : Fin d → ℝ} (hr : ∀ k, 0 ≤ r k) : radii (rpt r) = r :=
  funext fun k => by simp [radii, abs_of_nonneg (hr k)]

/-- Every point is on the torus orbit of the point of its radii. -/
theorem tpt_radii_arg (z : EuclideanSpace ℂ (Fin d)) :
    tpt (rpt (radii z)) (fun k => ((arg (z k) / (2 * π) : ℝ) : UnitAddCircle)) = z := by
  ext k
  rw [tpt_apply, fourier_one_coe, rpt_apply]
  conv_rhs => rw [← norm_mul_exp_arg_mul_I (z k)]
  congr 2
  push_cast
  field_simp

theorem norm_mono_rpt (α : Fin d → ℤ) {r : Fin d → ℝ} (hr : ∀ k, 0 < r k) :
    ‖mono α (rpt r)‖ = rmono α r := by
  simp only [mono, rmono, rpt_apply, norm_prod, norm_zpow, Complex.norm_real, Real.norm_eq_abs]
  exact Finset.prod_congr rfl fun k _ => by rw [abs_of_pos (hr k)]

theorem rmono_pos (α : Fin d → ℤ) {r : Fin d → ℝ} (hr : ∀ k, 0 < r k) : 0 < rmono α r :=
  Finset.prod_pos fun k _ => zpow_pos (hr k) _

theorem differentiableAt_mono (α : Fin d → ℤ) {w : EuclideanSpace ℂ (Fin d)}
    (hw : ∀ k, w k ≠ 0) : DifferentiableAt ℂ (mono α) w := by
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      DifferentiableAt ℂ (fun z : EuclideanSpace ℂ (Fin d) => z k ^ α k) w := fun k _ =>
    (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).differentiableAt.zpow
      (Or.inl (hw k))
  exact (HasFDerivAt.finsetProd fun k hk' => (hk k hk').hasFDerivAt).differentiableAt

/-- A *Reinhardt domain description* of `U`: an open convex set `S` of positive radii such
that every point with radii in `S` lies in `U`. -/
structure IsReinhardtIn (U : Set (EuclideanSpace ℂ (Fin d))) (S : Set (Fin d → ℝ)) : Prop where
  isOpen : IsOpen S
  convex : Convex ℝ S
  pos : ∀ r ∈ S, ∀ k, 0 < r k
  sub : ∀ z, radii z ∈ S → z ∈ U

/-- The Laurent coefficient of `f` computed on the torus of radius `r₀`. -/
def lcoeffAt (f : EuclideanSpace ℂ (Fin d) → ℂ) (r₀ : Fin d → ℝ) (α : Fin d → ℤ) : ℂ :=
  tcoeff f (rpt r₀) α * mono (-α) (rpt r₀)

section Reinhardt

variable {f : EuclideanSpace ℂ (Fin d) → ℂ} {U : Set (EuclideanSpace ℂ (Fin d))}
  {S : Set (Fin d → ℝ)} {r₀ : Fin d → ℝ}

theorem IsReinhardtIn.rpt_ne_zero (hS : IsReinhardtIn U S) {r : Fin d → ℝ} (hr : r ∈ S)
    (k : Fin d) : rpt r k ≠ 0 := by
  simpa using (hS.pos r hr k).ne'

theorem IsReinhardtIn.tpt_mem (hS : IsReinhardtIn U S) {r : Fin d → ℝ} (hr : r ∈ S)
    (x : UnitAddTorus (Fin d)) : tpt (rpt r) x ∈ U :=
  hS.sub _ (by rw [radii_tpt, radii_rpt fun k => (hS.pos r hr k).le]; exact hr)

/-- **The Laurent coefficient does not depend on the radius.** -/
theorem tcoeff_eq_lcoeffAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hS : IsReinhardtIn U S) (hr₀ : r₀ ∈ S) {r : Fin d → ℝ} (hr : r ∈ S) (α : Fin d → ℤ) :
    tcoeff f (rpt r) α = lcoeffAt f r₀ α * mono α (rpt r) := by
  set Ω : Set (EuclideanSpace ℂ (Fin d)) := {w | radii w ∈ S} with hΩdef
  have hΩ : IsOpen Ω := hS.isOpen.preimage continuous_radii
  have hΩU : ∀ w ∈ Ω, ∀ x, tpt w x ∈ U := fun w hw x =>
    hS.sub _ (by rw [radii_tpt]; exact hw)
  have htc := differentiableOn_tcoeff hU hf hΩ hΩU α
  set H : EuclideanSpace ℂ (Fin d) → ℂ := fun w => tcoeff f w α * mono (-α) w with hHdef
  have hrpt : ∀ r ∈ S, rpt r ∈ Ω := fun r hr => by
    show radii (rpt r) ∈ S
    rw [radii_rpt fun k => (hS.pos r hr k).le]
    exact hr
  have hH : ∀ r ∈ S, DifferentiableAt ℂ H (rpt r) := fun r hr =>
    ((htc _ (hrpt r hr)).differentiableAt (hΩ.mem_nhds (hrpt r hr))).mul
      (differentiableAt_mono _ (hS.rpt_ne_zero hr))
  have hinv : ∀ r ∈ S, ∀ y, H (tpt (rpt r) y) = H (rpt r) := by
    intro r hr y
    simp only [hHdef, tcoeff_tpt, mono_tpt]
    calc mFourier α y * tcoeff f (rpt r) α * (mono (-α) (rpt r) * mFourier (-α) y)
        = tcoeff f (rpt r) α * mono (-α) (rpt r) * (mFourier (-α) y * mFourier α y) := by ring
      _ = tcoeff f (rpt r) α * mono (-α) (rpt r) := by rw [mFourier_neg_mul, mul_one]
  have hconst := eq_of_torus_invariant hS.convex hS.pos hH hinv hr₀ hr
  calc tcoeff f (rpt r) α = H (rpt r) * mono α (rpt r) := by
        simp only [hHdef, mul_assoc, mono_neg_mul (hS.rpt_ne_zero hr), mul_one]
    _ = lcoeffAt f r₀ α * mono α (rpt r) := by rw [hconst]; rfl

/-- **Cauchy estimate**: `‖C_α‖ r^α ≤ sup_{|z| = r} |f|`. -/
theorem norm_lcoeffAt_mul_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hS : IsReinhardtIn U S) (hr₀ : r₀ ∈ S) {r : Fin d → ℝ} (hr : r ∈ S) {M : ℝ}
    (hM : ∀ x, ‖f (tpt (rpt r) x)‖ ≤ M) (α : Fin d → ℤ) :
    ‖lcoeffAt f r₀ α‖ * rmono α r ≤ M := by
  have h1 := norm_tcoeff_le hM α
  rwa [tcoeff_eq_lcoeffAt hU hf hS hr₀ hr, norm_mul, norm_mono_rpt α (hS.pos r hr)] at h1

theorem continuous_comp_tpt (hf : DifferentiableOn ℂ f U) (hS : IsReinhardtIn U S)
    {r : Fin d → ℝ} (hr : r ∈ S) : Continuous fun x => f (tpt (rpt r) x) :=
  hf.continuousOn.comp_continuous (continuous_tpt_right _) fun x => hS.tpt_mem hr x

theorem exists_bound_torus (hf : DifferentiableOn ℂ f U) (hS : IsReinhardtIn U S)
    {r : Fin d → ℝ} (hr : r ∈ S) : ∃ M, ∀ x, ‖f (tpt (rpt r) x)‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_comp_tpt hf hS hr).continuousOn
  exact ⟨M, fun x => hM x (mem_univ x)⟩

/-- `∑_{α ∈ ℤ^d} ∏_k q^{|α_k|} < ∞` for `0 ≤ q < 1`. -/
theorem summable_prod_pow_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable fun α : Fin d → ℤ => ∏ k, q ^ (α k).natAbs := by
  classical
  have hg : Summable fun a : ℤ => q ^ a.natAbs := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> simpa using summable_geometric_of_lt_one hq0 hq
  refine summable_of_sum_le (c := ∏ _k : Fin d, ∑' a : ℤ, q ^ a.natAbs)
    (fun α => Finset.prod_nonneg fun _ _ => pow_nonneg hq0 _) fun u => ?_
  set t : Fin d → Finset ℤ := fun k => u.image fun α => α k
  have hsub : u ⊆ Fintype.piFinset t := fun α hα =>
    Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hα
  calc ∑ α ∈ u, ∏ k, q ^ (α k).natAbs
      ≤ ∑ α ∈ Fintype.piFinset t, ∏ k, q ^ (α k).natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => pow_nonneg hq0 _
    _ = ∏ k, ∑ a ∈ t k, q ^ a.natAbs := (Finset.prod_univ_sum t fun _ a => q ^ a.natAbs).symm
    _ ≤ ∏ _k : Fin d, ∑' a : ℤ, q ^ a.natAbs :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg hq0 _)
          fun k _ => hg.sum_le_tsum _ fun _ _ => pow_nonneg hq0 _

theorem rmono_corner (α : Fin d → ℤ) (r : Fin d → ℝ) (lam : ℝ) :
    rmono α (fun k => if 0 ≤ α k then r k * lam else r k / lam) =
      rmono α r * ∏ k, lam ^ (α k).natAbs := by
  simp only [rmono, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs with h
  · have e : lam ^ α k = lam ^ (α k).natAbs := by
      rw [← zpow_natCast, Int.natAbs_of_nonneg h]
    rw [mul_zpow, e]
  · push Not at h
    have e : (r k / lam) ^ α k = r k ^ α k * lam ^ (α k).natAbs := by
      rw [div_zpow, div_eq_mul_inv, ← zpow_neg, ← zpow_natCast,
        Int.ofNat_natAbs_of_nonpos h.le]
    rw [e]

/-- **Summability of the Laurent coefficients** on the radii of `S`. -/
theorem summable_lcoeffAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hS : IsReinhardtIn U S) (hr₀ : r₀ ∈ S) {r : Fin d → ℝ} (hr : r ∈ S) :
    Summable fun α => ‖lcoeffAt f r₀ α‖ * rmono α r := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hS.isOpen r hr
  set R : ℝ := ∑ k, r k with hRdef
  have hR : ∀ k, r k ≤ R := fun k =>
    Finset.single_le_sum (f := r) (fun k _ => (hS.pos r hr k).le) (Finset.mem_univ k)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ => (hS.pos r hr k).le
  set η : ℝ := δ / (2 * (R + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hRη : R * η < δ := by
    rw [hηdef, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set lam : ℝ := 1 + η with hlamdef
  have hlam : 1 < lam := by linarith
  have hlam0 : 0 < lam := by linarith
  set corner : (Fin d → Bool) → Fin d → ℝ := fun ε k => if ε k then r k * lam else r k / lam
  have hcorner : ∀ ε, corner ε ∈ S := by
    intro ε
    refine hball ((dist_pi_lt_iff hδ).2 fun k => ?_)
    have hrk := hS.pos r hr k
    rw [Real.dist_eq]
    by_cases hε : ε k
    · simp only [corner, hε, if_true]
      rw [show r k * lam - r k = r k * η by rw [hlamdef]; ring, abs_of_pos (by positivity)]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hR k) hη.le) hRη
    · simp only [corner, hε, if_false, Bool.false_eq_true]
      rw [show r k / lam - r k = -(r k * η / lam) by field_simp; ring, abs_neg,
        abs_of_pos (by positivity), div_lt_iff₀ hlam0]
      calc r k * η ≤ R * η := mul_le_mul_of_nonneg_right (hR k) hη.le
        _ < δ := hRη
        _ ≤ δ * lam := le_mul_of_one_le_right hδ.le hlam.le
  choose M hM using fun ε => exists_bound_torus hf hS (hcorner ε)
  set Mt : ℝ := ∑ ε, |M ε|
  have key : ∀ α : Fin d → ℤ,
      ‖lcoeffAt f r₀ α‖ * rmono α r ≤ Mt * ∏ k, lam⁻¹ ^ (α k).natAbs := by
    intro α
    set ε : Fin d → Bool := fun k => decide (0 ≤ α k)
    have hc : corner ε = fun k => if 0 ≤ α k then r k * lam else r k / lam := by
      funext k
      simp [corner, ε]
    have h1 := norm_lcoeffAt_mul_le hU hf hS hr₀ (hcorner ε) (hM ε) α
    rw [hc, rmono_corner α r lam] at h1
    have hP : 0 < ∏ k, lam ^ (α k).natAbs := Finset.prod_pos fun k _ => pow_pos hlam0 _
    have h2 : M ε ≤ Mt := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun ε => |M ε|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ε))
    rw [← mul_assoc] at h1
    have h3 := (le_div_iff₀ hP).2 (h1.trans h2)
    calc ‖lcoeffAt f r₀ α‖ * rmono α r ≤ Mt / ∏ k, lam ^ (α k).natAbs := h3
      _ = Mt * ∏ k, lam⁻¹ ^ (α k).natAbs := by
        rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
        simp only [inv_pow]
  refine Summable.of_nonneg_of_le (fun α => mul_nonneg (norm_nonneg _)
    (rmono_pos α (hS.pos r hr)).le) key ?_
  exact (summable_prod_pow_natAbs (inv_nonneg.2 hlam0.le) (inv_lt_one_of_one_lt₀ hlam)).mul_left _

/-- **The Laurent expansion**: `f(z) = ∑_α C_α z^α` for every `z` with radii in `S`. -/
theorem hasSum_lcoeffAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hS : IsReinhardtIn U S) (hr₀ : r₀ ∈ S) {z : EuclideanSpace ℂ (Fin d)} (hz : radii z ∈ S) :
    HasSum (fun α => lcoeffAt f r₀ α * mono α z) (f z) := by
  set r := radii z with hrdef
  set x : UnitAddTorus (Fin d) := fun k => ((arg (z k) / (2 * π) : ℝ) : UnitAddCircle)
  have hzx : tpt (rpt r) x = z := tpt_radii_arg z
  set F : C(UnitAddTorus (Fin d), ℂ) := ⟨fun x => f (tpt (rpt r) x), continuous_comp_tpt hf hS hz⟩
  have hcoef : ∀ α, mFourierCoeff F α = lcoeffAt f r₀ α * mono α (rpt r) := fun α =>
    tcoeff_eq_lcoeffAt hU hf hS hr₀ hz α
  have hsum : Summable (mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simp_rw [hcoef, norm_mul, norm_mono_rpt _ (hS.pos _ hz)]
    exact summable_lcoeffAt hU hf hS hr₀ hz
  have h := hasSum_mFourier_series_apply_of_summable hsum x
  convert h using 1
  · funext α
    rw [hcoef, smul_eq_mul, mul_assoc, ← mono_tpt, hzx]
  · show f z = f (tpt (rpt r) x)
    rw [hzx]

end Reinhardt

end SGPT.GAGA.PN
