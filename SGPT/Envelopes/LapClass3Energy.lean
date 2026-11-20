import SGPT.Analysis.CZMatrix
import SGPT.Envelopes.LapClassDef
import SGPT.Okounkov.TranscendentalWNEnvelopeContact
import SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance

/-!
# The `L²` identity for complex Hessians on a compact Kähler manifold

Lane CZ-LP (`claude-cz-lp`, node `czlp:energy`).  For a chart-smooth function `u` on a compact
complex manifold `X` with a Kähler form `ω`, write, in a chart, `N` for the coefficient matrix of
`ω`, `A` for the complex Hessian of `u` and `B = N⁻¹A`.  Then

  `∫_X Re tr(B²) ωⁿ = ∫_X (Δ_ω u)² ωⁿ`                (`integral_hessEnergy_eq`)

(the Kähler identity `‖ddᶜu‖²_{L²} = ‖Δ_ω u‖²_{L²}`), and consequently, on every compact subset `K`
of a chart, `∫_K ∑ |A_pq|² ≤ C_K ∫_X (Δ_ω u)² ωⁿ` (`exists_setIntegral_hessian_sq_le`).  This is
the `L²` (Plancherel) case of the Calderón–Zygmund estimate, with variable coefficients, and needs
no singular integrals.

*Proof.*  `t ↦ (ω + t ddᶜu)ⁿ/ωⁿ = det(1 + tB)` is a polynomial whose coefficient of `tᵏ`
(`hessCoeff`) is a sum of mixed densities `ω^{n-k} ∧ (ddᶜu)ᵏ / ωⁿ`.  For `k ≥ 1` each of these
integrates to `0` (`MixedMassClassInvariance.integral_topRatio_ddc_eq_zero`: Stokes).  The
coefficient of `t` is `tr B = Δ_ω u` and twice the coefficient of `t²` is
`(tr B)² - tr B²` (`two_mul_coeff_two_det_one_add_X_smul`), so `Re tr B² = (Δ_ω u)² - 2 c₂`
integrates to `∫ (Δ_ω u)²`.  Finally `∑|A_pq|² ≤ (tr N)² Re tr B²` (`sum_norm_sq_le_re_trace_mul`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Polynomial
open scoped Topology ContDiff Matrix ComplexOrder

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Analysis.CZLp

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The slot densities -/

/-- The density `ω^{|s|} ∧ (ddᶜu)^{n-|s|} / ωⁿ` with the slots in `s` filled by `ω`. -/
def slotRatio (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u)
    (s : Finset (Fin n)) (x : M) : ℝ :=
  topRatio w.form.val (MixedMassClassInvariance.slotForm
    (s.piecewise (fun _ => w.form) (fun _ => ddcClosedForm u hu))) x

/-- The coefficient of `tᵏ` in `(ω + t ddᶜu)ⁿ / ωⁿ`. -/
def hessCoeff (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u) (k : ℕ)
    (x : M) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin n) => (Finset.univ \ s).card = k),
    slotRatio w u hu s x

/-- The polynomial `t ↦ (ω + t ddᶜu)ⁿ / ωⁿ` at `x`. -/
def hessPoly (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u) (x : M) :
    ℝ[X] :=
  ∑ s : Finset (Fin n), C (slotRatio w u hu s x) * X ^ (Finset.univ \ s).card

/-- **The intrinsic `L²` energy density of the complex Hessian**: `|ddᶜu|²_ω = Re tr((N⁻¹A)²)`
(`hessEnergy_eq_chart`), written as `(Δ_ω u)² - 2 c₂`. -/
def hessEnergy (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u) (x : M) :
    ℝ :=
  laplacian w.form.val u x ^ 2 - 2 * hessCoeff w u hu 2 x

theorem continuous_slotRatio (w : KahlerBackground n M) (u : M → ℝ)
    (hu : ChartSmooth (n := n) u) (s : Finset (Fin n)) : Continuous (slotRatio w u hu s) :=
  continuous_topRatio w.isKahler.1 _

theorem continuous_hessCoeff (w : KahlerBackground n M) (u : M → ℝ)
    (hu : ChartSmooth (n := n) u) (k : ℕ) : Continuous (hessCoeff w u hu k) :=
  continuous_finsetSum _ fun s _ => continuous_slotRatio w u hu s

theorem continuous_hessEnergy (w : KahlerBackground n M) (u : M → ℝ)
    (hu : ChartSmooth (n := n) u) : Continuous (hessEnergy w u hu) :=
  ((LapClass.continuous_laplacian_of_chartSmooth w.isKahler.1 hu).pow 2).sub
    (continuous_const.mul (continuous_hessCoeff w u hu 2))

theorem coeff_hessPoly (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u)
    (x : M) (k : ℕ) : (hessPoly w u hu x).coeff k = hessCoeff w u hu k x := by
  classical
  simp only [hessPoly, hessCoeff, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun s _ => by split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- `(ω + t ddᶜu)ⁿ / ωⁿ` is `hessPoly` evaluated at `t`. -/
theorem eval_hessPoly (w : KahlerBackground n M) (u : M → ℝ) (hu : ChartSmooth (n := n) u)
    (x : M) (t : ℝ) :
    (hessPoly w u hu x).eval t =
      topRatio w.form.val (formPow (w.form + t • ddcClosedForm u hu).val n) x := by
  classical
  rw [SGPT.Okounkov.TranscendentalWN.topRatio_formPow_add_smul]
  simp only [hessPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! ### Chart computation -/

theorem isOneOne_coeff (θ : ClosedRealOneOneForm n M) {e : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ e.val.target) : IsOneOne (θ.val.coeff e z) :=
  fun a b => θ.property.2 e z hz a b

theorem det_im_eq_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : H.det.im = 0 := by
  have h := congrArg Matrix.det hH.eq
  rw [Matrix.det_conjTranspose] at h
  exact Complex.conj_eq_iff_im.mp h

/-- **The density of `(ω + t ddᶜu)ⁿ` in a chart**: `det(N + tA) / det N`. -/
theorem topRatio_formPow_add_smul_ddc_eq (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) {e : ComplexChart n M} {x : M} (hx : x ∈ e.val.source)
    (t : ℝ) :
    (topRatio w.form.val (formPow (w.form + t • ddcClosedForm u hu).val n) x : ℂ) =
      (normalizedHermitianMatrix (w.form.val.coeff e (e.val x)) +
          (t : ℂ) • complexHessian (fun y => u (e.val.symm y)) (e.val x)).det /
        (normalizedHermitianMatrix (w.form.val.coeff e (e.val x))).det := by
  set z := e.val x with hzdef
  have hz : z ∈ e.val.target := e.val.map_source hx
  set N := normalizedHermitianMatrix (w.form.val.coeff e z) with hN
  set A := complexHessian (fun y => u (e.val.symm y)) z with hA
  have hu2 : ContDiffAt ℝ 2 (fun y => u (e.val.symm y)) z :=
    ((hu e z hz).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcoeff : normalizedHermitianMatrix ((w.form + t • ddcClosedForm u hu).val.coeff e z) =
      N + (t : ℂ) • A := by
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      normalizedHermitianMatrix_add, normalizedHermitianMatrix_smul, ddcClosedForm_coeff,
      normalizedHermitianMatrix_smoothDDC hu2]
    rfl
  have hden : ∀ θ : ClosedRealOneOneForm n M, topDensity ((formPow θ.val n).coeff e z) =
      (n.factorial : ℝ) / Real.pi ^ n *
        (normalizedHermitianMatrix (θ.val.coeff e z)).det.re := fun θ => by
    rw [formPow_coeff, topDensity_formPower,
      ConcentrationMassComparison.actualTopPowerDensity_eq_det (isOneOne_coeff θ hz)]
  have hNh : N.IsHermitian := (posDef_coeff w.isKahler.1 hz).1
  have hNtA : (N + (t : ℂ) • A).IsHermitian := by
    refine hNh.add ?_
    have hAh : A.IsHermitian := complexHessian_isHermitian hu2
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hAh.eq, Complex.star_def, Complex.conj_ofReal]
  rw [topRatio_eq_chartRatio w.isKahler.1 _ hx, chartRatio]
  have h1 := hden (w.form + t • ddcClosedForm u hu)
  have h2 := hden w.form
  rw [h1, hcoeff]
  change _ = _ / N.det
  rw [show (formPow w.form.val n) = (formPow w.form.val n) from rfl, h2]
  have hc : (n.factorial : ℝ) / Real.pi ^ n ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hc]
  have hreal : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ((H.det.re : ℝ) : ℂ) = H.det :=
    fun H hH => Complex.ext (by simp) (by simp [det_im_eq_zero hH])
  rw [Complex.ofReal_div, hreal _ hNtA, hreal _ hNh]

/-- **The density polynomial in a chart**: `t ↦ (ω + t ddᶜu)ⁿ/ωⁿ` is `t ↦ det(1 + t N⁻¹A)`. -/
theorem hessPoly_map_eq (w : KahlerBackground n M) {u : M → ℝ} (hu : ChartSmooth (n := n) u)
    {e : ComplexChart n M} {x : M} (hx : x ∈ e.val.source) :
    (hessPoly w u hu x).map (algebraMap ℝ ℂ) =
      Matrix.det (1 + (X : ℂ[X]) • ((normalizedHermitianMatrix (w.form.val.coeff e (e.val x)))⁻¹ *
        complexHessian (fun y => u (e.val.symm y)) (e.val x)).map C) := by
  set z := e.val x with hzdef
  have hz : z ∈ e.val.target := e.val.map_source hx
  set N := normalizedHermitianMatrix (w.form.val.coeff e z) with hN
  set A := complexHessian (fun y => u (e.val.symm y)) z with hA
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr (posDef_coeff w.isKahler.1 hz).det_pos.ne'
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℝ => (t : ℂ))
    Complex.ofReal_injective fun t => ?_
  show eval (t : ℂ) ((hessPoly w u hu x).map (algebraMap ℝ ℂ)) = eval (t : ℂ) _
  have hev : ∀ (r : ℂ) (Mx : Matrix (Fin n) (Fin n) ℂ[X]), eval r Mx.det = (Mx.map (eval r)).det :=
    fun r Mx => by rw [← coe_evalRingHom, RingHom.map_det]; rfl
  rw [hev, eval_map, show (t : ℂ) = algebraMap ℝ ℂ t from rfl, eval₂_at_apply]
  simp only [Complex.coe_algebraMap]
  rw [eval_hessPoly, topRatio_formPow_add_smul_ddc_eq w hu hx t]
  have hmap : (1 + (X : ℂ[X]) • (N⁻¹ * A).map C).map (eval (t : ℂ)) = 1 + (t : ℂ) • (N⁻¹ * A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, smul_eq_mul, eval_add, eval_mul, eval_X, eval_C,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine Eq.trans ?_ (congrArg Matrix.det hmap).symm
  have hfac : N + (t : ℂ) • A = N * (1 + (t : ℂ) • (N⁻¹ * A)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hNu, Matrix.one_mul]
  have key : (N + (t : ℂ) • A).det / N.det = (1 + (t : ℂ) • (N⁻¹ * A)).det := by
    rw [hfac, Matrix.det_mul, mul_comm, mul_div_assoc, div_self
      (posDef_coeff w.isKahler.1 hz).det_pos.ne', mul_one]
  exact key

/-- The coefficient of `t` is the Laplacian. -/
theorem hessCoeff_one_eq_laplacian (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) (x : M) : hessCoeff w u hu 1 x = laplacian w.form.val u x := by
  set e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h := congrArg (fun p : ℂ[X] => p.coeff 1) (hessPoly_map_eq w hu hx)
  simp only [coeff_map, coeff_hessPoly, coeff_one_det_one_add_X_smul] at h
  rw [LapClass.laplacian_eq_trace, ← h]
  simp

/-- **The energy density in a chart**: `hessEnergy = Re tr((N⁻¹A)²)`. -/
theorem hessEnergy_eq_chart (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) {e : ComplexChart n M} {x : M} (hx : x ∈ e.val.source) :
    hessEnergy w u hu x =
      ((normalizedHermitianMatrix (w.form.val.coeff e (e.val x)))⁻¹ *
          complexHessian (fun y => u (e.val.symm y)) (e.val x) *
        ((normalizedHermitianMatrix (w.form.val.coeff e (e.val x)))⁻¹ *
          complexHessian (fun y => u (e.val.symm y)) (e.val x))).trace.re := by
  set B := (normalizedHermitianMatrix (w.form.val.coeff e (e.val x)))⁻¹ *
    complexHessian (fun y => u (e.val.symm y)) (e.val x) with hB
  have hP := hessPoly_map_eq w hu hx
  rw [← hB] at hP
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hP
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hP
  simp only [coeff_map, coeff_hessPoly, coeff_one_det_one_add_X_smul] at h1 h2
  have hid := two_mul_coeff_two_det_one_add_X_smul B
  rw [← h2, ← h1] at hid
  have hre : (B * B).trace = ((hessCoeff w u hu 1 x ^ 2 - 2 * hessCoeff w u hu 2 x : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.coe_algebraMap] at hid
    linear_combination hid
  rw [hessEnergy, ← hessCoeff_one_eq_laplacian w hu x, hre, Complex.ofReal_re]

/-! ### Integrals -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- A slot density with a `ddᶜu` slot integrates to `0` (Stokes). -/
theorem integral_slotRatio_eq_zero (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) {s : Finset (Fin n)} (hs : s ≠ Finset.univ) :
    ∫ x, slotRatio w u hu s x ∂(kahlerVolume w) = 0 := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hs)
  set θ : Fin n → ClosedRealOneOneForm n M := s.piecewise (fun _ => w.form)
    (fun _ => ddcClosedForm u hu) with hθ
  have h := MixedMassClassInvariance.integral_topRatio_ddc_eq_zero w θ i₀
    (fun f hf => MixedMassClassInvariance.slotForm (Function.update θ i₀ (ddcClosedForm f hf)))
    (fun f hf e z _ => by
      rw [MixedMassClassInvariance.topDensity_slotForm_coeff]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi; simp
      · simp [Function.update_of_ne hi]) hu
  have hθi : θ i₀ = ddcClosedForm u hu := by
    rw [hθ]
    exact Finset.piecewise_eq_of_notMem _ _ _ hi₀
  have hupd : Function.update θ i₀ (ddcClosedForm u hu) = θ := by
    rw [← hθi]
    exact Function.update_eq_self i₀ θ
  rw [hupd] at h
  exact h

theorem integral_hessCoeff_eq_zero (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) {k : ℕ} (hk : 1 ≤ k) :
    ∫ x, hessCoeff w u hu k x ∂(kahlerVolume w) = 0 := by
  classical
  simp only [hessCoeff]
  rw [integral_finsetSum _ fun s _ => (continuous_slotRatio w u hu s).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))]
  refine Finset.sum_eq_zero fun s hs => integral_slotRatio_eq_zero w hu ?_
  rintro rfl
  simp only [Finset.mem_filter, Finset.sdiff_self, Finset.card_empty] at hs
  omega

/-- **The Kähler `L²` identity** `∫_X |ddᶜu|²_ω ωⁿ = ∫_X (Δ_ω u)² ωⁿ`. -/
theorem integral_hessEnergy_eq (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) :
    ∫ x, hessEnergy w u hu x ∂(kahlerVolume w) =
      ∫ x, laplacian w.form.val u x ^ 2 ∂(kahlerVolume w) := by
  have hint : ∀ f : M → ℝ, Continuous f → Integrable f (kahlerVolume w) := fun f hf =>
    hf.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  calc ∫ x, hessEnergy w u hu x ∂(kahlerVolume w)
      = (∫ x, laplacian w.form.val u x ^ 2 ∂(kahlerVolume w)) -
          ∫ x, 2 * hessCoeff w u hu 2 x ∂(kahlerVolume w) :=
        integral_sub (hint _ ((LapClass.continuous_laplacian_of_chartSmooth w.isKahler.1 hu).pow 2))
          (hint _ (continuous_const.mul (continuous_hessCoeff w u hu 2)))
    _ = ∫ x, laplacian w.form.val u x ^ 2 ∂(kahlerVolume w) := by
        rw [integral_const_mul, integral_hessCoeff_eq_zero w hu (by norm_num), mul_zero, sub_zero]

end SGPT.Envelopes.LapClass3
