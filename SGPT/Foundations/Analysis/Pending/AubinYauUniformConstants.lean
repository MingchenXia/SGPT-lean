import SGPT.Foundations.Analysis.Pending.AubinYauLocalStep
import SGPT.Foundations.Analysis.Pending.KahlerPotentialNormalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Uniform constants for Błocki's second-derivative estimate

The local step (`AubinYauLocalStep.re_trace_inv_le_of_isLocalMax`) needs, at the maximum point,
bounds for the background potential `ρ` that do not depend on the solution: Błocki's constants
`C₅, C₆, C₇` of `lnm2038-monge-ampere:page-0224` ("`1/C₇ ≤ λ_min(g_{ij̄}(y))`"; `C₆` bounds the
second derivatives of `log g_{ζζ̄}`, `C₅` those of `log det(g_{pq̄})`). On a compact set `K` inside an
open set `V` where the smooth `ρ` has positive Levi form (`exists_uniform_constants`):

* `c ‖w‖² ≤ ρ_{w w̄}` and `ρ_{w w̄} ≤ C ‖w‖²`;
* `(ρ_{ζζ̄})_{w w̄} ≤ M ‖w‖²` for `‖ζ‖ ≤ 1` (fourth derivatives, uniformly in the direction:
  `leviForm_leviForm_eq_sum`, a coordinate expansion);
* `(log det (ρ_{jk̄}))_{ζζ̄} ≥ -K₁` for `‖ζ‖ ≤ 1`.

Also: smooth functions on an open set agree near a ball with globally smooth ones
(`exists_contDiff_eqOn_ball`), and Levi forms / complex Hessians depend only on germs.

TN.4 B5, nonlinear track N3.
-/

open Set Filter Matrix Complex Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet SemiconcaveHessian
  BlockiLocalEstimate AubinYauLocalStep

noncomputable section

variable {n : ℕ}

/-! ### Germs and cutoffs -/

theorem leviForm_congr {F G : ComplexModel n → ℝ} {x : ComplexModel n} (h : F =ᶠ[𝓝 x] G)
    (v : ComplexModel n) : leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

theorem complexHessian_congr {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (h : f =ᶠ[𝓝 z] g) : complexHessian f z = complexHessian g z := by
  have h2 : iteratedFDeriv ℝ 2 f z = iteratedFDeriv ℝ 2 g z := (h.iteratedFDeriv ℝ 2).self_of_nhds
  ext j k
  simp [complexHessian, realHessian, h2]

/-- A function smooth on an open set agrees on a ball with a globally smooth function. -/
theorem exists_contDiff_eqOn_ball {W : Set (ComplexModel n)} (hW : IsOpen W)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f W) {c : ComplexModel n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRW : closedBall c R ⊆ W) :
    ∃ g : ComplexModel n → ℝ, ContDiff ℝ ∞ g ∧ EqOn g f (ball c r) := by
  let χ : ContDiffBump c := ⟨r, R, hr, hrR⟩
  refine ⟨fun z => χ z * f z, ?_, fun z hz => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : z ∈ W
    · exact (χ.contDiff.contDiffAt).mul (hf.contDiffAt (hW.mem_nhds hz))
    · have hzs : z ∉ tsupport χ := by
        rw [χ.tsupport_eq]; exact fun h => hz (hRW h)
      have h0 : (fun z => χ z * f z) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzs] with w hw
        simp [hw]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0
  · simp only
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_mul]

/-! ### Bounds of Levi forms on compact sets -/

/-- A uniform bound `|f_{w w̄}| ≤ B ‖w‖²` on a compact set. -/
theorem exists_abs_leviForm_le {V : Set (ComplexModel n)} (hV : IsOpen V)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ 2 f V) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ w, |leviForm f z w| ≤ B * ‖w‖ ^ 2 := by
  have hD2 : ContinuousOn (fun z => fderiv ℝ (fderiv ℝ f) z) V :=
    (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (E := ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) hK (hD2.mono hKV)
  refine ⟨max B 0, le_max_right _ _, fun z hz w => ?_⟩
  have hbd : ∀ v : ComplexModel n, |realHessian f z v v| ≤ max B 0 * ‖v‖ ^ 2 := by
    intro v
    rw [realHessian_eq_fderiv]
    have h1 : ‖fderiv ℝ (fderiv ℝ f) z v v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) z v‖ * ‖v‖ :=
      (fderiv ℝ (fderiv ℝ f) z v).le_opNorm v
    have h2 : ‖fderiv ℝ (fderiv ℝ f) z v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖ * ‖v‖ :=
      (fderiv ℝ (fderiv ℝ f) z).le_opNorm v
    have h3 : ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ max B 0 := (hB z hz).trans (le_max_left _ _)
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ f) z v v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖ * ‖v‖ * ‖v‖ :=
          h1.trans (mul_le_mul_of_nonneg_right h2 hv)
      _ ≤ max B 0 * ‖v‖ * ‖v‖ := by gcongr
      _ = max B 0 * ‖v‖ ^ 2 := by ring
  have hIw : ‖Complex.I • w‖ = ‖w‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h1 := hbd w
  have h2 := hbd (Complex.I • w)
  rw [hIw] at h2
  rw [leviForm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := abs_add_le (realHessian f z w w) (realHessian f z (Complex.I • w) (Complex.I • w))
  have hB0 : 0 ≤ max B 0 * ‖w‖ ^ 2 := by positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-! ### Coordinate expansions of Wirtinger derivatives -/

section Expansion

theorem wirt_negI_eq_dDir (v : ComplexModel n) (g : ComplexModel n → ℂ) (y : ComplexModel n) :
    wirt (-I) v g y = CauchyGreen.dDir v g y := by
  simp only [wirt, CauchyGreen.dDir]
  ring

theorem wirt_negI_sum_dir (g : ComplexModel n → ℂ) (w y : ComplexModel n) :
    wirt (-I) w g y = ∑ b, w b * wirt (-I) (coordinateVector b) g y := by
  rw [wirt_negI_eq_dDir]
  conv_lhs => rw [← coordinateVector_sum w]
  rw [CauchyGreen.dDir_sum_dir]
  simp only [wirt_negI_eq_dDir]

theorem wirt_I_sum_dir (g : ComplexModel n → ℂ) (v y : ComplexModel n) :
    wirt I v g y = ∑ a, star (v a) * wirt I (coordinateVector a) g y := by
  rw [← dbarDir_eq_wirt]
  conv_lhs => rw [← coordinateVector_sum v]
  rw [CauchyGreen.dbarDir_sum_dir]
  rfl

/-- `∂̄_v ∂_w g = ∑_{a,b} v̄_a w_b ∂̄_a ∂_b g`. -/
theorem wirt_I_wirt_negI_expand {g : ComplexModel n → ℂ} (hg : ContDiff ℝ ∞ g)
    (v w z : ComplexModel n) :
    wirt I v (wirt (-I) w g) z = ∑ a, ∑ b, star (v a) * w b *
      wirt I (coordinateVector a) (wirt (-I) (coordinateVector b) g) z := by
  rw [wirt_I_sum_dir]
  have hfun : wirt (-I) w g = fun y => ∑ b, w b * wirt (-I) (coordinateVector b) g y :=
    funext (wirt_negI_sum_dir g w)
  rw [hfun]
  have hd : ∀ b y, DifferentiableAt ℝ (wirt (-I) (coordinateVector b) g) y := fun b y =>
    (contDiff_wirt hg).differentiable (by simp) y
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wirt_sum Finset.univ (f := fun b y => w b * wirt (-I) (coordinateVector b) g y)
    fun b _ => (hd b z).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wirt_const_mul _ (hd b z)]
  ring

/-- Two operators applied to a finite linear combination of smooth functions. -/
theorem wirt_wirt_sum_const_mul {ι : Type*} [Fintype ι] {T : ι → ComplexModel n → ℂ}
    (hT : ∀ i, ContDiff ℝ ∞ (T i)) (k : ι → ℂ) (c₁ c₂ : ℂ) (v₁ v₂ z : ComplexModel n) :
    wirt c₁ v₁ (wirt c₂ v₂ (fun y => ∑ i, k i * T i y)) z =
      ∑ i, k i * wirt c₁ v₁ (wirt c₂ v₂ (T i)) z := by
  have hd : ∀ i y, DifferentiableAt ℝ (T i) y := fun i y => (hT i).differentiable (by simp) y
  have hd2 : ∀ i y, DifferentiableAt ℝ (wirt c₂ v₂ (T i)) y := fun i y =>
    (contDiff_wirt (hT i)).differentiable (by simp) y
  have hinner : wirt c₂ v₂ (fun y => ∑ i, k i * T i y) =
      fun y => ∑ i, k i * wirt c₂ v₂ (T i) y := by
    funext y
    rw [wirt_sum Finset.univ (f := fun i y => k i * T i y) fun i _ => (hd i y).const_mul _]
    exact Finset.sum_congr rfl fun i _ => wirt_const_mul _ (hd i y)
  rw [hinner, wirt_sum Finset.univ (f := fun i y => k i * wirt c₂ v₂ (T i) y)
    fun i _ => (hd2 i z).const_mul _]
  exact Finset.sum_congr rfl fun i _ => wirt_const_mul _ (hd2 i z)

/-- The fourth-order coefficients `∂̄_a ∂_b ∂̄_c ∂_d ρ`. -/
def fourthCoeff (ρ : ComplexModel n → ℝ) (a b c d : Fin n) (z : ComplexModel n) : ℂ :=
  wirt I (coordinateVector a) (wirt (-I) (coordinateVector b)
    (wirt I (coordinateVector c) (wirt (-I) (coordinateVector d) (fun y => (ρ y : ℂ))))) z

theorem contDiff_fourthCoeff {ρ : ComplexModel n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (a b c d : Fin n) :
    ContDiff ℝ ∞ (fourthCoeff ρ a b c d) :=
  contDiff_wirt (contDiff_wirt (contDiff_wirt (contDiff_wirt (contDiff_ofReal_comp hρ))))

/-- **The coordinate expansion** of `(ρ_{ζζ̄})_{w w̄}`. -/
theorem ofReal_leviForm_leviForm_eq_sum {ρ : ComplexModel n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (ζ w z : ComplexModel n) :
    ((leviForm (fun y => leviForm ρ y ζ) z w : ℝ) : ℂ) =
      ∑ a, ∑ b, star (w a) * w b * ∑ p : Fin n × Fin n,
        star (ζ p.1) * ζ p.2 * fourthCoeff ρ a b p.1 p.2 z := by
  have hF := contDiff_ofReal_comp hρ
  rw [ofReal_leviForm_eq_wirt (contDiff_leviForm hρ ζ) w z,
    wirt_I_wirt_negI_expand (contDiff_ofReal_comp (contDiff_leviForm hρ ζ))]
  set T : Fin n × Fin n → ComplexModel n → ℂ := fun p =>
    wirt I (coordinateVector p.1) (wirt (-I) (coordinateVector p.2) (fun y => (ρ y : ℂ)))
    with hTdef
  have hT : ∀ p, ContDiff ℝ ∞ (T p) := fun p => contDiff_wirt (contDiff_wirt hF)
  have hL : (fun y => ((leviForm ρ y ζ : ℝ) : ℂ)) =
      fun y => ∑ p : Fin n × Fin n, star (ζ p.1) * ζ p.2 * T p y := by
    funext y
    rw [ofReal_leviForm_eq_wirt hρ ζ y, wirt_I_wirt_negI_expand hF, ← Fintype.sum_prod_type']
  rw [hL]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [wirt_wirt_sum_const_mul hT]
  rfl

theorem leviForm_leviForm_le {ρ : ComplexModel n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {ζ : ComplexModel n} (hζ : ‖ζ‖ ≤ 1) (w z : ComplexModel n) :
    leviForm (fun y => leviForm ρ y ζ) z w ≤
      (∑ a, ∑ b, ∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖) * ‖w‖ ^ 2 := by
  have hζi : ∀ i, ‖ζ i‖ ≤ 1 := fun i => (PiLp.norm_apply_le ζ i).trans hζ
  have hwi : ∀ i, ‖w i‖ ≤ ‖w‖ := fun i => PiLp.norm_apply_le w i
  have h := ofReal_leviForm_leviForm_eq_sum hρ ζ w z
  have hle : leviForm (fun y => leviForm ρ y ζ) z w ≤
      ‖((leviForm (fun y => leviForm ρ y ζ) z w : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ?_
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_mul, norm_star, Finset.sum_mul]
  have hsum : ‖∑ p : Fin n × Fin n, star (ζ p.1) * ζ p.2 * fourthCoeff ρ a b p.1 p.2 z‖ ≤
      ∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
    have h1 := hζi p.1
    have h2 := hζi p.2
    have h0 : 0 ≤ ‖fourthCoeff ρ a b p.1 p.2 z‖ := norm_nonneg _
    calc ‖ζ p.1‖ * ‖ζ p.2‖ * ‖fourthCoeff ρ a b p.1 p.2 z‖
        ≤ 1 * 1 * ‖fourthCoeff ρ a b p.1 p.2 z‖ := by gcongr
      _ = ‖fourthCoeff ρ a b p.1 p.2 z‖ := by ring
  have hS0 : 0 ≤ ∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖ :=
    Finset.sum_nonneg fun p _ => norm_nonneg _
  rw [← Finset.sum_mul]
  calc ‖w a‖ * ‖w b‖ * ‖∑ p : Fin n × Fin n, star (ζ p.1) * ζ p.2 * fourthCoeff ρ a b p.1 p.2 z‖
      ≤ ‖w‖ * ‖w‖ * ∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖ := by
        gcongr
        · exact hwi a
        · exact hwi b
    _ = (∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖) * ‖w‖ ^ 2 := by ring

end Expansion

/-! ### The uniform constants -/

/-- **Uniform constants for the background potential** on a compact set `K ⊆ V`, `V` open, where
the smooth `ρ` has positive Levi form (Błocki's `C₅`–`C₇`, `lnm2038-monge-ampere:page-0224`). -/
theorem exists_uniform_constants (hn : 0 < n) {ρ : ComplexModel n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {V K : Set (ComplexModel n)} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hlevi : ∀ z ∈ V, ∀ v, v ≠ 0 → 0 < leviForm ρ z v) :
    ∃ c C M K₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ M ∧ 0 ≤ K₁ ∧ ∀ z ∈ K,
      (∀ w, c * ‖w‖ ^ 2 ≤ leviForm ρ z w) ∧ (∀ w, leviForm ρ z w ≤ C * ‖w‖ ^ 2) ∧
      (∀ ζ : ComplexModel n, ‖ζ‖ ≤ 1 → ∀ w,
        leviForm (fun y => leviForm ρ y ζ) z w ≤ M * ‖w‖ ^ 2) ∧
      (∀ ζ : ComplexModel n, ‖ζ‖ ≤ 1 →
        -K₁ ≤ leviForm (fun y => Real.log (complexHessian ρ y).det.re) z ζ) := by
  have hρ2 : ContDiffOn ℝ 2 ρ V :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
  obtain ⟨c, hc, hcK⟩ :=
    KahlerPotentialNormalization.exists_pos_mul_norm_sq_le_leviForm hn hV hρ2 hlevi hK hKV
  obtain ⟨C, hC, hCK⟩ := exists_abs_leviForm_le hV hρ2 hK hKV
  -- the fourth-order coefficients are bounded on `K`
  set S : ComplexModel n → ℝ := fun z =>
    ∑ a, ∑ b, ∑ p : Fin n × Fin n, ‖fourthCoeff ρ a b p.1 p.2 z‖ with hSdef
  have hSc : Continuous S := by
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun p _ => ?_
    exact ((contDiff_fourthCoeff hρ a b p.1 p.2).continuous).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hSc.continuousOn
  -- `log det` of the complex Hessian is smooth on `V`
  set D : ComplexModel n → ℝ := fun y => (complexHessian ρ y).det.re with hDdef
  have hDc : ContDiff ℝ ∞ D := Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hρ)
  have hDpos : ∀ z ∈ V, 0 < D z := fun z hz =>
    (Complex.pos_iff.mp (posDef_complexHessian (contDiffAt_two hρ z) (hlevi z hz)).det_pos).1
  have hlogD : ContDiffOn ℝ 2 (fun y => Real.log (D y)) V :=
    ((hDc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn).log
      fun z hz => (hDpos z hz).ne'
  obtain ⟨K₁, hK₁, hK₁K⟩ := exists_abs_leviForm_le hV hlogD hK hKV
  refine ⟨c, C, max M 0, K₁, hc, hC, le_max_right _ _, hK₁, fun z hz => ⟨hcK z hz, fun w => ?_,
    fun ζ hζ w => ?_, fun ζ hζ => ?_⟩⟩
  · exact (le_abs_self _).trans (hCK z hz w)
  · refine (leviForm_leviForm_le hρ hζ w z).trans ?_
    have hSz : S z ≤ max M 0 := by
      have := hM z hz
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    exact mul_le_mul_of_nonneg_right hSz (by positivity)
  · have h1 := hK₁K z hz ζ
    have h2 : K₁ * ‖ζ‖ ^ 2 ≤ K₁ := by
      have : ‖ζ‖ ^ 2 ≤ 1 := by
        have := norm_nonneg ζ
        nlinarith
      nlinarith
    have h3 := neg_abs_le (leviForm (fun y => Real.log (D y)) z ζ)
    simp only [hDdef] at h3 h1
    linarith

end

end SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants
