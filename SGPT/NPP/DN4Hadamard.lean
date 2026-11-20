import SGPT.NPP.DN3Divergence
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Holomorphy and bounds of Hadamard coefficients; smooth cutoffs

Lane DN4 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 4, eq.
`eq:chern-weight-divergence`).  Lane DN3 proved the divergence formula
`χ(|s|²) g(s) = ∑_l ∂̄_l(χ₁(|s|²) g̃_l(s))` (`SGPT.NPP.DN3.chi_mul_eq_sum_dbarDir`) for a holomorphic
`g` with `g(0) = 0`, assuming that the Hadamard coefficients `g̃_l(s) = ∫₀¹ ∂_l g(t s) dt`
(`SGPT.NPP.DN3.hadamardCoeff`) are holomorphic.  Here:

* `hasFDerivAt_hadamardCoeff`, `differentiableOn_hadamardCoeff`: `g̃_l` is holomorphic on every
  ball about `0` on which `g` is, with `D g̃_l(s) = ∫₀¹ t D(∂_l g)(t s) dt` (differentiation
  under the integral sign);
* `norm_hadamardCoeff_le`, `norm_fderiv_hadamardCoeff_le`: `|g̃_l| ≤ sup |Dg|` and
  `‖D g̃_l‖ ≤ sup ‖D²g‖` on the closed unit ball;
* `contDiff_mul_of_tsupport_subset`: a function smooth on an open set `U`, multiplied by a smooth
  function with support in `U`, is smooth everywhere;
* `dDir_eq_fderiv_of_differentiableAt`: `∂_v f = Df(v)` for holomorphic `f`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Interval

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.NPP.DN3

variable {n : ℕ}

/-! ### Cutoffs -/

/-- A function smooth on an open set `U`, multiplied by a smooth function supported in `U`, is
smooth everywhere. -/
theorem contDiff_mul_of_tsupport_subset {k : WithTop ℕ∞} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {f g : ComplexModel n → ℂ} (hg : ContDiff ℝ k g) (hf : ContDiffOn ℝ k f U)
    (hsupp : tsupport g ⊆ U) : ContDiff ℝ k (fun x => g x * f x) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact hg.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h => hx (hsupp h)
    have hev : (fun y => g y * f y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact (contDiffAt_const).congr_of_eventuallyEq hev

theorem tsupport_chiOne_normSq_subset :
    tsupport (fun y : ComplexModel n => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ)) ⊆ closedBall 0 1 := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  apply hy
  have h1 : 1 ≤ ‖y‖ ^ 2 := by
    rw [mem_closedBall, dist_zero_right, not_le] at h
    nlinarith
  simp [chiOne_eq_zero_of_le n h1]

theorem tsupport_chi_normSq_subset :
    tsupport (fun y : ComplexModel n => ((chi n (‖y‖ ^ 2) : ℝ) : ℂ)) ⊆ closedBall 0 1 := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  apply hy
  have h1 : 1 ≤ ‖y‖ ^ 2 := by
    rw [mem_closedBall, dist_zero_right, not_le] at h
    nlinarith
  simp [chi_eq_zero_of_le n h1]

/-! ### Wirtinger derivatives of holomorphic functions -/

theorem dDir_eq_fderiv_of_differentiableAt {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (hf : DifferentiableAt ℂ f x) (v : ComplexModel n) : dDir v f x = fderiv ℂ f x v := by
  have h : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  simp only [dDir, h, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  ring_nf
  rw [I_sq]
  ring

/-! ### Hadamard coefficients -/

/-- **Differentiation of the Hadamard coefficient**:
`D g̃_l(s) = ∫₀¹ t D(∂_l g)(t s) dt` for `g` holomorphic on `ball 0 ρ`, `s ∈ ball 0 ρ`. -/
theorem hasFDerivAt_hadamardCoeff {g : ComplexModel n → ℂ} {ρ : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 ρ)) (l : Fin n) {s : ComplexModel n}
    (hs : s ∈ ball 0 ρ) :
    HasFDerivAt (hadamardCoeff g l)
      (∫ t in (0 : ℝ)..1,
        (t : ℂ) • fderiv ℂ (fun y => fderiv ℂ g y (coordinateVector l)) (t • s)) s := by
  set G : ComplexModel n → ℂ := fun y => fderiv ℂ g y (coordinateVector l) with hG
  have hopen : IsOpen (ball (0 : ComplexModel n) ρ) := isOpen_ball
  have hgs : ContDiffOn ℂ ∞ g (ball 0 ρ) := contDiffOn_of_differentiableOn_complex hg hopen
  have hDg : ContDiffOn ℂ ∞ (fderiv ℂ g) (ball 0 ρ) :=
    hgs.fderiv_of_isOpen hopen (by simp)
  have hGs : ContDiffOn ℂ ∞ G (ball 0 ρ) := hDg.clm_apply contDiffOn_const
  have hGd : DifferentiableOn ℂ G (ball 0 ρ) := hGs.differentiableOn (by simp)
  have hGc : ContinuousOn G (ball 0 ρ) := hGs.continuousOn
  have hDGc : ContinuousOn (fderiv ℂ G) (ball 0 ρ) :=
    hGs.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hsρ : ‖s‖ < ρ := by simpa using hs
  set ε := (ρ - ‖s‖) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hK : closedBall (0 : ComplexModel n) (‖s‖ + ε) ⊆ ball 0 ρ :=
    closedBall_subset_ball (by rw [hε]; linarith)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ComplexModel n) (‖s‖ + ε)).exists_bound_of_continuousOn
    (hDGc.mono hK)
  -- points `t x` with `t ∈ [0, 1]`, `x ∈ ball s ε`
  have hmemK : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ ball s ε,
      t • x ∈ closedBall (0 : ComplexModel n) (‖s‖ + ε) := by
    intro t ht x hx
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hx' : ‖x‖ ≤ ‖s‖ + ε := by
      have := norm_le_norm_add_norm_sub' x s
      rw [mem_ball, dist_eq_norm] at hx
      linarith
    calc t * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)
      _ ≤ ‖s‖ + ε := by linarith
  have hsmul : ∀ (t : ℝ) (x : ComplexModel n), t • x = (t : ℂ) • x := fun t x =>
    (Complex.coe_smul t x).symm
  have hball : ball s ε ∈ 𝓝 s := ball_mem_nhds s hε0
  have hcont : ∀ x ∈ ball s ε, ContinuousOn (fun t : ℝ => G (t • x)) (Icc 0 1) := by
    intro x hx
    refine hGc.comp (continuous_id.smul continuous_const).continuousOn fun t ht => hK (hmemK t ht x hx)
  have hcont' : ContinuousOn (fun t : ℝ => (t : ℂ) • fderiv ℂ G (t • s)) (Icc 0 1) := by
    refine (Complex.continuous_ofReal.continuousOn).smul ?_
    exact hDGc.comp (continuous_id.smul continuous_const).continuousOn
      fun t ht => hK (hmemK t ht s (mem_ball_self hε0))
  have hIoc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume) (a := 0) (b := 1)
    (F := fun x t => G (t • x)) (F' := fun x t => (t : ℂ) • fderiv ℂ G (t • x))
    (bound := fun _ => C) hball
    (Filter.eventually_of_mem hball fun x hx =>
      ((hcont x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    ((hcont s (mem_ball_self hε0)).intervalIntegrable_of_Icc zero_le_one)
    ((hcont'.mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht' := hIoc ht
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      calc t * ‖fderiv ℂ G (t • x)‖ ≤ 1 * ‖fderiv ℂ G (t • x)‖ :=
            mul_le_mul_of_nonneg_right ht'.2 (norm_nonneg _)
        _ ≤ C := by rw [one_mul]; exact hC _ (hmemK t ht' x hx))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht' := hIoc ht
      have hGx : DifferentiableAt ℂ G (t • x) :=
        hGd.differentiableAt (hopen.mem_nhds (hK (hmemK t ht' x hx)))
      have hlin : HasFDerivAt (fun y : ComplexModel n => t • y)
          ((t : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) x := by
        have h0 : HasFDerivAt (fun y : ComplexModel n => (t : ℂ) • y)
            ((t : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) x :=
          (hasFDerivAt_id (𝕜 := ℂ) x).const_smul (t : ℂ)
        have e : (fun y : ComplexModel n => t • y) = fun y => (t : ℂ) • y :=
          funext fun y => hsmul t y
        rw [e]; exact h0
      have h := hGx.hasFDerivAt.comp x hlin
      have e2 : (fderiv ℂ G (t • x)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) =
          (t : ℂ) • fderiv ℂ G (t • x) := by
        ext v
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, map_smul]
      rw [e2] at h
      exact h)
  exact key

theorem differentiableOn_hadamardCoeff {g : ComplexModel n → ℂ} {ρ : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 ρ)) (l : Fin n) :
    DifferentiableOn ℂ (hadamardCoeff g l) (ball 0 ρ) := fun s hs =>
  (hasFDerivAt_hadamardCoeff hg l hs).differentiableAt.differentiableWithinAt

/-- `|g̃_l(s)| ≤ A` if `‖Dg‖ ≤ A` on the closed unit ball and `s` lies in it. -/
theorem norm_hadamardCoeff_le {g : ComplexModel n → ℂ} {A : ℝ}
    (hA : ∀ y ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ g y‖ ≤ A) (l : Fin n)
    {s : ComplexModel n} (hs : s ∈ closedBall (0 : ComplexModel n) 1) :
    ‖hadamardCoeff g l s‖ ≤ A := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => fderiv ℂ g (t • s) (coordinateVector l)) (C := A) (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
      have hts : t • s ∈ closedBall (0 : ComplexModel n) 1 := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
        rw [mem_closedBall, dist_zero_right] at hs
        nlinarith [ht'.2, norm_nonneg s]
      calc ‖fderiv ℂ g (t • s) (coordinateVector l)‖
          ≤ ‖fderiv ℂ g (t • s)‖ * ‖coordinateVector (n := n) l‖ :=
            (fderiv ℂ g (t • s)).le_opNorm _
        _ = ‖fderiv ℂ g (t • s)‖ := by simp [coordinateVector]
        _ ≤ A := hA _ hts)
  simpa [hadamardCoeff] using h

/-- `‖D g̃_l(s)‖ ≤ A₂` if `‖D²g‖ ≤ A₂` on the closed unit ball, for `g` holomorphic on a larger
ball. -/
theorem norm_fderiv_hadamardCoeff_le {g : ComplexModel n → ℂ} {ρ A₂ : ℝ} (hρ : 1 < ρ)
    (hg : DifferentiableOn ℂ g (ball 0 ρ))
    (hA : ∀ y ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fderiv ℂ g) y‖ ≤ A₂) (l : Fin n)
    {s : ComplexModel n} (hs : s ∈ closedBall (0 : ComplexModel n) 1) :
    ‖fderiv ℂ (hadamardCoeff g l) s‖ ≤ A₂ := by
  have hsρ : s ∈ ball (0 : ComplexModel n) ρ := closedBall_subset_ball hρ hs
  rw [(hasFDerivAt_hadamardCoeff hg l hsρ).fderiv]
  have hopen : IsOpen (ball (0 : ComplexModel n) ρ) := isOpen_ball
  have hDg' : ContDiffOn ℂ ∞ (fderiv ℂ g) (ball 0 ρ) :=
    (contDiffOn_of_differentiableOn_complex hg hopen).fderiv_of_isOpen hopen (by simp)
  have hDg : DifferentiableOn ℂ (fderiv ℂ g) (ball 0 ρ) := hDg'.differentiableOn (by simp)
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := A₂) ?_) (by norm_num)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
  have hts : t • s ∈ closedBall (0 : ComplexModel n) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
    rw [mem_closedBall, dist_zero_right] at hs
    nlinarith [ht'.2, norm_nonneg s]
  have hD : DifferentiableAt ℂ (fderiv ℂ g) (t • s) :=
    hDg.differentiableAt (hopen.mem_nhds (closedBall_subset_ball hρ hts))
  have hder : fderiv ℂ (fun y => fderiv ℂ g y (coordinateVector l)) (t • s) =
      (fderiv ℂ (fderiv ℂ g) (t • s)).flip (coordinateVector l) := by
    have := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector (n := n) l) (t • s))
    rw [this.fderiv]
    ext v
    simp
  rw [hder, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
  have h1 : ‖(fderiv ℂ (fderiv ℂ g) (t • s)).flip (coordinateVector l)‖ ≤
      ‖fderiv ℂ (fderiv ℂ g) (t • s)‖ := by
    refine ((fderiv ℂ (fderiv ℂ g) (t • s)).flip.le_opNorm _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    simp [coordinateVector]
  calc t * ‖(fderiv ℂ (fderiv ℂ g) (t • s)).flip (coordinateVector l)‖
      ≤ 1 * ‖fderiv ℂ (fderiv ℂ g) (t • s)‖ :=
        mul_le_mul ht'.2 h1 (norm_nonneg _) zero_le_one
    _ ≤ A₂ := by rw [one_mul]; exact hA _ hts

end SGPT.NPP.DN4
