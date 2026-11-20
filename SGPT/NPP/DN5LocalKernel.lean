import SGPT.NPP.DN5Smoothing
import SGPT.NPP.DN5ChangeVar
import SGPT.Envelopes.TosC11cMetric

/-!
# Kernel representation of the chart-level smoothing `localSmoothing`

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 222–224).  Chart-level version
of `SGPT.NPP.DN5.exists_localKernelRep`, for an abstract local fibre map `Φ` and a smooth strictly
positive `(1,1)` coefficient `α` (for lane DN4, `DN4/notes.md`):
near `(z₀, 0)` and for `0 < t < δ`,
`localSmoothing Φ α f z t = (∫ f(y) K((z, t), y) dy) / ∫ K((z, t), y) dy`,
`K ≥ 0` smooth in `((z, t), y)` and supported in a fixed compact set (`exists_localSmoothing_kernel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Analysis.KahlerNormal

variable {N : ℕ}

/-- The chart-level weight `χ(π α_z(ξ, iξ))`. -/
def localWeight (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (z ξ : ComplexModel N) :
    ℝ :=
  DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ])

variable {α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ}

theorem localWeight_nonneg (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ)
    (z ξ : ComplexModel N) : 0 ≤ localWeight α z ξ :=
  DN3.chi_nonneg N _

theorem contDiffOn_localWeight {U : Set (ComplexModel N)} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => localWeight α q.1 q.2)
      (U ×ˢ univ) := by
  have hm : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N =>
      SGPT.Envelopes.TosC11c.twoFormMetric (α q.1)) (U ×ˢ univ) :=
    (SGPT.Envelopes.TosC11c.isBoundedLinearMap_twoFormMetric (n := N)).contDiff.comp_contDiffOn
      (hα.comp contDiffOn_fst (fun q hq => hq.1))
  have hξ : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => q.2) (U ×ˢ univ) :=
    contDiffOn_snd
  exact (DN3.contDiff_chi N).comp_contDiffOn
    (contDiffOn_const.mul ((hm.clm_apply hξ).clm_apply hξ))

/-- In a frame `L` normalizing `α_z`, the weight is the Euclidean kernel. -/
theorem localWeight_frame {z : ComplexModel N} {L : ComplexModel N ≃L[ℂ] ComplexModel N}
    (hL : ∀ u v, α z ![L u, L v] = flatForm N ![u, v]) (s : ComplexModel N) :
    localWeight α z (L s) = DN3.kernel N s := by
  rw [localWeight, ← L.map_smul Complex.I s, hL, flatForm_apply_I_smul_self, ← mul_assoc,
    mul_inv_cancel₀ Real.pi_ne_zero, one_mul, DN3.kernel]

theorem integral_localWeight_pos {z : ComplexModel N} (h11 : IsOneOne (α z))
    (hpos : IsStrictlyPositive (α z)) : 0 < ∫ ξ, localWeight α z ξ := by
  obtain ⟨L, hL⟩ := exists_normalizing_linear h11 hpos
  rw [integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)]
  have : ∀ s, localWeight α z ((L.restrictScalars ℝ) s) = DN3.kernel N s :=
    fun s => localWeight_frame hL s
  simp_rw [this, DN3.integral_kernel, mul_one]
  exact abs_det_pos _

/-- The support of the weight is bounded uniformly near a point of positivity. -/
theorem exists_localWeight_support_bound {U : Set (ComplexModel N)} (hU : IsOpen U)
    (hα : ContDiffOn ℝ ∞ α U) (hpos : ∀ z ∈ U, IsStrictlyPositive (α z))
    {z₀ : ComplexModel N} (hz₀ : z₀ ∈ U) :
    ∃ U' : Set (ComplexModel N), IsOpen U' ∧ z₀ ∈ U' ∧ U' ⊆ U ∧ ∃ R : ℝ,
      ∀ z ∈ U', ∀ ξ, localWeight α z ξ ≠ 0 → ‖ξ‖ ≤ R := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hK : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrsub
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul hα.continuousOn hpos
    (isCompact_closedBall z₀ (r / 2)) hK
  refine ⟨ball z₀ (r / 2), isOpen_ball, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hK, 1 + (Real.pi * m)⁻¹, ?_⟩
  intro z hz ξ hξ
  have hlt : Real.pi * α z ![ξ, Complex.I • ξ] < 1 := by
    by_contra h
    exact hξ (DN3.chi_eq_zero_of_le N (not_lt.mp h))
  have hle := hmK z (ball_subset_closedBall hz) ξ
  have hpm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have h2 : Real.pi * m * ‖ξ‖ ^ 2 < 1 := by nlinarith [Real.pi_pos]
  have h3 : ‖ξ‖ ^ 2 ≤ (Real.pi * m)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpm]
    linarith
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

/-- **Kernel representation of the chart-level smoothing.** -/
theorem exists_localSmoothing_kernel {Φ : ComplexModel N → ComplexModel N → ComplexModel N}
    {O : Set (ComplexModel N × ComplexModel N)} (hΦ : IsLocalFibreMap Φ O)
    {U : Set (ComplexModel N)} (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (h11 : ∀ z ∈ U, IsOneOne (α z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (α z))
    {z₀ : ComplexModel N} (hz₀U : z₀ ∈ U) (hz₀O : (z₀, (0 : ComplexModel N)) ∈ O)
    {W : Set (ComplexModel N)} (hW : W ∈ 𝓝 z₀) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ C : Set (ComplexModel N), IsCompact C ∧ C ⊆ W ∧
      ∃ K : ComplexModel N × ℝ → ComplexModel N → ℝ,
        ContDiffOn ℝ ∞ (fun q : (ComplexModel N × ℝ) × ComplexModel N => K q.1 q.2)
          ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ) ∧
        (∀ p y, y ∉ C → K p y = 0) ∧ (∀ p y, 0 ≤ K p y) ∧ ball z₀ ε ⊆ U ∧
        (∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ ξ, localWeight α z ξ ≠ 0 → (z, t • ξ) ∈ O) ∧
        (∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, 0 < ∫ y, K (z, t) y) ∧
        ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ f : ComplexModel N → ℝ,
          localSmoothing Φ α f z t = (∫ y, f y * K (z, t) y) / ∫ y, K (z, t) y := by
  obtain ⟨U', hU', hz₀U', hU'U, R, hR⟩ := exists_localWeight_support_bound hU hα hpos hz₀U
  have hk := (contDiffOn_localWeight hα).mono
    (prod_mono hU'U (subset_refl (univ : Set (ComplexModel N))))
  obtain ⟨ε, δ, hε, hδ, C, hC, hCW, K, hK, hKC, hK0, hεU, hsrc, hrep⟩ :=
    exists_transportKernel hΦ hU' hk hR hz₀U' hz₀O hW
  have hden : ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ,
      (∫ ξ, localWeight α z ξ) = ∫ y, K (z, t) y := by
    intro z hz t ht
    have H := hrep z hz t ht (fun _ => 1)
    simp only [one_mul] at H
    exact H
  refine ⟨ε, δ, hε, hδ, C, hC, hCW, K, hK, hKC, hK0 (localWeight_nonneg α), hεU.trans hU'U,
    hsrc, fun z hz t ht => ?_, fun z hz t ht f => ?_⟩
  · rw [← hden z hz t ht]
    exact integral_localWeight_pos (h11 z (hU'U (hεU hz))) (hpos z (hU'U (hεU hz)))
  · rw [← hden z hz t ht, ← hrep z hz t ht f]
    rfl

end SGPT.NPP.DN5
