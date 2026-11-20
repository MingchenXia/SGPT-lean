import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Time derivatives of `C¹` families of holomorphic functions

Infrastructure of lane COHERENT (source `lma:fibIeq`; blueprint `claude-coherent.tex`), for the
generator of a circle action (`CohCircle`).

Let `H : ℝ × E → ℂ` be `C¹` (over `ℝ`) on an open set containing the closed ball of radius `ρ`
around `(0, w₀)`, and put `∂_θ H(0, w) = dH_{(0,w)}(1, 0)` (`timeDeriv H w`).

* `hasDerivAt_timeDeriv`: `θ ↦ H(θ, w)` has derivative `∂_θ H(0, w)` at `0`.
* `tendstoUniformlyOn_diffQuot`: the difference quotients `(m + 1)(H(1/(m+1), w) - H(0, w))`
  converge to `∂_θ H(0, w)` uniformly on the ball of radius `ρ` around `w₀` (mean value
  inequality and uniform continuity of `dH` on the compact closed ball).
* `differentiableOn_timeDeriv`: if `E` is a complex space and the slices `w ↦ H(θ, w)` are
  holomorphic, then `w ↦ ∂_θ H(0, w)` is holomorphic (Weierstrass, from `SGPT.Foundations.Analysis`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace SGPT.GAGA.Coherent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The partial derivative in the time variable at time `0`: `∂_θ H(0, w) = dH_{(0,w)}(1, 0)`. -/
def timeDeriv (H : ℝ × E → ℂ) (w : E) : ℂ :=
  fderiv ℝ H ((0 : ℝ), w) ((1 : ℝ), (0 : E))

/-- The curve `θ ↦ (θ, w)` has velocity `(1, 0)`. -/
theorem hasDerivAt_pair (θ : ℝ) (w : E) :
    HasDerivAt (fun τ : ℝ => ((τ, w) : ℝ × E)) ((1 : ℝ), (0 : E)) θ :=
  (hasDerivAt_id θ).prodMk (hasDerivAt_const θ w)

/-- `θ ↦ H(θ, w)` has derivative `dH_{(θ,w)}(1,0)` at `θ`. -/
theorem hasDerivAt_slice {H : ℝ × E → ℂ} {θ : ℝ} {w : E} (hH : DifferentiableAt ℝ H (θ, w)) :
    HasDerivAt (fun τ : ℝ => H (τ, w)) (fderiv ℝ H (θ, w) ((1 : ℝ), (0 : E))) θ :=
  hH.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_pair θ w)

/-- `θ ↦ H(θ, w)` has derivative `∂_θ H(0, w)` at `0`. -/
theorem hasDerivAt_timeDeriv {H : ℝ × E → ℂ} {w : E} (hH : DifferentiableAt ℝ H ((0 : ℝ), w)) :
    HasDerivAt (fun τ : ℝ => H (τ, w)) (timeDeriv H w) 0 :=
  hasDerivAt_slice hH

/-- The difference quotient at time `1/(m+1)`. -/
def diffQuot (H : ℝ × E → ℂ) (m : ℕ) (w : E) : ℂ :=
  ((m : ℂ) + 1) * (H (((m : ℝ) + 1)⁻¹, w) - H ((0 : ℝ), w))

omit [NormedSpace ℂ E] in
theorem norm_pair_one_zero : ‖(((1 : ℝ), (0 : E)) : ℝ × E)‖ = 1 := by
  simp [Prod.norm_def]

/-- **Uniform convergence of difference quotients.** -/
theorem tendstoUniformlyOn_diffQuot [ProperSpace E] {H : ℝ × E → ℂ} {Ω : Set (ℝ × E)}
    (hΩ : IsOpen Ω) (hH : ContDiffOn ℝ 1 H Ω) {w₀ : E} {ρ : ℝ}
    (hK : closedBall (((0 : ℝ), w₀) : ℝ × E) ρ ⊆ Ω) :
    TendstoUniformlyOn (diffQuot H) (timeDeriv H) atTop (ball w₀ ρ) := by
  have hcont : ContinuousOn (fderiv ℝ H) Ω := hH.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hKc : IsCompact (closedBall (((0 : ℝ), w₀) : ℝ × E) ρ) := isCompact_closedBall _ _
  have huc := hKc.uniformContinuousOn_of_continuous (hcont.mono hK)
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδK⟩ := huc (ε / 2) (half_pos hε)
  have hev : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1)⁻¹ < δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
    refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
    have hm' : δ⁻¹ < (m : ℝ) + 1 := by
      have : (N : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [inv_lt_comm₀ (by positivity) hδ]
    exact hm'
  have hev' : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1)⁻¹ ≤ ρ ∨ ¬ (ball w₀ ρ).Nonempty := by
    by_cases hne : (ball w₀ ρ).Nonempty
    · have hρ : 0 < ρ := by
        obtain ⟨w, hw⟩ := hne
        exact lt_of_le_of_lt dist_nonneg hw
      obtain ⟨N, hN⟩ := exists_nat_gt ρ⁻¹
      refine eventually_atTop.2 ⟨N, fun m hm => Or.inl ?_⟩
      have hm' : ρ⁻¹ < (m : ℝ) + 1 := by
        have : (N : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      rw [inv_le_comm₀ (by positivity) hρ]
      exact hm'.le
    · exact Eventually.of_forall fun _ => Or.inr hne
  filter_upwards [hev, hev'] with m hm hm' w hw
  have hρ' : ((m : ℝ) + 1)⁻¹ ≤ ρ := hm'.resolve_right (not_not.2 ⟨w, hw⟩)
  set θ : ℝ := ((m : ℝ) + 1)⁻¹ with hθ
  have hθpos : 0 < θ := by positivity
  set D := timeDeriv H w with hD
  have hmemK : ∀ τ ∈ Icc (0 : ℝ) θ, ((τ, w) : ℝ × E) ∈ closedBall (((0 : ℝ), w₀) : ℝ × E) ρ := by
    intro τ hτ
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
      exact hτ.2.trans hρ'
    · exact (mem_ball.1 hw).le
  set φ : ℝ → ℂ := fun τ => H (τ, w) - (τ : ℂ) * D with hφ
  have hderiv : ∀ τ ∈ Icc (0 : ℝ) θ,
      HasDerivWithinAt φ (fderiv ℝ H (τ, w) ((1 : ℝ), (0 : E)) - D) (Icc 0 θ) τ := by
    intro τ hτ
    have hdiff : DifferentiableAt ℝ H (τ, w) :=
      (hH.contDiffAt (hΩ.mem_nhds (hK (hmemK τ hτ)))).differentiableAt one_ne_zero
    have h1 := hasDerivAt_slice hdiff
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * D) (1 * D) τ :=
      ((hasDerivAt_id τ).ofReal_comp).mul_const D
    rw [one_mul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ τ ∈ Ico (0 : ℝ) θ, ‖fderiv ℝ H (τ, w) ((1 : ℝ), (0 : E)) - D‖ ≤ ε / 2 := by
    intro τ hτ
    have hτK := hmemK τ (Ico_subset_Icc_self hτ)
    have h0K := hmemK 0 ⟨le_rfl, hθpos.le⟩
    have hdist : dist ((τ, w) : ℝ × E) (0, w) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
      exact max_lt (hτ.2.trans hm) hδ
    have h := hδK _ hτK _ h0K hdist
    rw [dist_eq_norm] at h
    calc ‖fderiv ℝ H (τ, w) ((1 : ℝ), (0 : E)) - D‖
        = ‖(fderiv ℝ H (τ, w) - fderiv ℝ H (0, w)) ((1 : ℝ), (0 : E))‖ := by
          rw [hD, timeDeriv]; rfl
      _ ≤ ‖fderiv ℝ H (τ, w) - fderiv ℝ H (0, w)‖ * ‖(((1 : ℝ), (0 : E)) : ℝ × E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε / 2 := by rw [norm_pair_one_zero, mul_one]; exact h.le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound θ
    (right_mem_Icc.2 hθpos.le)
  have hφ0 : φ 0 = H (0, w) := by simp [hφ]
  have hkey : diffQuot H m w - D = ((m : ℂ) + 1) * (φ θ - φ 0) := by
    have hmθ : ((m : ℂ) + 1) * (θ : ℂ) = 1 := by
      rw [hθ]
      push_cast
      field_simp
    rw [hφ0]
    show ((m : ℂ) + 1) * (H (θ, w) - H (0, w)) - D = _
    simp only [hφ]
    linear_combination D * hmθ
  rw [dist_comm, dist_eq_norm, hkey, norm_mul]
  have hnm : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hnm]
  calc ((m : ℝ) + 1) * ‖φ θ - φ 0‖ ≤ ((m : ℝ) + 1) * (ε / 2 * (θ - 0)) :=
        mul_le_mul_of_nonneg_left hmv (by positivity)
    _ = ε / 2 := by
        rw [sub_zero, hθ]
        field_simp
    _ < ε := half_lt_self hε

/-- **Holomorphy of the time derivative** (Weierstrass). If the slices `w ↦ H(1/(m+1), w)` (for
large `m`) and `w ↦ H(0, w)` are holomorphic on a ball and the difference quotients converge uniformly there,
then `w ↦ ∂_θ H(0, w)` is holomorphic on the ball. -/
theorem differentiableOn_timeDeriv {H : ℝ × E → ℂ} {w₀ : E} {ρ : ℝ}
    (hhol : ∀ᶠ m : ℕ in atTop,
      DifferentiableOn ℂ (fun w => H (((m : ℝ) + 1)⁻¹, w)) (ball w₀ ρ))
    (h0 : DifferentiableOn ℂ (fun w => H ((0 : ℝ), w)) (ball w₀ ρ))
    (hlim : TendstoUniformlyOn (diffQuot H) (timeDeriv H) atTop (ball w₀ ρ)) :
    DifferentiableOn ℂ (timeDeriv H) (ball w₀ ρ) := by
  intro w hw
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 isOpen_ball w hw
  have hd : ∀ᶠ m : ℕ in atTop, DifferentiableOn ℂ (diffQuot H m) (ball w r) := by
    filter_upwards [hhol] with m hm
    exact ((hm.sub h0).const_mul ((m : ℂ) + 1)).mono hrsub
  exact (SGPT.Foundations.Analysis.FirstPass.differentiableAt_of_tendstoUniformlyOn_ball hr hd
    (hlim.mono hrsub)).differentiableWithinAt

end SGPT.GAGA.Coherent
