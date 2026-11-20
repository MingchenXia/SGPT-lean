import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies

set_option autoImplicit false

/-!
# Local limits from convergence on a dense set

A sequence already chosen by a simultaneous diagonal argument is retained here: local
boundedness and holomorphicity turn Cauchy convergence on a dense set into local uniform
convergence to a holomorphic limit. This is an auxiliary normal-family result, independent
of the weighted extension theorem.
-/

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

namespace SGPT

noncomputable section

variable {n : ℕ}

/-- Preserve the original sequence when passing from dense-set Cauchy convergence to a
holomorphic, locally uniform limit. -/
theorem holomorphic_limit_of_eventually_bounded_of_cauchy_dense
    {U D : Set (ComplexModel n)} (hU : IsOpen U) (f : ℕ → ComplexModel n → ℂ)
    (hf : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (f i) (ball x r) ∧ ∀ y ∈ ball x r, ‖f i y‖ ≤ M)
    (hUD : U ⊆ closure D) (hD : ∀ d ∈ D, CauchySeq fun i => f i d) :
    DifferentiableOn ℂ (fun y => limUnder atTop fun i => f i y) U ∧
      TendstoLocallyUniformlyOn f (fun y => limUnder atTop fun i => f i y) atTop U ∧
      ∀ y ∈ U, Tendsto (fun i => f i y) atTop
        (𝓝 (limUnder atTop fun i => f i y)) := by
  choose! R hR hRU hRd hRc using fun x (hx : x ∈ U) =>
    exists_uniformCauchySeqOn_ball_of_eventually_bounded hU hf hUD hD hx
  set G : ComplexModel n → ℂ := fun y => limUnder atTop fun i => f i y
  have hG : ∀ y ∈ U, Tendsto (fun i => f i y) atTop (𝓝 (G y)) := fun y hy =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      ((hRc y hy).cauchySeq (mem_ball_self (hR y hy))))
  have hunif : ∀ x ∈ U, TendstoUniformlyOn f G atTop (ball x (R x)) := fun x hx =>
    (hRc x hx).tendstoUniformlyOn_of_tendsto fun y hy => hG y (hRU x hx hy)
  refine ⟨fun x hx => ?_, tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx =>
    ⟨ball x (R x), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hR x hx)), hunif x hx⟩,
    hG⟩
  set ρ := R x
  have hρ : 0 < ρ := hR x hx
  have hder : UniformCauchySeqOn (fun i => fderiv ℂ (f i)) atTop (ball x (ρ / 2)) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hRd x hx)
    obtain ⟨N₂, hN₂⟩ := Metric.uniformCauchySeqOn_iff.1 (hRc x hx) (ε * (ρ / 2) / 2)
      (by positivity)
    refine ⟨max N₁ N₂, fun m hm k hk y hy => ?_⟩
    rw [dist_eq_norm]
    calc ‖fderiv ℂ (f m) y - fderiv ℂ (f k) y‖ ≤ ε * (ρ / 2) / 2 / (ρ / 2) :=
          norm_fderiv_sub_le_of_forall_norm_sub_le hρ (hN₁ m (le_of_max_le_left hm))
            (hN₁ k (le_of_max_le_left hk)) (fun z hz => by
              rw [← dist_eq_norm]
              exact (hN₂ m (le_of_max_le_right hm) k (le_of_max_le_right hk) z hz).le) hy
      _ < ε := by
        have : ε * (ρ / 2) / 2 / (ρ / 2) = ε / 2 := by field_simp
        linarith
  set g' : ComplexModel n → ComplexModel n →L[ℂ] ℂ :=
    fun y => limUnder atTop fun i => fderiv ℂ (f i) y
  have hderU : TendstoUniformlyOn (fun i => fderiv ℂ (f i)) g' atTop (ball x (ρ / 2)) :=
    hder.tendstoUniformlyOn_of_tendsto fun y hy =>
      tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hder.cauchySeq hy))
  have hGx : HasFDerivAt G (g' x) x := by
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (f := f) (f' := fun i => fderiv ℂ (f i))
      (hderU.tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.2 (ball_mem_nhds x (half_pos hρ)))) ?_ ?_
    · filter_upwards [(hRd x hx).prod_mk (ball_mem_nhds x hρ)] with p hp
      exact (hp.1.differentiableAt (isOpen_ball.mem_nhds hp.2)).hasFDerivAt
    · filter_upwards [ball_mem_nhds x hρ] with y hy
      exact hG y (hRU x hx hy)
  exact hGx.differentiableAt.differentiableWithinAt

end
end SGPT
