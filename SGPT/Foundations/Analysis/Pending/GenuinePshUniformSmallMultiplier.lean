import SGPT.Foundations.Analysis.Pending.NormalizedPshUniformUnitMultiplier
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim

set_option autoImplicit false

/-! # Genuine uniform unit multiplier levels, with a real zero-dimensional branch -/

open Metric Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.GenuinePshUniformSmallMultiplier
open FirstPass FirstPass.HolomorphicIdealSheaves

noncomputable section

/-- Genuine nondegeneracy on the actual open singleton gives every positive unit level. -/
theorem one_mem_multiplierIdeal_of_dim_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] {θ : SmoothRealForm 0 M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {d : ℝ} (hd : 0 < d) (x : M) :
    (multiplierIdeal (n := 0) d u).mem x (fun _ => (1 : ℂ)) := by
  let e : ComplexChart 0 M := complexChartAt (n := 0) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hbot : u x ≠ ⊥ := FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hu x
  have htop : u x ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top x
  have hval : ∀ z : ComplexModel 0, chartFunction u e z = ((u x).toReal : EReal) := by
    intro z
    have hz : z = e.val x := Subsingleton.elim _ _
    change u (e.val.symm z) = _
    rw [hz, e.val.left_inv hxs]
    exact (EReal.coe_toReal htop hbot).symm
  have hdens : multiplierDensity (chartFunction u e) d (fun _ => (1 : ℂ)) =
      fun _ => ENNReal.ofReal (Real.exp (-(d * (u x).toReal))) := by
    funext z
    simp only [multiplierDensity, hval z, norm_one, one_pow, ENNReal.ofReal_one, one_mul,
      multiplierWeight_coe]
  refine ⟨holomorphicAt_const (n := 0) (M := M) 1, hd,
    ball (e.val x) 1, isOpen_ball, mem_ball_self one_pos,
    differentiableOn_const (1 : ℂ), ?_, ?_⟩
  · change AEMeasurable (multiplierDensity (chartFunction u e) d (fun _ => (1 : ℂ))) _
    rw [hdens]
    exact aemeasurable_const
  · change (∫⁻ z in ball (e.val x) 1,
      multiplierDensity (chartFunction u e) d (fun _ => (1 : ℂ)) z) < ⊤
    rw [hdens, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]

/-- The actual dimension-zero finite chart integral extends the produced common
small unit level to every complex dimension, without a zero-dimensional Lelong claim. -/
theorem exists_uniform_small_level_one_mem
    {θ : SmoothRealForm n M 2} (hθ : HasSmoothLocalPotentials θ) :
    ∃ a : ℝ, 0 < a ∧ ∀ u : M → EReal, IsThetaPshPotential θ u →
      ∀ x : M, (multiplierIdeal (n := n) a u).mem x (fun _ => (1 : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact ⟨1, one_pos, fun u hu x => one_mem_multiplierIdeal_of_dim_zero hu one_pos x⟩
  · exact NormalizedPshUniformUnitMultiplier.exists_uniform_small_level_one_mem_of_genuine hn hθ


end
end SGPT.Foundations.Analysis.Pending.GenuinePshUniformSmallMultiplier
