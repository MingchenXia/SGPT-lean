import SGPT.NPP.CodexC11ChartBallDensity
import SGPT.Envelopes.DNTC11Local

/-! The original obstacle supplies all finite polarization directions on one
actual chart ball. This does not yet identify a matrix-valued current.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11PolarizingDirections.lean` (module `C11PolarizingDirections`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11ChartBallDensity
open SGPT.Envelopes.DNTC11

namespace SGPT.NPP.Codex.C11PolarizingDirections
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A single actual ball carries bounded weak Levi densities for all four
polarization directions of every pair of complex coordinate vectors. -/
theorem exists_original_polarizing_direction_densities
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ (2*r) ⊆ e.val.target ∧
      let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
      ∃ (A : Fin n → Fin n → Fin 4 → ℝ)
        (d : Fin n → Fin n → Fin 4 → Ω → ℝ),
        ∀ j k t, 0 ≤ A j k t ∧ Measurable (d j k t) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |d j k t z| ≤ A j k t) ∧
          ∀ φ : 𝓓(Ω, ℝ),
            (∫ z, f (e.val.symm z) * leviForm φ z (polVec j k t)) =
              ∫ z : Ω, φ z * d j k t z ∂(volume.comap Subtype.val) := by
  obtain ⟨r,hr,htarget,hd⟩ := exists_chart_ball_directional_densities hf e hz₀
  refine ⟨r,hr,htarget,?_⟩
  choose A d hA hm hb ht using fun j k t => hd (polVec j k t)
  exact ⟨A,d,fun j k t => ⟨hA j k t,hm j k t,hb j k t,ht j k t⟩⟩

end SGPT.NPP.Codex.C11PolarizingDirections
