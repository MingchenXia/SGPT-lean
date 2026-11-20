import SGPT.PSH.HermitianBalayageFrozenCorrections

/-!
# A common quadratic dominating all frozen upper corrections

One actual quadratic is chosen on a compact coordinate buffer before
all centers, scales and potentials. Domination of the coefficient field
augmented by the maximal flat error gives both background domination and
domination of every frozen upper correction. This is the fixed current
used to sum the local mass estimates.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorCollar
open scoped Topology ContDiff

/-- A single genuine quadratic dominates both the varying background and
all frozen upper corrections with flat error bounded by `T`. The coefficient
is selected before every center, error and constant-background potential. -/
theorem exists_compact_common_frozen_correction {n : ℕ}
    (b : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hb : ContinuousOn b K)
    {T : ℝ} (hT : 0 ≤ T) (z₀ : ComplexModel n) :
    ∃ A : ℝ, 0 < A ∧
      (∀ z ∈ K, ∀ v : ComplexModel n,
        b z ![v, Complex.I • v] ≤ smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v]) ∧
      ∀ a ∈ K, ∀ δ : ℝ, δ ≤ T → ∀ h : ComplexModel n → ℝ,
        ContDiff ℝ ∞ h → (∀ z, smoothDDC h z = b a) →
        ∀ z v : ComplexModel n,
          smoothDDC (frozenUpperCorrection h a δ) z ![v, Complex.I • v] ≤
            smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] := by
  let c := fun z => b z + T • kahlerForm n
  have hc : ContinuousOn c K := hb.add continuousOn_const
  obtain ⟨A, hA, hdom⟩ := HermitianQuadratic.exists_compact_quadratic_domination c hK hc z₀
  have hq := contDiff_ballPot A z₀ 0
  have hconstant (x y v : ComplexModel n) :
      smoothDDC (ballPot A z₀ 0) x ![v, Complex.I • v] =
        smoothDDC (ballPot A z₀ 0) y ![v, Complex.I • v] := by
    rw [smoothDDC_complexDiagonal_eq_leviForm
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      smoothDDC_complexDiagonal_eq_leviForm
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      leviForm_ballPot, leviForm_ballPot]
  have haug (z : ComplexModel n) (hz : z ∈ K) (v : ComplexModel n) :
      b z ![v, Complex.I • v] + T * ‖v‖ ^ 2 ≤
        smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] := by
    simpa only [c, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, kahlerForm_apply_I] using hdom z hz v
  refine ⟨A, hA, ?_, ?_⟩
  · intro z hz v
    exact (le_add_of_nonneg_right (mul_nonneg hT (sq_nonneg _))).trans (haug z hz v)
  · intro a ha δ hδ h hh hddc z v
    have hupper : smoothDDC (frozenUpperCorrection h a δ) z = b a + δ • kahlerForm n := by
      change smoothDDC (fun y => h y + δ * centeredFlatQuadratic a y) z = _
      rw [smoothDDC_add isOpen_univ hh.contDiffOn
        (contDiff_const.mul (contDiff_centeredFlatQuadratic a)).contDiffOn (mem_univ z), hddc]
      have hs := smoothDDC_smul isOpen_univ (contDiff_centeredFlatQuadratic a).contDiffOn δ (mem_univ z)
      simpa only [smul_eq_mul, smoothDDC_centeredFlatQuadratic] using congrArg (fun Q => b a + Q) hs
    rw [hupper]
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, kahlerForm_apply_I]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hδ (sq_nonneg _))).trans
      ((haug a ha v).trans_eq (hconstant a z v))

end SGPT.PSH.HermitianBalayage
