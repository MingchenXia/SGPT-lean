import SGPT.Foundations.Analysis.Pending.FubiniStudyLineLevi
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# Levi forms for the Kähler form of a blowup

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  Three pointwise
computations used in the local positivity of `P^*ω + ddᶜ(ε log R + Σ|h_k|²)`:

* `smoothDDC_log_pos_of_line`: if along the complex line `w₀ + t v` a weight equals
  `‖X + t Y‖²` with `X ≠ 0` and `Y ∉ ℂ X` (Fubini–Study in the fibre), then
  `ddᶜ log R (v, iv) > 0` at `w₀`;
* `quad_smoothDDC_norm_sq`: `ddᶜ ‖H‖² (v, iv) = ‖dH v‖² / π` for holomorphic `H`;
* `fderiv_monomial_eq_zero`: a vector killed by the differential of a monomial chart
  `σ_j(w) = (w_l)_{l<k}, w_j, (w_j w_l)_{l ≥ k, l ≠ j}` has vanishing coordinates `l < k` and `j`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Unibranch.KS3FibreLevi

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FubiniStudyLineLevi BlowupMonomialCharts

section Line

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

/-- **Fubini–Study positivity in a fibre direction.** -/
theorem smoothDDC_log_pos_of_line {n : ℕ} {Rw : ComplexModel n → ℝ} {w₀ v : ComplexModel n}
    {X Y : H} (hC2 : ContDiffAt ℝ 2 (fun w => Real.log (Rw w)) w₀)
    (hline : ∀ t : ℂ, Rw (w₀ + t • v) = ‖X + t • Y‖ ^ 2)
    (hind : ∀ r : ℂ, Y ≠ r • X) (hX : X ≠ 0) :
    0 < smoothDDC (fun w => Real.log (Rw w)) w₀ ![v, Complex.I • v] := by
  rw [quad_smoothDDC_eq_leviForm hC2, leviForm_eq_line hC2]
  apply div_pos _ Real.pi_pos
  have hfun : (fun t : ℂ => Real.log (Rw (w₀ + t • v))) =
      fun t : ℂ => Real.log (‖X + t • Y‖ ^ 2) := funext fun t => by rw [hline]
  rw [hfun]
  exact leviForm_log_normSq_line_pos hind hX

end Line

/-- **`ddᶜ` of `‖H‖²`** for a holomorphic map `H`. -/
theorem quad_smoothDDC_norm_sq {n s : ℕ} {T : Set (ComplexModel n)} (hT : IsOpen T)
    {Hf : ComplexModel n → ComplexModel s} (hH : ContDiffOn ℂ ∞ Hf T) {z : ComplexModel n}
    (hz : z ∈ T) (v : ComplexModel n) :
    smoothDDC (fun u => ‖Hf u‖ ^ 2) z ![v, Complex.I • v] = ‖fderiv ℝ Hf z v‖ ^ 2 / Real.pi := by
  have h2 : ContDiffAt ℝ 2 (fun u => ‖Hf u‖ ^ 2) z :=
    (((contDiff_norm_sq ℝ).comp_contDiffOn (hH.restrict_scalars ℝ)).contDiffAt
      (hT.mem_nhds hz)).of_le (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [smoothDDC_complexDiagonal_eq_leviForm h2 v,
    LeviFormHolomorphicComp.leviForm_comp hT isOpen_univ hH (contDiff_norm_sq ℝ).contDiffOn
      (mapsTo_univ _ _) hz v, leviForm_norm_sq]

/-- The sum of `|H_k|²` is `‖H‖²`. -/
theorem sum_normSq_eq_norm_sq {s : ℕ} (w : ComplexModel s) :
    ∑ k, Complex.normSq (w k) = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun k _ => Complex.normSq_eq_norm_sq _

/-- **The kernel of a monomial chart.** -/
theorem fderiv_monomial_eq_zero {n k : ℕ} {j : Fin n} (_hj : k ≤ j.1) (w₀ v : ComplexModel n)
    (h : fderiv ℝ (monomial k j) w₀ v = 0) :
    (∀ i : Fin n, i.1 < k → v i = 0) ∧ v j = 0 := by
  have hm : HasFDerivAt (monomial k j) (fderiv ℝ (monomial k j) w₀) w₀ :=
    (((contDiff_monomial k j).restrict_scalars ℝ).differentiable (by simp) w₀).hasFDerivAt
  have hcoord : ∀ i : Fin n, ¬ (k ≤ i.1 ∧ i ≠ j) → v i = 0 := by
    intro i hi
    let L : ComplexModel n →L[ℝ] ℂ := (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ
    have h1 : HasFDerivAt (L ∘ monomial k j) (L.comp (fderiv ℝ (monomial k j) w₀)) w₀ :=
      L.hasFDerivAt.comp w₀ hm
    have hfun : L ∘ monomial k j = L := by
      funext w
      change (monomial k j w) i = w i
      rw [monomial_apply, if_neg hi]
    rw [hfun] at h1
    have h2 := h1.unique L.hasFDerivAt
    have h3 := congrArg (fun T : ComplexModel n →L[ℝ] ℂ => T v) h2
    simp only [ContinuousLinearMap.comp_apply, h, map_zero] at h3
    simpa [L] using h3.symm
  refine ⟨fun i hi => hcoord i (fun h' => by omega), hcoord j (fun h' => h'.2 rfl)⟩

end SGPT.Unibranch.KS3FibreLevi
