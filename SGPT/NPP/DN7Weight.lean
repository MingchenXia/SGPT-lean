import SGPT.Foundations.Analysis.Pending.FactorizedWeightPsh
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# The logarithm of a factorized weight off its zeros

Lane DN7, `thm:DNT23_C11bar` (FPT `thm:big-metric-laplacian-rooftop`, passage to a modification;
FPT `def:gentle-analytic-singularities`).

A weight `U ≥ 0` on a complex manifold with local factorizations `U = |gₓ|² Uₓ'` (`gₓ`
holomorphic, `Uₓ'` smooth and positive: TN `FactorizedWeightForm.WeightFactorization`) has a glued
smooth closed form `Θ_U = ddᶜ log Uₓ'` (`WeightFactorization.closedForm`).  This is the *gentle*
normal form `log U = log |gₓ|² + smooth`.  Off the zeros of `U` the function `log U` is a smooth
local potential of `Θ_U`, in every chart (`log |gₓ|²` is pluriharmonic where `gₓ ≠ 0`).

We also record the elementary algebra of smooth local potentials used in the assembly: congruence
on an open set and adding a constant.

## Main results

* `SGPT.NPP.DN7.exists_isSmoothLocalPotential_log_weight`;
* `SGPT.NPP.DN7.isSmoothLocalPotential_congr`, `SGPT.NPP.DN7.isSmoothLocalPotential_add_const`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.NPP.DN7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.FactorizedWeightForm

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- Smooth local potentials only depend on the values on the (open) domain. -/
theorem isSmoothLocalPotential_congr {a : SmoothRealForm n Y 2} {e : ComplexChart n Y}
    {W : Set (ComplexModel n)} {ρ σ : ComplexModel n → ℝ} (h : IsSmoothLocalPotential a e W ρ)
    (heq : EqOn ρ σ W) : IsSmoothLocalPotential a e W σ := by
  refine ⟨h.1, h.2.1, h.2.2.1.congr fun z hz => (heq hz).symm, fun z hz => ?_⟩
  rw [← h.2.2.2 hz]
  exact smoothDDC_congr (Filter.eventuallyEq_of_mem (h.1.mem_nhds hz) heq).symm

/-- Adding a constant to a smooth local potential. -/
theorem isSmoothLocalPotential_add_const {a : SmoothRealForm n Y 2} {e : ComplexChart n Y}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (h : IsSmoothLocalPotential a e W ρ)
    (c : ℝ) : IsSmoothLocalPotential a e W (fun z => ρ z + c) := by
  refine ⟨h.1, h.2.1, h.2.2.1.add contDiffOn_const, fun z hz => ?_⟩
  rw [smoothDDC_add h.1 h.2.2.1 contDiffOn_const hz, GlobalPotentialTransforms.smoothDDC_const, add_zero]
  exact h.2.2.2 hz

/-- Restricting a smooth local potential to a smaller open set. -/
theorem isSmoothLocalPotential_inter {a : SmoothRealForm n Y 2} {e : ComplexChart n Y}
    {W V : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (h : IsSmoothLocalPotential a e W ρ)
    (hV : IsOpen V) : IsSmoothLocalPotential a e (W ∩ V) ρ :=
  h.mono (h.1.inter hV) inter_subset_left

/-- **Off its zeros, `log U` is a smooth local potential of the glued form `Θ_U`**, in every
chart.  The neighbourhood can be taken inside the positivity set of `U`. -/
theorem exists_isSmoothLocalPotential_log_weight {U : Y → ℝ} (F : WeightFactorization n U)
    (e : ComplexChart n Y) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hU : U (e.val.symm z) ≠ 0) :
    ∃ W : Set (ComplexModel n), z ∈ W ∧
      IsSmoothLocalPotential F.closedForm.val e W (fun ζ => Real.log (U (e.val.symm ζ))) ∧
      ∀ ζ ∈ W, 0 < U (e.val.symm ζ) := by
  set x := e.val.symm z with hx
  set S : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' F.domain x with hSdef
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (F.isOpen_domain x)
  set G : ComplexModel n → ℂ := fun ζ => F.gen x (e.val.symm ζ) with hGdef
  have hGd : ∀ ζ ∈ S, DifferentiableAt ℂ G ζ := fun ζ hζ =>
    differentiableAt_comp_chart_symm e hζ.1 (F.gen_mdifferentiable x _ hζ.2)
  have hGdiff : DifferentiableOn ℂ G S := fun ζ hζ => (hGd ζ hζ).differentiableWithinAt
  set W : Set (ComplexModel n) := S ∩ G ⁻¹' {w : ℂ | w ≠ 0} with hWdef
  have hW : IsOpen W := hGdiff.continuousOn.isOpen_inter_preimage hS isOpen_ne
  have hWS : W ⊆ S := inter_subset_left
  have hxdom : x ∈ F.domain x := F.mem_domain x
  have hzW : z ∈ W := ⟨⟨hz, hxdom⟩, F.gen_ne_zero_of hxdom hU⟩
  have hfac : ∀ ζ ∈ W, U (e.val.symm ζ) =
      Complex.normSq (G ζ) * F.smoothPart x (e.val.symm ζ) := fun ζ hζ =>
    F.factor x _ (hWS hζ).2
  have hns : ∀ ζ ∈ W, 0 < Complex.normSq (G ζ) := fun ζ hζ =>
    Complex.normSq_pos.mpr hζ.2
  have hsp : ∀ ζ ∈ W, 0 < F.smoothPart x (e.val.symm ζ) := fun ζ hζ =>
    F.pos x _ (hWS hζ).2
  have hpos : ∀ ζ ∈ W, 0 < U (e.val.symm ζ) := fun ζ hζ => by
    rw [hfac ζ hζ]; exact mul_pos (hns ζ hζ) (hsp ζ hζ)
  have hlogsp : ContDiffOn ℝ ∞ (fun ζ => Real.log (F.smoothPart x (e.val.symm ζ))) W :=
    ((F.smooth x e).log fun ζ hζ => (F.pos x _ hζ.2).ne').mono hWS
  have hlogG : ContDiffOn ℝ ∞ (fun ζ => Real.log (Complex.normSq (G ζ))) W := fun ζ hζ =>
    (MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hS hGdiff (hWS hζ)
      hζ.2).contDiffWithinAt
  have heq : EqOn (fun ζ => Real.log (Complex.normSq (G ζ)) +
      Real.log (F.smoothPart x (e.val.symm ζ))) (fun ζ => Real.log (U (e.val.symm ζ))) W := by
    intro ζ hζ
    simp only
    rw [hfac ζ hζ, Real.log_mul (hns ζ hζ).ne' (hsp ζ hζ).ne']
  have hpot : IsSmoothLocalPotential F.closedForm.val e W (fun ζ =>
      Real.log (Complex.normSq (G ζ)) + Real.log (F.smoothPart x (e.val.symm ζ))) := by
    refine ⟨hW, fun ζ hζ => (hWS hζ).1, hlogG.add hlogsp, fun ζ hζ => ?_⟩
    have hharm : smoothDDC (fun y => Real.log (Complex.normSq (G y))) ζ = 0 :=
      PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
        (Filter.eventually_of_mem (hS.mem_nhds (hWS hζ)) fun y hy => hGd y hy) hζ.2
    rw [smoothDDC_add hW hlogG hlogsp hζ, hharm, zero_add,
      (F.closedForm_coeff_eventuallyEq x e (hWS hζ).1 (hWS hζ).2).self_of_nhds]
  exact ⟨W, hzW, isSmoothLocalPotential_congr hpot heq, hpos⟩

end SGPT.NPP.DN7
