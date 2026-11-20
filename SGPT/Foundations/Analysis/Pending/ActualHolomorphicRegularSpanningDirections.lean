import SGPT.Foundations.Analysis.Pending.RegularDirectionDense
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic

set_option autoImplicit false

/-! # Actual unit regular directions forming a basis

The original nonzero holomorphic germ internally produces a genuine
basis of unit regular directions, including the empty basis in dimension zero.
-/

noncomputable section
open Set Filter Metric Module
open scoped Topology
namespace SGPT.Foundations.Analysis.Pending.ActualHolomorphicRegularSpanningDirections
open RegularDirectionDense

/-- A genuine nonzero holomorphic germ internally produces an actual basis
of unit regular directions, without supplied spanning or regularity data. -/
theorem exists_unit_regular_basis {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (hg : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), DifferentiableAt ℂ g x)
    (hne : ¬ ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), g x = 0) :
    ∃ b : Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i, ‖b i‖ = 1 ∧ RegularAlong g (b i) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  have hdiff : DifferentiableOn ℂ g (ball 0 r) :=
    fun x hx => (hball x hx).differentiableWithinAt
  have hdense := dense_setOf_regularAlong hr hdiff hne
  have hdensePi : Dense (Set.pi (Set.univ : Set (Fin n))
      (fun _ => {w : EuclideanSpace ℂ (Fin n) | RegularAlong g w})) :=
    dense_pi Set.univ (fun _ _ => hdense)
  have hopen : IsOpen {w : Fin n → EuclideanSpace ℂ (Fin n) | LinearIndependent ℂ w} :=
    isOpen_setOfPred_linearIndependent
  have hnonempty : {w : Fin n → EuclideanSpace ℂ (Fin n) |
      LinearIndependent ℂ w}.Nonempty :=
    ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.linearIndependent⟩
  obtain ⟨w, hwreg, hwli⟩ := hdensePi.exists_mem_open hopen hnonempty
  let c : Fin n → ℂ := fun i => (‖w i‖ : ℂ)⁻¹
  have hc (i : Fin n) : c i ≠ 0 := by
    change (‖w i‖ : ℂ)⁻¹ ≠ 0
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (LinearIndependent.ne_zero i hwli)
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => c i • w i
  have hvli : LinearIndependent ℂ v := by
    have h := hwli.units_smul (fun i => Units.mk0 (c i) (hc i))
    exact h
  have hv : ∀ i, ‖v i‖ = 1 ∧ RegularAlong g (v i) := by
    intro i
    refine ⟨norm_smul_inv_norm (LinearIndependent.ne_zero i hwli), ?_⟩
    exact (regularAlong_smul (hc i) (w i)).mpr (hwreg i (Set.mem_univ i))
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hvli (by simp), ?_⟩
  simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv

end SGPT.Foundations.Analysis.Pending.ActualHolomorphicRegularSpanningDirections
