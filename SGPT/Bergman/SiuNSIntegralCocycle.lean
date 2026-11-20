import SGPT.Bergman.SiuNSCartierMetric
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Finite signed integral products of the actual original Cartier scalar
transitions, with their compatible actual smooth physical metric weights. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace ScalarLineCocycle

/-- The actual signed integral product cocycle is defined on one genuine
finite common cover. Its fibre transitions are the exact tensor/dual products. -/
def integralProduct {N : ℕ} (C : Fin N → ScalarLineCocycle n X)
    (b : Fin N → ℤ) : ScalarLineCocycle n X where
  dom i := ⋂ k, (C k).dom i
  open_dom i := isOpen_iInter_of_finite fun k => (C k).open_dom i
  mem_dom i := mem_iInter.mpr fun k => (C k).mem_dom i
  transition i j p := ∏ k, (C k).transition i j p ^ b k
  hol i j := by
    apply contMDiffOn_finsetProd
    intro k _
    have h : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ ((C k).transition i j)
        ((⋂ k, (C k).dom i) ∩ (⋂ k, (C k).dom j)) :=
      ((C k).hol i j).mono (fun p hp =>
      ⟨mem_iInter.mp hp.1 k, mem_iInter.mp hp.2 k⟩)
    cases hb : b k with
    | ofNat m => simpa using h.pow m
    | negSucc m =>
      simpa only [zpow_negSucc] using (h.pow (m + 1)).inv₀
        (fun p hp => pow_ne_zero _ ((C k).nonzero i j p
          ⟨mem_iInter.mp hp.1 k, mem_iInter.mp hp.2 k⟩))
  nonzero i j p hp := Finset.prod_ne_zero_iff.mpr fun k _ =>
    zpow_ne_zero _ ((C k).nonzero i j p ⟨mem_iInter.mp hp.1 k, mem_iInter.mp hp.2 k⟩)
  refl i p hp := by simp only [(C _).refl i p (mem_iInter.mp hp _), one_zpow, Finset.prod_const_one]
  mul i j l p hi hj hl := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    rw [← mul_zpow, (C k).mul i j l p (mem_iInter.mp hi k)
      (mem_iInter.mp hj k) (mem_iInter.mp hl k)]

end ScalarLineCocycle

private theorem log_norm_sq_integral_product {N : ℕ} (t : Fin N → ℂ)
    (ht : ∀ k, t k ≠ 0) (b : Fin N → ℤ) :
    Real.log (‖∏ k, t k ^ b k‖ ^ 2) = ∑ k, (b k : ℝ) * Real.log (‖t k‖ ^ 2) := by
  rw [norm_prod, Real.log_pow, Real.log_prod (fun k _ =>
    norm_ne_zero_iff.mpr (zpow_ne_zero _ (ht k)))]
  simp only [norm_zpow, Real.log_zpow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_pow]
  ring

namespace CompatibleScalarWeights

/-- Exact metric weights of the actual signed tensor/dual cocycle. -/
def integralProduct {N : ℕ} {C : Fin N → ScalarLineCocycle n X}
    (W : ∀ k, CompatibleScalarWeights (C k)) (b : Fin N → ℤ) :
    CompatibleScalarWeights (ScalarLineCocycle.integralProduct C b) where
  weight i p := ∑ k, (b k : ℝ) * (W k).weight i p
  smooth i c := by
    apply ContDiffOn.sum
    intro k _
    have h : ContDiffOn ℝ ∞ (fun z => (W k).weight i (c.val.symm z))
        (c.val.target ∩ c.val.symm ⁻¹' (⋂ k, (C k).dom i)) :=
      ((W k).smooth i c).mono (fun p hp => ⟨hp.1, mem_iInter.mp hp.2 k⟩)
    exact contDiffOn_const.mul h
  compatible i j p hi hj := by
    change (∑ k, (b k : ℝ) * (W k).weight i p) =
      Real.log (‖∏ k, (C k).transition i j p ^ b k‖ ^ 2) + ∑ k, (b k : ℝ) * (W k).weight j p
    rw [log_norm_sq_integral_product _ (fun k =>
      (C k).nonzero i j p ⟨mem_iInter.mp hi k, mem_iInter.mp hj k⟩)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [(W k).compatible i j p (mem_iInter.mp hi k) (mem_iInter.mp hj k)]
    ring

end CompatibleScalarWeights
end SGPT.BDivisor.NSKodaira
