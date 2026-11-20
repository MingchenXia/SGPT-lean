import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false

/-! # Nonzero original tests under actual noncollapsed holomorphic pullback

The modification consumer internally supplies local noncollapse from the
actual off-analytic inverse. No nonzero composed test or Jacobian order is
supplied. This is a supplementary inverse-function/identity-theorem route;
it does not identify local reader pieces with whole global prime divisors.
Reference: Demailly, *Complex Analytic and Differential Geometry*, holomorphic
identity theorem and local holomorphic geometry.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.HolomorphicJacobianTestNonzeroPullback

open FirstPass DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

/-- Actual local noncollapse and the original nonzero holomorphic germ produce
nonzero values of the Jacobian-weighted test; no composed-test certificate. -/
theorem frequently_comp_mul_jacobian_ne_zero {n : ℕ}
    {f : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hf : ContDiffOn ℂ ∞ f D) {p : ComplexModel n} (hp : p ∈ D)
    (hJ : ∃ᶠ z in 𝓝 p, complexJacobian f z ≠ 0)
    {g : ComplexModel n → ℂ}
    (hg : ∀ᶠ y in 𝓝 (f p), DifferentiableAt ℂ g y)
    (hgnon : ∃ᶠ y in 𝓝 (f p), g y ≠ 0) :
    ∃ᶠ z in 𝓝 p, g (f z) * complexJacobian f z ≠ 0 := by
  obtain ⟨R, hR, hRg⟩ := Metric.eventually_nhds_iff_ball.mp hg
  have hgB : DifferentiableOn ℂ g (ball (f p) R) :=
    fun y hy => (hRg y hy).differentiableWithinAt
  have hfc : ContinuousAt f p := (hf.contDiffAt (hD.mem_nhds hp)).continuousAt
  by_contra hnot
  have hzero : ∀ᶠ z in 𝓝 p, g (f z) * complexJacobian f z = 0 := by
    filter_upwards [Filter.not_frequently.mp hnot] with z hz
    exact not_ne_iff.mp hz
  have hnear : ∀ᶠ z in 𝓝 p,
      z ∈ D ∧ f z ∈ ball (f p) R ∧ g (f z) * complexJacobian f z = 0 := by
    filter_upwards [hD.mem_nhds hp, hfc (ball_mem_nhds (f p) hR), hzero] with z hz hzB hz0
    exact ⟨hz, hzB, hz0⟩
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  obtain ⟨z, hzJ, hzB⟩ := (hJ.and_eventually (ball_mem_nhds p hε)).exists
  have hzD : z ∈ D := (hεall z hzB).1
  have hzimage : f z ∈ ball (f p) R := (hεall z hzB).2.1
  have hJcont : ContinuousAt (complexJacobian f) z :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hf.continuousOn_fderiv_of_isOpen hD (by simp)).continuousAt (hD.mem_nhds hzD))
  have hJnear : ∀ᶠ w in 𝓝 z, complexJacobian f w ≠ 0 :=
    hJcont (isOpen_ne.mem_nhds hzJ)
  have hgcomp : ∀ᶠ w in 𝓝 z, g (f w) = 0 := by
    filter_upwards [hJnear, isOpen_ball.mem_nhds hzB] with w hwJ hwB
    exact (mul_eq_zero.mp (hεall w hwB).2.2).resolve_right hwJ
  have hdet : (fderiv ℂ f z).toLinearMap.det ≠ 0 := hzJ
  have hunit : IsUnit (fderiv ℂ f z).toLinearMap :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hbij : Function.Bijective (fderiv ℂ f z) := (Module.End.isUnit_iff _).mp hunit
  let L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearEquiv.ofBijective (fderiv ℂ f z).toLinearMap hbij).toContinuousLinearEquiv
  have hLeq : (L : ComplexModel n →L[ℂ] ComplexModel n) = fderiv ℂ f z :=
    ContinuousLinearMap.ext fun _ => rfl
  have hstrict : HasStrictFDerivAt f (L : ComplexModel n →L[ℂ] ComplexModel n) z := by
    rw [hLeq]
    exact (hf.contDiffAt (hD.mem_nhds hzD)).hasStrictFDerivAt (by simp)
  have hgz : ∀ᶠ y in 𝓝 (f z), g y = 0 := by
    rw [← hstrict.map_nhds_eq_of_equiv]
    exact hgcomp
  have hgzero := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero
    isOpen_ball (convex_ball (f p) R).isPreconnected hgB hzimage hgz
      (f p) (mem_ball_self hR)
  obtain ⟨y, hynon, hyzero⟩ := (hgnon.and_eventually hgzero).exists
  exact hynon hyzero

/-- Genuine analytic modification geometry supplies the noncollapse premise,
so every original nonzero preferred-chart test gives a nonzero weighted lift. -/
theorem frequently_flat_jacobian_test_ne_zero
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x)
    {g : ComplexModel (m + 1) → ℂ}
    (hg : ∀ᶠ z in 𝓝 ((complexChartAt (n := m + 1) (π x)).val (π x)),
      DifferentiableAt ℂ g z)
    (hgnon : ∃ᶠ z in 𝓝 ((complexChartAt (n := m + 1) (π x)).val (π x)), g z ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      g (flatCoordMap π Φ z) * complexJacobian (flatCoordMap π Φ) z ≠ 0 := by
  have hD := Φ.isOpen_flatDomain hπ.1.continuous
  have hfd := Φ.differentiableOn_flatCoordMap hπ.1
  apply frequently_comp_mul_jacobian_ne_zero hD
    (contDiffOn_of_differentiableOn_complex hfd hD) (Φ.zero_mem_flatDomain π)
    (AnalyticModificationLocalDiscrepancy.frequently_complexJacobian_ne_zero_of_isAnalyticModification
      hπ Φ)
  · simpa only [Φ.flatCoordMap_zero π] using hg
  · simpa only [Φ.flatCoordMap_zero π] using hgnon

end
end SGPT.Foundations.Analysis.Pending.HolomorphicJacobianTestNonzeroPullback
