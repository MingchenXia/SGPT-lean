import SGPT.Foundations.Analysis.Pending.HolomorphicJacobianTestNonzeroPullback
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

set_option autoImplicit false

/-! # Actual preferred Jacobian readers preserve nonzero original tests -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationPreferredJacobianTest

open FirstPass FirstPass.HolomorphicMaps FirstPass.BlowupSequences
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section


private theorem bijective_chart_derivatives {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      e.val (e.val.symm z)) ∧
    Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val.symm z) := by
  let I := 𝓘(ℂ, ComplexModel n)
  have hi : MDifferentiableAt I I e.val.symm z :=
    mdifferentiableAt_atlas_symm (I := I) e.property hz
  have he : MDifferentiableAt I I e.val (e.val.symm z) :=
    mdifferentiableAt_atlas (I := I) e.property (e.val.map_target hz)
  have hright : (e.val ∘ e.val.symm) =ᶠ[𝓝 z] id := by
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    exact e.val.right_inv hw
  have hleft : (e.val.symm ∘ e.val) =ᶠ[𝓝 (e.val.symm z)] id := by
    filter_upwards [e.val.open_source.mem_nhds (e.val.map_target hz)] with w hw
    exact e.val.left_inv hw
  have hdi : (mfderiv I I e.val (e.val.symm z)).comp (mfderiv I I e.val.symm z) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← mfderiv_comp z he hi, hright.mfderiv_eq, mfderiv_id]
    rfl
  have hid : (mfderiv I I e.val.symm z).comp (mfderiv I I e.val (e.val.symm z)) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    have hi' : MDifferentiableAt I I e.val.symm (e.val (e.val.symm z)) := by
      rw [e.val.right_inv hz]
      exact hi
    have h : (mfderiv I I e.val.symm (e.val (e.val.symm z))).comp
        (mfderiv I I e.val (e.val.symm z)) = ContinuousLinearMap.id ℂ (ComplexModel n) := by
      rw [← mfderiv_comp (e.val.symm z) hi' he, hleft.mfderiv_eq, mfderiv_id]
      rfl
    rw [e.val.right_inv hz] at h
    exact h
  have heInv := ContinuousLinearMap.IsInvertible.of_inverse hdi hid
  have hiInv := ContinuousLinearMap.IsInvertible.of_inverse hid hdi
  obtain ⟨L, hL⟩ := heInv
  obtain ⟨K, hK⟩ := hiInv
  constructor
  · rw [← hL]
    exact L.bijective
  · rw [← hK]
    exact K.bijective

private theorem preferred_jacobian_ne_zero_of_not_exceptional
    {n : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (e : ComplexChart n Y) (d : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain π e d)
    (hne : e.val.symm z ∉ exceptionalLocus n π) :
    complexJacobian (coordinateMap π e d) z ≠ 0 := by
  let I := 𝓘(ℂ, ComplexModel n)
  have hi : MDifferentiableAt I I e.val.symm z :=
    mdifferentiableAt_atlas_symm (I := I) e.property hz.1
  have hp : MDifferentiableAt I I π (e.val.symm z) :=
    (hπ (e.val.symm z)).mdifferentiableAt (by simp)
  have hd : MDifferentiableAt I I d.val (π (e.val.symm z)) :=
    mdifferentiableAt_atlas (I := I) d.property hz.2
  have hbP : Function.Bijective (mfderiv I I π (e.val.symm z)) := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hne
  have hbI := (bijective_chart_derivatives e hz.1).2
  have hbD : Function.Bijective (mfderiv I I d.val (π (e.val.symm z))) := by
    have h := (bijective_chart_derivatives d (d.val.map_source hz.2)).1
    change Function.Bijective (mfderiv I I d.val (d.val.symm (d.val (π (e.val.symm z))))) at h
    rw [d.val.left_inv hz.2] at h
    exact h
  have hder : mfderiv I I (coordinateMap π e d) z =
      (mfderiv I I d.val (π (e.val.symm z))).comp
        ((mfderiv I I π (e.val.symm z)).comp (mfderiv I I e.val.symm z)) := by
    change mfderiv I I (d.val ∘ π ∘ e.val.symm) z = _
    rw [mfderiv_comp z hd (hp.comp z hi), mfderiv_comp z hp hi]
    rfl
  have hbij : Function.Bijective (mfderiv I I (coordinateMap π e d) z) := by
    rw [hder]
    exact hbD.comp (hbP.comp hbI)
  rw [mfderiv_eq_fderiv] at hbij
  let L := LinearEquiv.ofBijective (fderiv ℂ (coordinateMap π e d) z).toLinearMap hbij
  change LinearMap.det (L : ComplexModel n →ₗ[ℂ] ComplexModel n) ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

private theorem frequently_preferred_jacobian_ne_zero
    {n : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (y : Y) :
    ∃ᶠ z in 𝓝 ((complexChartAt (n := n) y).val y),
      complexJacobian (coordinateMap π (complexChartAt (n := n) y)
        (complexChartAt (n := n) (π y))) z ≠ 0 := by
  classical
  let e := complexChartAt (n := n) y
  let d := complexChartAt (n := n) (π y)
  let D := coordinateDomain π e d
  have hD : IsOpen D := coordinateDomain_isOpen hπ.1 e d
  have hyD : e.val y ∈ D :=
    mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  obtain ⟨A, _, hA, hint, _, hnonexc⟩ :=
    AnalyticModificationLocalDiscrepancy.exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hnull : volume (pluripolarChartSet A e) = 0 :=
    (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
      hA hint).chart_measure_eq_zero e volume
  apply frequently_nhds_iff.mpr
  intro U hyU hU
  have hnear : U ∩ D ∈ 𝓝 (e.val y) := inter_mem (hU.mem_nhds hyU) (hD.mem_nhds hyD)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hnsub : ¬ ball (e.val y) r ⊆ pluripolarChartSet A e := by
    intro hsub
    exact (measure_ball_pos volume (e.val y) hr).ne' (measure_mono_null hsub hnull)
  obtain ⟨z, hz, hzN⟩ := Set.not_subset.mp hnsub
  have hzD : z ∈ D := (hrsub hz).2
  have hzA : e.val.symm z ∉ A := fun h => hzN ⟨hzD.1, h⟩
  exact ⟨z, (hrsub hz).1,
    preferred_jacobian_ne_zero_of_not_exceptional hπ.1 e d hzD (hnonexc _ hzA)⟩

/-- Actual modification geometry produces noncollapse for the literal preferred
reader, so an original nonzero test stays nonzero after Jacobian weighting. -/
theorem frequently_preferred_jacobian_test_ne_zero
    {n : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (y : Y) {g : ComplexModel n → ℂ}
    (hg : ∀ᶠ z in 𝓝 ((complexChartAt (n := n) (π y)).val (π y)), DifferentiableAt ℂ g z)
    (hgnon : ∃ᶠ z in 𝓝 ((complexChartAt (n := n) (π y)).val (π y)), g z ≠ 0) :
    ∃ᶠ z in 𝓝 ((complexChartAt (n := n) y).val y),
      g (coordinateMap π (complexChartAt (n := n) y) (complexChartAt (n := n) (π y)) z) *
        complexJacobian (coordinateMap π (complexChartAt (n := n) y)
          (complexChartAt (n := n) (π y))) z ≠ 0 := by
  let e := complexChartAt (n := n) y
  let d := complexChartAt (n := n) (π y)
  have hFy : coordinateMap π e d (e.val y) = d.val (π y) :=
    coordinateMap_at (mem_complexChartAt_source y)
  exact HolomorphicJacobianTestNonzeroPullback.frequently_comp_mul_jacobian_ne_zero
    (coordinateDomain_isOpen hπ.1 e d) (coordinateMap_contDiffOn hπ.1 e d)
    (mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y)))
    (frequently_preferred_jacobian_ne_zero hπ y)
    (by simpa only [hFy] using hg) (by simpa only [hFy] using hgnon)

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationPreferredJacobianTest
