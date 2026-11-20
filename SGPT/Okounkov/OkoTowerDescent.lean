import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison
import SGPT.Foundations.Analysis.Pending.StrongOpennessSliceInduction
import SGPT.Foundations.Analysis.Pending.FactorizedWeightForm

/-!
# Descent of multiplier sections along a modification

Lane OKO-TOWER, blueprint `claude-oko-tower.tex`, node `claude-oko-tower:descent`.  Used in the
proof of `prop:birinvO` (chapter *The theory of Okounkov bodies*): for a modification
`π : Y → X` and `φ` quasi-psh on `X`, `π_* 𝓘(π^*φ) ⊆ 𝓘(φ)`.

* **`multiplierIdeal_mem_of_forall_comp_mem`**: let `π : Y → X` be an analytic modification of
  complex manifolds of the same dimension, `u` quasi-psh on `X`, `c > 0` and `F` holomorphic near
  `x`.  If `F ∘ π ∈ 𝓘(c (u ∘ π))_y` at every point `y` of the fibre `π⁻¹(x)`, then
  `F ∈ 𝓘(cu)_x`.  Proof: the Jacobian criterion
  (`AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs`:
  `F ∈ 𝓘(cu)_x` iff `(F ∘ π) · J_π ∈ 𝓘(c (u ∘ π))_y` for every `y ∈ π⁻¹(x)`, the change of
  variables `∫_U |F|² e^{-cu} = ∫_{π⁻¹U} |F ∘ π|² |J_π|² e^{-c u ∘ π}`), and `J_π` is holomorphic, so
  multiplying by it preserves `𝓘(c (u ∘ π))_y`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OkoTower

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables

universe u

/-- The holomorphic Jacobian determinant of a holomorphic map of open sets of `ℂⁿ` is
holomorphic. -/
theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hF : DifferentiableOn ℂ F D) :
    DifferentiableOn ℂ (complexJacobian F) D := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) D :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hD
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ D).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- **Descent of multiplier-ideal membership along a modification** (`π_* 𝓘(c π^*u) ⊆ 𝓘(cu)`):
if `F` is holomorphic near `x` and `F ∘ π ∈ 𝓘(c (u ∘ π))` at every point of the fibre over `x`,
then `F ∈ 𝓘(cu)_x`. -/
theorem multiplierIdeal_mem_of_forall_comp_mem {π : Y → M}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u) {c : ℝ} (hc : 0 < c)
    {x : M} {F : M → ℂ} (hF : HolomorphicAt (m + 1) F x)
    (h : ∀ y : Y, π y = x →
      (multiplierIdeal (n := m + 1) c (fun w => u (π w))).mem y (fun w => F (π w))) :
    (multiplierIdeal (n := m + 1) c u).mem x F := by
  refine ⟨hF, ?_⟩
  let d := complexChartAt (n := m + 1) x
  let g : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm z)
  have hd : d.val x ∈ d.val.target := d.val.map_source (mem_complexChartAt_source x)
  have hg : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ g z := by
    have h1 := (MultiplierIdealProductComparison.tendsto_complexChartAt_symm (n := m + 1) x).eventually hF
    have h2 : ∀ᶠ z in 𝓝 (d.val x), z ∈ d.val.target := d.val.open_target.mem_nhds hd
    filter_upwards [h1, h2] with z hz1 hz2
    exact FactorizedWeightForm.differentiableAt_comp_chart_symm d hz2 hz1
  apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x hc (hu d (d.val x) hd) hg).mpr
  intro y hy
  let e := complexChartAt (n := m + 1) y
  let f := coordinateMap π e d
  have hD := coordinateDomain_isOpen hπ.1 e d
  have hpD : e.val y ∈ coordinateDomain π e d := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hy]
    exact mem_complexChartAt_source x
  have hcongrw : (chartFunction (fun w => u (π w)) e) =ᶠ[𝓝 (e.val y)]
      (fun z => chartFunction u d (f z)) := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change u (π (e.val.symm z)) = u (d.val.symm (d.val (π (e.val.symm z))))
    rw [d.val.left_inv hz.2]
  have hcongrg : (fun z => F (π (e.val.symm z))) =ᶠ[𝓝 (e.val y)] (fun z => g (f z)) := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change F (π (e.val.symm z)) = F (d.val.symm (d.val (π (e.val.symm z))))
    rw [d.val.left_inv hz.2]
  have hY : MultiplierIntegrableAt (fun z => chartFunction u d (f z)) c (fun z => g (f z))
      (e.val y) volume := (h y hy).2.congr hcongrw hcongrg
  have hfd : DifferentiableOn ℂ f (coordinateDomain π e d) :=
    (coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp)
  have hJ : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ (complexJacobian f) z := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    exact (differentiableOn_complexJacobian hD hfd z hz).differentiableAt (hD.mem_nhds hz)
  have hmul := multiplierIntegrableAt_differentiable_mul hY hJ
  refine hmul.congr (EventuallyEq.refl _ _) (Eventually.of_forall fun z => ?_)
  exact mul_comm _ _

end SGPT.Okounkov.OkoTower

end
