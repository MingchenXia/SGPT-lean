import SGPT.Foundations.Analysis.Pending.GlobalJacobianCoefficient
import SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.OverBaseJacobianOrder

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong HironakaHolomorphicJetRankLoci
  FixedGermNormalOrder ActualFlatNormalOrder GlobalRelativeJacobianIdeal
  UnramifiedNormalOrder

universe u

section OriginalFunctions
variable {m : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {E : Set Y} {y : Y}

/-- The ENTIRE original product germ gives the extended additive order, retaining zero/infinity. -/
theorem functionNormalOrder_mul (Φ : DivisorFlattening (m := m) E y)
    (f h : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) (hh : HolomorphicAt (m + 1) h y) :
    functionNormalOrder Φ (fun w => f w * h w) (hf.mul hh) =
      functionNormalOrder Φ f hf + functionNormalOrder Φ h hh := by
  have hproduct : chartTranslatedGerm y y (mem_chart_source _ y) (fun w => f w * h w) (hf.mul hh) =
      chartTranslatedGerm y y (mem_chart_source _ y) f hf *
        chartTranslatedGerm y y (mem_chart_source _ y) h hh := by
    unfold chartTranslatedGerm translatedGerm
    rw [← HolGerm.mk_mul]
  unfold functionNormalOrder
  rw [hproduct, normalOrder_mul]

/-- A nonzero ORIGINAL value internally manufactures a unit germ and order zero. -/
theorem functionNormalOrder_eq_zero_of_ne_zero (Φ : DivisorFlattening (m := m) E y)
    (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) (hf0 : f y ≠ 0) :
    functionNormalOrder Φ f hf = 0 := by
  apply normalOrder_unit Φ
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  unfold chartTranslatedGerm translatedGerm
  rw [HolGerm.eval_mk]
  simpa only [zero_add, (chartAt (ComplexModel (m + 1)) y).left_inv (mem_chart_source _ y)] using hf0
end OriginalFunctions

section LiteralJacobian
variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Actual chart round trips and COMPLEX derivative composition prove the original scalar Jacobian chain. -/
theorem chartJacobianFunction_comp_eventually {π : Y → X} {g : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) (z : Z) :
    chartJacobianFunction (n := n) (π ∘ g) z (π (g z)) =ᶠ[𝓝 z]
      fun w => chartJacobianFunction (n := n) π (g z) (π (g z)) (g w) *
        chartJacobianFunction (n := n) g z (g z) w := by
  let e := complexChartAt (n := n) z
  let d := complexChartAt (n := n) (g z)
  let c := complexChartAt (n := n) (π (g z))
  filter_upwards [e.val.open_source.mem_nhds (mem_complexChartAt_source z),
    hg.continuous.continuousAt.eventually (d.val.open_source.mem_nhds (mem_complexChartAt_source (g z))),
    (hπ.comp hg).continuous.continuousAt.eventually
      (c.val.open_source.mem_nhds (mem_complexChartAt_source (π (g z))))] with w hwe hwd hwc
  have hwDg : e.val w ∈ coordinateDomain g e d := mem_coordinateDomain hwe hwd
  have hwDπ : coordinateMap g e d (e.val w) ∈ coordinateDomain π d c := by
    rw [coordinateMap_at hwe]
    exact mem_coordinateDomain hwd hwc
  have heq : coordinateMap (π ∘ g) e c =ᶠ[𝓝 (e.val w)]
      (coordinateMap π d c) ∘ coordinateMap g e d := by
    filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hwDg] with t ht
    simp only [coordinateMap, Function.comp_apply, d.val.left_inv ht.2]
  have hP := (coordinateMap_contDiffAt hg e d hwDg).differentiableAt (by simp)
  have hQ := (coordinateMap_contDiffAt hπ d c hwDπ).differentiableAt (by simp)
  have hJ : DivisorialChangeOfVariables.complexJacobian (coordinateMap (π ∘ g) e c) (e.val w) =
      DivisorialChangeOfVariables.complexJacobian (coordinateMap π d c)
        (coordinateMap g e d (e.val w)) *
          DivisorialChangeOfVariables.complexJacobian (coordinateMap g e d) (e.val w) := by
    simp only [DivisorialChangeOfVariables.complexJacobian]
    rw [heq.fderiv_eq, fderiv_comp (e.val w) hQ hP, ContinuousLinearMap.det]
    change LinearMap.det ((fderiv ℂ (coordinateMap π d c) (coordinateMap g e d (e.val w))).toLinearMap.comp
      (fderiv ℂ (coordinateMap g e d) (e.val w)).toLinearMap) = _
    exact LinearMap.det_comp _ _
  rw [coordinateMap_at hwe] at hJ
  exact hJ

omit [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- Intrinsic unramified geometry makes the actual preferred original Jacobian nonzero, for every n. -/
theorem chartJacobianFunction_ne_zero_of_not_exceptional {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {z : Z} (hz : z ∉ exceptionalLocus n g) :
    chartJacobianFunction (n := n) g z (g z) z ≠ 0 := by
  let I := 𝓘(ℂ, ComplexModel n)
  let e := (complexChartAt (n := n) z).val
  let d := (complexChartAt (n := n) (g z)).val
  let F : ComplexModel n → ComplexModel n := fun u => d (g (e.symm u))
  have hrange : range I = univ := by simp [I]
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have hbij := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hbij
    rw [hderiv] at hbij
    exact hbij.1
  change (fderiv ℂ F (e z)).toLinearMap.det ≠ 0
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hinj)
end LiteralJacobian

section ActualLocalOrder
variable {m : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

private theorem functionJacobianOrder_eq_flat {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y) :
    functionNormalOrder Φ (chartJacobianFunction (n := m + 1) π y (π y))
      (holomorphicAt_chartJacobianFunction hπ y (π y)
        (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))) =
        flatJacobianOrder hπ Φ := by
  unfold functionNormalOrder
  rw [GlobalJacobianCoefficient.chartTranslatedJacobian_eq_preferred hπ y]
  exact preferredJacobianOrder_eq_flat hπ Φ

/-- The actual unramified original domination preserves the entire local Jacobian order, including infinity. -/
theorem flatJacobianOrder_comp_eq_of_not_exceptional {π : Y → X} {g : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {z : Z} (hz : z ∉ exceptionalLocus (m + 1) g)
    {E : Set Y} {E' : Set Z}
    (Φ : DivisorFlattening (m := m) E (g z)) (Ψ : DivisorFlattening (m := m) E' z)
    (hsets : ∀ᶠ z' in 𝓝 z, z' ∈ E' ↔ g z' ∈ E) :
    flatJacobianOrder (hπ.comp hg) Ψ = flatJacobianOrder hπ Φ := by
  let jπ := chartJacobianFunction (n := m + 1) π (g z) (π (g z))
  let jg := chartJacobianFunction (n := m + 1) g z (g z)
  let jc := chartJacobianFunction (n := m + 1) (π ∘ g) z (π (g z))
  have hjπ : HolomorphicAt (m + 1) jπ (g z) :=
    holomorphicAt_chartJacobianFunction hπ (g z) (π (g z))
      (mem_complexChartAt_source (g z)) (mem_complexChartAt_source (π (g z)))
  have hjg : HolomorphicAt (m + 1) jg z :=
    holomorphicAt_chartJacobianFunction hg z (g z)
      (mem_complexChartAt_source z) (mem_complexChartAt_source (g z))
  have hjc : HolomorphicAt (m + 1) jc z :=
    holomorphicAt_chartJacobianFunction (hπ.comp hg) z (π (g z))
      (mem_complexChartAt_source z) (mem_complexChartAt_source (π (g z)))
  have hjpull : HolomorphicAt (m + 1) (jπ ∘ g) z :=
    hjπ.comp_contMDiff (Eventually.of_forall fun _ => hg.contMDiffAt)
  calc
    flatJacobianOrder (hπ.comp hg) Ψ = functionNormalOrder Ψ jc hjc :=
      (functionJacobianOrder_eq_flat (hπ.comp hg) Ψ).symm
    _ = functionNormalOrder Ψ (fun w => jπ (g w) * jg w) (hjpull.mul hjg) :=
      functionNormalOrder_congr Ψ hjc (hjpull.mul hjg) (chartJacobianFunction_comp_eventually hπ hg z)
    _ = functionNormalOrder Ψ (jπ ∘ g) hjpull + functionNormalOrder Ψ jg hjg :=
      functionNormalOrder_mul Ψ (jπ ∘ g) jg hjpull hjg
    _ = functionNormalOrder Φ jπ hjπ + 0 := by
      rw [functionNormalOrder_comp_eq_of_not_exceptional hg hz Φ Ψ hsets jπ hjπ,
        functionNormalOrder_eq_zero_of_ne_zero Ψ jg hjg
          (chartJacobianFunction_ne_zero_of_not_exceptional hg hz)]
    _ = flatJacobianOrder hπ Φ := by
      rw [add_zero]
      exact functionJacobianOrder_eq_flat hπ Φ
end ActualLocalOrder

end SGPT.Foundations.Analysis.Pending.OverBaseJacobianOrder
