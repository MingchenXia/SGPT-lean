import SGPT.Foundations.Analysis.Pending.BorelChartWeightedPatchCurrent
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! # Whole-chart overlap pairings of the original signed Borel patch current

The entire mathematical statement and proof precede this file.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions Manifold

namespace SGPT.Foundations.Analysis.Pending.BorelChartWeightedOverlapFullPairing

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.HolomorphicMaps
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback ClosedProductCurrents WeightedFullTestPullbackDensity
  WholeChartPotentialPatchTransition BorelChartWeightedPatchCurrent

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

private theorem projection_zero {n : ℕ} :
    oneOneProjection (0 : RealForm n 2) = 0 := by
  apply Subtype.ext
  ext v
  simp [oneOneProjection, pi11, ContinuousAlternatingMap.compContinuousLinearMap_apply]

private theorem projected_relation {n : ℕ} {a b : RealForm n 2}
    (D : ComplexModel n →L[ℝ] ComplexModel n)
    (hJ : ∀ w, D (Complex.I • w) = Complex.I • D w)
    (hab : ∀ v, a v = b (fun i => D (v i))) :
    ∀ v, pi11 a v = pi11 b (fun i => D (v i)) := by
  intro v
  obtain ⟨x, y, rfl⟩ : ∃ x y, v = ![x, y] := ⟨v 0, v 1, eq_vec_two v⟩
  have h1 : (fun i => D (![x, y] i)) = ![D x, D y] := by
    funext i
    fin_cases i <;> rfl
  have h2 : (fun i => D (![Complex.I • x, Complex.I • y] i)) =
      ![Complex.I • D x, Complex.I • D y] := by
    funext i
    fin_cases i <;> simp [hJ]
  rw [h1, pi11_apply, pi11_apply, hab, hab, h1, h2]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- Every pair of genuine overlap tests gives the same actual full patch pairing. -/
theorem chartBorelWeightedFullTestFunctional_overlap (e d : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (η : LocalCurrents.TestForm (overlapSource e d) 2)
    (ζ : LocalCurrents.TestForm (overlapTarget e d) 2)
    (hrel : OverlapTestRelated e d η ζ) :
    chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb
      (TestFunction.monoCLM ℝ η) =
    chartBorelWeightedFullTestFunctional d P hT χ hχ hsupp hnonneg f hf hb
      (TestFunction.monoCLM ℝ ζ) := by
  let α : LocalCurrents.TestForm (chartTarget e) 2 := TestFunction.monoCLM ℝ η
  let β : LocalCurrents.TestForm (chartTarget d) 2 := TestFunction.monoCLM ℝ ζ
  have hα (z : ComplexModel n) : α z = η z :=
    LocalCurrents.testForm_inclusion_apply (overlapSource_le e d) η z
  have hβ (z : ComplexModel n) : β z = ζ z :=
    LocalCurrents.testForm_inclusion_apply (overlapTarget_le e d) ζ z
  let Be := patchOverlapDomain e P
  let Bf := patchOverlapDomain d P
  let C : Set (ComplexModel n) := (Be : Set (ComplexModel n)) ∩ Bf
  let Fe (y : ComplexModel n) := (f (P.chart.val.symm y) * χ (P.chart.val.symm y)) * densityForm hT y
    (pullSpan 1 (fderiv ℂ (patchToChart e P) y)
      (oneOneProjection (η (patchToChart e P y))))
  let Ff (y : ComplexModel n) := (f (P.chart.val.symm y) * χ (P.chart.val.symm y)) * densityForm hT y
    (pullSpan 1 (fderiv ℂ (patchToChart d P) y)
      (oneOneProjection (ζ (patchToChart d P y))))
  have he := chartBorelWeightedFullTestFunctional_density e P hT χ hχ hsupp hnonneg f hf hb α
  have hdf := chartBorelWeightedFullTestFunctional_density d P hT χ hχ hsupp hnonneg f hf hb β
  have hIe : chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb α =
      ∫ y in Be, Fe y ∂hT.traceMeasure := by
    rw [he.2]
    apply setIntegral_congr_fun Be.isOpen.measurableSet
    intro y _
    dsimp only [Fe]
    rw [hα]
  have hIf : chartBorelWeightedFullTestFunctional d P hT χ hχ hsupp hnonneg f hf hb β =
      ∫ y in Bf, Ff y ∂hT.traceMeasure := by
    rw [hdf.2]
    apply setIntegral_congr_fun Bf.isOpen.measurableSet
    intro y _
    dsimp only [Ff]
    rw [hβ]
  have hEz : ∀ y ∈ (Be : Set (ComplexModel n)) \ C, Fe y = 0 := by
    intro y hy
    have hnot : y ∉ Bf := fun h => hy.2 ⟨hy.1, h⟩
    have hη : η (patchToChart e P y) = 0 := by
      apply Function.notMem_support.mp
      intro h
      have hv := η.tsupport_subset (subset_tsupport η h)
      have hs : P.chart.val.symm y ∈ d.val.source := by
        have hh := hv.2
        change e.val.symm (e.val (P.chart.val.symm y)) ∈ d.val.source at hh
        rw [e.val.left_inv hy.1.2] at hh
        exact hh
      exact hnot ⟨hy.1.1, hs⟩
    simp only [Fe, hη, projection_zero, map_zero, mul_zero]
  have hFz : ∀ y ∈ (Bf : Set (ComplexModel n)) \ C, Ff y = 0 := by
    intro y hy
    have hnot : y ∉ Be := fun h => hy.2 ⟨h, hy.1⟩
    have hζ : ζ (patchToChart d P y) = 0 := by
      apply Function.notMem_support.mp
      intro h
      have hv := ζ.tsupport_subset (subset_tsupport ζ h)
      have hs : P.chart.val.symm y ∈ e.val.source := by
        have hh := hv.2
        change d.val.symm (d.val (P.chart.val.symm y)) ∈ e.val.source at hh
        rw [d.val.left_inv hy.1.2] at hh
        exact hh
      exact hnot ⟨hy.1.1, hs⟩
    simp only [Ff, hζ, projection_zero, map_zero, mul_zero]
  have hEq : ∀ y ∈ C, Fe y = Ff y := by
    intro y hy
    have hye : y ∈ coordinateDomain (id : M → M) P.chart e :=
      ⟨P.domain_le_target hy.1.1, hy.1.2⟩
    have hyf : y ∈ coordinateDomain (id : M → M) P.chart d :=
      ⟨P.domain_le_target hy.2.1, hy.2.2⟩
    have hxe : patchToChart e P y ∈ (chartTransition e d).source :=
      coordinateMap_mem_transition_source hye hyf
    have hpoint : patchToChart d P y = chartTransition e d (patchToChart e P y) :=
      coordinateMap_change_target hye
    have hDe : fderiv ℝ (patchToChart e P) y =
        (fderiv ℂ (patchToChart e P) y).restrictScalars ℝ :=
      coordinateMap_fderiv_restrictScalars contMDiff_id P.chart e hye
    have hDf : fderiv ℝ (patchToChart d P) y =
        (fderiv ℂ (patchToChart d P) y).restrictScalars ℝ :=
      coordinateMap_fderiv_restrictScalars contMDiff_id P.chart d hyf
    have hchain : fderiv ℝ (patchToChart d P) y =
        (chartTransitionDerivative e d (patchToChart e P y)).comp
          (fderiv ℝ (patchToChart e P) y) :=
      coordinateMap_fderiv_change_target contMDiff_id P.chart e d hye hyf
    have hDc (v : ComplexModel n) : fderiv ℂ (patchToChart d P) y v =
        chartTransitionDerivative e d (patchToChart e P y)
          (fderiv ℂ (patchToChart e P) y v) := by
      change ((fderiv ℂ (patchToChart d P) y).restrictScalars ℝ) v =
        chartTransitionDerivative e d (patchToChart e P y)
          (((fderiv ℂ (patchToChart e P) y).restrictScalars ℝ) v)
      rw [← hDf, ← hDe, hchain]
      rfl
    have hforms :
        pullSpan 1 (fderiv ℂ (patchToChart e P) y)
          (oneOneProjection (η (patchToChart e P y))) =
        pullSpan 1 (fderiv ℂ (patchToChart d P) y)
          (oneOneProjection (ζ (patchToChart d P y))) := by
      apply Subtype.ext
      ext v
      simp only [coe_pullSpan, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      change pi11 (η (patchToChart e P y))
          (fun i => fderiv ℂ (patchToChart e P) y (v i)) =
        pi11 (ζ (patchToChart d P y))
          (fun i => fderiv ℂ (patchToChart d P) y (v i))
      rw [projected_relation _
        (fun w => chartTransitionDerivative_complex_smul e d _ hxe Complex.I w)
        (hrel _ hxe), ← hpoint]
      congr 1
      funext i
      exact (hDc (v i)).symm
    dsimp only [Fe, Ff]
    rw [hforms]
  calc
    chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb α =
        ∫ y in Be, Fe y ∂hT.traceMeasure := hIe
    _ = ∫ y in C, Fe y ∂hT.traceMeasure :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Be.isOpen.measurableSet
        inter_subset_left hEz
    _ = ∫ y in C, Ff y ∂hT.traceMeasure :=
      setIntegral_congr_fun (Be.isOpen.inter Bf.isOpen).measurableSet hEq
    _ = ∫ y in Bf, Ff y ∂hT.traceMeasure :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Bf.isOpen.measurableSet
        inter_subset_right hFz).symm
    _ = chartBorelWeightedFullTestFunctional d P hT χ hχ hsupp hnonneg f hf hb β := hIf.symm

end SGPT.Foundations.Analysis.Pending.BorelChartWeightedOverlapFullPairing
