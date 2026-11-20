import SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarChartIntegral
import SGPT.Foundations.Analysis.FirstPass.FiniteMeasureGluing
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamily

set_option autoImplicit false

/-! # Whole-manifold original analytic non-pluripolar integrals
Complete NEW mathematics and ENTIRE proofs precede this import-only baseline.
The finite original potential cover is produced internally before all sets.
No total-mass or desired density/current certificate is an input.
-/

noncomputable section
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ContDiff Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarGlobalIntegral
open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.GlobalPotentialPatches FirstPass.MongeAmpere GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The internally selected actual finite cover gives the whole original mixed
NP measure on every measurable set by the original off-pole exterior density. -/
theorem exists_finite_cover_original_mixed_measure_eq_lintegral
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (han : ∀ i, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (u i)) :
    ∃ C : FiniteCover θ u,
      let E : Fin C.count → Set M := disjointed (fun j => (C.patch j).source)
      ∀ A : Set M, MeasurableSet A →
        globalMixedMeasure θ u (fun i => (hu i).1) A =
          ∑ j : Fin C.count,
            ∫⁻ y in (C.patch j).domain ∩
              (C.patch j).chart.val.symm ⁻¹' (A ∩ E j) ∩
              (C.patch j).chart.val.symm ⁻¹' (⋃ i, {x | u i x = ⊥})ᶜ,
              ENNReal.ofReal (actualMixedTopDensity (fun i =>
                (θ i).val.coeff (C.patch j).chart y +
                smoothDDC (fun w => (chartFunction (u i) (C.patch j).chart w).toReal) y)) := by
  classical
  let C : FiniteCover θ u := Classical.choice (nonempty_finiteCover (fun i => (hu i).1))
  let U : Fin C.count → Set M := fun j => (C.patch j).source
  let E : Fin C.count → Set M := disjointed U
  have hU : ∀ j, MeasurableSet (U j) := fun j => (C.patch j).source.isOpen.measurableSet
  have hE : ∀ j, MeasurableSet (E j) :=
    FirstPass.FiniteMeasureGluing.measurableSet_disjointed U hU
  have hEdisj : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed U
  have hEsource : ∀ j, E j ⊆ (C.patch j).source := fun j => disjointed_subset U j
  have hUunion : (⋃ j, U j) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, hx⟩ := C.covers x
    exact mem_iUnion.mpr ⟨j, hx⟩
  have hEunion : (⋃ j, E j) = univ := by
    change (⋃ j, disjointed U j) = univ
    rw [iUnion_disjointed, hUunion]
  refine ⟨C, ?_⟩
  change ∀ A : Set M, MeasurableSet A → _
  intro A hA
  let μ : Measure M := globalMixedMeasure θ u (fun i => (hu i).1)
  have hpiece (j : Fin C.count) :
      μ (A ∩ E j) =
        ∫⁻ y in (C.patch j).domain ∩
          (C.patch j).chart.val.symm ⁻¹' (A ∩ E j) ∩
          (C.patch j).chart.val.symm ⁻¹' (⋃ i, {x | u i x = ⊥})ᶜ,
          ENNReal.ofReal (actualMixedTopDensity (fun i =>
            (θ i).val.coeff (C.patch j).chart y +
            smoothDDC (fun w => (chartFunction (u i) (C.patch j).chart w).toReal) y)) := by
    let Q := C.patch j
    let S : Set (ComplexModel n) := Q.domain ∩ Q.chart.val.symm ⁻¹' (A ∩ E j)
    have hS : MeasurableSet S :=
      SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
        Q.domain.isOpen.measurableSet
        (Q.chart.val.continuousOn_symm.mono Q.domain_le_target) (hA.inter (hE j))
    have hStarget : S ⊆ Q.chart.val.target :=
      inter_subset_left.trans Q.domain_le_target
    have himage : Q.chart.val.symm '' S = A ∩ E j := by
      apply Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact hy.2
      · intro x hx
        have hxQ : x ∈ Q.source := hEsource j hx.2
        refine ⟨Q.chart.val x, ⟨Q.map_source hxQ, ?_⟩,
          Q.chart.val.left_inv (Q.source_subset hxQ)⟩
        change Q.chart.val.symm (Q.chart.val x) ∈ A ∩ E j
        rwa [Q.chart.val.left_inv (Q.source_subset hxQ)]
    have h :=
      ActualAnalyticNonPluripolarChartIntegral.original_mixed_measure_chart_piece_eq_off_pole_lintegral
        hu han Q.chart hS hStarget
    rw [himage] at h
    exact h
  have hAdisj : Pairwise (Function.onFun Disjoint (fun j => A ∩ E j)) := by
    intro i j hij
    exact (hEdisj hij).mono inter_subset_right inter_subset_right
  have hAunion : (⋃ j, A ∩ E j) = A := by
    rw [← inter_iUnion, hEunion, inter_univ]
  calc
    μ A = μ (⋃ j, A ∩ E j) := by rw [hAunion]
    _ = ∑' j, μ (A ∩ E j) := measure_iUnion hAdisj (fun j => hA.inter (hE j))
    _ = ∑ j : Fin C.count, μ (A ∩ E j) := tsum_fintype _
    _ = _ := Finset.sum_congr rfl (fun j _ => hpiece j)

/-- The actual diagonal non-pluripolar mass is the genuine top exterior power
of the original reader off its original repeated-slot pole union, including n=0. -/
theorem exists_finite_cover_original_diagonal_mass_eq_top_lintegral
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) :
    ∃ C : FiniteCover (fun _ : Fin n => θ) (fun _ : Fin n => u),
      let E : Fin C.count → Set M := disjointed (fun j => (C.patch j).source)
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ : Fin n => u)
        (fun _ => hu.1) univ =
        ∑ j : Fin C.count,
          ∫⁻ y in (C.patch j).domain ∩
            (C.patch j).chart.val.symm ⁻¹' E j ∩
            (C.patch j).chart.val.symm ⁻¹' (⋃ _ : Fin n, {x | u x = ⊥})ᶜ,
            ENNReal.ofReal (actualTopPowerDensity
              (θ.val.coeff (C.patch j).chart y +
                smoothDDC (fun w => (chartFunction u (C.patch j).chart w).toReal) y)) := by
  obtain ⟨C, hC⟩ := exists_finite_cover_original_mixed_measure_eq_lintegral
    (fun _ : Fin n => hu) (fun _ : Fin n => han)
  refine ⟨C, ?_⟩
  simpa only [univ_inter, actualMixedTopDensity_const] using hC univ MeasurableSet.univ

end SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarGlobalIntegral
