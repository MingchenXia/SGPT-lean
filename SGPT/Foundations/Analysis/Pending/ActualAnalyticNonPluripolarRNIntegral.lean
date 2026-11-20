import SGPT.Foundations.Analysis.Pending.ActualAnalyticRNDensityIdentification
import SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarGlobalIntegral

set_option autoImplicit false
/-! Complete NEW mathematics and ENTIRE proof precede this import baseline. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarRNIntegral
open FirstPass FirstPass.NumericalRestrictedVolumeScaffold FirstPass.GlobalPotentialPatches
  FirstPass.MongeAmpere GlobalNonPluripolar ActualAnalyticCurrentLocalDensity
  ActualAnalyticRNDensityIdentification LocalCurrentDeterminant
  GlobalCurrentPotentials CanonicalCurrentFrame

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]

/-- The actual original NP measure on ALL measurable sets is the actual top
power of the SAME original current's canonical RN density, on entire patches. -/
theorem exists_finite_cover_original_measure_eq_acForm_top_lintegral
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u) :
    ∃ C : FiniteCover (fun _ : Fin (m + 1) => θ) (fun _ : Fin (m + 1) => u),
      let E : Fin C.count → Set M := disjointed (fun j => (C.patch j).source)
      ∀ A : Set M, MeasurableSet A →
        globalMixedMeasure (fun _ : Fin (m + 1) => θ) (fun _ : Fin (m + 1) => u)
          (fun _ => hu.1) A =
          ∑ j : Fin C.count,
            ∫⁻ y in (C.patch j).domain ∩ (C.patch j).chart.val.symm ⁻¹' (A ∩ E j),
              ENNReal.ofReal (actualTopPowerDensity
                (acForm (isPositive_chartSpanCurrent θ.val u hu (C.patch j).chart) y)) := by
  classical
  obtain ⟨C, hC⟩ :=
    ActualAnalyticNonPluripolarGlobalIntegral.exists_finite_cover_original_mixed_measure_eq_lintegral
      (fun _ : Fin (m + 1) => hu) (fun _ : Fin (m + 1) => han)
  let E : Fin C.count → Set M := disjointed (fun j => (C.patch j).source)
  have hE : ∀ j, MeasurableSet (E j) :=
    FirstPass.FiniteMeasureGluing.measurableSet_disjointed
      (fun j : Fin C.count => ((C.patch j).source : Set M))
      (fun j => (C.patch j).source.isOpen.measurableSet)
  refine ⟨C, ?_⟩
  change ∀ A : Set M, MeasurableSet A → _
  intro A hA
  have hOld := hC A hA
  simp only [actualMixedTopDensity_const] at hOld
  apply hOld.trans
  apply Finset.sum_congr rfl
  intro j _
  let Q := C.patch j
  let S : Set (ComplexModel (m + 1)) := Q.domain ∩ Q.chart.val.symm ⁻¹' (A ∩ E j)
  have hS : MeasurableSet S :=
    SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      Q.domain.isOpen.measurableSet
      (Q.chart.val.continuousOn_symm.mono Q.domain_le_target) (hA.inter (hE j))
  have hStarget : S ⊆ Q.chart.val.target := inter_subset_left.trans Q.domain_le_target
  have hfin := quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
    (Nat.succ_pos m) u hu.quasiPshPotential Q.chart
  rw [addHaar_canonicalBasis] at hfin
  have hfin' := (ae_restrict_iff' Q.chart.val.open_target.measurableSet).mp hfin
  have hsets :
      (S ∩ Q.chart.val.symm ⁻¹' (⋃ _ : Fin (m + 1), {x | u x = ⊥})ᶜ :
        Set (ComplexModel (m + 1))) =ᵐ[volume] S := by
    filter_upwards [hfin'] with y hy
    apply propext
    constructor
    · exact fun h => h.1
    · intro hyS
      refine ⟨hyS, ?_⟩
      intro hP
      obtain ⟨i, hi⟩ := mem_iUnion.mp hP
      exact (hy (hStarget hyS)).2 hi
  change (∫⁻ y in S ∩ Q.chart.val.symm ⁻¹' (⋃ _ : Fin (m + 1), {x | u x = ⊥})ᶜ,
      ENNReal.ofReal (actualTopPowerDensity
        (θ.val.coeff Q.chart y + smoothDDC (fun w => (chartFunction u Q.chart w).toReal) y))) =
      ∫⁻ y in S, ENNReal.ofReal (actualTopPowerDensity
        (acForm (isPositive_chartSpanCurrent θ.val u hu Q.chart) y))
  rw [setLIntegral_congr hsets]
  apply setLIntegral_congr_fun_ae hS
  filter_upwards [ae_acForm_eq_original_reader θ u hu han Q.chart] with y hy hyS
  rw [hy (hStarget hyS)]

end SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarRNIntegral
