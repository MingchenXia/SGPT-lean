import SGPT.Foundations.Analysis.FirstPass.SmoothOffPole
import SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
import SGPT.Foundations.Analysis.Pending.MixedCoordinateDensity

set_option autoImplicit false

/-! # The actual original non-pluripolar measure has its smooth density off poles
The complete NEW mathematical statement and ENTIRE proof were written and
snapshotted before the import-only baseline. Weak analytic remainders are smooth
only off their original zero set. No selected patch or measure comparison is an input.
-/

noncomputable section
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ContDiff Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarOffPoleMeasure
open FirstPass FirstPass.PositiveClasses FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.GlobalPotentialPatches
  FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Natural original weak analytic and genuine theta-PSH inputs internally
produce smooth local representatives and the actual exterior-product density
of the original global mixed measure on ALL measurable subsets of one ball. -/
theorem exists_ball_original_mixed_measure_eq_density
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (han : ∀ i, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (u i))
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : ∀ i, chartFunction (u i) e z ≠ ⊥) :
    ∃ r : ℝ, 0 < r ∧
      ∃ (g ρ : Fin n → ComplexModel n → ℝ),
        let B : Opens (ComplexModel n) := ⟨ball z r, isOpen_ball⟩
        (B : Set (ComplexModel n)) ⊆ e.val.target ∧
        (∀ i, ContDiffOn ℝ ∞ (g i) B ∧
          EqOn (chartFunction (u i) e) (fun y => (g i y : EReal)) B ∧
          IsSmoothLocalPotential (θ i).val e B (ρ i)) ∧
        IsSmoothMixedPshOn B (fun i y => g i y + ρ i y) ∧
        ∀ A : Set (ComplexModel n), MeasurableSet A → A ⊆ B →
          globalMixedMeasure θ u (fun i => (hu i).1) (e.val.symm '' A) =
            ∫⁻ y in A, ENNReal.ofReal
              (actualMixedTopDensity (fun i => (θ i).val.coeff e y + smoothDDC (g i) y)) := by
  classical
  obtain ⟨Q, hQ, hzQ⟩ := exists_patch_in_chart (fun i => (hu i).1) e hz
  have hlocal (i : Fin n) :=
    exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt
      (han i e z hz) (hpole i)
  choose g hg heq using hlocal
  have hgood : {y | ∀ i, ContDiffAt ℝ ∞ (g i) y ∧
      chartFunction (u i) e y = (g i y : EReal)} ∩
      (Q.domain : Set (ComplexModel n)) ∈ 𝓝 z :=
    inter_mem (eventually_all.mpr fun i => (hg i).and (heq i))
      (Q.domain.isOpen.mem_nhds hzQ)
  obtain ⟨Uset, hUsub, hUopen, hzU⟩ := _root_.mem_nhds_iff.mp hgood
  let U : Opens (ComplexModel n) := ⟨Uset, hUopen⟩
  have hUQ : U ≤ Q.domain := fun y hy => (hUsub hy).2
  have hgU (i : Fin n) : ContDiffOn ℝ ∞ (g i) U :=
    fun y hy => ((hUsub hy).1 i).1.contDiffWithinAt
  have heqU (i : Fin n) :
      EqOn (chartFunction (u i) e) (fun y => (g i y : EReal)) U :=
    fun y hy => ((hUsub hy).1 i).2
  let f : Fin n → ComplexModel n → ℝ := fun i y => g i y + Q.potential i y
  have hρU (i : Fin n) : ContDiffOn ℝ ∞ (Q.potential i) U :=
    (Q.localPotential i).2.2.1.mono hUQ
  have hfU (i : Fin n) : ContDiffOn ℝ ∞ (f i) U := (hgU i).add (hρU i)
  have hcorrect (i : Fin n) {y : ComplexModel n} (hy : y ∈ U) :
      Q.corrected i y = (f i y : EReal) := by
    rw [Patch.corrected, hQ, heqU i hy, ← EReal.coe_add]
  have hpshU (i : Fin n) : PlurisubharmonicOn (fun y => (f i y : EReal)) U := by
    intro y hy
    apply (Q.plurisubharmonic i y (hUQ hy)).congr
    filter_upwards [U.isOpen.mem_nhds hy] with w hw
    exact hcorrect i hw
  have hsmU : IsSmoothMixedPshOn U f :=
    MixedMongeAmpere.isSmoothMixedPshOn_of_components
      (fun i => isSmoothPshOn_of_psh (hfU i) (hpshU i))
  have hcont (i : Fin n) : ContinuousAt (f i) z :=
    (hfU i).continuousOn.continuousAt (U.isOpen.mem_nhds hzU)
  have hlow (i : Fin n) : {y | f i z - 1 < f i y} ∈ 𝓝 z :=
    (hcont i).eventually (lt_mem_nhds (by linarith))
  have hnhds : (U : Set (ComplexModel n)) ∩
      ⋂ i, {y | f i z - 1 < f i y} ∈ 𝓝 z :=
    inter_mem (U.isOpen.mem_nhds hzU) (iInter_mem.mpr hlow)
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hnhds
  let B : Opens (ComplexModel n) := ⟨ball z r, isOpen_ball⟩
  have hBU : B ≤ U := fun y hy => (hball (ball_subset_closedBall hy)).1
  have hBQ : B ≤ Q.domain := hBU.trans hUQ
  have hBrel : RelativelyCompactIn B Q.domain := by
    refine ⟨(isCompact_closedBall z r).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall, fun y hy => ?_⟩
    exact hUQ ((hball (closure_ball_subset_closedBall hy)).1)
  obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, |f i z| + 1)
  have hBk : (B : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k := by
    intro y hy
    refine ⟨hBQ hy, fun i => ?_⟩
    rw [hcorrect i (hBU hy)]
    have h1 : f i z - 1 < f i y :=
      mem_iInter.mp (hball (ball_subset_closedBall hy)).2 i
    have h2 : |f i z| ≤ ∑ j, |f j z| :=
      Finset.single_le_sum (f := fun j => |f j z|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := neg_abs_le (f i z)
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hsmB : IsSmoothMixedPshOn B f := hsmU.mono hBU
  have hcorrectReal (i : Fin n) :
      EqOn (fun y => (Q.corrected i y).toReal) (f i) B := by
    intro y hy
    change (Q.corrected i y).toReal = f i y
    rw [hcorrect i (hBU hy), EReal.toReal_coe]
  have hsmQ : IsSmoothMixedPshOn B (fun i y => (Q.corrected i y).toReal) :=
    LocalNonPluripolarDensity.isSmoothMixedPshOn_of_eqOn hsmB hcorrectReal
  have hρB (i : Fin n) : IsSmoothLocalPotential (θ i).val e B (Q.potential i) := by
    rw [← hQ]
    exact (Q.localPotential i).mono B.isOpen hBQ
  have hgB (i : Fin n) : ContDiffOn ℝ ∞ (g i) B := (hgU i).mono hBU
  have hdens {y : ComplexModel n} (hy : y ∈ B) :
      mixedDensity f y =
        actualMixedTopDensity (fun i => (θ i).val.coeff e y + smoothDDC (g i) y) := by
    have hf2 (i : Fin n) : ContDiffAt ℝ 2 (f i) y :=
      (((hfU i).mono hBU y hy).contDiffAt (B.isOpen.mem_nhds hy)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    rw [← actualMixedTopDensity_smoothDDC hf2]
    congr 1
    funext i
    rw [show f i = fun w => g i w + Q.potential i w from rfl,
      smoothDDC_add B.isOpen (hgB i) (hρB i).2.2.1 hy,
      (hρB i).2.2.2 hy, add_comm]
  refine ⟨r, hr, g, Q.potential, ?_, ?_, hsmB, ?_⟩
  · intro y hy
    rw [← hQ]
    exact Q.domain_le_target (hBQ hy)
  · intro i
    exact ⟨hgB i, (heqU i).mono hBU, hρB i⟩
  · intro A hA hAB
    have hlocalMeasure :=
      FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure
        (fun i => (hu i).1) Q B hBQ k hBrel hBk hsmQ hAB
    rw [hQ] at hlocalMeasure
    rw [hlocalMeasure, LocalNonPluripolarDensity.smoothMixedMeasure_eq_of_eqOn
      hsmQ hsmB hcorrectReal, smoothMixedMeasure,
      withDensity_apply _ hA, Measure.restrict_restrict hA,
      show A ∩ (B : Set (ComplexModel n)) = A from inter_eq_left.mpr hAB]
    exact setLIntegral_congr_fun hA fun y hy => congrArg ENNReal.ofReal (hdens (hAB hy))

end SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarOffPoleMeasure
