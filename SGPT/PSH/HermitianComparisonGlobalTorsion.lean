import SGPT.PSH.HermitianComparisonCanonicalOneFactor
import SGPT.PSH.HermitianComparisonPartitionBounds
import SGPT.PSH.HermitianComparisonPureBudget

/-!
# Uniform actual torsion aggregation on strict coordinate sublevels

Compact geometry chooses the derivative constants before all potentials.
The original positive part is read through genuine bounded PSH corrections,
which supply its Borel zero extension without assumptions on the inverse
chart outside its target.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts
open Hermitian HermitianGlobalProducts HermitianComparisonOneFactor
  HermitianComparisonStrict HermitianComparisonCutoff HermitianComparisonPureBudget
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The literal original coordinate strict sublevel, confined to its domain. -/
def comparisonSublevel (P : BackgroundPatch omega) (a : M → EReal) (c : ℝ) :
    Set (ComplexModel (m + 1)) :=
  (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
    P.geometry.chart.val.symm ⁻¹' {x | a x < (c : EReal)}

/-- The actual positive part has a Borel representative equal to it on the
original patch, with exactly its strict comparison support. -/
theorem exists_measurable_positivePart (P : BackgroundPatch omega)
    {a : M → EReal} (ha : IsHermitianPSH omega a)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal)) (c : ℝ) :
    ∃ f : ComplexModel (m + 1) → ℝ, Measurable f ∧
      (∀ z ∈ P.geometry.domain,
        f z = max (c - (a (P.geometry.chart.val.symm z)).toReal) 0) ∧
      (∀ z ∈ P.geometry.domain, z ∉ comparisonSublevel P a c → f z = 0) := by
  have hc : IsHermitianPSH omega (fun _ : M => (c : EReal)) :=
    HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c
  have hcb : ∃ e f : ℝ, ∀ x : M, (e : EReal) ≤ (c : EReal) ∧ (c : EReal) ≤ (f : EReal) :=
    ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩
  let ga := (P.geometry.domain : Set (ComplexModel (m + 1))).indicator (P.correctedReal a)
  let gc := (P.geometry.domain : Set (ComplexModel (m + 1))).indicator
    (P.correctedReal (fun _ : M => (c : EReal)))
  let f : ComplexModel (m + 1) → ℝ := fun z => max (gc z - ga z) 0
  have hga : Measurable ga := measurable_indicator_of_isLocallyBoundedPshOn
    (P.correctedReal_isLocallyBoundedPshOn ha hab)
  have hgc : Measurable gc := measurable_indicator_of_isLocallyBoundedPshOn
    (P.correctedReal_isLocallyBoundedPshOn hc hcb)
  refine ⟨f, (hgc.sub hga).max measurable_const, ?_, ?_⟩
  · intro z hz
    dsimp only [f, ga, gc]
    rw [indicator_of_mem hz, indicator_of_mem hz]
    apply congrArg (fun t : ℝ => max t 0)
    dsimp only [BackgroundPatch.correctedReal, chartFunction]
    rw [EReal.toReal_coe]
    ring
  · intro z hz hnot
    have hle : P.correctedReal (fun _ : M => (c : EReal)) z ≤ P.correctedReal a z := by
      apply le_of_not_gt
      intro hlt
      exact hnot ⟨hz, (correctedReal_lt_iff P hab hcb z).mp hlt⟩
    dsimp only [f, ga, gc]
    rw [indicator_of_mem hz, indicator_of_mem hz, max_eq_right (sub_nonpos.mpr hle)]

/-- Compact geometry chooses every local derivative constant before every
mixed tuple and distinguished potential. Only actual proper trace budgets
on the original coordinate strict sublevels remain on the right. -/
theorem exists_torsionDifference_setBudget_bound (C : CompactPartition omega) :
    ∃ B : Fin C.outer.count → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
        (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
        {a : M → EReal} (_ha : IsHermitianPSH omega a)
        (_hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
        (c : ℝ) {δ : ℝ} (_hδ : 0 ≤ δ)
        (_hgap : ∀ x, max (c - (a x).toReal) 0 ≤ δ),
        |torsionDifference C u hu hb a (fun _ => (c : EReal))| ≤
          ∑ i, B i * δ * patchProperBudget (C.patch i) u hu hb
            (comparisonSublevel (C.patch i) a c ∩ tsupport (C.weight i)) := by
  classical
  choose B hB hbound using fun i =>
    HermitianComparisonBackgroundTorsion.exists_background_derivative_setMass_bound m
      (C.patch i).residual_smooth (C.weight i).hasCompactSupport (C.weight i).tsupport_subset
  refine ⟨B, hB, ?_⟩
  intro u hu hb a ha hab c δ hδ hgap
  have hlocal (i : Fin C.outer.count) :
      |derivativeWeight (patchResidual (C.patch i) u hu hb) (C.weight i)
        (fun z => max (((fun _ : M => (c : EReal))
          ((C.patch i).geometry.chart.val.symm z)).toReal -
          (a ((C.patch i).geometry.chart.val.symm z)).toReal) 0)| ≤
        B i * δ * patchProperBudget (C.patch i) u hu hb
          (comparisonSublevel (C.patch i) a c ∩ tsupport (C.weight i)) := by
    let P := C.patch i
    obtain ⟨f, hf, hread, hzero⟩ := exists_measurable_positivePart P ha hab c
    have hA : MeasurableSet (comparisonSublevel P a c) :=
      (P.geometry.isOpen_coordinate_preimage
        (ha.quasiPshPotential.1.upperSemicontinuous.isOpen_preimage (c : EReal))).measurableSet
    have hfb : ∀ z ∈ P.geometry.domain, |f z| ≤ δ := by
      intro z hz
      rw [hread z hz, abs_of_nonneg (le_max_right _ _)]
      exact hgap _
    have h := hbound i
      (oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1))
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
      (fun j => P.correctedReal (u j))
      (fun j => P.correctedReal_isLocallyBoundedPshOn (hu j) (hb j)) (C.weight i)
      (fun _ hz => hz) (C.abs_weight_le_one i) (comparisonSublevel P a c) hA
      δ hδ f hf hfb hzero
    change |derivativeWeight (patchResidual P u hu hb) (C.weight i) f| ≤
      B i * δ * patchProperBudget P u hu hb
        (comparisonSublevel P a c ∩ tsupport (C.weight i)) at h
    have heq : derivativeWeight (patchResidual P u hu hb) (C.weight i) f =
        derivativeWeight (patchResidual P u hu hb) (C.weight i)
          (fun z => max (((fun _ : M => (c : EReal)) (P.geometry.chart.val.symm z)).toReal -
            (a (P.geometry.chart.val.symm z)).toReal) 0) := by
      unfold derivativeWeight
      apply Finset.sum_congr rfl
      intro s _
      apply ddcWedgePairing_congr_on
      intro z hz
      simpa only [EReal.toReal_coe] using hread z hz
    rw [heq] at h
    exact h
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hlocal i))

end SGPT.PSH.HermitianComparisonGlobalOneFactor
