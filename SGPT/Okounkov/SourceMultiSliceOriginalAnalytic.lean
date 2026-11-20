import SGPT.Okounkov.SourceMultiSliceOriginalRestriction

/-! Actual all-k analytic slices, from the same original finite target point.
Restriction PSH witnesses and the source zero-dimensional body are outputs. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.SourceSlice

/-- Actual original analytic first-slice restriction, now also including
the genuine zero-dimensional target. -/
theorem first_slice_analytic_restriction_all_dimensions
    {r : ℕ} (F : OriginalFlagGeometry.{u} (r + 1))
    {θ : ClosedRealOneOneForm (r + 1) F.carrier} {φ : F.carrier → EReal}
    (hA : φ ∈ globalAnalyticCurrents θ)
    (hr : IsThetaPshPotential (firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => φ y.val)) :
    firstCoordinateSlice (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hA.1⟩) 0 =
      SourceTestCurveAllDimensions.generalBody F.tail (firstFlagRestriction F θ)
        ⟨fun y : F.tail.carrier => φ y.val, hr⟩ := by
  cases r with
  | zero =>
      obtain ⟨y, _, hy⟩ := hr.2 (Classical.choice inferInstance) Set.univ isOpen_univ (mem_univ _)
      exact Valuative.slice_zero_generalBody_eq_of_dim_one F hA.1
        (flagValuation_zero_eq_zero_of_ne_bot F hA.1 y.property hy) hr
  | succ r => exact slice_zero_of_globalAnalytic_of_restriction_psh F hA hr

/-- The same actual finite target point internally supplies all intermediate
restrictions and the entire analytic first-k-zero slice. This includes k=0,
k=n and target dimension zero, with the actual source body in each branch. -/
theorem analytic_zeroSlice_eq_of_original_target_finite
    (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k))
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    (hA : φ ∈ globalAnalyticCurrents θ)
    (hfinite : ∃ y : (originalTail m k F).carrier, φ (originalInclusion m k F y) ≠ ⊥) :
    ∃ hR : IsThetaPshPotential (originalRestriction m k F θ).val
        (fun y => φ (originalInclusion m k F y)),
      zeroSlice m k (SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hA.1⟩) =
        SourceTestCurveAllDimensions.generalBody (originalTail m k F)
          (originalRestriction m k F θ) ⟨fun y => φ (originalInclusion m k F y), hR⟩ := by
  induction k with
  | zero => exact ⟨hA.1, rfl⟩
  | succ k ih =>
      have hne : ∃ z : F.tail.carrier, φ z.val ≠ ⊥ := by
        obtain ⟨y, hy⟩ := hfinite
        exact ⟨originalInclusion m k F.tail y, hy⟩
      have hpull := GlobalPotentialPullback.thetaPlurisubharmonic_comp
        (contMDiff_firstFlagInclusion F) hA.1.1
      have hnd := ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpull hne
      have hfirst : IsThetaPshPotential (firstFlagRestriction F θ).val
          (fun z : F.tail.carrier => φ z.val) := ⟨hpull, hnd⟩
      have hAfirst : (fun z : F.tail.carrier => φ z.val) ∈
          globalAnalyticCurrents (firstFlagRestriction F θ) :=
        ⟨hfirst, TranscendentalVolId.restrict_hasAnalyticSingularities (F := F) hA.2⟩
      obtain ⟨hR, hbody⟩ := ih F.tail hAfirst hfinite
      refine ⟨hR, ?_⟩
      rw [zeroSlice_succ, first_slice_analytic_restriction_all_dimensions F hA hfirst]
      exact hbody
end SGPT.Okounkov.SourceMultiSlice
