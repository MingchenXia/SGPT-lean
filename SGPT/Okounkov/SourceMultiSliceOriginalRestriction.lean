import SGPT.Okounkov.SourceMultiSliceOriginalTail

/-! Actual original iterated form and Kahler restriction, with genuine
geometric functoriality to the same original point inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN

/-- Literal iterated restriction of the same original smooth form. Actual
comparison with direct pullback is geometric, not a false stored-form equality. -/
def originalRestriction (m : ℕ) : (k : ℕ) → (F : OriginalFlagGeometry.{u} (m + k)) →
    ClosedRealOneOneForm (m + k) F.carrier →
      ClosedRealOneOneForm m (originalTail m k F).carrier
  | 0, _, θ => θ
  | k + 1, F, θ => originalRestriction m k F.tail (firstFlagRestriction F θ)

/-- Direct and iterated restrictions retain the same original geometric form. -/
theorem originalRestriction_geometricallyEq (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    (θ : ClosedRealOneOneForm (m + k) F.carrier) :
    (originalRestriction m k F θ).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (originalInclusion_contMDiff m k F) θ).val := by
  induction k with
  | zero => exact (SmoothRealForm.pullback_id_geometricallyEq θ.val).symm
  | succ k ih =>
      have h := TranscendentalVolId.pullback_comp_geometricallyEq'
        (contMDiff_firstFlagInclusion F) (originalInclusion_contMDiff m k F.tail) θ.val
      exact (ih F.tail (firstFlagRestriction F θ)).trans h.symm

/-- Actual restriction is linear on the stored original forms, so the
same original positive perturbations pass to the same actual target. -/
theorem originalRestriction_add_smul (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    (θ η : ClosedRealOneOneForm (m + k) F.carrier) (c : ℝ) :
    originalRestriction m k F (θ + c • η) =
      originalRestriction m k F θ + c • originalRestriction m k F η := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hfirst : firstFlagRestriction F (θ + c • η) =
          firstFlagRestriction F θ + c • firstFlagRestriction F η := by
        let hf := contMDiff_firstFlagInclusion F
        have ha := TranscendentalBody.pullback_add' hf θ (c • η)
        have hs := TranscendentalBody.pullback_smul' hf c η
        exact ha.trans (congrArg (fun ρ => ClosedRealOneOneForm.pullback hf θ + ρ) hs)
      change originalRestriction m k F.tail (firstFlagRestriction F (θ + c • η)) = _
      rw [hfirst]
      exact ih F.tail (firstFlagRestriction F θ) (firstFlagRestriction F η)

/-- Actual restriction of the same original Kahler form to every original tail. -/
def originalKahler (m : ℕ) : (k : ℕ) → (F : OriginalFlagGeometry.{u} (m + k)) →
    KahlerBackground (m + k) F.carrier → KahlerBackground m (originalTail m k F).carrier
  | 0, _, κ => κ
  | k + 1, F, κ => originalKahler m k F.tail
      (TranscendentalSlice.restrictedKahlerForm (F := F) κ)

/-- The restricted background form is exactly the iterated original restriction. -/
theorem originalKahler_form (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k))
    (κ : KahlerBackground (m + k) F.carrier) :
    (originalKahler m k F κ).form = originalRestriction m k F κ.form := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih F.tail (TranscendentalSlice.restrictedKahlerForm (F := F) κ)

/-- The actual original point inclusion pulls back the original Kahler form
to a genuine Kahler form; there is no incoming immersion/model certificate. -/
theorem originalInclusion_pullback_isKahler (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (κ : KahlerBackground (m + k) F.carrier) :
    (ClosedRealOneOneForm.pullback (originalInclusion_contMDiff m k F) κ.form).val.IsKahler := by
  have hgeo := originalRestriction_geometricallyEq m k F κ.form
  have hK : (originalRestriction m k F κ.form).val.IsKahler := by
    rw [← originalKahler_form m k F κ]
    exact (originalKahler m k F κ).isKahler
  exact hgeo.isKahler_iff.mp hK
end SGPT.Okounkov.SourceMultiSlice
