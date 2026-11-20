import SGPT.Okounkov.SourceMultiSliceOriginalTail

/-! Canonical comparison of true nested original tails with the SAME direct
original Y_k carrier and its actual inherited submanifold complex atlas. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

/-- Genuine original Y_k regularity in exactly the remaining source dimension. -/
theorem directCarrier_regular (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    ∀ x ∈ F.flag (originalIndex m k),
      RegularAtDim (n := m + k) (F.flag (originalIndex m k)) x m := by
  simpa only [originalIndex, Nat.add_sub_cancel_right] using
    (F.smooth.2.2 (originalIndex m k)).2.2

/-- The original Y_k inherits its genuine original submanifold atlas. -/
@[instance_reducible]
def directCarrierCharts (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    ChartedSpace (ComplexModel m) (F.flag (originalIndex m k)) :=
  SubmanifoldChartedSpace.chartedSpace (by omega) (directCarrier_regular m k F)

/-- Its original inherited atlas is complex; no transferred atlas is used. -/
theorem directCarrierComplex (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    letI := directCarrierCharts m k F
    IsComplexManifold m (F.flag (originalIndex m k)) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace _ _

/-- Actual projection corestricted to the whole unchanged original carrier. -/
def originalCarrierEquiv (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    (originalTail m k F).carrier ≃ F.flag (originalIndex m k) :=
  Equiv.ofBijective (fun y => ⟨originalInclusion m k F y, by
    rw [← originalInclusion_range m k F]
    exact mem_range_self y⟩) (by
      constructor
      · intro a b hab
        exact originalInclusion_injective m k F (congrArg Subtype.val hab)
      · intro x
        have hx : x.val ∈ Set.range (originalInclusion m k F) := by
          rw [originalInclusion_range]
          exact x.property
        obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext hy⟩)

/-- Compactness and the actual continuous original projection give the same
original topology, without declaring a transported complex atlas. -/
def originalCarrierHomeomorph (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    (originalTail m k F).carrier ≃ₜ F.flag (originalIndex m k) := by
  let e := originalCarrierEquiv m k F
  have hc : Continuous e := (originalInclusion_contMDiff m k F).continuous.subtype_mk _
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- The comparison is literally the same unchanged original point projection. -/
theorem originalCarrierHomeomorph_val (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k))
    (y : (originalTail m k F).carrier) :
    (originalCarrierHomeomorph m k F y).val = originalInclusion m k F y := rfl

/-- Forward holomorphy is genuine original-point inclusion plus actual
submanifold corestriction, not a declaration of transported geometry. -/
theorem originalCarrierHomeomorph_contMDiff (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) :
    letI := directCarrierCharts m k F
    letI := directCarrierComplex m k F
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (originalCarrierHomeomorph m k F) := by
  let _ := directCarrierCharts m k F
  let _ := directCarrierComplex m k F
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + k)) ∞
      (fun y => (originalCarrierHomeomorph m k F y).val) := by
    simpa only [originalCarrierHomeomorph_val] using originalInclusion_contMDiff m k F
  exact SubmanifoldCodRestrict.contMDiff_codRestrict (by omega)
    (directCarrier_regular m k F) hval (fun y => (originalCarrierHomeomorph m k F y).property)

/-- The genuine inverse inserts exactly the original nested carrier data. -/
theorem originalCarrierHomeomorph_symm_succ (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + (k + 1))) :
    ⇑(originalCarrierHomeomorph m (k + 1) F).symm =
      (originalCarrierHomeomorph m k F.tail).symm ∘
        (F.tailComponentHomeomorph (originalIndex m k)).symm := by
  funext x
  apply (originalCarrierHomeomorph m (k + 1) F).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change x.val = (originalInclusion m k F.tail
    ((originalCarrierHomeomorph m k F.tail).symm
      ((F.tailComponentHomeomorph (originalIndex m k)).symm x))).val
  have h := congrArg Subtype.val
    ((originalCarrierHomeomorph m k F.tail).apply_symm_apply
      ((F.tailComponentHomeomorph (originalIndex m k)).symm x))
  change originalInclusion m k F.tail
    ((originalCarrierHomeomorph m k F.tail).symm
      ((F.tailComponentHomeomorph (originalIndex m k)).symm x)) = _ at h
  exact (congrArg Subtype.val h).symm
end SGPT.Okounkov.SourceMultiSlice
