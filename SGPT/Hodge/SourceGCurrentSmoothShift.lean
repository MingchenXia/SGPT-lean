import SGPT.Hodge.SourceNefProjectiveFamilies
import SGPT.Hodge.SourceCurrentSmoothShift

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Genuine smooth addition on the WHOLE original G set. Class, nondivisoriality
and positive original I-volume are internally proved. -/
def gCurrentSmoothShift (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : GCurrent α) (σ : ClosedRealOneOneForm n X) (hσ : σ.val.IsSemipositive) :
    GCurrent (α + RealBottChern.ofRepresentative σ) :=
  ⟨semipositiveShiftCurrent T.val σ hσ,
    by rw [semipositiveShiftCurrent_class, T.property.1],
    by
      apply current_eq_regular_of_root_eq_class
      rw [semipositiveShiftCurrent_bdivisor]
      change (currentBDivisorAnyOn (ModelSystem.blowup n X) T.val).val ModelSystem.Model.root +
        (rootCartierAny (RealBottChern.ofRepresentative σ)).val ModelSystem.Model.root = _
      rw [currentBDivisorAnyOn_root_of_regular T.val T.property.2.1,
        rootCartierAny_root, semipositiveShiftCurrent_class]
      rfl,
    by
      rw [currentIVolumeAny_eq_bdivisorVolume ω, semipositiveShiftCurrent_bdivisor]
      have hpos := T.property.2.2
      rw [currentIVolumeAny_eq_bdivisorVolume ω] at hpos
      exact hpos.trans_le (volumeAny_le_add_root_semipositive ω _
        (DTUniformDraft.currentBDivisorAnyOn_isNef ω T.val) σ hσ)⟩

/-- The original T↦T+ζ−κ transition, without any supplied potential, regularity
certificate, volume certificate or target representative. -/
def gCurrentTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : GCurrent (α + indexClass κ)) : GCurrent (α + indexClass ζ) :=
  let S := gCurrentSmoothShift ω (α + indexClass κ) T (indexDifference κ ζ) hκζ
  ⟨S.val, by
    rw [S.property.1, indexDifference_class]
    abel, S.property.2⟩

theorem gCurrentTransition_bdivisor (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : GCurrent (α + indexClass κ)) :
    currentBDivisorAnyOn (ModelSystem.blowup n X) (gCurrentTransition ω α hκζ T).val =
      currentBDivisorAnyOn (ModelSystem.blowup n X) T.val +
        rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)) :=
  semipositiveShiftCurrent_bdivisor T.val _ hκζ

/-- Quotient descent through the already proved faithful actual-current
correspondence. The next identity proves the exact original current map induces it. -/
def quotientTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ) :
    Quotient (gCurrentISetoid ω (α + indexClass κ)) →
      Quotient (gCurrentISetoid ω (α + indexClass ζ)) := fun q =>
  (sourceCurrentBDivisorEquiv ω (α + indexClass ζ)).symm
    (bigNefTransition ω α hκζ (sourceCurrentBDivisorEquiv ω (α + indexClass κ) q))

theorem quotientTransition_mk (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (T : GCurrent (α + indexClass κ)) :
    quotientTransition ω α hκζ (Quotient.mk _ T) =
      Quotient.mk _ (gCurrentTransition ω α hκζ T) := by
  apply (sourceCurrentBDivisorEquiv ω (α + indexClass ζ)).injective
  change (sourceCurrentBDivisorEquiv ω (α + indexClass ζ))
    ((sourceCurrentBDivisorEquiv ω (α + indexClass ζ)).symm _) = _
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (gCurrentTransition_bdivisor ω α hκζ T).symm

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
