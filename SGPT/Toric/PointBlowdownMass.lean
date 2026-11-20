import SGPT.Toric.PointBlowupUniversal
import SGPT.Projective.FubiniStudy
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.BlowupCodimOne
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.BlowupNonKahlerLocusEq
import SGPT.Foundations.Analysis.Pending.FlatComplexTorusNakamaye
import Lean.Elab.Command

section FsBlowdownCanonicalFragmentOriginalBlowdownMassDraft
/- BEGIN OriginalBlowdownMassDraft; original frozen source SHA256 bb27453f586b709a078fe379420e365ee1d9580c4423a31f0241ae6594cbeb2f -/
/-! Genuine geometric mass transport for the SAME accepted original blowdown.
No output modification, integral normalization or Chern comparison is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric.SourceBlowdownMassNext

open Set MeasureTheory
open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
open SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped BigOperators Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual source point-blowup UP internally produces modification geometry. -/
theorem originalBlowdown_actualAnalyticModification :
    IsAnalyticModification (n := 2) (originalBlowdown hs) :=
  PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong
    (originalBlowdown_isBlowupAlong hs)

/-- The actual smooth mixed integral of the SAME native pulled-back FS form.
All geometric inputs except the original polytope smoothness are manufactured. -/
theorem originalBlowdown_fs_slotIntegral_eq :
    slotIntegral (polytopeToricKahlerBackground blowupGenerator hs)
      (fun _ : Fin 2 => ClosedRealOneOneForm.pullback
        (contMDiff_originalBlowdown hs) (ComplexProjectiveSpace.fsClosedForm (N := 2))) =
    slotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
      (fun _ : Fin 2 => ComplexProjectiveSpace.fsClosedForm (N := 2)) := by
  have hX : ∀ _ : Fin 2, ThetaPlurisubharmonic
      (ComplexProjectiveSpace.fsClosedForm (N := 2)).val (fun _ => (0 : EReal)) :=
    fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
      (ComplexProjectiveSpace.fsBackground (N := 2)).isSemipositive).1
  have hY : ∀ _ : Fin 2, ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
        (ComplexProjectiveSpace.fsClosedForm (N := 2))).val (fun _ => (0 : EReal)) :=
    fun i => thetaPlurisubharmonic_comp (contMDiff_originalBlowdown hs) (hX i)
  have hmass := globalMixedMeasure_univ_pullback_of_isAnalyticModification
    (originalBlowdown_actualAnalyticModification hs) hX
  calc
    slotIntegral (polytopeToricKahlerBackground blowupGenerator hs)
        (fun _ : Fin 2 => ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
          (ComplexProjectiveSpace.fsClosedForm (N := 2))) =
        (globalMixedMeasure
          (fun _ : Fin 2 => ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
            (ComplexProjectiveSpace.fsClosedForm (N := 2)))
          (fun _ _ => (0 : EReal)) hY).real univ :=
      (globalMixedMeasure_real_univ_eq_integral
        (polytopeToricKahlerBackground blowupGenerator hs) _ hY).symm
    _ = (globalMixedMeasure
        (fun _ : Fin 2 => ComplexProjectiveSpace.fsClosedForm (N := 2))
        (fun _ _ => (0 : EReal)) hX).real univ := congrArg ENNReal.toReal hmass
    _ = slotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
        (fun _ : Fin 2 => ComplexProjectiveSpace.fsClosedForm (N := 2)) :=
      globalMixedMeasure_real_univ_eq_integral
        (ComplexProjectiveSpace.fsBackground (N := 2)) _ hX

end SGPT.Toric.SourceBlowdownMassNext

end
/- END OriginalBlowdownMassDraft -/
end FsBlowdownCanonicalFragmentOriginalBlowdownMassDraft

section FsBlowdownCanonicalFragmentOriginalBlowdownLocusDraft
/- BEGIN OriginalBlowdownLocusDraft; original frozen source SHA256 aba6a6eb61c51f97807e1b5ba58ffd2761cb6f769e7e787ce7f2ff0db4529cd5 -/
/-! Actual differential exceptional locus and native non-Kähler locus for
the SAME original blowdown. Physical-H Chern comparison remains separate. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric.SourceBlowdownMassNext

open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open scoped Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The genuine differential exceptional locus is the SAME actual printed E. -/
theorem originalBlowdown_exceptionalLocus_eq :
    exceptionalLocus 2 (originalBlowdown hs) =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  rw [← originalBlowdown_fibre_origin hs]
  ext p
  constructor
  · intro hp
    exact mem_singleton_iff.mp
      (BlowupIsomorphismOff.exceptionalLocus_subset_preimage
        (originalBlowdown_isBlowupAlong hs) hp)
  · intro hp
    change originalBlowdown hs p = blowdownOrigin at hp
    have hreg : RegularAtDim (n := 2)
        ({blowdownOrigin} : Set (ComplexProjectiveSpace 2)) blowdownOrigin 0 :=
      (DominationLogResolution.isClosedConnectedSubmanifold_singleton blowdownOrigin).2.2
        blowdownOrigin (mem_singleton blowdownOrigin)
    obtain ⟨_, _, phi, hsrc, _, hflat⟩ := hreg
    exact BlowupCodimOne.mem_exceptionalLocus_of_codim_ge_two
      (originalBlowdown_isBlowupAlong hs) hsrc hflat (by decide)
      (by rw [hp]; exact mem_flatDomain_self phi)
      (by rw [hp]; exact mem_singleton blowdownOrigin)

/-- The actual native non-Kähler locus of the SAME pulled-back original FS class. -/
theorem originalBlowdown_pullbackFS_nonKahlerLocus_eq :
    nonKahlerLocus (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
        (ComplexProjectiveSpace.fsClosedForm (N := 2)))) =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  have hbase : nonKahlerLocus (RealBottChern.ofRepresentative
      (ComplexProjectiveSpace.fsClosedForm (N := 2))) = ∅ :=
    FlatComplexTorusNakamaye.nonKahlerLocus_kahler_eq_empty (by decide)
      (ComplexProjectiveSpace.fsBackground (N := 2))
  have h := BlowupNonKahlerLocusEq.nonKahlerLocus_pullback_eq
    ⟨ComplexProjectiveSpace.fsBackground (N := 2)⟩
    (ComplexProjectiveSpace.fsClosedForm (N := 2)) (originalBlowdown_isBlowupAlong hs)
  rw [hbase, preimage_empty, empty_union, originalBlowdown_exceptionalLocus_eq hs] at h
  exact h

end SGPT.Toric.SourceBlowdownMassNext

end
/- END OriginalBlowdownLocusDraft -/
end FsBlowdownCanonicalFragmentOriginalBlowdownLocusDraft


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden original private module in actual proper FS/blowdown provider: {m}"
