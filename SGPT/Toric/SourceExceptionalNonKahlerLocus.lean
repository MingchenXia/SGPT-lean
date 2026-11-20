import SGPT.Toric.PointBlowupGeometry
import SGPT.Toric.ToricAugmentedBaseLocus
import SGPT.Toric.PointBlowdownMass
import SGPT.Toric.HyperplanePullbackChern
import SGPT.PSH.BookDeep2Boucksom
import SGPT.Toric.ToricFanConeRealDimension
import Lean.Elab.Command

section ExceptionalNonKahlerCanonicalFragment001
/- BEGIN OriginalExceptionalFaceDraft; original frozen source SHA256 4bbbc3ce7d7441b8df9cc7e16ad0f40fa4e43901d7d91fab7e7d80a0e94bd083 -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Toric.SourceBlowdownMassNext
open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME original face is the actual singleton at the literal lattice origin. -/
theorem originalExceptionalFace_eq_singleton :
    toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs} =
      {latticeVector ![0, 0]} := by
  have hset : toricRaysIn hs {blowupRay7} = {blowupExceptionalRay hs} := by
    ext ray
    simp [toricRaysIn, blowupExceptionalRay, Subtype.ext_iff]
  simpa only [hset] using (toricDivisorFace_blowupHyperplaneDivisor hs).2.2.1

/-- The genuine affine-direction span of that actual singleton face has dimension zero. -/
theorem originalExceptionalFace_dimension_zero :
    Module.finrank ℝ (vectorSpan ℝ
      (toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs})) = 0 := by
  rw [originalExceptionalFace_eq_singleton hs]
  simp

/-- The expected dimension is literally surface dimension two minus one ray. -/
theorem originalExceptionalFace_expected_dimension :
    2 - Nat.card ({blowupExceptionalRay hs} : Set (PolytopeToricRays blowupGenerator hs)) = 1 := by
  simp

/-- Actual deficiency uses the existing dimension predicate, not a renamed scalar. -/
theorem originalExceptionalFace_deficient :
    ToricDivisorFaceDeficient (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs} := by
  apply Or.inr
  rw [originalExceptionalFace_dimension_zero hs, originalExceptionalFace_expected_dimension hs]
  decide

end SGPT.Toric.SourceBlowdownMassNext

end

/- END OriginalExceptionalFaceDraft -/
end ExceptionalNonKahlerCanonicalFragment001

section ExceptionalNonKahlerCanonicalFragment002
/- BEGIN OriginalP2NonKahlerSourceDraft; original frozen source SHA256 0ac76087269a2ce6c4f6d5598c8d9ed56b4a937150750411eccbc88b8e43dacb -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Toric.SourceBlowdownMassNext
open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME physical original H class has actual non-Kähler locus E for EVERY metric. -/
theorem originalHyperplane_nonKahlerLocus_all_metrics
    (h : BigToricMetric (blowupHyperplaneDivisor hs)) :
    nonKahlerLocus (RealBottChern.ofRepresentative h.form) =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  rw [toricSameDivisor_firstChernClass h (nativeSourceHyperplaneMetric hs),
    physicalOriginalHyperplane_firstChernClass_fs hs]
  exact originalBlowdown_pullbackFS_nonKahlerLocus_eq hs

/-- WHOLE literal original ex:P2bl_nK: actual face, actual dimension/deficiency,
and SAME physical H native non-Kähler locus, with all geometry produced internally. -/
theorem source_original_P2bl_nK :
    toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs} =
        {latticeVector ![0, 0]} ∧
    Module.finrank ℝ (vectorSpan ℝ
      (toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs})) = 0 ∧
    2 - Nat.card ({blowupExceptionalRay hs} : Set (PolytopeToricRays blowupGenerator hs)) = 1 ∧
    ToricDivisorFaceDeficient (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs} ∧
    nonKahlerLocus (RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form) =
      toricPrimeDivisor (blowupExceptionalRay hs) ∧
    (∀ h : BigToricMetric (blowupHyperplaneDivisor hs),
      nonKahlerLocus (RealBottChern.ofRepresentative h.form) =
        toricPrimeDivisor (blowupExceptionalRay hs)) := by
  exact ⟨originalExceptionalFace_eq_singleton hs,
    originalExceptionalFace_dimension_zero hs, originalExceptionalFace_expected_dimension hs,
    originalExceptionalFace_deficient hs,
    originalHyperplane_nonKahlerLocus_all_metrics hs (nativeSourceHyperplaneMetric hs),
    originalHyperplane_nonKahlerLocus_all_metrics hs⟩

end SGPT.Toric.SourceBlowdownMassNext

end

/- END OriginalP2NonKahlerSourceDraft -/
end ExceptionalNonKahlerCanonicalFragment002

section ExceptionalNonKahlerCanonicalFragment003
/- BEGIN BookOriginalExceptionalLocusDraft; original frozen source SHA256 ca99c6c84c99bc7f1c89005fe03e2f25e876dad82faffa59a7137d9738f21d41 -/
/-! The literal book current/polar-locus definition, not only its native
all-current Lelong presentation. All bigness/cone hypotheses are produced. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric.SourceBlowdownMassNext
open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Actual bigness is internally forced by the proved locus and actual nonexceptional point. -/
theorem originalHyperplane_isBigClass (h : BigToricMetric (blowupHyperplaneDivisor hs)) :
    IsBigClass (RealBottChern.ofRepresentative h.form) := by
  classical
  by_contra hbig
  have hwhole := nonKahlerLocus_eq_univ_of_not_isBigClass hbig
  rw [originalHyperplane_nonKahlerLocus_all_metrics hs h] at hwhole
  let a : Fin 2 → ℂˣ := fun _ => 1
  let p := polytopeToricEmbedding blowupGenerator hs a
  have hp : p ∈ toricPrimeDivisor (blowupExceptionalRay hs) := by
    rw [hwhole]
    exact mem_univ p
  have hpi : originalBlowdown hs p = blowdownOrigin := by
    have hmem : p ∈ {q | originalBlowdown hs q = blowdownOrigin} := by
      rw [originalBlowdown_fibre_origin hs]
      exact hp
    exact hmem
  exact originalBlowdown_torus_ne_origin hs a hpi

/-- The literal book intersection of analytic Kähler-current POLAR loci equals E. -/
theorem originalHyperplane_bookNonKahlerLocus_all_metrics
    (h : BigToricMetric (blowupHyperplaneDivisor hs)) :
    SGPT.PSH.BookCurrent.currentNonKahlerLocus (RealBottChern.ofRepresentative h.form) =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  rw [SGPT.PSH.BookCurrent.currentNonKahlerLocus_eq_sourceNonKahlerLocus,
    SGPT.PSH.BookDeep2Boucksom.sourceNonKahlerLocus_eq_nonKahlerLocus _
      (originalHyperplane_isBigClass hs h)]
  exact originalHyperplane_nonKahlerLocus_all_metrics hs h

/-- WHOLE original ex:P2bl_nK in the LITERAL book current definition, actual real-cone
dimension, genuine big class and SAME physical original H, with ONLY hs incoming. -/
theorem source_P2bl_nK_whole_book :
    toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs} =
        {latticeVector ![0, 0]} ∧
    Module.finrank ℝ (vectorSpan ℝ
      (toricDivisorFace (blowupHyperplaneDivisor hs) {blowupExceptionalRay hs})) = 0 ∧
    Module.finrank ℝ (toricFanConeRealSpan {blowupExceptionalRay hs}) = 1 ∧
    2 - Module.finrank ℝ (toricFanConeRealSpan {blowupExceptionalRay hs}) = 1 ∧
    SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form) ∧
    SGPT.PSH.BookCurrent.currentNonKahlerLocus
      (RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form) =
        toricPrimeDivisor (blowupExceptionalRay hs) ∧
    (∀ h : BigToricMetric (blowupHyperplaneDivisor hs),
      SGPT.PSH.BookCurrent.currentNonKahlerLocus (RealBottChern.ofRepresentative h.form) =
        toricPrimeDivisor (blowupExceptionalRay hs)) := by
  obtain ⟨v, j, hj⟩ := (blowupExceptionalRay hs).property
  have hray : polytopeToricRay blowupGenerator hs v j = blowupExceptionalRay hs :=
    Subtype.ext hj
  have hcone : IsToricFanCone ({blowupExceptionalRay hs} : Set (PolytopeToricRays blowupGenerator hs)) := by
    refine ⟨v, ({j} : Set (Fin 2)), ?_⟩
    simp only [Set.image_singleton, hray]
  have hdim : Module.finrank ℝ (toricFanConeRealSpan {blowupExceptionalRay hs}) = 1 := by
    simpa using finrank_toricFanConeRealSpan hcone
  refine ⟨originalExceptionalFace_eq_singleton hs, originalExceptionalFace_dimension_zero hs,
    hdim, ?_, ?_, originalHyperplane_bookNonKahlerLocus_all_metrics hs (nativeSourceHyperplaneMetric hs),
    originalHyperplane_bookNonKahlerLocus_all_metrics hs⟩
  · rw [hdim]
  · exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr
      (originalHyperplane_isBigClass hs (nativeSourceHyperplaneMetric hs))

end SGPT.Toric.SourceBlowdownMassNext

end

/- END BookOriginalExceptionalLocusDraft -/
end ExceptionalNonKahlerCanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`BookOriginalExceptionalLocusDraft, `ExceptionalCurveChernIntegralDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalNegativeChernDraft, `ExceptionalNegativeMetricDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalTautologicalVectorDraft, `NativeHolomorphicChernPullbackDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicMetricTransferDraft, `NativeNefCurvePullbackDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalBlowdownLocusDraft, `OriginalBlowdownMassDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalExceptionalFaceDraft, `OriginalExceptionalTransitionDraft, `OriginalHyperplaneSelfIntersectionDraft, `OriginalNonNefBigCurrentDraft, `OriginalNonNefCurveObstructionDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefRestrictionDraft, `OriginalP2NonKahlerSourceDraft, `PhysicalOriginalHyperplaneChernDraft, `PhysicalProjectiveHyperplaneChernDraft, `SimplexOriginalFsFormDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalMassTransportDraft, `SourceF1BigNonNefExampleDraft, `SourceF1ExceptionalIntersectionsDraft, `ToricOriginalSmoothMassDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden original private module in source exceptional non-Kahler provider: {m}"
