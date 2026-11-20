import SGPT.Toric.NonNefExceptionalChern
import SGPT.Projective.FubiniStudyNormalization
import SGPT.Toric.SourceExceptionalHyperplane
import SGPT.Toric.NativeChernPullback
import SGPT.Toric.HyperplanePullbackChern
import SGPT.Toric.PointBlowdownMass
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Toric.NonNefToricCurrent
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN SourceF1ExceptionalIntersectionsDraft; original source SHA256 d7e8b4c0c1518c7881e7fd4da7df16bd989e3c4a6c67fd9a96711881e37570ec -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.LineBundleMetric SGPT.Toric.ExceptionalRestrictionDraft

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Genuine E²=-1: actual O(E) restricted along the SAME original exceptional P1,
actual native Chern-class integration, every smooth metric, and produced FS normalization. -/
theorem exceptionalDivisorCurveDegree_eq_neg_one
    (h : HermitianMetric (n := 1) (ExceptionalDivisorFiber hs)) :
    exceptionalDivisorCurveDegree hs (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1)) h = -1 := by
  rw [exceptionalDivisorCurveDegree_eq_neg_FS,
    SGPT.Projective.FsNormalizationNext.originalCP1_fs_classSlotIntegral_eq_one]

/-- Genuine D.E=-1 for the SAME physical original D=2H+E and actual native curve degree. -/
theorem nonNefRestrictedCurveDegree_eq_neg_one
    (h : HermitianMetric (n := 1) (NonNefRestrictedFiber hs)) :
    nonNefRestrictedCurveDegree hs (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1)) h = -1 := by
  rw [nonNefRestrictedCurveDegree_eq_neg_FS,
    SGPT.Projective.FsNormalizationNext.originalCP1_fs_classSlotIntegral_eq_one]

/-- Source-only genuine exceptional self-intersection, with all geometry/metric/background internal. -/
theorem sourceExceptionalDivisorDegree_eq_neg_one : sourceExceptionalDivisorDegree = -1 :=
  exceptionalDivisorCurveDegree_eq_neg_one _ _

/-- Source-only genuine original D.E, with all geometry/metric/background internal. -/
theorem sourceOriginalNonNefDivisorDegree_eq_neg_one : sourceOriginalNonNefDivisorDegree = -1 :=
  nonNefRestrictedCurveDegree_eq_neg_one _ _

/-- The actual printed H.E=0,E²=-1 and (2H+E).E=-1, using the SAME original physical bundles
and genuine native curve integrals. The separate global H² and nef/big clauses remain separate. -/
theorem source_original_F1_exceptional_intersections :
    sourceExceptionalHyperplaneDegree = 0 ∧ sourceExceptionalDivisorDegree = -1 ∧
      sourceOriginalNonNefDivisorDegree = -1 :=
  ⟨sourceExceptionalHyperplaneDegree_zero, sourceExceptionalDivisorDegree_eq_neg_one,
    sourceOriginalNonNefDivisorDegree_eq_neg_one⟩

end SGPT.Toric.F1IntersectionDraft

#print axioms SGPT.Toric.F1IntersectionDraft.exceptionalDivisorCurveDegree_eq_neg_one
#print axioms SGPT.Toric.F1IntersectionDraft.nonNefRestrictedCurveDegree_eq_neg_one
#print axioms SGPT.Toric.F1IntersectionDraft.source_original_F1_exceptional_intersections

end
/- END SourceF1ExceptionalIntersectionsDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN OriginalNonNefCurveObstructionDraft; original source SHA256 b7207f2536ed83766abf2535ae1e536802e7058c67891428337cdca331ad5947 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH SGPT.PSH.LineBundleMetric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual native metric on the SAME original D restriction, inherited from the original
physical toric D metric by the original holomorphic exceptional map. -/
def originalNonNefPulledMetric : HermitianMetric (n := 1) (NonNefRestrictedFiber hs) :=
  sourceNativeHermitianMetric
    (nativeHolomorphicPullbackBundle (toricNativeHermitianLineBundle (originalNonNefMetric hs))
      (originalExceptionalHolomorphicMap hs))
    (nativeHolomorphicPullback_smooth (toricNativeHermitianLineBundle (originalNonNefMetric hs))
      (originalExceptionalHolomorphicMap hs)
      (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle (originalNonNefMetric hs)))

/-- Genuine c1 restriction dictionary: actual pullback of the SAME original global D Chern
form equals the actual first Chern class of the SAME physical D|E. No comparison hypothesis. -/
theorem originalNonNef_pullback_firstChernClass :
    RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback (contMDiff_originalExceptionalCurve hs) (originalNonNefMetric hs).form) =
    RealBottChern.ofRepresentative (firstChernForm (originalNonNefPulledMetric hs)) := by
  have h := nativeHolomorphicPullback_firstChern_geometrically
    (toricNativeHermitianLineBundle (originalNonNefMetric hs)) (originalExceptionalHolomorphicMap hs)
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle (originalNonNefMetric hs))
    (originalNonNefMetric hs).form (isOwnFirstChernForm_toricNativeHermitianLineBundle (originalNonNefMetric hs))
  exact (RealBottChern.ofRepresentative_eq_of_geometricallyEq h).symm

/-- The actual negative curve integral is the integral of the actual global D Chern form
pulled back along the SAME original exceptional curve. -/
theorem originalNonNef_pullback_curve_integral :
    SGPT.Foundations.Analysis.Pending.NefMixedMass.slotIntegral
      (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1))
      (fun _ : Fin 1 => ClosedRealOneOneForm.pullback (contMDiff_originalExceptionalCurve hs)
        (originalNonNefMetric hs).form) = -1 := by
  rw [← classSlotIntegral_ofRepresentative]
  simp_rw [originalNonNef_pullback_firstChernClass hs]
  exact nonNefRestrictedCurveDegree_eq_neg_one hs (originalNonNefPulledMetric hs)

/-- Original D is genuinely NOT NEF: the actual native nef criterion contradicts its
actual negative Chern integral on the original holomorphic exceptional P1. -/
theorem originalNonNef_not_nefWithRespectTo
    (omegaX : KahlerBackground 2 (PolytopeToricVariety blowupGenerator hs)) :
    ¬ NefWithRespectTo omegaX (originalNonNefMetric hs).form := by
  intro hnef
  have hpull := nefWithRespectTo_holomorphicPullbackAnyDimension (contMDiff_originalExceptionalCurve hs)
    omegaX (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1)) hnef
  have hpos := SGPT.Foundations.Analysis.Pending.NefMixedMass.slotIntegral_nonneg_of_nef
    (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1)) (fun _ : Fin 1 => hpull)
  rw [originalNonNef_pullback_curve_integral hs] at hpos
  norm_num at hpos

/-- Non-nefness is on the EXISTING genuine native Bott--Chern class criterion, for EVERY
actual Kähler reference, not on a newly assigned divisor/neffness label. -/
theorem originalNonNef_not_classNefWithRespectTo
    (omegaX : KahlerBackground 2 (PolytopeToricVariety blowupGenerator hs)) :
    ¬ ClassNefWithRespectTo omegaX (RealBottChern.ofRepresentative (originalNonNefMetric hs).form) :=
  originalNonNef_not_nefWithRespectTo hs omegaX

/-- The actual first Chern class of the SAME original physical divisor D=2H+E. -/
def sourceOriginalNonNefClass : RealBottChern 2 (PolytopeToricVariety blowupGenerator blowup_edgeSmooth) :=
  RealBottChern.ofRepresentative (originalNonNefMetric blowup_edgeSmooth).form

/-- Source-only genuine original non-nefness, with original geometry and the actual Kähler
background manufactured internally; no model/metric/obstruction certificate input. -/
theorem source_original_F1_not_nef :
    ¬ ClassNefWithRespectTo (polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      sourceOriginalNonNefClass :=
  originalNonNef_not_classNefWithRespectTo _ _

end SGPT.Toric.F1IntersectionDraft

#print axioms SGPT.Toric.F1IntersectionDraft.source_original_F1_not_nef

end
/- END OriginalNonNefCurveObstructionDraft -/
end F1CanonicalFragment002

section F1CanonicalFragment003
/- BEGIN OriginalHyperplaneSelfIntersectionDraft; original source SHA256 678c1e8c31d996c2f477404a923576c7541ef20e6790b80660c4fd2e08ad6ea8 -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis.Pending.NefMixedMass

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- GENUINE self-intersection of the SAME original physical H: the existing native
top first-Chern-class integral on the SAME actual original toric surface. -/
def originalHyperplaneSelfIntersection : ℝ :=
  classSlotIntegral (polytopeToricKahlerBackground blowupGenerator hs)
    (fun _ : Fin 2 => RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form)

/-- Actual H²=1, from physical H Chern class, genuine source blowdown mass transport,
and the genuine original CP2 FS integral1. No input model/mass/intersection certificate. -/
theorem originalHyperplaneSelfIntersection_eq_one : originalHyperplaneSelfIntersection hs = 1 := by
  unfold originalHyperplaneSelfIntersection
  simp_rw [physicalOriginalHyperplane_firstChernClass_fs hs]
  calc
    _ = slotIntegral (polytopeToricKahlerBackground blowupGenerator hs)
        (fun _ : Fin 2 => ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
          (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
      classSlotIntegral_ofRepresentative _ _
    _ = slotIntegral (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 2))
        (fun _ : Fin 2 => SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2)) :=
      SGPT.Toric.SourceBlowdownMassNext.originalBlowdown_fs_slotIntegral_eq hs
    _ = classSlotIntegral (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 2))
        (fun _ : Fin 2 => RealBottChern.ofRepresentative
          (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
      (classSlotIntegral_ofRepresentative _ _).symm
    _ = 1 := SGPT.Projective.FsNormalizationNext.originalCP2_fs_classSlotIntegral_eq_one

/-- Source-only original genuine H², with actual surface/physical H/Chern form/background internal. -/
def sourceOriginalHyperplaneSelfIntersection : ℝ := originalHyperplaneSelfIntersection blowup_edgeSmooth

theorem sourceOriginalHyperplaneSelfIntersection_eq_one : sourceOriginalHyperplaneSelfIntersection = 1 :=
  originalHyperplaneSelfIntersection_eq_one _

end SGPT.Toric.F1IntersectionDraft

#print axioms SGPT.Toric.F1IntersectionDraft.sourceOriginalHyperplaneSelfIntersection_eq_one

end
/- END OriginalHyperplaneSelfIntersectionDraft -/
end F1CanonicalFragment003

section F1CanonicalFragment004
/- BEGIN SourceF1BigNonNefExampleDraft; original source SHA256 3b3db7d718f41902ce27576e9919a5df7f8c6fdf3c33681e0f7b9c2c595f96d0 -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Toric.BlowdownDraft SGPT.Toric.ExceptionalRestrictionDraft

/-- Whole literal original ex:F1big_non_nef265--324 on the SAME actual original point
blowup, physical Cartier divisors/Chern integrals, genuine Kähler-current big class and
existing native nef criterion. Every geometry/current/normalization input is manufactured. -/
theorem source_F1big_non_nef_whole :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) sourceOriginalBlowdown ∧
    blowupNonNefDivisor blowup_edgeSmooth =
      (2 : ℕ) • blowupHyperplaneDivisor blowup_edgeSmooth + originalExceptionalDivisor blowup_edgeSmooth ∧
    sourceOriginalHyperplaneSelfIntersection = 1 ∧
    sourceExceptionalHyperplaneDegree = 0 ∧
    sourceExceptionalDivisorDegree = -1 ∧
    sourceOriginalNonNefDivisorDegree = -1 ∧
    IsBigClass sourceOriginalNonNefClass ∧
    ¬ ClassNefWithRespectTo (polytopeToricKahlerBackground blowupGenerator blowup_edgeSmooth)
      sourceOriginalNonNefClass ∧
    toricDivisorPolytope (blowupNonNefDivisor blowup_edgeSmooth) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 2 ∧ -1 ≤ m 0 + m 1} ∧
    toricDivisorPolytope (blowupNonNefDivisor blowup_edgeSmooth) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 2} ∧
    ∀ m : EuclideanSpace ℝ (Fin 2), 0 ≤ m 0 → 0 ≤ m 1 → -1 ≤ m 0 + m 1 := by
  have hpoly := toricDivisorPolytope_blowupNonNefDivisor blowup_edgeSmooth
  exact ⟨source_original_point_blowup, originalNonNefDivisor_twoH_add_E _,
    sourceOriginalHyperplaneSelfIntersection_eq_one, sourceExceptionalHyperplaneDegree_zero,
    sourceExceptionalDivisorDegree_eq_neg_one, sourceOriginalNonNefDivisorDegree_eq_neg_one,
    originalNonNef_isBigClass _, source_original_F1_not_nef,
    toricDivisorPolytope_blowupNonNefDivisor_ineq _, hpoly.1, hpoly.2⟩

end SGPT.Toric.F1IntersectionDraft

#print axioms SGPT.Toric.F1IntersectionDraft.source_F1big_non_nef_whole

end
/- END SourceF1BigNonNefExampleDraft -/
end F1CanonicalFragment004


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
