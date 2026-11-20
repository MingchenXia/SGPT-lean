import SGPT.Toric.NativeChernPullback
import SGPT.Toric.SameDivisorChernClass
import SGPT.Projective.SimplexFubiniStudy
import SGPT.Toric.PointBlowupHyperplane
import SGPT.BDivisor.ClassPullback
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN PhysicalProjectiveHyperplaneChernDraft; original source SHA256 a9e07483d0af6bfcd5307583a0816c28b5f05c3bd84d80faf5c8c0cdc183f716 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.PSH SGPT.PSH.LineBundleMetric SGPT.BDivisor
open scoped Topology Manifold ContDiff

/-- The genuine full-lattice FS metric on the SAME original simplex hyperplane divisor. -/
def physicalProjectiveFsSimplexMetric : BigToricMetric (simplexHyperplaneDivisor targetSimplexSmooth) where
  form := (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).form
  weight := (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).weight
  smooth := (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).smooth
  coeff := (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).coeff
  invariant := (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).invariant
  transition v w a := by
    rw [simplexHyperplaneDivisor_eq_ample targetSimplexSmooth]
    exact (toricFullLatticeMetric (γ := simplexGenerator 2) (hs := targetSimplexSmooth)).transition v w a

/-- The SAME published actual physical projective O(1) has a genuine smooth inherited metric. -/
theorem physicalProjectiveHyperplane_sourceSmooth : IsSourceSmoothHermitianMetric nativeProjectiveHyperplaneBundle :=
  nativeHolomorphicPullback_smooth (toricNativeHermitianLineBundle nativeSimplexHyperplaneMetric)
    simplexInverseHolomorphicMap (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle nativeSimplexHyperplaneMetric)

/-- The SAME published physical O_P2(1) has the actual ORIGINAL FS first Chern class.
All geometry and metric comparisons are manufactured from the actual simplex biholomorphism. -/
theorem physicalProjectiveHyperplane_firstChernClass :
    RealBottChern.ofRepresentative (sourceNativeFirstChernForm nativeProjectiveHyperplaneBundle
      physicalProjectiveHyperplane_sourceSmooth) =
      RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2)) := by
  let a := RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2))
  have hchoice := toricSameDivisor_firstChernClass nativeSimplexHyperplaneMetric physicalProjectiveFsSimplexMetric
  have hcurv := nativeHolomorphicPullback_firstChern_geometrically
    (toricNativeHermitianLineBundle nativeSimplexHyperplaneMetric) simplexInverseHolomorphicMap
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle nativeSimplexHyperplaneMetric)
    nativeSimplexHyperplaneMetric.form (isOwnFirstChernForm_toricNativeHermitianLineBundle nativeSimplexHyperplaneMetric)
  have hsource : RealBottChern.ofRepresentative (sourceNativeFirstChernForm nativeProjectiveHyperplaneBundle
      physicalProjectiveHyperplane_sourceSmooth) =
      classPullback simplexInverseHolomorphicMap.contMDiff (RealBottChern.ofRepresentative nativeSimplexHyperplaneMetric.form) :=
    RealBottChern.ofRepresentative_eq_of_geometricallyEq hcurv
  have hFS : physicalProjectiveFsSimplexMetric.form =
      ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph targetSimplexSmooth)
        (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2)) :=
    SGPT.Projective.FsNormalizationNext.simplexFullLatticeMetric_form_eq_original_fs_pullback targetSimplexSmooth
  have hfunc : (fun p : SGPT.Projective.ComplexProjectiveSpace 2 =>
      simplexProjectiveHomeomorph targetSimplexSmooth (simplexInverseHolomorphicMap p)) = id :=
    funext fun p => (simplexProjectiveHomeomorph targetSimplexSmooth).apply_symm_apply p
  have hcomp := classPullback_comp (contMDiff_simplexProjectiveHomeomorph targetSimplexSmooth)
    simplexInverseHolomorphicMap.contMDiff a
  have hid : classPullback ((contMDiff_simplexProjectiveHomeomorph targetSimplexSmooth).comp
      simplexInverseHolomorphicMap.contMDiff) a = a :=
    (classPullback_congr hfunc ((contMDiff_simplexProjectiveHomeomorph targetSimplexSmooth).comp
      simplexInverseHolomorphicMap.contMDiff) contMDiff_id a).trans (classPullback_id a)
  calc
    _ = classPullback simplexInverseHolomorphicMap.contMDiff
        (RealBottChern.ofRepresentative nativeSimplexHyperplaneMetric.form) := hsource
    _ = classPullback simplexInverseHolomorphicMap.contMDiff
        (RealBottChern.ofRepresentative physicalProjectiveFsSimplexMetric.form) := congrArg _ hchoice
    _ = classPullback simplexInverseHolomorphicMap.contMDiff
        (classPullback (contMDiff_simplexProjectiveHomeomorph targetSimplexSmooth) a) := by rw [hFS]; rfl
    _ = a := hcomp.symm.trans hid

end SGPT.Toric.F1IntersectionDraft

end
/- END PhysicalProjectiveHyperplaneChernDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN PhysicalOriginalHyperplaneChernDraft; original source SHA256 0cf55a48fd650c3845cd4749ac905b3324616fcd5de9ae4cf0bcff8b6d993e48 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.PSH SGPT.PSH.LineBundleMetric SGPT.BDivisor
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME published physical pi*O_P2(1) has its genuine inherited smooth native metric. -/
theorem physicalBlowdownPullbackHyperplane_sourceSmooth :
    IsSourceSmoothHermitianMetric (nativeBlowdownPullbackHyperplaneBundle hs) :=
  nativeHolomorphicPullback_smooth nativeProjectiveHyperplaneBundle (originalBlowdownHolomorphicMap hs)
    physicalProjectiveHyperplane_sourceSmooth

/-- Actual smooth metric on the SAME original physical H, pulled back through the actual723
coefficient-one holomorphic line-bundle identification H ≃ pi*O_P2(1). -/
def physicalOriginalHyperplaneTransferredMetric :
    HermitianMetric (n := 2) (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) :=
  nativeMetricTransfer (nativeBlowdownHyperplaneFiberEquiv hs) (contMDiff_nativeBlowdownHyperplaneTotalMap hs)
    (sourceNativeHermitianMetric (nativeBlowdownPullbackHyperplaneBundle hs)
      (physicalBlowdownPullbackHyperplane_sourceSmooth hs))

/-- The SAME original physical hyperplane bundle has the ACTUAL pulled-back original CP2 FS
first Chern class. Every physical bundle/metric/geometry dictionary is produced internally. -/
theorem physicalOriginalHyperplane_firstChernClass_fs :
    RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback (contMDiff_originalBlowdown hs)
        (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2))) := by
  let mH := sourceNativeHermitianMetric (toricNativeHermitianLineBundle (nativeSourceHyperplaneMetric hs))
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle (nativeSourceHyperplaneMetric hs))
  let mP := sourceNativeHermitianMetric (nativeBlowdownPullbackHyperplaneBundle hs)
    (physicalBlowdownPullbackHyperplane_sourceSmooth hs)
  let cP := sourceNativeFirstChernForm nativeProjectiveHyperplaneBundle physicalProjectiveHyperplane_sourceSmooth
  have hH : RealBottChern.ofRepresentative (firstChernForm mH) =
      RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form :=
    RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (toricNativeFirstChernForm_geometricallyEq (nativeSourceHyperplaneMetric hs))
  have hpullCurv := nativeHolomorphicPullback_firstChern_geometrically nativeProjectiveHyperplaneBundle
    (originalBlowdownHolomorphicMap hs) physicalProjectiveHyperplane_sourceSmooth cP
    (sourceNativeFirstChernForm_isOwn nativeProjectiveHyperplaneBundle physicalProjectiveHyperplane_sourceSmooth)
  have hpull : RealBottChern.ofRepresentative (firstChernForm mP) =
      classPullback (contMDiff_originalBlowdown hs) (RealBottChern.ofRepresentative cP) :=
    RealBottChern.ofRepresentative_eq_of_geometricallyEq hpullCurv
  calc
    _ = RealBottChern.ofRepresentative (firstChernForm mH) := hH.symm
    _ = RealBottChern.ofRepresentative (firstChernForm (physicalOriginalHyperplaneTransferredMetric hs)) :=
      firstChernClass_eq mH (physicalOriginalHyperplaneTransferredMetric hs)
    _ = RealBottChern.ofRepresentative (firstChernForm mP) :=
      nativeMetricTransfer_firstChernClass (nativeBlowdownHyperplaneFiberEquiv hs)
        (contMDiff_nativeBlowdownHyperplaneTotalMap hs) mP
    _ = classPullback (contMDiff_originalBlowdown hs) (RealBottChern.ofRepresentative cP) := hpull
    _ = classPullback (contMDiff_originalBlowdown hs)
        (RealBottChern.ofRepresentative (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
      congrArg _ physicalProjectiveHyperplane_firstChernClass
    _ = _ := rfl

end SGPT.Toric.F1IntersectionDraft

#print axioms SGPT.Toric.F1IntersectionDraft.physicalOriginalHyperplane_firstChernClass_fs

end
/- END PhysicalOriginalHyperplaneChernDraft -/
end F1CanonicalFragment002


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"
