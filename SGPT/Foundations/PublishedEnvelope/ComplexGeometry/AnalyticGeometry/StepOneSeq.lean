import SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ExtSeqTransport
import SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.MaxOrderValue
import SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOnePhase

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Step 1 (maximal-order) value for a lower invariant with per-sequence local finiteness

The maximal-order value and its properties depend on the lower invariant
through properties (1)--(7) and (4'), rather than its local-finiteness field.
This permits the kernel-checked transport from the uniform structure
`ResolutionInvariantExt.ResolutionInvariant` to the per-sequence structure
`ResolutionInvariantSeq.ResolutionInvariant`.

**The Step 1 construction for the per-sequence structure.**  The command `transport_ext_to_seq_module` (`ExtSeqTransport`) adds, for every
declaration of the modules listed below that depends on `ResolutionInvariantExt.ResolutionInvariant`, a kernel-checked copy in
the namespace `SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.Seq` (e.g. `Seq.StepOneValueMasked.stepOneInvM`,
`Seq.StepOneBridge.admissible_field`, `Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM`), stated for
`R : ResolutionInvariantSeq.ResolutionInvariant`, with `R.f` replaced by `R.isInvValue.f` for the fields (1)--(7), (4').  That the
command succeeds shows that none of these proofs uses property (8) of the lower invariant.

## Main results (stated here as ordinary theorems)

* **`isMaxOrderValue_stepOneInvM`**: for `R : ResolutionInvariantSeq.ResolutionInvariant n (k - 1) Λ` and `0 < n`, the masked
  Step 1 value `Seq.StepOneValueMasked.stepOneInvM R` is a value function for the marked ideals of maximal order in dimension
  `≤ k` (`MaxOrderValue.IsMaxOrderValue`);
* `stepOneInvM_ofExt`: for a uniform invariant, the value of `ofExt R` is definitionally the value of `R`, through `ResolutionInvariantSeq.ResolutionInvariant.ofExt`;
* `stepDrop_stepOneInvM`, `isAdmissibleCentre_maxLocus_stepOneInvM`, `exists_isGeoResolution_stepOneInvM`: the drop along
  canonical segments, the admissibility of the maximum locus, and the resolution of a marked ideal of maximal order for
  well-founded `Λ` (`StepOneWellFounded`), for the per-sequence structure.

This module does not import, even transitively,
`AnalyticGeometry.RelativePrincipalization` or `AnalyticGeometry.EmbeddedResolution`.
-/

open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ExtSeqTransport

/-! ### The transport of the Step 1 stack -/

transport_ext_to_seq_module
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.BlowupTowerSplit SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.MaxLocusLocal
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.InvDomainRebase SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.MaximalOrderStepOneB
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactStageRebase SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactMarkedCanonical
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactRepresentative SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactStageKept
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactEmptyPrefix SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.ContactLowerValue
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.MemberRestrictTowerIso SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.CompanionRebase
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.NonmonomialOrderRegime
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneValue SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneNearby
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneValueMasked SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneCompare
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneTangentChange SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneCanonicalTail
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneUSC SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneAdmissibleTop
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneSpecialDrop SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneAdmissible
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneEmptyPrefix SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneRepresentative
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneRestrictOpen SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneTowerIso
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneBridge SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOneWellFounded
  SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.StepOnePhase SGPT.Foundations.PublishedEnvelope.ComplexGeometry.AnalyticGeometry.MaxOrderValue

transport_ext_to_seq
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isAdmissibleCentre_maxLocus
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isGeoTestTower_of_isCanonical
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isInvDomain_of_isCanonical
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isCanonical_restrict
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isCanonical_of_isTowerIso
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantExt.isCanonical_append_iff

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.StepOneSeq

open Pluripotential Pluripotential.HolomorphicIdealSheaves Pluripotential.BlowupSequences
open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.MarkedIdeals SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.MarkedIdeals.MarkedIdeal
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.BlowupTowers SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.BlowupTowerTransforms
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.MaxOrderValue SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantSeq
  SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.StepOneWellFounded
open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.ResolutionDriver (maxLocus IsCanonicalSegment)
open SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The new Step 1 value extends the old one**: for an invariant `R` of the old structure, the masked Step 1 value of
`ofExt R` is that of `R`. -/
theorem stepOneInvM_ofExt (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    Seq.StepOneValueMasked.stepOneInvM (ResolutionInvariant.ofExt R) 𝔍 T y = StepOneValueMasked.stepOneInvM R 𝔍 T y :=
  rfl

/-- **The masked Step 1 value of a lower invariant of the new structure is a value function for the marked ideals of
maximal order** (step one seq; `0 < n`): properties (1)--(7), (4') along its canonical segments, for every marked ideal
of the domain in dimension `≤ k` of maximal order along its submanifold. -/
theorem isMaxOrderValue_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (hn : 0 < n) :
    IsMaxOrderValue n k (fun {X} 𝔍 {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R 𝔍 (Y := Y) T y) :=
  Seq.MaxOrderValue.isMaxOrderValue_stepOneInvM R hn

/-- **The value drops along canonical segments** (the hypothesis of the well-founded driver), for the new structure. -/
theorem stepDrop_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    StepDrop 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) :=
  Seq.StepOneWellFounded.stepDrop_stepOneInvM R 𝔍 h hmax hn

/-- **The maximum locus is an admissible centre** along a canonical segment, for the new structure. -/
theorem isAdmissibleCentre_maxLocus_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) {𝔍 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) T) :
    (geoTransformAlong 𝔍 T).IsAdmissibleCentre
      (maxLocus (Seq.StepOneValueMasked.stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) :=
  Seq.StepOneWellFounded.isAdmissibleCentre_maxLocus_stepOneInvM R 𝔍 h hmax hn T hcan

/-- **Well-founded lower values resolve the marked ideals of maximal order** over a compact base by a canonical segment of the
Step 1 value, for the new structure. -/
theorem exists_isGeoResolution_stepOneInvM [CompactSpace X] [WellFoundedLT Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
    {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔍 (Seq.StepOneValueMasked.stepOneInvM R 𝔍) T ∧ IsGeoResolution 𝔍 T :=
  Seq.StepOneWellFounded.exists_isGeoResolution_stepOneInvM R 𝔍 h hmax hn

end

end SGPT.Foundations.PublishedAnalysis.AnalyticGeometry.StepOneSeq
