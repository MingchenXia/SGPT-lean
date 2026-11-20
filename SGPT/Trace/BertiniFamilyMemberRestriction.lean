import SGPT.Trace.NativeTensorPullbackSectionRestriction
import SGPT.Trace.BertiniMemberPullbackAdjunction
import SGPT.Trace.BertiniFamilyVerticalTangent
import SGPT.Trace.BertiniMemberHodgeEnergy

/-! Actual arbitrary family section restriction into genuine original member
canonical physical sections. The full incidence retains its base locus. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyNativeMemberSourceSection
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →
    HolomorphicSections (n := d) (nativeHolomorphicPullbackBundle
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L)
      (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))).Fiber := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  exact NativeTensorRestriction.tensorPullbackSectionRestriction
    (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p))
    L (familyNativeXMap p i a v U hsm) (familyMemberLift p i a v U hsm t) S

theorem familyNativeMemberSourceSection_apply
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber) (y : member p (affinePoint i (a - t.val 0 • v))),
      familyNativeMemberSourceSection p i a v U hsm L t S y =
        S ⟨(t,y.val),y.property⟩ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S y
  rfl

def familyNativeMemberAdjunctionSection
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →
    HolomorphicSections (n := d) (tensor
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i (a - t.val 0 • v))))
      (nativeHolomorphicPullbackBundle L
        (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))).Fiber := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  exact nativeBertiniMemberPullbackAdjunctionSection p i (a - t.val 0 • v) (hsm t) L
    (familyNativeMemberSourceSection p i a v U hsm L t S)

theorem familyNativeMemberAdjunctionSection_apply
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber) (y : member p (affinePoint i (a - t.val 0 • v))),
      familyNativeMemberAdjunctionSection p i a v U hsm L t S y =
        nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - t.val 0 • v) (hsm t) L y
          (S ⟨(t,y.val),y.property⟩) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S y
  rfl

theorem familyNativeMemberAdjunctionSection_congr
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (S T : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber),
      (∀ y : member p (affinePoint i (a - t.val 0 • v)),
        S ⟨(t,y.val),y.property⟩ = T ⟨(t,y.val),y.property⟩) →
      familyNativeMemberAdjunctionSection p i a v U hsm L t S =
        familyNativeMemberAdjunctionSection p i a v U hsm L t T := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S T hST
  ext y
  rw [familyNativeMemberAdjunctionSection_apply, familyNativeMemberAdjunctionSection_apply, hST y]

def familyNativeMemberHodgeEnergy
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  exact nativeBertiniMemberHodgeEnergy p i (a - t.val 0 • v) (hsm t) L φ
    (familyNativeMemberAdjunctionSection p i a v U hsm L t S)

theorem familyNativeMemberHodgeEnergy_congr
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (S T : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber),
      (∀ y : member p (affinePoint i (a - t.val 0 • v)),
        S ⟨(t,y.val),y.property⟩ = T ⟨(t,y.val),y.property⟩) →
      familyNativeMemberHodgeEnergy p i a v U hsm L φ t S =
        familyNativeMemberHodgeEnergy p i a v U hsm L φ t T := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S T hST
  exact congrArg (nativeBertiniMemberHodgeEnergy p i (a - t.val 0 • v) (hsm t) L φ)
    (familyNativeMemberAdjunctionSection_congr p i a v U hsm L t S T hST)

end SGPT.Trace.BertiniFamilyCanonical
