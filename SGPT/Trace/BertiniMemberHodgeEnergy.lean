import SGPT.Trace.NativeCanonicalPhysicalHodgeIntegral
import SGPT.Trace.BertiniGlobalPhysicalResidueDensity

/-! Actual original member/global-adjunction-image intrinsic physical Hodge energy. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

def nativeBertiniMemberHodgeEnergy
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber → ℝ≥0∞ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  letI : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  letI : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  exact fun S => nativePhysicalHodgeEnergy
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
    S (fun y => multiplierWeight 1 (φ y.val))

theorem nativeBertiniMemberHodgeEnergy_eq_partition
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal) :
    let := nativeBertiniMemberChartedSpace p i ζ hsm
    let := nativeBertiniMemberComplex p i ζ hsm
    let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
    let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
    ∀ (S : HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber)
      (P : NativeCanonicalChartPartition d (member p (affinePoint i ζ))),
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S =
        nativeCanonicalPartitionEnergy
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
          S (fun y => multiplierWeight 1 (φ y.val)) P := by
  dsimp only
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  intro S P
  exact nativePhysicalHodgeEnergy_eq_partition
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
    S (fun y => multiplierWeight 1 (φ y.val)) P

def nativeBertiniAdjunctionHodgeEnergy
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal)
    (S : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber) : ℝ≥0∞ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  exact nativeBertiniMemberHodgeEnergy p i ζ hsm L φ
    (nativeBertiniPhysicalAdjunctionSection p i ζ hsm L S)

theorem nativeBertiniAdjunctionHodgeEnergy_congr_on_member
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal)
    (S T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber)
    (hST : ∀ y : member p (affinePoint i ζ), S y.val = T y.val) :
    nativeBertiniAdjunctionHodgeEnergy p i ζ hsm L φ S =
      nativeBertiniAdjunctionHodgeEnergy p i ζ hsm L φ T := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  have h : nativeBertiniPhysicalAdjunctionSection p i ζ hsm L S =
      nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T := by
    ext y
    rw [nativeBertiniPhysicalAdjunctionSection_apply,
      nativeBertiniPhysicalAdjunctionSection_apply, hST y]
  exact congrArg (nativeBertiniMemberHodgeEnergy p i ζ hsm L φ) h

end SGPT.Trace.Bertini
