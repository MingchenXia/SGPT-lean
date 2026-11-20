import SGPT.Projective.OriginalLinePullbackTensor

/-! Actual original distinct-line tensor arithmetic, by genuine local frame
descent, for actual mixed Euler operations. Blueprint: original-line-tensor-arithmetic.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite

variable {X : Scheme.{0}}

/-- ONLY the actual original sheafified tensor and its genuine paired atlas. -/
def originalLineTensor (A B : IntrinsicLineBundle X) : IntrinsicLineBundle X where
  sheaf := bundleTensor A.sheaf B.sheaf
  atlas := A.atlas.tensor B.atlas

/-- Genuine actual original associator for THREE independently specified
original lines. No same-line power, global frame or compatibility premise. -/
def originalLineTensorAssociatorIso {L N P : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (c : LineBundleAtlas P) :
    bundleTensor (bundleTensor L N) P ≅ bundleTensor L (bundleTensor N P) := by
  let I := a.I × (b.I × c.I)
  let U (i : I) := a.opens i.1 ⊓ (b.opens i.2.1 ⊓ c.opens i.2.2)
  let ea (i : I) : LocalBundleFrame L (U i) :=
    bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
      (homOfLE inf_le_left) (a.frame i.1)
  let eb (i : I) : LocalBundleFrame N (U i) :=
    bundleHomRestrictionIso N (SheafOfModules.unit X.ringCatSheaf)
      (homOfLE (inf_le_right.trans inf_le_left)) (b.frame i.2.1)
  let ec (i : I) : LocalBundleFrame P (U i) :=
    bundleHomRestrictionIso P (SheafOfModules.unit X.ringCatSheaf)
      (homOfLE (inf_le_right.trans inf_le_right)) (c.frame i.2.2)
  have hU : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨j, hj⟩ := b.covers x
    obtain ⟨k, hk⟩ := c.covers x
    exact ⟨⟨i, j, k⟩, hi, hj, hk⟩
  apply nativeMatchingBundleFrameIso _ _ U hU
    (fun i => ((ea i).tensor (eb i)).tensor (ec i))
    (fun i => (ea i).tensor ((eb i).tensor (ec i)))
  intro i j W h k
  simp only [localBundleFrameTransition_tensor, mul_assoc]

/-- Genuine actual original commutor for TWO independently specified
original lines, with actual paired chart frames and true original transitions. -/
def originalLineTensorCommutorIso {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) : bundleTensor L N ≅ bundleTensor N L := by
  let I := a.I × b.I
  let U (i : I) := a.opens i.1 ⊓ b.opens i.2
  let ea (i : I) : LocalBundleFrame L (U i) :=
    bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
      (Opens.infLELeft _ _) (a.frame i.1)
  let eb (i : I) : LocalBundleFrame N (U i) :=
    bundleHomRestrictionIso N (SheafOfModules.unit X.ringCatSheaf)
      (Opens.infLERight _ _) (b.frame i.2)
  have hU : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨j, hj⟩ := b.covers x
    exact ⟨⟨i, j⟩, hi, hj⟩
  apply nativeMatchingBundleFrameIso _ _ U hU
    (fun i => (ea i).tensor (eb i)) (fun i => (eb i).tensor (ea i))
  intro i j W h k
  rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensor]
  exact mul_comm _ _

/-- Swap the last TWO distinct original lines in an actual left-associated
testing tensor, retaining the actual original first line and all sheaf maps. -/
def originalLineTensorRightSwapIso {B L N : X.Modules}
    (b : LineBundleAtlas B) (a : LineBundleAtlas L) (c : LineBundleAtlas N) :
    bundleTensor (bundleTensor B L) N ≅ bundleTensor (bundleTensor B N) L :=
  originalLineTensorAssociatorIso b a c ≪≫
    bundleTensorIso (Iso.refl B) (originalLineTensorCommutorIso a c) ≪≫
      (originalLineTensorAssociatorIso b c a).symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
