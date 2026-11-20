import SGPT.Projective.OriginalPullbackFrameTransition
import SGPT.Foundations.Schemes.TensorSectionZeroIdeals
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison

/-! Genuine actual original pullback/tensor/power isomorphisms, descended
from SAME actual original frames and proved original scalar transition square.
Blueprint: original-line-pullback-tensor.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private theorem originalMatching_on_all_source_opens {I : Type} {P Q : X.Modules}
    (U : I → Y.Opens)
    (p : ∀ i, LocalBundleFrame P (f ⁻¹ᵁ U i)) (q : ∀ i, LocalBundleFrame Q (f ⁻¹ᵁ U i))
    (hi : ∀ i j (V : Y.Opens) (h : V ⟶ U i) (k : V ⟶ U j),
      localBundleFrameTransition (p i) (p j) ((Opens.map f.base).map h) ((Opens.map f.base).map k) =
        localBundleFrameTransition (q i) (q j) ((Opens.map f.base).map h) ((Opens.map f.base).map k))
    (i j : I) (W : X.Opens) (h : W ⟶ f ⁻¹ᵁ U i) (k : W ⟶ f ⁻¹ᵁ U j) :
    localBundleFrameTransition (p i) (p j) h k = localBundleFrameTransition (q i) (q j) h k := by
  let V := U i ⊓ U j
  let a : V ⟶ U i := Opens.infLELeft _ _
  let b : V ⟶ U j := Opens.infLERight _ _
  let c : W ⟶ f ⁻¹ᵁ V := homOfLE (show W ≤ f ⁻¹ᵁ V from le_inf h.le k.le)
  have he := hi i j V a b
  apply Units.ext
  have hr := congrArg (fun z : (X.sheaf.obj.obj (.op (f ⁻¹ᵁ V)))ˣ => X.sheaf.obj.map c.op
    (z : X.sheaf.obj.obj (.op (f ⁻¹ᵁ V)))) he
  rw [← localBundleFrameTransition_restrict, ← localBundleFrameTransition_restrict] at hr
  exact hr

private theorem originalPullbackPower_matching_inverse {L : Y.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (i j : a.I) (V : Y.Opens) (h : V ⟶ a.opens i) (k : V ⟶ a.opens j) :
    localBundleFrameTransition (matePullbackFrame f ((a.frame i).tensorPower m))
      (matePullbackFrame f ((a.frame j).tensorPower m))
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) =
    localBundleFrameTransition ((matePullbackFrame f (a.frame i)).tensorPower m)
      ((matePullbackFrame f (a.frame j)).tensorPower m)
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) := by
  apply Units.ext
  rw [matePullbackFrame_transition, localBundleFrameTransition_tensorPower,
    Units.val_pow_eq_pow_val, map_pow, localBundleFrameTransition_tensorPower,
    Units.val_pow_eq_pow_val, matePullbackFrame_transition]

/-- ANY actual original line/power commutes with the actual whole sheaf
pullback through a genuine coefficient-preserving original frame descent.
No positivity, generation, tensor compatibility or comparison premise. -/
def originalLinePullbackPowerIso {L : Y.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (bundleTensorPower L m) ≅
      bundleTensorPower ((Scheme.Modules.pullback f).obj L) m :=
  nativeMatchingBundleFrameIso _ _ (fun i => f ⁻¹ᵁ a.opens i) (fun x => a.covers (f x))
    (fun i => matePullbackFrame f ((a.frame i).tensorPower m))
    (fun i => (matePullbackFrame f (a.frame i)).tensorPower m)
    (originalMatching_on_all_source_opens f a.opens _ _ (originalPullbackPower_matching_inverse f a m))

/-- Exact SAME original pulled-power/tensor-power coefficient reader on
EVERY source subopen of the genuine original inverse-image atlas. -/
theorem originalLinePullbackPowerIso_coefficients {L : Y.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (i : a.I) {W : X.Opens} (h : W ⟶ f ⁻¹ᵁ a.opens i)
    (s : Γ((Scheme.Modules.pullback f).obj (bundleTensorPower L m), W)) :
    ((matePullbackFrame f (a.frame i)).tensorPower m).coefficients h
      ((originalLinePullbackPowerIso f a m).hom.val.app (.op W) s) =
    (matePullbackFrame f ((a.frame i).tensorPower m)).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients _ _ (fun j => f ⁻¹ᵁ a.opens j)
    (fun x => a.covers (f x)) _ _
    (originalMatching_on_all_source_opens f a.opens _ _ (originalPullbackPower_matching_inverse f a m)) i h s

private def originalPairedLeftFrame {L N : Y.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    (i : a.I × b.I) : LocalBundleFrame L ((a.tensor b).opens i) :=
  bundleHomRestrictionIso L (SheafOfModules.unit Y.ringCatSheaf)
    (Opens.infLELeft (a.opens i.1) (b.opens i.2)) (a.frame i.1)

private def originalPairedRightFrame {L N : Y.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    (i : a.I × b.I) : LocalBundleFrame N ((a.tensor b).opens i) :=
  bundleHomRestrictionIso N (SheafOfModules.unit Y.ringCatSheaf)
    (Opens.infLERight (a.opens i.1) (b.opens i.2)) (b.frame i.2)

private theorem originalPullbackTensor_matching_inverse {L N : Y.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (i j : a.I × b.I) (V : Y.Opens)
    (h : V ⟶ (a.tensor b).opens i) (k : V ⟶ (a.tensor b).opens j) :
    localBundleFrameTransition (matePullbackFrame f ((a.tensor b).frame i))
      (matePullbackFrame f ((a.tensor b).frame j))
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) =
    localBundleFrameTransition
      ((matePullbackFrame f (originalPairedLeftFrame a b i)).tensor
        (matePullbackFrame f (originalPairedRightFrame a b i)))
      ((matePullbackFrame f (originalPairedLeftFrame a b j)).tensor
        (matePullbackFrame f (originalPairedRightFrame a b j)))
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) := by
  apply Units.ext
  rw [matePullbackFrame_transition]
  change f.app V (localBundleFrameTransition
    ((originalPairedLeftFrame a b i).tensor (originalPairedRightFrame a b i))
    ((originalPairedLeftFrame a b j).tensor (originalPairedRightFrame a b j)) h k).val = _
  rw [localBundleFrameTransition_tensor, Units.val_mul, map_mul,
    localBundleFrameTransition_tensor, Units.val_mul,
    matePullbackFrame_transition, matePullbackFrame_transition]

/-- Genuine actual pullback of ANY two DISTINCT original line sheaves is
isomorphic to the tensor of their SAME actual pulled sheaves. Original
paired frames and true original ring transition square manufacture it. -/
def originalLinePullbackTensorIso {L N : Y.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas N) :
    (Scheme.Modules.pullback f).obj (bundleTensor L N) ≅
      bundleTensor ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj N) :=
  nativeMatchingBundleFrameIso _ _ (fun i => f ⁻¹ᵁ (a.tensor b).opens i)
    (fun x => (a.tensor b).covers (f x))
    (fun i => matePullbackFrame f ((a.tensor b).frame i))
    (fun i => (matePullbackFrame f (originalPairedLeftFrame a b i)).tensor
      (matePullbackFrame f (originalPairedRightFrame a b i)))
    (originalMatching_on_all_source_opens f (a.tensor b).opens _ _
      (originalPullbackTensor_matching_inverse f a b))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
