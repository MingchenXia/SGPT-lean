import SGPT.Projective.OkounkovOriginalIsoMultiplier

/-! Actual original rational perturbation tensor regrouping sheaves, by genuine original frame descent.
Blueprint: okounkov-original-perturb-isomorphisms.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbIsomorphisms
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov.ValGen2
variable {X : Scheme.{0}} {L A : X.Modules}

/-- The actual extra ample power regroups in the SAME original sheaves, all exponents including0. -/
def perturbAddIso (a : LineBundleAtlas L) (b : LineBundleAtlas A) (q p r : ℕ) :
    bundleTensor (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) (bundleTensorPower A r) ≅
      bundleTensor (bundleTensorPower L q) (bundleTensorPower A (p+r)) :=
  nativeMatchingBundleFrameIso _ _ (pairwiseTensorAtlas a b).opens (pairwiseTensorAtlas a b).covers
    (fun ij => (((leftRestrictedFrame a b ij).tensorPower q).tensor
      ((rightRestrictedFrame a b ij).tensorPower p)).tensor ((rightRestrictedFrame a b ij).tensorPower r))
    (fun ij => ((leftRestrictedFrame a b ij).tensorPower q).tensor
      ((rightRestrictedFrame a b ij).tensorPower (p+r)))
    (by
      intro i j W h k
      simp only [localBundleFrameTransition_tensor,localBundleFrameTransition_tensorPower,pow_add,mul_assoc])

/-- The literal original zero ample power is genuinely removed, on the SAME original sheaf. -/
def perturbZeroIso (a : LineBundleAtlas L) (b : LineBundleAtlas A) (q : ℕ) :
    bundleTensor (bundleTensorPower L q) (bundleTensorPower A 0) ≅ bundleTensorPower L q :=
  nativeMatchingBundleFrameIso _ _ (pairwiseTensorAtlas a b).opens (pairwiseTensorAtlas a b).covers
    (fun ij => ((leftRestrictedFrame a b ij).tensorPower q).tensor ((rightRestrictedFrame a b ij).tensorPower 0))
    (fun ij => (leftRestrictedFrame a b ij).tensorPower q)
    (by
      intro i j W h k
      simp only [localBundleFrameTransition_tensor,localBundleFrameTransition_tensorPower,pow_zero,mul_one])

/-- Actual original rational presentations regather after any true positive power, also valid in degree0. -/
def perturbPowerIso (a : LineBundleAtlas L) (b : LineBundleAtlas A) (q p r : ℕ) :
    bundleTensorPower (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) r ≅
      bundleTensor (bundleTensorPower L (q*r)) (bundleTensorPower A (p*r)) :=
  nativeMatchingBundleFrameIso _ _ (pairwiseTensorAtlas a b).opens (pairwiseTensorAtlas a b).covers
    (fun ij => (((leftRestrictedFrame a b ij).tensorPower q).tensor
      ((rightRestrictedFrame a b ij).tensorPower p)).tensorPower r)
    (fun ij => ((leftRestrictedFrame a b ij).tensorPower (q*r)).tensor
      ((rightRestrictedFrame a b ij).tensorPower (p*r)))
    (by
      intro i j W h k
      simp only [localBundleFrameTransition_tensor,localBundleFrameTransition_tensorPower,mul_pow,pow_mul])
end SGPT.Okounkov.OriginalPerturbIsomorphisms
