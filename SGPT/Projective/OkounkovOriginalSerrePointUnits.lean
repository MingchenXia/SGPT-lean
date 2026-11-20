import SGPT.Projective.OriginalGeneratedPointUnit
import SGPT.Projective.OkounkovOriginalUnitPowers

/-! Genuine ordinary original Serre point-unit sections, ONE threshold before EVERY high degree and original scheme point.
Blueprint: okounkov-original-serre-point-units.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalSerrePointUnits
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Projective.NumEq.AlgebraicCurveDegree
variable {X : Scheme.{0}}

/-- An actual original tensor swap, descended from the SAME original atlas frames and scalar commutativity. -/
def tensorSwapIso {L N : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas N) :
    bundleTensor L N ≅ bundleTensor N L :=
  nativeMatchingBundleFrameIso _ _ (pairwiseTensorAtlas a b).opens (pairwiseTensorAtlas a b).covers
    (fun ij => (leftRestrictedFrame a b ij).tensor (rightRestrictedFrame a b ij))
    (fun ij => (rightRestrictedFrame a b ij).tensor (leftRestrictedFrame a b ij))
    (by
      intro i j W h k
      rw [localBundleFrameTransition_tensor,localBundleFrameTransition_tensor,mul_comm])

/-- ONE genuine original Serre threshold BEFORE ALL high degrees and points, no geometric or section certificate. -/
theorem exists_original_ampleTwist_point_units
    (f : X ⟶ Spec (.of ℂ)) {A R : X.Modules} (aA : LineBundleAtlas A)
    (P : SGPT.LineBundle.AmplePolarization f A) (aR : LineBundleAtlas R) :
    ∃ d : ℕ, 0<d ∧ ∃ B : ℕ, ∀ D : ℕ, B≤D → ∀ c : X,
      ∃ s : Γ(bundleTensor R (bundleTensorPower A (d*D)),⊤),
        ∀ b : LineBundleAtlas (bundleTensor R (bundleTensorPower A (d*D))),
          c∉(sectionZeroIdealSheaf b s).support := by
  obtain ⟨B,hB⟩ := exists_originalProjectiveTwist_generators P.map aR
  refine ⟨P.power,P.power_pos,B,?_⟩
  intro D hD c
  obtain ⟨G,hG⟩ := hB D hD
  let Q := (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf
  let aQ := (nativePolynomialPullbackAtlas ℂ P.ambientDimension P.map).tensorPower D
  let aT := pairwiseTensorAtlas aQ aR
  obtain ⟨t,ht⟩ := exists_originalGeneratedSection_avoids_point aT G c
  let eP : bundleTensorPower A (P.power*D) ≅ bundleTensorPower Q D :=
    nativeLineTensorPowerMulIso aA P.power D ≪≫ nativeLineTensorPowerIso P.iso D
  let e : bundleTensor (bundleTensorPower Q D) R ≅ bundleTensor R (bundleTensorPower A (P.power*D)) :=
    bundleTensorIso eP.symm (Iso.refl R) ≪≫ tensorSwapIso (aA.tensorPower (P.power*D)) aR
  let s := e.hom.val.app (.op ⊤) t
  refine ⟨s,?_⟩
  intro b
  have heq := OriginalUnitPowers.sectionZeroSupport_iso aT b e t
  exact heq.symm ▸ ht
end SGPT.Okounkov.OriginalSerrePointUnits
