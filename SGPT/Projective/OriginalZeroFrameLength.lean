import SGPT.Projective.OriginalTensorZeroSupport

/-! ENTIRE actual original zero stalk/full quotient length in ANY original
frame, and original unit/zero quotient length off ENTIRE original zero support.
Blueprint: original-zero-frame-length.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
variable {X : Scheme.{0}} {L : X.Modules} {U : X.Opens}

/-- Add the SAME actual original local frame to the SAME genuine original covering atlas. -/
def originalAtlasWithFrame (a : LineBundleAtlas L) (e : LocalBundleFrame L U) : LineBundleAtlas L where
  I := Option a.I
  opens := fun i => match i with | none => U | some j => a.opens j
  covers x := by
    obtain ⟨i, hi⟩ := a.covers x
    exact ⟨some i, hi⟩
  frame := fun i => match i with | none => e | some j => a.frame j

/-- ACTUAL original dual-evaluation zero ideal data are literally atlas independent. -/
theorem originalAtlasWithFrame_zeroIdeal (a : LineBundleAtlas L) (e : LocalBundleFrame L U)
    (s : Γ(L, ⊤)) : sectionZeroIdealSheaf (originalAtlasWithFrame a e) s = sectionZeroIdealSheaf a s := rfl

/-- FULL SAME original zero-stalk length in ANY actual original frame containing the original image point. -/
theorem originalZeroStalk_fullLength_anyFrame (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (z : sectionZeroSubscheme a s) (e : LocalBundleFrame L U) (hz : sectionZeroι a s z ∈ U) :
    Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
      ((sectionZeroSubscheme a s).presheaf.stalk z) =
      Module.length (X.presheaf.stalk (sectionZeroι a s z))
        ((X.presheaf.stalk (sectionZeroι a s z)) ⧸
          Ideal.span {originalSectionFrameGerm e s (sectionZeroι a s z) hz}) := by
  exact sectionZeroStalk_length_eq_principalLength (originalAtlasWithFrame a e) s z none hz

/-- Actual original arbitrary-frame germ is a TRUE original local unit off ENTIRE original zero support. -/
theorem originalFrameGerm_isUnit_off_zeroSupport (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (e : LocalBundleFrame L U) (x : X) (hx : x ∈ U)
    (hout : x ∉ (sectionZeroIdealSheaf a s).support) : IsUnit (originalSectionFrameGerm e s x hx) := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  let j : V ⟶ U := homOfLE hVU
  let c : Γ(X, V) := e.coefficients j (L.val.map V.leTop.op s)
  have hbasic : x ∈ X.basicOpen c := by
    by_contra h
    exact hout ((originalZero_support_iff_not_basicOpen a s ⟨V, hV⟩ e j x hxV).mpr h)
  have hunit := (X.mem_basicOpen c x hxV).mp hbasic
  have hc : c = X.presheaf.map j.op (e.coefficients (𝟙 U) (L.val.map U.leTop.op s)) := by
    have h := e.coefficients_restrict (𝟙 U) j (L.val.map U.leTop.op s)
    have hr : L.val.map j.op (L.val.map U.leTop.op s) = L.val.map V.leTop.op s := by
      rw [← L.val.map_comp_apply]
      rfl
    rw [hr] at h
    exact h
  have hg : X.presheaf.germ V x hxV c = originalSectionFrameGerm e s x hx := by
    rw [hc]
    exact X.presheaf.germ_res_apply j x hxV _
  exact hg ▸ hunit

/-- SAME FULL original principal length is zero off ENTIRE actual original zero support. -/
theorem originalFramePrincipalLength_zero_off_zeroSupport (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (e : LocalBundleFrame L U) (x : X) (hx : x ∈ U)
    (hout : x ∉ (sectionZeroIdealSheaf a s).support) :
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      Ideal.span {originalSectionFrameGerm e s x hx}) = 0 :=
  Ring.ord_of_isUnit (originalFrameGerm_isUnit_off_zeroSupport a s e x hx hout)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
