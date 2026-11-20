import SGPT.Projective.AlgebraicSectionZeroStalk
import SGPT.Foundations.Schemes.LineBundleSectionRing

/-! Independent ORIGINAL actual tensor-section coefficient product and FULL
principal quotient length additivity, via true original quotient exact sequence.
Blueprint: original-tensor-section-length.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped nonZeroDivisors
variable {X : Scheme.{0}} {L N : X.Modules} {U : X.Opens}

/-- SAME actual original arbitrary frame's original section coefficient in original scheme stalk. -/
def originalSectionFrameGerm (e : LocalBundleFrame L U) (s : Γ(L, ⊤))
    (x : X) (hx : x ∈ U) : X.presheaf.stalk x :=
  X.presheaf.germ U x hx (e.coefficients (𝟙 U) (L.val.map U.leTop.op s))

/-- ACTUAL original sheafified tensor section gives product of SAME original frame germs. -/
theorem originalTensorSectionFrameGerm_mul (e : LocalBundleFrame L U) (d : LocalBundleFrame N U)
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (x : X) (hx : x ∈ U) :
    originalSectionFrameGerm (e.tensor d) (tensorSection L N ⊤ s t) x hx =
      originalSectionFrameGerm e s x hx * originalSectionFrameGerm d t x hx := by
  unfold originalSectionFrameGerm
  rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients, map_mul]

/-- Actual original integral restriction and actual original germ injection, in ANY genuine frame. -/
theorem originalSectionFrameGerm_ne_zero [IsIntegral X] (a : LineBundleAtlas L)
    (e : LocalBundleFrame L U) (s : Γ(L, ⊤)) (hs : s ≠ 0) (x : X) (hx : x ∈ U) :
    originalSectionFrameGerm e s x hx ≠ 0 := by
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  have hr := sectionCoefficient_ne_zero a s hs e (𝟙 U)
  intro hg
  apply hr
  apply germ_injective_of_isIntegral X x hx
  change X.presheaf.germ U x hx (e.coefficients (𝟙 U) (L.val.map U.leTop.op s)) =
    X.presheaf.germ U x hx 0
  exact hg.trans (map_zero _).symm

/-- FULL original local principal lengths add for SAME actual tensor section; independent algebraic proof. -/
theorem originalTensorSection_principalLength_add [IsIntegral X]
    (b : LineBundleAtlas N) (e : LocalBundleFrame L U) (d : LocalBundleFrame N U)
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (ht : t ≠ 0) (x : X) (hx : x ∈ U) :
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      Ideal.span {originalSectionFrameGerm (e.tensor d) (tensorSection L N ⊤ s t) x hx}) =
      Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
        Ideal.span {originalSectionFrameGerm e s x hx}) +
      Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
        Ideal.span {originalSectionFrameGerm d t x hx}) := by
  rw [originalTensorSectionFrameGerm_mul]
  have hnd : originalSectionFrameGerm d t x hx ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (originalSectionFrameGerm_ne_zero b d t ht x hx)
  exact Ring.ord_mul (X.presheaf.stalk x) hnd

end SGPT.Projective.NumEq.AlgebraicCurveDegree
