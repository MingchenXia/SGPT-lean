import SGPT.TestCurve.TCActualCentralPoints
import SGPT.Projective.OriginalLinePullbackTensor

/-! Original geometric coefficients on the genuine native central line,
with actual pulled-frame transitions and the literal central action square. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- Actual adjunction-compatible pulled atlas of the SAME original central line. -/
@[reducible] def centralActionAtlas : LineBundleAtlas (centralFiberLine T) where
  I := T.atlas.I
  opens i := centralFiberInclusion T ⁻¹ᵁ T.atlas.opens i
  covers x := T.atlas.covers (centralFiberInclusion T x)
  frame i := matePullbackFrame (centralFiberInclusion T) (T.atlas.frame i)

/-- Every central transition is the SAME original structural pullback, with no comparison input. -/
theorem centralActionAtlas_transition (i j : T.atlas.I) :
    atlasTransition (centralActionAtlas T) i j =
      (centralFiberInclusion T).app (T.atlas.opens i ⊓ T.atlas.opens j)
        (atlasTransition T.atlas i j) := by
  exact matePullbackFrame_transition (centralFiberInclusion T) (T.atlas.frame i) (T.atlas.frame j)
    (homOfLE inf_le_left) (homOfLE inf_le_right)

variable (Λ : GeomLinearization T)

private def originalAtlasPhiAt (c : ℂˣ) (i j : T.atlas.I) :
    Γ(T.space, pullOpen T.atlas T.atlas (Λ.action.actAt c) i j) :=
  Λ.phiAt c (.inl i) (.inl j)

private theorem originalAtlasPhiAt_isCechHom (c : ℂˣ) :
    IsCechHom T.atlas T.atlas (Λ.action.actAt c) (originalAtlasPhiAt T Λ c) := by
  intro i i' j j'
  exact Λ.isCechHom_phiAt c (.inl i) (.inl i') (.inl j) (.inl j')

private theorem centralPullOpen_le (c : ℂˣ) (i j : T.atlas.I) :
    pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
      centralFiberInclusion T ⁻¹ᵁ pullOpen T.atlas T.atlas (Λ.action.actAt c) i j := by
  rintro x ⟨hx,hy⟩
  refine ⟨?_,hy⟩
  change (centralFiberInclusion T ≫ Λ.action.actAt c) x ∈ T.atlas.opens i
  rw [← centralActAt_inclusion]
  exact hx

/-- The original point linearization coefficient on the genuine intrinsic central frame patch. -/
def centralPhiAt (c : ℂˣ) (i j : T.atlas.I) :
    Γ(centralFiberScheme T,
      pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j) :=
  (centralFiberInclusion T).appLE _ _ (centralPullOpen_le T Λ c i j)
    (Λ.phiAt c (.inl i) (.inl j))

/-- The actual native central-line Cech morphism is manufactured from original geometric data. -/
theorem centralPhiAt_isCechHom (c : ℂˣ) :
    IsCechHom (centralActionAtlas T) (centralActionAtlas T)
      (centralActAt T Λ.action c) (centralPhiAt T Λ c) := by
  change ∀ (i i' j j' : T.atlas.I), _
  intro i i' j j'
  have hle : pullOverlap (centralActionAtlas T) (centralActionAtlas T)
      (centralActAt T Λ.action c) i i' j j' ≤
      centralFiberInclusion T ⁻¹ᵁ pullOverlap T.atlas T.atlas (Λ.action.actAt c) i i' j j' := by
    rintro x ⟨hx,hy⟩
    refine ⟨?_,hy⟩
    change (centralFiberInclusion T ≫ Λ.action.actAt c) x ∈ T.atlas.opens i ⊓ T.atlas.opens i'
    rw [← centralActAt_inclusion]
    exact hx
  have hh := congrArg ((centralFiberInclusion T).appLE _ _ hle)
    (originalAtlasPhiAt_isCechHom T Λ c i i' j j')
  rw [map_mul,map_mul,appLE_appLE,appLE_of_res,appLE_of_res,appLE_of_res] at hh
  have htarget : pullOverlap (centralActionAtlas T) (centralActionAtlas T)
      (centralActAt T Λ.action c) i i' j j' ≤
      (centralActAt T Λ.action c ≫ centralFiberInclusion T) ⁻¹ᵁ
        (T.atlas.opens i ⊓ T.atlas.opens i') := by
    rintro x ⟨hx,_hy⟩
    exact hx
  rw [appLE_congr_hom (centralActAt_inclusion T Λ.action c).symm _ _ _ htarget] at hh
  change _ * _ = _ * _
  rw [centralActionAtlas_transition,centralActionAtlas_transition]
  rw [Scheme.Hom.app_eq_appLE,Scheme.Hom.app_eq_appLE]
  dsimp only [centralPhiAt,centralActionAtlas,matePullbackAtlas,pullOpen,pullOverlap]
  simp only [Scheme.Hom.preimage_inf]
  rw [appLE_appLE]
  rw [appLE_res,appLE_res,appLE_res]
  simpa only [originalAtlasPhiAt,centralActionAtlas,matePullbackAtlas,pullOpen,pullOverlap,
    Scheme.Hom.preimage_inf] using hh

end SGPT.TestCurve.CentralFiber
