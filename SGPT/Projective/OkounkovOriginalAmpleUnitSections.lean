import SGPT.Foundations.Schemes.NativePositiveCoordinateCrossCoefficients
import SGPT.Projective.OriginalTensorZeroSupport
import SGPT.LineBundle.RiemannRochAmple

/-! Actual original ample-power ordinary sections with unit coefficient at EVERY actual original point.
Fresh narrow coordinate source port from ProjectiveGeneratedRegularDivisors.lean:14–52;
same original objects and maps, no Fano/regular-divisor implementation or conclusions imported.
Blueprint: okounkov-original-ample-unit-sections.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalAmpleUnits
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME original pulled coordinate sheaf morphism at scalar ONE, as a true ordinary section. -/
def coordinateSection (K : Type) [Field K] (N : ℕ) {X : Scheme} (g : X ⟶ polynomialProj K N)
    (i : Fin (N+1)) : Γ((Scheme.Modules.pullback g).obj (polynomialProjTwistingLine K N).sheaf,⊤) :=
  (nativePullbackGlobalHom g (homogeneousPolynomialCoordinateGlobalHom (K:=K) i)).val.app
    (.op ⊤) (1:Γ(X,⊤))

/-- Genuine original coordinate section has coefficient EXACTLY ONE in its SAME original coordinate frame. -/
theorem coordinateSection_self_coefficient (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (g : X ⟶ polynomialProj K N) (i : Fin (N+1)) :
    ((nativePolynomialPullbackAtlas K N g).frame i).coefficients (𝟙 _)
      (((Scheme.Modules.pullback g).obj (polynomialProjTwistingLine K N).sheaf).val.map
        ((nativePolynomialPullbackAtlas K N g).opens i).leTop.op (coordinateSection K N g i)) = 1 := by
  let M := (Scheme.Modules.pullback g).obj (polynomialProjTwistingLine K N).sheaf
  let a := nativePolynomialPullbackAtlas K N g
  let U := a.opens i
  let α := nativePullbackGlobalHom g (homogeneousPolynomialCoordinateGlobalHom (K:=K) i)
  have h0 := nativePolynomialPullbackCoordinate_cross_coefficients K N g i i
  rw [polynomialProjCoordinateRatio_self] at h0
  have ha : homogeneousPolynomialBasicOpenAwayEquiv (K:=K) i
      (1:polynomialProjCoordinateRing K N i) = (1:Γ(polynomialProj K N,polynomialProjCoordinateOpen K N i)) := map_one _
  have hb : g.app (polynomialProjCoordinateOpen K N i)
      (1:Γ(polynomialProj K N,polynomialProjCoordinateOpen K N i)) =
      (1:Γ(X,g ⁻¹ᵁ polynomialProjCoordinateOpen K N i)) := (g.app _).hom.map_one
  have h01 := h0.trans ((congrArg (fun z : Γ(polynomialProj K N,polynomialProjCoordinateOpen K N i) =>
    g.app (polynomialProjCoordinateOpen K N i) z) ha).trans hb)
  change (a.frame i).coefficients (𝟙 U) (M.val.map U.leTop.op (α.val.app (.op ⊤) (1:Γ(X,⊤))))=1
  have hα : M.val.map U.leTop.op (α.val.app (.op ⊤) (1:Γ(X,⊤))) =
      α.val.app (.op U) (1:Γ(X,U)) := nativeGlobalHom_one_restrict α U
  rw [hα]
  exact h01

/-- Actual original sheaf isomorphism transports the genuine original local frame. -/
def transportFrame {X : Scheme} {P Q : X.Modules} (e : P ≅ Q) {U : X.Opens}
    (d : LocalBundleFrame Q U) : LocalBundleFrame P U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e ≪≫ d

/-- EVERY genuine subordinate-open coefficient reads the literal original sheaf map then frame. -/
theorem transportFrame_coefficients {X : Scheme} {P Q : X.Modules} (e : P ≅ Q)
    {U W : X.Opens} (d : LocalBundleFrame Q U) (i : W ⟶ U) (s : Γ(P,W)) :
    (transportFrame e d).coefficients i s=d.coefficients i (e.hom.val.app (.op W) s) := rfl

/-- ONE actual ample power BEFORE ALL points manufactures a genuine ordinary section avoiding each original point. -/
theorem exists_fixed_positive_power_section_avoids_every_point
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {A : X.Modules}
    (P : SGPT.LineBundle.AmplePolarization f A) :
    ∃ d : ℕ, 0<d ∧ ∀ c : X, ∃ t : Γ(bundleTensorPower A d,⊤),
      ∀ b : LineBundleAtlas (bundleTensorPower A d), c∉(sectionZeroIdealSheaf b t).support := by
  refine ⟨P.power,P.power_pos,?_⟩
  intro c
  let Q := (Scheme.Modules.pullback P.map).obj (polynomialProjTwistingLine ℂ P.ambientDimension).sheaf
  let a := nativePolynomialPullbackAtlas ℂ P.ambientDimension P.map
  obtain ⟨i,hi⟩ := a.covers c
  let U := a.opens i
  let σ := coordinateSection ℂ P.ambientDimension P.map i
  let t : Γ(bundleTensorPower A P.power,⊤) := P.iso.inv.val.app (.op ⊤) σ
  let e : LocalBundleFrame (bundleTensorPower A P.power) U := transportFrame P.iso (a.frame i)
  have hcancel : P.iso.hom.val.app (.op ⊤) t=σ :=
    congr($((P.iso.inv_hom_id)).val.app (.op ⊤) |>.hom σ)
  have hcoefficient : e.coefficients (𝟙 U) ((bundleTensorPower A P.power).val.map U.leTop.op t)=1 := by
    rw [transportFrame_coefficients]
    rw [PresheafOfModules.naturality_apply P.iso.hom.val U.leTop.op t,hcancel]
    exact coordinateSection_self_coefficient ℂ P.ambientDimension P.map i
  have hU : IsAffineOpen U := (polynomialProjCoordinateOpen_isAffine ℂ P.ambientDimension i).preimage P.map
  refine ⟨t,?_⟩
  intro b hbad
  have hn := (originalZero_support_iff_not_basicOpen b t ⟨U,hU⟩ e (𝟙 U) c hi).mp hbad
  rw [hcoefficient,X.basicOpen_one] at hn
  exact hn hi
end SGPT.Okounkov.OriginalAmpleUnits
