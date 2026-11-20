import SGPT.Foundations.Schemes.NativePositiveProjectiveFrameNormalization
/-!
# NativePositiveProjectiveCoordinateSections

Actual positive projective coordinate morphisms applied to the real global regular one give genuine original degree-q sections. Their actual positive frame coefficients are one on every smaller coordinate open.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem nativeGlobalHom_one_restrict {Z : Scheme} {P : Z.Modules}
    (α : SheafOfModules.unit Z.ringCatSheaf ⟶ P) (W : Z.Opens) :
    P.val.map (homOfLE (show W ≤ ⊤ from le_top)).op
      (α.val.app (.op ⊤) (1 : Γ(Z, ⊤))) = α.val.app (.op W) (1 : Γ(Z, W)) := by
  have he := PresheafOfModules.naturality_apply α.val
    (homOfLE (show W ≤ ⊤ from le_top)).op (1 : Γ(Z, ⊤))
  change α.val.app (.op W) (Z.presheaf.map (homOfLE le_top).op 1) = _ at he
  rw [map_one] at he
  exact he.symm

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The genuine global positive projective coordinate section in the original full-ring degree-q space. -/
def nativePositiveProjectiveCoordinateSection (i : Fin (n + 1)) : bundlePowerGlobalSections L.sheaf q :=
  (nativeProjectiveCoordinateGenerator f (L.tensorPower q) e i).val.app (.op ⊤) (1 : Γ(X, ⊤))

/-- The actual global coordinate section has true coefficient one in the genuine positive coordinate frame on every smaller coordinate open. -/
theorem nativePositiveProjectiveCoordinateSection_coefficients (i : Fin (n + 1))
    {W : X.Opens} (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) :
    (nativePositiveProjectiveCoordinateFrame K n f L q e i).coefficients h
      ((bundleTensorPower L.sheaf q).val.map (homOfLE le_top).op
        (nativePositiveProjectiveCoordinateSection K n f L q e i)) = 1 := by
  let α := nativeProjectiveCoordinateGenerator f (L.tensorPower q) e i
  let β := nativePullbackGlobalHom f (homogeneousPolynomialCoordinateGlobalHom (K := K) i)
  let d := (nativePolynomialPullbackAtlas K n f).frame i
  have hi := congrArg (fun a ↦ a.val.app (.op W) (β.val.app (.op W) (1 : Γ(X, W)))) e.inv_hom_id
  change e.hom.val.app (.op W) (α.val.app (.op W) (1 : Γ(X, W))) =
    β.val.app (.op W) (1 : Γ(X, W)) at hi
  have hc : d.coefficients h (β.val.app (.op W) (1 : Γ(X, W))) = 1 :=
    nativeGlobalGeneratorFrame_hom_one β (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) h
  change d.coefficients h (e.hom.val.app (.op W)
    ((bundleTensorPower L.sheaf q).val.map (homOfLE le_top).op
      (α.val.app (.op ⊤) (1 : Γ(X, ⊤))))) = 1
  have hr := nativeGlobalHom_one_restrict α W
  exact (congrArg (fun t ↦ d.coefficients h (e.hom.val.app (.op W) t)) hr).trans
    ((congrArg (d.coefficients h) hi).trans hc)

end
end SGPT.Foundations.Schemes
