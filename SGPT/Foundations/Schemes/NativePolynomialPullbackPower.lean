import SGPT.Foundations.Schemes.NativeGeneratorPullbackTransitions
/-!
# NativePolynomialPullbackPower

Actual inverse-image coordinate frames and genuine transition identities descend a real pullback/tensor-power comparison for native projective O(1), preserving coefficients on every subordinate open.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativeGeneratorFrameEqualityValue {Z : Scheme} {P : Z.Modules}
    (α : SheafOfModules.unit Z.ringCatSheaf ⟶ P) (U : Z.Opens)
    [IsIso ((SheafOfModules.overFunctor Z.ringCatSheaf U).map α)]
    (d : LocalBundleFrame P U)
    (he : (SheafOfModules.overFunctor Z.ringCatSheaf U).map α = d.inv) :
    nativeGlobalGeneratorFrame α U = d := by
  apply Iso.ext
  change inv ((SheafOfModules.overFunctor Z.ringCatSheaf U).map α) = d.hom
  apply IsIso.inv_eq_of_hom_inv_id
  rw [he]
  exact d.inv_hom_id

instance nativePolynomialCoordinateHom_over_isIso (i : Fin (n + 1)) :
    IsIso ((SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
      (polynomialProjCoordinateOpen K n i)).map
        (homogeneousPolynomialCoordinateGlobalHom (K := K) i)) := by
  have he := projectiveTwistingCoordinateGlobalHom_over
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
  change (SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
    (polynomialProjCoordinateOpen K n i)).map
      (homogeneousPolynomialCoordinateGlobalHom (K := K) i) =
        ((polynomialProjTwistingLine K n).atlas.frame i).inv at he
  rw [he]
  infer_instance

/-- The actual degree-one generator frame is the original O(1) coordinate frame. -/
theorem nativePolynomialCoordinateHom_generatorFrame (i : Fin (n + 1)) :
    nativeGlobalGeneratorFrame (homogeneousPolynomialCoordinateGlobalHom (K := K) i)
      (polynomialProjCoordinateOpen K n i) = (polynomialProjTwistingLine K n).atlas.frame i := by
  have he := projectiveTwistingCoordinateGlobalHom_over
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
  change (SheafOfModules.overFunctor (polynomialProj K n).ringCatSheaf
    (polynomialProjCoordinateOpen K n i)).map
      (homogeneousPolynomialCoordinateGlobalHom (K := K) i) =
        ((polynomialProjTwistingLine K n).atlas.frame i).inv at he
  exact nativeGeneratorFrameEqualityValue
    (homogeneousPolynomialCoordinateGlobalHom (K := K) i) (polynomialProjCoordinateOpen K n i)
    ((polynomialProjTwistingLine K n).atlas.frame i) he

variable {X : Scheme} (f : X ⟶ polynomialProj K n)

/-- A genuine atlas of the literal pullback of projective O(1), using its actual global coordinate generators. -/
def nativePolynomialPullbackAtlas : LineBundleAtlas
    ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) where
  I := Fin (n + 1)
  opens i := f ⁻¹ᵁ polynomialProjCoordinateOpen K n i
  covers x := (polynomialProjTwistingLine K n).atlas.covers (f.base x)
  frame i := nativePullbackGeneratorFrame f
    (homogeneousPolynomialCoordinateGlobalHom (K := K) i) (polynomialProjCoordinateOpen K n i)

private theorem nativePolynomialPullbackPowerMatching_on_inverse (m : ℕ)
    (i j : Fin (n + 1)) (W : (polynomialProj K n).Opens)
    (h : W ⟶ polynomialProjCoordinateOpen K n i)
    (k : W ⟶ polynomialProjCoordinateOpen K n j) :
    localBundleFrameTransition (nativePolynomialPowerPullbackFrame K n f m i)
      (nativePolynomialPowerPullbackFrame K n f m j)
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) =
    localBundleFrameTransition (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m)
      (((nativePolynomialPullbackAtlas K n f).frame j).tensorPower m)
      ((Opens.map f.base).map h) ((Opens.map f.base).map k) := by
  rw [localBundleFrameTransition_tensorPower]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  have hm := nativePullbackGeneratorFrame_transition f
    (nativePolynomialPowerCoordinateHom K n m i) (nativePolynomialPowerCoordinateHom K n m j)
    (polynomialProjCoordinateOpen K n i) (polynomialProjCoordinateOpen K n j) W h k
  rw [nativePolynomialPowerCoordinateHom_generatorFrame,
    nativePolynomialPowerCoordinateHom_generatorFrame, localBundleFrameTransition_tensorPower,
    Units.val_pow_eq_pow_val, map_pow] at hm
  have h1 := nativePullbackGeneratorFrame_transition f
    (homogeneousPolynomialCoordinateGlobalHom (K := K) i)
    (homogeneousPolynomialCoordinateGlobalHom (K := K) j)
    (polynomialProjCoordinateOpen K n i) (polynomialProjCoordinateOpen K n j) W h k
  rw [nativePolynomialCoordinateHom_generatorFrame, nativePolynomialCoordinateHom_generatorFrame] at h1
  exact hm.trans (congrArg (fun r ↦ r ^ m) h1.symm)

private theorem nativePolynomialPullbackPowerMatching (m : ℕ)
    (i j : Fin (n + 1)) (W : X.Opens)
    (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
    (k : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n j) :
    localBundleFrameTransition (nativePolynomialPowerPullbackFrame K n f m i)
      (nativePolynomialPowerPullbackFrame K n f m j) h k =
    localBundleFrameTransition (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m)
      (((nativePolynomialPullbackAtlas K n f).frame j).tensorPower m) h k := by
  let V := polynomialProjCoordinateOpen K n i ⊓ polynomialProjCoordinateOpen K n j
  let a : V ⟶ polynomialProjCoordinateOpen K n i := Opens.infLELeft _ _
  let b : V ⟶ polynomialProjCoordinateOpen K n j := Opens.infLERight _ _
  let c : W ⟶ f ⁻¹ᵁ V := homOfLE (show W ≤ f ⁻¹ᵁ V from le_inf h.le k.le)
  have he := nativePolynomialPullbackPowerMatching_on_inverse K n f m i j V a b
  apply Units.ext
  have hr := congrArg (fun z : (X.sheaf.obj.obj (.op (f ⁻¹ᵁ V)))ˣ ↦ X.sheaf.obj.map c.op
    (z : X.sheaf.obj.obj (.op (f ⁻¹ᵁ V)))) he
  rw [← localBundleFrameTransition_restrict, ← localBundleFrameTransition_restrict] at hr
  exact hr

/-- Actual pullback commutes with actual projective tensor powers through a genuinely descended coefficient-preserving sheaf isomorphism. -/
def nativePolynomialPullbackPowerIso (m : ℕ) :
    (Scheme.Modules.pullback f).obj (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) ≅
      bundleTensorPower ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) m :=
  nativeMatchingBundleFrameIso _ _ (nativePolynomialPullbackAtlas K n f).opens
    (nativePolynomialPullbackAtlas K n f).covers
    (nativePolynomialPowerPullbackFrame K n f m)
    (fun i ↦ ((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m)
    (nativePolynomialPullbackPowerMatching K n f m)

/-- The actual descended pullback-power comparison retains every real subordinate-open coefficient. -/
theorem nativePolynomialPullbackPowerIso_coefficients (m : ℕ) (i : Fin (n + 1))
    {W : X.Opens} (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
    (s : bundleSections ((Scheme.Modules.pullback f).obj
      (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)) W) :
    (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m).coefficients h
      ((nativePolynomialPullbackPowerIso K n f m).hom.val.app (.op W) s) =
      (nativePolynomialPowerPullbackFrame K n f m i).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients _ _ (nativePolynomialPullbackAtlas K n f).opens
    (nativePolynomialPullbackAtlas K n f).covers (nativePolynomialPowerPullbackFrame K n f m)
    (fun i ↦ ((nativePolynomialPullbackAtlas K n f).frame i).tensorPower m)
    (nativePolynomialPullbackPowerMatching K n f m) i h s

end
end SGPT.Foundations.Schemes
