import SGPT.Foundations.Schemes.NativeLineGeneratingSections
import SGPT.Foundations.Schemes.ProjectiveTwistingSheaf
/-!
# NativeProjectiveConeProper

Literal homogeneous coordinate morphisms are inverse frames on true Proj coordinate opens. Native pullback and a genuine line-sheaf isomorphism produce actual generating sections. Over a proper affine base the actual full-cone contraction is proper.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The literal homogeneous coordinate section gives its actual global scalar morphism. -/
def projectiveTwistingCoordinateGlobalHom (k : ℕ) (a : 𝒜 1) :
    SheafOfModules.unit (Proj 𝒜).ringCatSheaf ⟶ projectiveTwistingSheaf 𝒜 k :=
  (projectiveTwistingSheaf 𝒜 k).unitHomEquiv.symm
    ((projectiveTwistingSheaf 𝒜 k).val.sectionsMk
      (fun U ↦ projectiveTwistingCoordinateSection 𝒜 k a U.unop) (fun {_ _} _ ↦ rfl))

/-- Its literal component multiplies the true global coordinate section. -/
theorem projectiveTwistingCoordinateGlobalHom_app (k : ℕ) (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (r : Γ(Proj 𝒜, U)) :
    (projectiveTwistingCoordinateGlobalHom 𝒜 k a).val.app (.op U) r =
      projectiveTwistingCoordinateMul 𝒜 k a U r := rfl

/-- On its true projective coordinate open, the coordinate morphism is the actual inverse frame. -/
theorem projectiveTwistingCoordinateGlobalHom_over (k : ℕ) (a : 𝒜 1) :
    (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf (Proj.basicOpen 𝒜 a.val)).map
        (projectiveTwistingCoordinateGlobalHom 𝒜 k a) =
      (projectiveTwistingCoordinateFrame 𝒜 k a).inv := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact projectiveTwistingCoordinateGlobalHom_app 𝒜 k a U.unop.left r

/-- The genuine homogeneous coordinate morphism is locally invertible on its true basic open. -/
theorem projectiveTwistingCoordinateGlobalHom_restrict_isIso (k : ℕ) (a : 𝒜 1) :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 a.val).ι).map
      (projectiveTwistingCoordinateGlobalHom 𝒜 k a)) := by
  have : IsIso ((SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf
      (Proj.basicOpen 𝒜 a.val)).map (projectiveTwistingCoordinateGlobalHom 𝒜 k a)) := by
    rw [projectiveTwistingCoordinateGlobalHom_over]
    infer_instance
  exact (nativeModuleHom_over_isIso_iff_restrict _ _).mp inferInstance

section Polynomial
variable {K I : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual coordinate morphism of the actual polynomial Proj O(1). -/
def homogeneousPolynomialCoordinateGlobalHom (i : I) :
    SheafOfModules.unit (Proj (MvPolynomial.homogeneousSubmodule I K)).ringCatSheaf ⟶
      projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) 1 :=
  projectiveTwistingCoordinateGlobalHom _ 1 ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩

variable {X : Scheme.{u}} (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule I K))
  (L : IntrinsicLineBundle X)
  (e : L.sheaf ≅ (Scheme.Modules.pullback f).obj
    (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) 1))

/-- Pulling back a literal projective coordinate and the actual line-sheaf isomorphism gives an actual global generator morphism. -/
def nativeProjectiveCoordinateGenerator (i : I) :
    SheafOfModules.unit X.ringCatSheaf ⟶ L.sheaf :=
  nativePullbackGlobalHom f (homogeneousPolynomialCoordinateGlobalHom (K := K) i) ≫ e.inv

/-- Genuine pulled-back projective coordinates generate the literal line sheaf locally. -/
theorem nativeProjectiveCoordinateGenerator_restrict_isIso (i : I) :
    IsIso ((Scheme.Modules.restrictFunctor
      (f ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i)).ι).map
        (nativeProjectiveCoordinateGenerator f L e i)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen _ (MvPolynomial.X i)).ι).map
        (homogeneousPolynomialCoordinateGlobalHom (K := K) i)) :=
    projectiveTwistingCoordinateGlobalHom_restrict_isIso
    (MvPolynomial.homogeneousSubmodule I K) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
  have := nativePullbackGlobalHom_restrict_isIso f
    (homogeneousPolynomialCoordinateGlobalHom (K := K) i)
    (Proj.basicOpen _ (MvPolynomial.X i))
  dsimp [nativeProjectiveCoordinateGenerator]
  rw [Functor.map_comp]
  infer_instance

/-- The actual pullback of polynomial-Proj O(1) has genuine generating degree-one sections. -/
theorem nativeProjectiveCoordinateSections_generate :
    L.NativeSectionsGenerate
      (fun i ↦ nativeHomDegreeOneSection L (nativeProjectiveCoordinateGenerator f L e i)) := by
  apply L.nativeSectionsGenerate_of_local_generator_homs
    (fun i ↦ nativeProjectiveCoordinateGenerator f L e i)
    (fun i ↦ f ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
  · intro x
    exact (homogeneousPolynomialTwistingAtlas (K := K) (I := I) 1).covers (f x)
  · exact nativeProjectiveCoordinateGenerator_restrict_isIso f L e

include f e in
/-- Actual proper affine-base geometry and actual projective positivity produce the proper full-cone contraction. -/
theorem nativeProjectiveLineConeMap_isProper {R : CommRingCat.{u}}
    (p : X ⟶ Spec R) [IsProper p] : IsProper L.nativeConeMap :=
  L.nativeConeMap_isProper_of_generated_over_affine
    (fun i ↦ nativeHomDegreeOneSection L (nativeProjectiveCoordinateGenerator f L e i))
    (nativeProjectiveCoordinateSections_generate f L e) p

end Polynomial
end
end SGPT.Foundations.Schemes
