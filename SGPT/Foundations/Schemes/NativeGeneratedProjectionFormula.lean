import SGPT.Foundations.Schemes.NativeLineProjectionLocalFrame
import SGPT.Foundations.Schemes.NativeLineGeneratingSections
import SGPT.Foundations.Schemes.NativeProjectiveConeProper
/-!
# NativeGeneratedProjectionFormula

Actual global generator morphisms and their genuine pullbacks obey the true adjunction-unit square. Their real inverse local frames give literal native projection-map coefficient squares and local isomorphisms. Actual local inverse descent proves the global canonical projection formula, supplied concretely by true projective coordinate morphisms.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X Y : Scheme.{u}}

/-- The actual global generator and its actual pulled-back generator have the true adjunction-unit square. -/
theorem nativePullbackGlobalHom_unit_square (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) :
    α ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (nativePullbackGlobalHom f α) := by
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (nativeSchemePullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _
      (nativeSchemePullbackUnitIso f).hom |>.symm.trans (nativeSchemePullbackUnitIso_mate f))
  rw [← hu, Category.assoc, ← Functor.map_comp]
  have he : (nativeSchemePullbackUnitIso f).hom ≫ nativePullbackGlobalHom f α =
      (Scheme.Modules.pullback f).map α := by
    unfold nativePullbackGlobalHom
    simp
  rw [he]
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality α

/-- A genuinely locally invertible global scalar morphism gives an actual local line frame. -/
def nativeGlobalGeneratorFrame {Z : Scheme.{u}} {L : Z.Modules}
    (α : SheafOfModules.unit Z.ringCatSheaf ⟶ L) (U : Z.Opens)
    [IsIso ((SheafOfModules.overFunctor Z.ringCatSheaf U).map α)] : LocalBundleFrame L U :=
  (asIso ((SheafOfModules.overFunctor Z.ringCatSheaf U).map α)).symm

/-- The genuine local coefficient square follows from actual invertible generator morphisms and the true adjunction square. -/
theorem nativeGeneratorPullback_coefficient_square (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [hα : IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)]
    [hβ : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).map
      (nativePullbackGlobalHom f α))]
    (W : Y.Opens) (i : W ⟶ U) (s : bundleSections L W) :
    ((nativeGlobalGeneratorFrame (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)).coefficients ((Opens.map f.base).map i))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s) =
      f.app W (((nativeGlobalGeneratorFrame α U).coefficients i) s) := by
  let e := nativeGlobalGeneratorFrame α U
  let d := nativeGlobalGeneratorFrame (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)
  have ha : α.val.app (.op W) (e.coefficients i s) = s := by
    have he := congrArg (fun m ↦ m.val.app (.op (Over.mk i)) s) e.hom_inv_id
    exact he
  have hb (r : Γ(X, f ⁻¹ᵁ W)) :
      d.coefficients ((Opens.map f.base).map i)
        ((nativePullbackGlobalHom f α).val.app (.op (f ⁻¹ᵁ W)) r) = r := by
    have he := congrArg (fun m ↦ m.val.app (.op (Over.mk ((Opens.map f.base).map i))) r)
      d.inv_hom_id
    exact he
  have hs := congrArg (fun m ↦ m.val.app (.op W) (e.coefficients i s))
    (nativePullbackGlobalHom_unit_square f α)
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W)
      (α.val.app (.op W) (e.coefficients i s)) =
    (nativePullbackGlobalHom f α).val.app (.op (f ⁻¹ᵁ W))
      (f.app W (e.coefficients i s)) at hs
  rw [ha] at hs
  change d.coefficients ((Opens.map f.base).map i) _ = _
  rw [hs, hb]

/-- A genuine global generator defines the actual local projection isomorphism on every true generating open. -/
def nativeGeneratedLineProjectionLocalIso (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)] (M : X.Modules) :
    (bundleTensor L ((Scheme.Modules.pushforward f).obj M)).over U ≅
      ((Scheme.Modules.pushforward f).obj (bundleTensor ((Scheme.Modules.pullback f).obj L) M)).over U := by
  have := (nativeModuleHom_over_isIso_iff_restrict α U).mp inferInstance
  have := nativePullbackGlobalHom_restrict_isIso f α U
  have := (nativeModuleHom_over_isIso_iff_restrict (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)).mpr inferInstance
  exact nativeSchemeLineProjectionLocalIso f ((Scheme.Modules.pullback f).obj L) M
    (asIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)).symm
    (asIso ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).map
      (nativePullbackGlobalHom f α))).symm

/-- The independently constructed local projection inverse is an inverse for the literal native projection map. -/
theorem nativeGeneratedLineProjectionLocalIso_hom (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)] (M : X.Modules) :
    (nativeGeneratedLineProjectionLocalIso f α U M).hom =
      (SheafOfModules.overFunctor Y.ringCatSheaf U).map (nativeSchemeProjectionMap f L M) := by
  have := (nativeModuleHom_over_isIso_iff_restrict α U).mp inferInstance
  have := nativePullbackGlobalHom_restrict_isIso f α U
  have := (nativeModuleHom_over_isIso_iff_restrict (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)).mpr inferInstance
  apply nativeSchemeLineProjectionLocalIso_hom
  exact nativeGeneratorPullback_coefficient_square f α U

/-- The actual locally invertible pullback generator supplies a genuine pullback frame. -/
def nativePullbackGeneratorFrame (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)] :
    LocalBundleFrame ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) := by
  have := (nativeModuleHom_over_isIso_iff_restrict α U).mp inferInstance
  have := nativePullbackGlobalHom_restrict_isIso f α U
  have := (nativeModuleHom_over_isIso_iff_restrict (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)).mpr inferInstance
  exact nativeGlobalGeneratorFrame (nativePullbackGlobalHom f α) (f ⁻¹ᵁ U)

/-- The actual native projection map retains the genuine tensor coefficients on every subordinate generating open. -/
theorem nativeGeneratedLineProjectionMap_coefficients (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map α)] (M : X.Modules)
    (W : Y.Opens) (h : W ⟶ U)
    (x : bundleSections (bundleTensor L ((Scheme.Modules.pushforward f).obj M)) W) :
    (nativePullbackGeneratorFrame f α U).tensorModuleCoefficients M ((Opens.map f.base).map h)
      ((nativeSchemeProjectionMap f L M).val.app (.op W) x) =
    (nativeGlobalGeneratorFrame α U).tensorModuleCoefficients ((Scheme.Modules.pushforward f).obj M) h x := by
  let D := nativeSchemePushforwardTensorFrameSectionEquiv f ((Scheme.Modules.pullback f).obj L)
    M (nativePullbackGeneratorFrame f α U) h
  let C := (nativeGlobalGeneratorFrame α U).tensorModuleCoefficients
    ((Scheme.Modules.pushforward f).obj M) h
  have he := congrArg (fun k ↦ k.val.app (.op (Over.mk h)) x)
    (nativeGeneratedLineProjectionLocalIso_hom f α U M)
  change (nativeGeneratedLineProjectionLocalIso f α U M).hom.val.app (.op (Over.mk h)) x =
    (nativeSchemeProjectionMap f L M).val.app (.op W) x at he
  change D ((nativeSchemeProjectionMap f L M).val.app (.op W) x) = C x
  rw [← he]
  change D (D.symm (C x)) = C x
  exact D.apply_symm_apply _

/-- Genuine local inverses on an actual covering family descend to an inverse of the original module morphism. -/
theorem nativeModuleHom_isIso_of_over_cover {ι : Type*} {P Q : Y.Modules}
    (γ : P ⟶ Q) (U : ι → Y.Opens) (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (hγ : ∀ i, IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf (U i)).map γ)) :
    IsIso γ := by
  let E (i : ι) : P.over (U i) ≅ Q.over (U i) := by
    have := hγ i
    exact asIso ((SheafOfModules.overFunctor Y.ringCatSheaf (U i)).map γ)
  have hE : ∀ i j, bundleHomRestriction P Q (Opens.infLELeft (U i) (U j)) (E i).hom =
      bundleHomRestriction P Q (Opens.infLERight (U i) (U j)) (E j).hom := by
    intro i j
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl
  have he : (bundleGlueIso P Q U hU E hE).hom = γ := by
    apply bundleHom_ext P Q U hU
    intro i
    exact bundleGlueHom_restrict P Q U hU (fun j ↦ (E j).hom) hE i
  rw [← he]
  infer_instance

/-- True globally defined local generators prove that the literal native line projection map is an isomorphism. -/
theorem nativeGeneratedLineProjectionMap_isIso (f : X ⟶ Y) {L : Y.Modules}
    {I : Type u} (α : I → (SheafOfModules.unit Y.ringCatSheaf ⟶ L))
    (U : I → Y.Opens) (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (hα : ∀ i, IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf (U i)).map (α i)))
    (M : X.Modules) : IsIso (nativeSchemeProjectionMap f L M) := by
  apply nativeModuleHom_isIso_of_over_cover (nativeSchemeProjectionMap f L M) U hU
  intro i
  have := hα i
  rw [← nativeGeneratedLineProjectionLocalIso_hom f (α i) (U i) M]
  infer_instance

section Projective
variable {A σ I : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (a : I → 𝒜 1)

/-- Actual homogeneous coordinates on a genuine Proj cover produce the native projection formula for every actual twisting sheaf. -/
theorem nativeProjectiveTwistingProjectionMap_isIso
    {T : Scheme.{u}} (f : T ⟶ Proj 𝒜) (k : ℕ)
    (ha : ∀ x : Proj 𝒜, ∃ i, x ∈ Proj.basicOpen 𝒜 (a i).val) (M : T.Modules) :
    IsIso (nativeSchemeProjectionMap f (projectiveTwistingSheaf 𝒜 k) M) := by
  apply nativeGeneratedLineProjectionMap_isIso f
    (fun i ↦ projectiveTwistingCoordinateGlobalHom 𝒜 k (a i))
    (fun i ↦ Proj.basicOpen 𝒜 (a i).val) ha
  intro i
  rw [projectiveTwistingCoordinateGlobalHom_over]
  infer_instance

end Projective

section Polynomial
variable {K I : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial-Proj twisting projection formula has no supplied projection/generation premise. -/
theorem nativePolynomialTwistingProjectionMap_isIso {T : Scheme.{u}}
    (f : T ⟶ Proj (MvPolynomial.homogeneousSubmodule I K)) (k : ℕ) (M : T.Modules) :
    IsIso (nativeSchemeProjectionMap f
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) M) :=
  nativeProjectiveTwistingProjectionMap_isIso (MvPolynomial.homogeneousSubmodule I K)
    (fun i ↦ ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩) f k
    (homogeneousPolynomialTwistingAtlas (K := K) (I := I) k).covers M

end Polynomial

end
end SGPT.Foundations.Schemes
