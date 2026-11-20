import SGPT.Foundations.Schemes.NativeGeneratedConeProper
import SGPT.Foundations.Schemes.NativeLinePullbackFrames
/-!
# NativeLineGeneratingSections

Actual sheaf pullback preserves local invertibility on true inverse-image opens. Genuine locally invertible generator morphisms produce actual degree-one sections with locally unit coefficients in the original line atlas.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

private theorem map_isIso_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (α : A ⟶ B) [IsIso (G.map α)] :
    IsIso (F.map α) := by
  rw [← NatIso.naturality_2 e α]
  infer_instance

variable {X Y : Scheme.{u}}

/-- Actual inverse image preserves local isomorphisms on genuine inverse-image opens. -/
theorem nativeModuleHom_pullback_isIso_on_open (f : X ⟶ Y) {P Q : Y.Modules}
    (α : P ⟶ Q) (U : Y.Opens) [IsIso ((Scheme.Modules.pullback U.ι).map α)] :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map α)) := by
  let E : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm
  have : IsIso ((Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)).map α) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pullback (f ∣_ U)).map
      ((Scheme.Modules.pullback U.ι).map α)))
  exact map_isIso_of_natIso E α

/-- Genuine open restriction and genuine pullback detect the same local isomorphisms. -/
theorem nativeModuleHom_restrict_isIso_iff_pullback {P Q : Y.Modules} (α : P ⟶ Q)
    (U : Y.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) ↔
      IsIso ((Scheme.Modules.pullback U.ι).map α) := by
  constructor
  · intro h
    exact map_isIso_of_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm α
  · intro h
    exact map_isIso_of_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι) α

/-- Local invertibility is preserved by actual module pullback and actual open restriction. -/
theorem nativeModuleHom_pullback_restrict_isIso (f : X ⟶ Y) {P Q : Y.Modules}
    (α : P ⟶ Q) (U : Y.Opens) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map α)] :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullback f).map α)) := by
  have := (nativeModuleHom_restrict_isIso_iff_pullback α U).mp inferInstance
  have := nativeModuleHom_pullback_isIso_on_open f α U
  exact (nativeModuleHom_restrict_isIso_iff_pullback _ _).mpr inferInstance

/-- The actual global scalar map of a section pulls back using the true structure-unit comparison. -/
def nativePullbackGlobalHom (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj L :=
  (nativeSchemePullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map α

/-- A real local generator remains a real local generator under native sheaf pullback. -/
theorem nativePullbackGlobalHom_restrict_isIso (f : X ⟶ Y) {L : Y.Modules}
    (α : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (U : Y.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map α)] :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (nativePullbackGlobalHom f α)) := by
  have := nativeModuleHom_pullback_restrict_isIso f α U
  dsimp [nativePullbackGlobalHom]
  rw [Functor.map_comp]
  infer_instance

/-- The over-site spelling and actual open-subscheme spelling detect the same local isomorphisms. -/
theorem nativeModuleHom_over_isIso_iff_restrict {P Q : X.Modules} (α : P ⟶ Q) (U : X.Opens) :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map α) ↔
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  constructor
  · intro h
    have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U ⋙
        (Scheme.Modules.overEquiv U).functor).map α) :=
      inferInstanceAs (IsIso ((Scheme.Modules.overEquiv U).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)))
    exact map_isIso_of_natIso (Scheme.Modules.overFunctorEquiv U).symm α
  · intro h
    have h' := map_isIso_of_natIso (Scheme.Modules.overFunctorEquiv U) α
    exact (isIso_iff_of_reflects_iso
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)
      (Scheme.Modules.overEquiv U).functor).mp h'

/-- A real locally invertible scalar morphism has a genuine unit coefficient in every local frame. -/
theorem nativeModuleHom_frame_coefficient_isUnit {P : X.Modules}
    (α : SheafOfModules.unit X.ringCatSheaf ⟶ P) (U : X.Opens)
    [IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)]
    {V W : X.Opens} (e : LocalBundleFrame P V) (i : W ⟶ V) (hW : W ≤ U) :
    IsUnit (e.coefficients i (α.val.app (.op W) (1 : Γ(X, W)))) := by
  have : IsIso (α.val.app (.op W)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (.op (Over.mk (homOfLE hW)))).map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map α)))
  have hα := (ConcreteCategory.isIso_iff_bijective (α.val.app (.op W))).mp inferInstance
  let a : Γ(X, W) →ₗ[Γ(X, W)] bundleSections P W := (α.val.app (.op W)).hom
  change IsUnit (show Γ(X, W) from e.coefficients i (a 1))
  apply IsUnit.isUnit_iff_mulRight_bijective.mpr
  have he : (fun r : Γ(X, W) ↦ r * (show Γ(X, W) from e.coefficients i (a 1))) =
      (e.coefficients i) ∘ a := by
    funext r
    have ha : a r = r • a 1 := by
      simpa only [smul_eq_mul, mul_one] using a.map_smul r (1 : Γ(X, W))
    change _ = e.coefficients i (a r)
    rw [ha, (e.coefficients i).map_smul]
    rfl
  rw [he]
  exact (e.coefficients i).bijective.comp hα

/-- Genuine local generator morphisms produce the actual degree-one global sections. -/
def nativeHomDegreeOneSection (L : IntrinsicLineBundle X)
    (α : SheafOfModules.unit X.ringCatSheaf ⟶ L.sheaf) :
    bundlePowerGlobalSections L.sheaf 1 :=
  (α ≫ (bundleTensorLeftUnitIso L.sheaf).inv).val.app (.op ⊤) (1 : Γ(X, ⊤))

/-- Local invertibility on a genuine open cover produces actual local unit generation for the cone. -/
theorem IntrinsicLineBundle.nativeSectionsGenerate_of_local_generator_homs
    (L : IntrinsicLineBundle X) {I : Type u}
    (α : I → (SheafOfModules.unit X.ringCatSheaf ⟶ L.sheaf))
    (U : I → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hα : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map (α i))) :
    L.NativeSectionsGenerate (fun i ↦ nativeHomDegreeOneSection L (α i)) := by
  intro x
  obtain ⟨i, hi⟩ := hU x
  obtain ⟨j, hj⟩ := L.atlas.covers x
  let W := U i ⊓ L.atlas.opens j
  let c : NativeFramedOpen L.atlas := ⟨j, ⟨W, inf_le_right⟩⟩
  refine ⟨c, ⟨hi, hj⟩, i, ?_⟩
  let γ := α i ≫ (bundleTensorLeftUnitIso L.sheaf).inv
  have : IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map γ) := by
    have := hα i
    dsimp [γ]
    rw [Functor.map_comp]
    infer_instance
  have := (nativeModuleHom_over_isIso_iff_restrict γ (U i)).mpr inferInstance
  have hu := nativeModuleHom_frame_coefficient_isUnit γ (U i)
    ((L.atlas.frame j).tensorPower 1) (homOfLE (show W ≤ L.atlas.opens j from inf_le_right))
    (show W ≤ U i from inf_le_left)
  have hg : (bundleTensorPower L.sheaf 1).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
      (nativeHomDegreeOneSection L (α i)) = γ.val.app (.op W) (1 : Γ(X, W)) := by
    change (bundleTensor (SheafOfModules.unit X.ringCatSheaf) L.sheaf).val.map
      (homOfLE (show W ≤ ⊤ from le_top)).op
      (γ.val.app (.op ⊤) (1 : Γ(X, ⊤))) = γ.val.app (.op W) (1 : Γ(X, W))
    have he := PresheafOfModules.naturality_apply γ.val
      (homOfLE (show W ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))
    change γ.val.app (.op W) (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op 1) = _ at he
    rw [map_one] at he
    exact he.symm
  apply IsUnit.map c.2.1.topIso.inv.hom
  change IsUnit (X.sheaf.obj.map (homOfLE (show W ≤ L.atlas.opens j from inf_le_right)).op
    (((L.atlas.frame j).tensorPower 1).coefficients (𝟙 _)
      ((bundleTensorPower L.sheaf 1).val.map (homOfLE le_top).op
        (nativeHomDegreeOneSection L (α i)))))
  rw [← LocalBundleFrame.global_coefficients_restrict (L.atlas.frame j) 1
    (homOfLE (show W ≤ L.atlas.opens j from inf_le_right)), hg]
  exact hu

end
end SGPT.Foundations.Schemes
