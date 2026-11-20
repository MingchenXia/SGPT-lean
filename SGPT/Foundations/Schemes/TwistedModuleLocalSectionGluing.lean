import SGPT.Foundations.Schemes.TwistedModuleSectionAction

/-! # True local twist actions and genuine sheaf gluing

A real global line section acts on real local module sections through their
actual frames.  Killing the literal actual overlap errors suffices for native
sheaf gluing; no extension or finiteness conclusion is assumed.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {T : X.Modules}

/-- The actual local tensor action on a genuine local twisted-module section. -/
def atlasTwistedLocalSectionAction (a : LineBundleAtlas T) (M : X.Modules) (r d : ℕ)
    (s : bundlePowerGlobalSections T r) (j : a.I)
    (t : bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j)) :
    bundleSections (bundleTensor (bundleTensorPower T (r + d)) M) (a.opens j) :=
  (((a.frame j).tensorPower (r + d)).tensorModuleCoefficients M (𝟙 _)).symm
    (atlasPowerGlobalCoefficients a r j s •
      (((a.frame j).tensorPower d).tensorModuleCoefficients M (𝟙 _) t))

/-- True local acted sections retain their actual coefficient products under all real restrictions. -/
theorem atlasTwistedLocalSectionAction_coefficients_restrict
    (a : LineBundleAtlas T) (M : X.Modules) (r d : ℕ)
    (s : bundlePowerGlobalSections T r) (j : a.I)
    (t : bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j))
    {V : X.Opens} (i : V ⟶ a.opens j) :
    ((a.frame j).tensorPower (r + d)).tensorModuleCoefficients M i
        ((bundleTensor (bundleTensorPower T (r + d)) M).val.map i.op
          (atlasTwistedLocalSectionAction a M r d s j t)) =
      X.sheaf.obj.map i.op (atlasPowerGlobalCoefficients a r j s) •
        ((a.frame j).tensorPower d).tensorModuleCoefficients M i
          ((bundleTensor (bundleTensorPower T d) M).val.map i.op t) := by
  have h := ((a.frame j).tensorPower (r + d)).tensorModuleCoefficients_restrict M
    (𝟙 _) i (atlasTwistedLocalSectionAction a M r d s j t)
  simp only [Category.comp_id, atlasTwistedLocalSectionAction, LinearEquiv.apply_symm_apply] at h
  have hd := ((a.frame j).tensorPower d).tensorModuleCoefficients_restrict M (𝟙 _) i t
  simp only [Category.comp_id] at hd
  exact h.trans ((M.val.map_smul i.op _ _).trans
    (congrArg (fun z => X.sheaf.obj.map i.op (atlasPowerGlobalCoefficients a r j s) • z) hd.symm))

/-- The true local tensor action has the same actual scalar action in every intersecting frame. -/
theorem atlasTwistedLocalSectionAction_coefficients_other_frame
    (a : LineBundleAtlas T) (M : X.Modules) (r d : ℕ)
    (s : bundlePowerGlobalSections T r) (j k : a.I)
    (t : bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens k))
    {V : X.Opens} (l : V ⟶ a.opens j) (q : V ⟶ a.opens k) :
    ((a.frame j).tensorPower (r + d)).tensorModuleCoefficients M l
        ((bundleTensor (bundleTensorPower T (r + d)) M).val.map q.op
          (atlasTwistedLocalSectionAction a M r d s k t)) =
      X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a r j s) •
        ((a.frame j).tensorPower d).tensorModuleCoefficients M l
          ((bundleTensor (bundleTensorPower T d) M).val.map q.op t) := by
  have hs : X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a r j s) =
      (localBundleFrameTransition (a.frame k) (a.frame j) q l : X.sheaf.obj.obj (op V)) ^ r *
        X.sheaf.obj.map q.op (atlasPowerGlobalCoefficients a r k s) :=
    LocalBundleFrame.global_coefficients_transition (a.frame k) (a.frame j) q l r s
  rw [LocalBundleFrame.tensorModuleCoefficients_transition
    ((a.frame k).tensorPower (r + d)) ((a.frame j).tensorPower (r + d)) M q l,
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val,
    atlasTwistedLocalSectionAction_coefficients_restrict]
  rw [LocalBundleFrame.tensorModuleCoefficients_transition
    ((a.frame k).tensorPower d) ((a.frame j).tensorPower d) M q l,
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val, hs]
  simp only [pow_add, ← mul_smul]
  congr 1
  ring

/-- The literal module-valued coefficient of the actual difference on a true overlap. -/
def atlasTwistedLocalSectionError (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (t : ∀ j, bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j))
    (j k : a.I) : bundleSections M (a.opens j ⊓ a.opens k) :=
  ((a.frame j).tensorPower d).tensorModuleCoefficients M (homOfLE inf_le_left)
    ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE inf_le_left).op (t j)) -
  ((a.frame j).tensorPower d).tensorModuleCoefficients M (homOfLE inf_le_left)
    ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE inf_le_right).op (t k))

/-- Killing the literal local coefficient differences makes the actual acted sections compatible. -/
theorem atlasTwistedLocalSectionAction_compatible
    (a : LineBundleAtlas T) (M : X.Modules) (r d : ℕ)
    (s : bundlePowerGlobalSections T r)
    (t : ∀ j, bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j))
    (h : ∀ j k,
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a r j s) • atlasTwistedLocalSectionError a M d t j k = 0) :
    TopCat.Presheaf.IsCompatible (bundleTensor (bundleTensorPower T (r + d)) M).val.presheaf
      a.opens (fun j => atlasTwistedLocalSectionAction a M r d s j (t j)) := by
  intro j k
  let V := a.opens j ⊓ a.opens k
  let l : V ⟶ a.opens j := homOfLE inf_le_left
  let q : V ⟶ a.opens k := homOfLE inf_le_right
  change (bundleTensor (bundleTensorPower T (r + d)) M).val.map l.op
      (atlasTwistedLocalSectionAction a M r d s j (t j)) =
    (bundleTensor (bundleTensorPower T (r + d)) M).val.map q.op
      (atlasTwistedLocalSectionAction a M r d s k (t k))
  apply (((a.frame j).tensorPower (r + d)).tensorModuleCoefficients M l).injective
  have hk := h j k
  unfold atlasTwistedLocalSectionError at hk
  rw [smul_sub, sub_eq_zero] at hk
  rw [atlasTwistedLocalSectionAction_coefficients_restrict,
    atlasTwistedLocalSectionAction_coefficients_other_frame]
  exact hk

/-- The genuine acted local sections glue to a unique actual global twisted-module section. -/
theorem atlasTwistedLocalSectionAction_existsUnique
    (a : LineBundleAtlas T) (M : X.Modules) (r d : ℕ)
    (s : bundlePowerGlobalSections T r)
    (t : ∀ j, bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j))
    (h : ∀ j k,
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a r j s) • atlasTwistedLocalSectionError a M d t j k = 0) :
    ∃! z : bundleTwistedGlobalSections T M (r + d), ∀ j,
      (bundleTensor (bundleTensorPower T (r + d)) M).val.map (homOfLE le_top).op z =
        atlasTwistedLocalSectionAction a M r d s j (t j) := by
  have hc : (⊤ : X.Opens) ≤ iSup a.opens := by
    intro x hx
    obtain ⟨j, hj⟩ := a.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  let S : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(bundleTensor (bundleTensorPower T (r + d)) M).val.presheaf,
      (bundleTensor (bundleTensorPower T (r + d)) M).isSheaf⟩
  exact TopCat.Sheaf.existsUnique_gluing' S a.opens ⊤ (fun _ => homOfLE le_top) hc
    (fun j => atlasTwistedLocalSectionAction a M r d s j (t j))
    (atlasTwistedLocalSectionAction_compatible a M r d s t h)

end

end SGPT.Foundations.Schemes
