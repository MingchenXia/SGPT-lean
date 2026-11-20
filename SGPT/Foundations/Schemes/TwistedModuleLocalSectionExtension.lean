import SGPT.Foundations.Schemes.TwistedModuleLocalSectionGluing

/-! # Genuine local extensions and their actual overlap errors -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {T : X.Modules}

/-- Actual inverse frames reconstruct the actual local twisted-module lifts. -/
def atlasTwistedLocalSectionOfCoefficients (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (c : ∀ j, bundleSections M (a.opens j)) (j : a.I) :
    bundleSections (bundleTensor (bundleTensorPower T d) M) (a.opens j) :=
  (((a.frame j).tensorPower d).tensorModuleCoefficients M (𝟙 _)).symm (c j)

/-- Reconstructed actual lifts retain their actual module coefficients on every true subopen. -/
theorem atlasTwistedLocalSectionOfCoefficients_restrict (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (c : ∀ j, bundleSections M (a.opens j)) (j : a.I)
    {V : X.Opens} (l : V ⟶ a.opens j) :
    ((a.frame j).tensorPower d).tensorModuleCoefficients M l
      ((bundleTensor (bundleTensorPower T d) M).val.map l.op
        (atlasTwistedLocalSectionOfCoefficients a M d c j)) = M.val.map l.op (c j) := by
  have h := ((a.frame j).tensorPower d).tensorModuleCoefficients_restrict M (𝟙 _) l
    (atlasTwistedLocalSectionOfCoefficients a M d c j)
  simpa only [Category.comp_id, atlasTwistedLocalSectionOfCoefficients,
    LinearEquiv.apply_symm_apply] using h

/-- True pair-overlap lift identities restrict to every actual smaller open. -/
theorem atlasTwistedLocalSectionLift_identity_restrict
    (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (z : bundlePowerGlobalSections T d) (i : a.I) (s : bundleSections M (a.opens i))
    (c : ∀ j, bundleSections M (a.opens j))
    (hc : ∀ j, M.val.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op (c j) =
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z) •
      M.val.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op s)
    (j : a.I) {V : X.Opens} (hj : V ≤ a.opens j) (hi : V ≤ a.opens i) :
    M.val.map (homOfLE hj).op (c j) =
      X.sheaf.obj.map (homOfLE hj).op (atlasPowerGlobalCoefficients a d j z) •
        M.val.map (homOfLE hi).op s := by
  let w : V ⟶ a.opens j ⊓ a.opens i := homOfLE (le_inf hj hi)
  have h := congrArg (fun t => M.val.map w.op t) (hc j)
  rw [M.val.map_smul] at h
  have hl : (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op ≫ w.op =
      (homOfLE hj).op := Subsingleton.elim _ _
  have hr : (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op ≫ w.op =
      (homOfLE hi).op := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hl,
    ← PresheafOfModules.map_comp_apply, hr] at h
  have he : X.sheaf.obj.map w.op
      (X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z)) =
      X.sheaf.obj.map (homOfLE hj).op (atlasPowerGlobalCoefficients a d j z) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hl]
  exact h.trans (congrArg (fun r : X.sheaf.obj.obj (op V) =>
    r • M.val.map (homOfLE hi).op s) he)

/-- The real inverse-frame lifts have the prescribed actual source-chart coefficients wherever that chart meets them. -/
theorem atlasTwistedLocalSectionOfCoefficients_source_frame
    (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (z : bundlePowerGlobalSections T d) (i : a.I) (hz : atlasPowerGlobalCoefficients a d i z = 1)
    (s : bundleSections M (a.opens i)) (c : ∀ j, bundleSections M (a.opens j))
    (hc : ∀ j, M.val.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op (c j) =
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z) •
      M.val.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op s)
    (j : a.I) {V : X.Opens} (hj : V ≤ a.opens j) (hi : V ≤ a.opens i) :
    ((a.frame i).tensorPower d).tensorModuleCoefficients M (homOfLE hi)
      ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE hj).op
        (atlasTwistedLocalSectionOfCoefficients a M d c j)) =
      M.val.map (homOfLE hi).op s := by
  have hs : X.sheaf.obj.map (homOfLE hi).op (atlasPowerGlobalCoefficients a d i z) =
      (localBundleFrameTransition (a.frame j) (a.frame i) (homOfLE hj) (homOfLE hi) :
        X.sheaf.obj.obj (op V)) ^ d *
        X.sheaf.obj.map (homOfLE hj).op (atlasPowerGlobalCoefficients a d j z) :=
    LocalBundleFrame.global_coefficients_transition (a.frame j) (a.frame i)
      (homOfLE hj) (homOfLE hi) d z
  have he : (localBundleFrameTransition (a.frame j) (a.frame i) (homOfLE hj) (homOfLE hi) :
        X.sheaf.obj.obj (op V)) ^ d *
      X.sheaf.obj.map (homOfLE hj).op (atlasPowerGlobalCoefficients a d j z) = 1 := by
    rw [hz, map_one] at hs
    exact hs.symm
  rw [LocalBundleFrame.tensorModuleCoefficients_transition
    ((a.frame j).tensorPower d) ((a.frame i).tensorPower d) M (homOfLE hj) (homOfLE hi),
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val,
    atlasTwistedLocalSectionOfCoefficients_restrict,
    atlasTwistedLocalSectionLift_identity_restrict a M d z i s c hc j hj hi,
    ← mul_smul, he, one_smul]

/-- The actual reconstructed local lifts agree on every true common subopen of the source chart. -/
theorem atlasTwistedLocalSectionOfCoefficients_eq_on_source
    (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (z : bundlePowerGlobalSections T d) (i : a.I) (hz : atlasPowerGlobalCoefficients a d i z = 1)
    (s : bundleSections M (a.opens i)) (c : ∀ j, bundleSections M (a.opens j))
    (hc : ∀ j, M.val.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op (c j) =
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z) •
      M.val.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op s)
    (j k : a.I) {V : X.Opens} (hj : V ≤ a.opens j) (hk : V ≤ a.opens k) (hi : V ≤ a.opens i) :
    (bundleTensor (bundleTensorPower T d) M).val.map (homOfLE hj).op
      (atlasTwistedLocalSectionOfCoefficients a M d c j) =
    (bundleTensor (bundleTensorPower T d) M).val.map (homOfLE hk).op
      (atlasTwistedLocalSectionOfCoefficients a M d c k) := by
  apply (((a.frame i).tensorPower d).tensorModuleCoefficients M (homOfLE hi)).injective
  rw [atlasTwistedLocalSectionOfCoefficients_source_frame a M d z i hz s c hc j hj hi,
    atlasTwistedLocalSectionOfCoefficients_source_frame a M d z i hz s c hc k hk hi]

/-- The literal actual overlap errors of the genuine lifts vanish on the true source triple overlap. -/
theorem atlasTwistedLocalSectionError_zero_on_source
    (a : LineBundleAtlas T) (M : X.Modules) (d : ℕ)
    (z : bundlePowerGlobalSections T d) (i : a.I) (hz : atlasPowerGlobalCoefficients a d i z = 1)
    (s : bundleSections M (a.opens i)) (c : ∀ j, bundleSections M (a.opens j))
    (hc : ∀ j, M.val.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op (c j) =
      X.sheaf.obj.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z) •
      M.val.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op s)
    (j k : a.I) :
    M.val.map (homOfLE (show a.opens j ⊓ (a.opens k ⊓ a.opens i) ≤ a.opens j ⊓ a.opens k from
      le_inf inf_le_left (inf_le_right.trans inf_le_left))).op
      (atlasTwistedLocalSectionError a M d (atlasTwistedLocalSectionOfCoefficients a M d c) j k) = 0 := by
  let W := a.opens j ⊓ (a.opens k ⊓ a.opens i)
  let V := a.opens j ⊓ a.opens k
  let v : W ⟶ V := homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left))
  let l : V ⟶ a.opens j := homOfLE inf_le_left
  let q : V ⟶ a.opens k := homOfLE inf_le_right
  let hWj : W ≤ a.opens j := inf_le_left
  let hWk : W ≤ a.opens k := inf_le_right.trans inf_le_left
  let hWi : W ≤ a.opens i := inf_le_right.trans inf_le_right
  let F := bundleTensor (bundleTensorPower T d) M
  let t := atlasTwistedLocalSectionOfCoefficients a M d c
  have he := atlasTwistedLocalSectionOfCoefficients_eq_on_source a M d z i hz s c hc
    j k hWj hWk hWi
  have hl := ((a.frame j).tensorPower d).tensorModuleCoefficients_restrict M l v
    (F.val.map l.op (t j))
  have hq := ((a.frame j).tensorPower d).tensorModuleCoefficients_restrict M l v
    (F.val.map q.op (t k))
  have hj : v ≫ l = homOfLE hWj := Subsingleton.elim _ _
  have hk : v ≫ q = homOfLE hWk := Subsingleton.elim _ _
  rw [hj, ← PresheafOfModules.map_comp_apply] at hl hq
  rw [← op_comp, hj] at hl
  rw [← op_comp, hk] at hq
  change M.val.map v.op (atlasTwistedLocalSectionError a M d t j k) = 0
  unfold atlasTwistedLocalSectionError
  rw [map_sub, ← hl, ← hq, he, sub_self]


end

end SGPT.Foundations.Schemes
