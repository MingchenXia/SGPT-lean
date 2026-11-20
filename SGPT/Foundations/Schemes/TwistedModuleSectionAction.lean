import SGPT.Foundations.Schemes.TwistedModuleFrames
import Mathlib.Algebra.Module.GradedModule

/-! # The actual action on twisted global module sections

The coefficient products below are glued using the actual sheaf axiom and
the actual line-frame transition units.  The module being twisted is an
arbitrary genuine scheme module.  No global generation, finiteness, or graded
representation conclusion is assumed.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}} {T : X.Modules}

/-- Actual global sections of the actual tensor twist. -/
abbrev bundleTwistedGlobalSections (T M : X.Modules) (d : ℕ) : Type u :=
  bundleSections (bundleTensor (bundleTensorPower T d) M) ⊤

/-- Genuine global twisted-module sections have actual module-valued chart coefficients. -/
def atlasTwistedGlobalCoefficients (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (i : a.I) (s : bundleTwistedGlobalSections T M d) :
    bundleSections M (a.opens i) :=
  ((a.frame i).tensorPower d).tensorModuleCoefficients M (𝟙 _)
    ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s)

/-- Actual module-valued coefficients restrict along the genuine sheaf maps. -/
theorem LocalBundleFrame.twisted_global_coefficients_restrict {U V : X.Opens}
    (e : LocalBundleFrame T U) (M : X.Modules) (d : ℕ) (i : V ⟶ U)
    (s : bundleTwistedGlobalSections T M d) :
    (e.tensorPower d).tensorModuleCoefficients M i
        ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s) =
      M.val.map i.op ((e.tensorPower d).tensorModuleCoefficients M (𝟙 _)
        ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s)) := by
  have h := (e.tensorPower d).tensorModuleCoefficients_restrict M (𝟙 U) i
    ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s)
  have hi : (homOfLE (le_top : U ≤ ⊤)).op ≫ i.op =
      (homOfLE (le_top : V ≤ ⊤)).op := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hi] at h
  simpa only [Category.comp_id] using h

/-- The true twisted-module coefficients separate the actual global sections. -/
theorem atlasTwistedGlobalCoefficients_ext (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (s t : bundleTwistedGlobalSections T M d)
    (h : ∀ i, atlasTwistedGlobalCoefficients a M d i s =
      atlasTwistedGlobalCoefficients a M d i t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (bundleTensor (bundleTensorPower T d) M).val.presheaf)
    (bundleTensor (bundleTensorPower T d) M).isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  refine ⟨a.opens i, le_top, hi, ?_⟩
  exact (((a.frame i).tensorPower d).tensorModuleCoefficients M (𝟙 _)).injective (h i)

/-- The actual module-valued coefficients obey the literal power transition law. -/
theorem LocalBundleFrame.twisted_global_coefficients_transition {U V W : X.Opens}
    (e : LocalBundleFrame T U) (f : LocalBundleFrame T V) (M : X.Modules)
    (i : W ⟶ U) (j : W ⟶ V) (d : ℕ) (s : bundleTwistedGlobalSections T M d) :
    M.val.map j.op ((f.tensorPower d).tensorModuleCoefficients M (𝟙 _)
        ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s)) =
      (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) ^ d •
        M.val.map i.op ((e.tensorPower d).tensorModuleCoefficients M (𝟙 _)
          ((bundleTensor (bundleTensorPower T d) M).val.map (homOfLE le_top).op s)) := by
  rw [← LocalBundleFrame.twisted_global_coefficients_restrict f M d j s,
    ← LocalBundleFrame.twisted_global_coefficients_restrict e M d i s,
    LocalBundleFrame.tensorModuleCoefficients_transition,
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val]

/-- The actual local action is the inverse true frame applied to the actual scalar product. -/
def atlasTwistedLocalAction (a : LineBundleAtlas T) (M : X.Modules) (d e : ℕ)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) (i : a.I) :
    bundleSections (bundleTensor (bundleTensorPower T (d + e)) M) (a.opens i) :=
  (((a.frame i).tensorPower (d + e)).tensorModuleCoefficients M (𝟙 _)).symm
    (atlasPowerGlobalCoefficients a d i s • atlasTwistedGlobalCoefficients a M e i t)

/-- Restriction of the actual local action has the literal restricted scalar product. -/
theorem atlasTwistedLocalAction_coefficients_restrict (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e)
    (i : a.I) {V : X.Opens} (j : V ⟶ a.opens i) :
    ((a.frame i).tensorPower (d + e)).tensorModuleCoefficients M j
      ((bundleTensor (bundleTensorPower T (d + e)) M).val.map j.op
        (atlasTwistedLocalAction a M d e s t i)) =
      X.sheaf.obj.map j.op (atlasPowerGlobalCoefficients a d i s) •
        M.val.map j.op (atlasTwistedGlobalCoefficients a M e i t) := by
  have h := ((a.frame i).tensorPower (d + e)).tensorModuleCoefficients_restrict M (𝟙 _) j
    (atlasTwistedLocalAction a M d e s t i)
  simp only [Category.comp_id, atlasTwistedLocalAction, LinearEquiv.apply_symm_apply] at h
  exact h.trans (M.val.map_smul j.op _ _)

/-- True transition powers make the actual local products agree on every actual overlap. -/
theorem atlasTwistedLocalAction_compatible (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) :
    TopCat.Presheaf.IsCompatible (bundleTensor (bundleTensorPower T (d + e)) M).val.presheaf
      a.opens (atlasTwistedLocalAction a M d e s t) := by
  intro i j
  let V := a.opens i ⊓ a.opens j
  let l : V ⟶ a.opens i := homOfLE inf_le_left
  let r : V ⟶ a.opens j := homOfLE inf_le_right
  have hs : X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients a d j s) =
      (localBundleFrameTransition (a.frame i) (a.frame j) l r : X.sheaf.obj.obj (op V)) ^ d *
        X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a d i s) :=
    LocalBundleFrame.global_coefficients_transition (a.frame i) (a.frame j) l r d s
  have ht : M.val.map r.op (atlasTwistedGlobalCoefficients a M e j t) =
      (localBundleFrameTransition (a.frame i) (a.frame j) l r : X.sheaf.obj.obj (op V)) ^ e •
        M.val.map l.op (atlasTwistedGlobalCoefficients a M e i t) :=
    LocalBundleFrame.twisted_global_coefficients_transition (a.frame i) (a.frame j) M l r e t
  change (bundleTensor (bundleTensorPower T (d + e)) M).val.map l.op
      (atlasTwistedLocalAction a M d e s t i) =
    (bundleTensor (bundleTensorPower T (d + e)) M).val.map r.op
      (atlasTwistedLocalAction a M d e s t j)
  apply (((a.frame j).tensorPower (d + e)).tensorModuleCoefficients M r).injective
  rw [LocalBundleFrame.tensorModuleCoefficients_transition
    ((a.frame i).tensorPower (d + e)) ((a.frame j).tensorPower (d + e)) M l r,
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val,
    atlasTwistedLocalAction_coefficients_restrict,
    atlasTwistedLocalAction_coefficients_restrict]
  rw [hs, ht]
  simp only [pow_add, ← mul_smul]
  congr 1
  ring

/-- The true local action glues uniquely to an actual global twisted-module section. -/
theorem atlasTwistedGlobalAction_existsUnique (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) :
    ∃! z : bundleTwistedGlobalSections T M (d + e), ∀ i,
      (bundleTensor (bundleTensorPower T (d + e)) M).val.map (homOfLE le_top).op z =
        atlasTwistedLocalAction a M d e s t i := by
  have hcover : (⊤ : X.Opens) ≤ iSup a.opens := by
    intro x hx
    obtain ⟨i, hi⟩ := a.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let S : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(bundleTensor (bundleTensorPower T (d + e)) M).val.presheaf,
      (bundleTensor (bundleTensorPower T (d + e)) M).isSheaf⟩
  exact TopCat.Sheaf.existsUnique_gluing' S a.opens ⊤ (fun _ => homOfLE le_top) hcover
    (atlasTwistedLocalAction a M d e s t) (atlasTwistedLocalAction_compatible a M d e s t)

/-- Actual global action chosen from its proved unique genuine sheaf gluing. -/
def atlasTwistedGlobalAction (a : LineBundleAtlas T) (M : X.Modules) (d e : ℕ)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) :
    bundleTwistedGlobalSections T M (d + e) :=
  Classical.choose (atlasTwistedGlobalAction_existsUnique a M d e s t).exists

/-- The constructed global action restricts to the actual local products. -/
theorem atlasTwistedGlobalAction_restrict (a : LineBundleAtlas T) (M : X.Modules) (d e : ℕ)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) (i : a.I) :
    (bundleTensor (bundleTensorPower T (d + e)) M).val.map (homOfLE le_top).op
        (atlasTwistedGlobalAction a M d e s t) = atlasTwistedLocalAction a M d e s t i :=
  Classical.choose_spec (atlasTwistedGlobalAction_existsUnique a M d e s t).exists i

/-- The actual global action has precisely the actual module-valued coefficient products. -/
theorem atlasTwistedGlobalAction_coefficients (a : LineBundleAtlas T) (M : X.Modules) (d e : ℕ)
    (s : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) (i : a.I) :
    atlasTwistedGlobalCoefficients a M (d + e) i (atlasTwistedGlobalAction a M d e s t) =
      atlasPowerGlobalCoefficients a d i s • atlasTwistedGlobalCoefficients a M e i t := by
  unfold atlasTwistedGlobalCoefficients
  rw [atlasTwistedGlobalAction_restrict]
  exact LinearEquiv.apply_symm_apply _ _

/-- Actual module-valued coefficients preserve addition of actual global sections. -/
theorem atlasTwistedGlobalCoefficients_add (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (i : a.I) (s t : bundleTwistedGlobalSections T M d) :
    atlasTwistedGlobalCoefficients a M d i (s + t) =
      atlasTwistedGlobalCoefficients a M d i s + atlasTwistedGlobalCoefficients a M d i t := by
  simp [atlasTwistedGlobalCoefficients]

/-- The actual zero section has actual zero coefficients. -/
theorem atlasTwistedGlobalCoefficients_zero (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (i : a.I) :
    atlasTwistedGlobalCoefficients a M d i 0 = 0 := by
  simp [atlasTwistedGlobalCoefficients]

/-- Actual coefficients identify sections even across an equality of degree indices. -/
theorem atlasTwistedGlobalCoefficients_heq (a : LineBundleAtlas T) (M : X.Modules)
    {d e : ℕ} (h : d = e) (s : bundleTwistedGlobalSections T M d)
    (t : bundleTwistedGlobalSections T M e)
    (hc : ∀ i, atlasTwistedGlobalCoefficients a M d i s =
      atlasTwistedGlobalCoefficients a M e i t) : HEq s t := by
  subst e
  exact heq_of_eq (atlasTwistedGlobalCoefficients_ext a M d s t hc)

/-- The constructed true global action is additive in the actual module section. -/
theorem atlasTwistedGlobalAction_add_right (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s : bundlePowerGlobalSections T d) (t t' : bundleTwistedGlobalSections T M e) :
    atlasTwistedGlobalAction a M d e s (t + t') =
      atlasTwistedGlobalAction a M d e s t + atlasTwistedGlobalAction a M d e s t' := by
  apply atlasTwistedGlobalCoefficients_ext a M (d + e)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasTwistedGlobalCoefficients_add, smul_add]

/-- The constructed true global action is additive in the actual line section. -/
theorem atlasTwistedGlobalAction_add_left (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s s' : bundlePowerGlobalSections T d) (t : bundleTwistedGlobalSections T M e) :
    atlasTwistedGlobalAction a M d e (s + s') t =
      atlasTwistedGlobalAction a M d e s t + atlasTwistedGlobalAction a M d e s' t := by
  apply atlasTwistedGlobalCoefficients_ext a M (d + e)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasTwistedGlobalCoefficients_add,
    atlasPowerGlobalCoefficients_add, add_smul]

/-- The actual zero module section is annihilated by the true global action. -/
theorem atlasTwistedGlobalAction_zero_right (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (s : bundlePowerGlobalSections T d) :
    atlasTwistedGlobalAction a M d e s 0 = 0 := by
  apply atlasTwistedGlobalCoefficients_ext a M (d + e)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasTwistedGlobalCoefficients_zero, smul_zero]

/-- The actual zero line section acts by zero on the true module section. -/
theorem atlasTwistedGlobalAction_zero_left (a : LineBundleAtlas T) (M : X.Modules)
    (d e : ℕ) (t : bundleTwistedGlobalSections T M e) :
    atlasTwistedGlobalAction a M d e 0 t = 0 := by
  apply atlasTwistedGlobalCoefficients_ext a M (d + e)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasPowerGlobalCoefficients_zero,
    atlasTwistedGlobalCoefficients_zero, zero_smul]

/-- The actual degree-zero structure-ring unit acts identically on genuine twists. -/
theorem atlasTwistedGlobalAction_one_left (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (s : bundleTwistedGlobalSections T M d) :
    HEq (atlasTwistedGlobalAction a M 0 d (bundlePowerGlobalOne T) s) s := by
  apply atlasTwistedGlobalCoefficients_heq a M (Nat.zero_add d)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasPowerGlobalCoefficients_one, one_smul]

/-- The true action is associative with the actual global multiplication of line sections. -/
theorem atlasTwistedGlobalAction_assoc (a : LineBundleAtlas T) (M : X.Modules)
    (d e f : ℕ) (s : bundlePowerGlobalSections T d) (t : bundlePowerGlobalSections T e)
    (z : bundleTwistedGlobalSections T M f) :
    HEq (atlasTwistedGlobalAction a M (d + e) f (atlasPowerGlobalMul a d e s t) z)
      (atlasTwistedGlobalAction a M d (e + f) s (atlasTwistedGlobalAction a M e f t z)) := by
  apply atlasTwistedGlobalCoefficients_heq a M (Nat.add_assoc d e f)
  intro i
  simp only [atlasTwistedGlobalAction_coefficients, atlasPowerGlobalMul_coefficients, mul_smul]

/-- The true twisted global sections form a native graded module over the actual
line section ring, with every action law proved from actual coefficient gluing. -/
@[instance_reducible]
def atlasTwistedGradedModule (a : LineBundleAtlas T) (M : X.Modules) :
    let _ := atlasPowerGradedCommRing a
    DirectSum.Gmodule (bundlePowerGlobalSections T) (bundleTwistedGlobalSections T M) := by
  let _ := atlasPowerGradedCommRing a
  let _ : GradedMonoid.GSMul (bundlePowerGlobalSections T) (bundleTwistedGlobalSections T M) :=
    ⟨fun {d e} => atlasTwistedGlobalAction a M d e⟩
  exact {
    smul {d e} := atlasTwistedGlobalAction a M d e
    smul_add := fun s t t' => atlasTwistedGlobalAction_add_right a M _ _ s t t'
    smul_zero := fun s => atlasTwistedGlobalAction_zero_right a M _ _ s
    add_smul := fun s s' t => atlasTwistedGlobalAction_add_left a M _ _ s s' t
    zero_smul := fun t => atlasTwistedGlobalAction_zero_left a M _ _ t
    one_smul := by
      rintro ⟨d, s⟩
      exact Sigma.ext (Nat.zero_add d) (atlasTwistedGlobalAction_one_left a M d s)
    mul_smul := by
      rintro ⟨d, s⟩ ⟨e, t⟩ ⟨f, z⟩
      exact Sigma.ext (Nat.add_assoc d e f) (atlasTwistedGlobalAction_assoc a M d e f s t z)
  }

/-- The actual direct sum of the genuine tensor-twisted section modules. -/
def IntrinsicLineBundle.twistedSectionModule (L : IntrinsicLineBundle X) (M : X.Modules) : Type u :=
  ⨁ d : ℕ, bundleTwistedGlobalSections L.sheaf M d

/-- Addition is the actual native direct-sum additive group. -/
instance intrinsicLineBundleTwistedSectionModuleAddCommGroup (L : IntrinsicLineBundle X)
    (M : X.Modules) : AddCommGroup (L.twistedSectionModule M) :=
  inferInstanceAs (AddCommGroup (⨁ d : ℕ, bundleTwistedGlobalSections L.sheaf M d))

/-- The actual line section ring acts on the actual twisted section direct sum. -/
instance intrinsicLineBundleTwistedSectionModuleModule (L : IntrinsicLineBundle X) (M : X.Modules) :
    Module L.sectionRing (L.twistedSectionModule M) := by
  let _ := atlasPowerGradedCommRing L.atlas
  let _ := atlasTwistedGradedModule L.atlas M
  exact inferInstanceAs
    (Module (⨁ d : ℕ, bundlePowerGlobalSections L.sheaf d)
      (⨁ d : ℕ, bundleTwistedGlobalSections L.sheaf M d))

/-- The true homogeneous-degree inclusion into the actual twisted section direct sum. -/
def IntrinsicLineBundle.ofTwistedSection (L : IntrinsicLineBundle X) (M : X.Modules) (d : ℕ) :
    bundleTwistedGlobalSections L.sheaf M d →+ L.twistedSectionModule M :=
  DirectSum.of (bundleTwistedGlobalSections L.sheaf M) d

/-- Homogeneous inclusion is faithful for every actual twisted degree. -/
theorem IntrinsicLineBundle.ofTwistedSection_injective (L : IntrinsicLineBundle X)
    (M : X.Modules) (d : ℕ) : Function.Injective (L.ofTwistedSection M d) :=
  DirectSum.of_injective (β := bundleTwistedGlobalSections L.sheaf M) d

/-- The actual ordinary scalar action agrees with the actual homogeneous global section action. -/
theorem IntrinsicLineBundle.ofSection_smul_ofTwistedSection (L : IntrinsicLineBundle X)
    (M : X.Modules) (d e : ℕ) (s : bundlePowerGlobalSections L.sheaf d)
    (t : bundleTwistedGlobalSections L.sheaf M e) :
    L.ofSection d s • L.ofTwistedSection M e t =
      L.ofTwistedSection M (d + e) (atlasTwistedGlobalAction L.atlas M d e s t) := by
  let _ := atlasPowerGradedCommRing L.atlas
  let _ := atlasTwistedGradedModule L.atlas M
  exact DirectSum.Gmodule.of_smul_of (bundlePowerGlobalSections L.sheaf)
    (bundleTwistedGlobalSections L.sheaf M) s t

/-- True module-valued chart coefficients retain the actual global regular-section action. -/
theorem atlasTwistedGlobalCoefficients_smul (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (i : a.I) (r : X.sheaf.obj.obj (op ⊤))
    (s : bundleTwistedGlobalSections T M d) :
    atlasTwistedGlobalCoefficients a M d i (r • s) =
      X.sheaf.obj.map (homOfLE (le_top : a.opens i ≤ ⊤)).op r •
        atlasTwistedGlobalCoefficients a M d i s := by
  have h := (bundleTensor (bundleTensorPower T d) M).val.map_smul
    (homOfLE (le_top : a.opens i ≤ ⊤)).op r s
  exact (congrArg (((a.frame i).tensorPower d).tensorModuleCoefficients M (𝟙 _)) h).trans
    ((((a.frame i).tensorPower d).tensorModuleCoefficients M (𝟙 _)).map_smul _ _)

/-- The degree-zero action is the native scalar action of genuine global regular sections. -/
theorem atlasTwistedGlobalAction_regular_scalar (a : LineBundleAtlas T) (M : X.Modules)
    (d : ℕ) (r : X.sheaf.obj.obj (op ⊤)) (s : bundleTwistedGlobalSections T M d) :
    HEq (atlasTwistedGlobalAction a M 0 d r s) (r • s) := by
  apply atlasTwistedGlobalCoefficients_heq a M (Nat.zero_add d)
  intro i
  calc
    atlasTwistedGlobalCoefficients a M (0 + d) i (atlasTwistedGlobalAction a M 0 d r s) =
        atlasPowerGlobalCoefficients a 0 i r • atlasTwistedGlobalCoefficients a M d i s :=
      atlasTwistedGlobalAction_coefficients a M 0 d r s i
    _ = X.sheaf.obj.map (homOfLE le_top).op r • atlasTwistedGlobalCoefficients a M d i s :=
      congrArg (fun q => q • atlasTwistedGlobalCoefficients a M d i s)
        (atlasPowerGlobalCoefficients_degree_zero a i r)
    _ = atlasTwistedGlobalCoefficients a M d i (r • s) :=
      (atlasTwistedGlobalCoefficients_smul a M d i r s).symm

/-- Native homogeneous inclusions respect the actual regular-section scalar action. -/
theorem IntrinsicLineBundle.ofSection_constant_smul_ofTwistedSection
    (L : IntrinsicLineBundle X) (M : X.Modules) (d : ℕ) (r : Γ(X, ⊤))
    (s : bundleTwistedGlobalSections L.sheaf M d) :
    L.ofSection 0 r • L.ofTwistedSection M d s = L.ofTwistedSection M d (r • s) := by
  calc
    L.ofSection 0 r • L.ofTwistedSection M d s =
        L.ofTwistedSection M (0 + d) (atlasTwistedGlobalAction L.atlas M 0 d r s) :=
      L.ofSection_smul_ofTwistedSection M 0 d r s
    _ = L.ofTwistedSection M d (r • s) :=
      DirectSum.of_eq_of_gradedMonoid_eq
        (Sigma.ext (Nat.zero_add d) (atlasTwistedGlobalAction_regular_scalar L.atlas M d r s))

/-- The structural field acts through its actual degree-zero regular sections. -/
@[instance_reducible]
def IntrinsicLineBundle.twistedSectionModuleBaseModule {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (M : X.Modules) (f : X ⟶ Spec (.of K)) :
    Module K (L.twistedSectionModule M) :=
  Module.compHom (L.twistedSectionModule M) (L.sectionRingBaseMap f)

/-- The constructed structural field action has the literal actual constant action on each degree. -/
theorem IntrinsicLineBundle.twistedSectionModuleBase_smul_ofTwistedSection {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (M : X.Modules) (f : X ⟶ Spec (.of K)) (d : ℕ) (c : K)
    (s : bundleTwistedGlobalSections L.sheaf M d) :
    let _ := L.twistedSectionModuleBaseModule M f
    c • L.ofTwistedSection M d s = L.ofTwistedSection M d ((schemeConstantMap f c) • s) := by
  let _ := L.twistedSectionModuleBaseModule M f
  change L.ofSection 0 (schemeConstantMap f c) • L.ofTwistedSection M d s = _
  exact L.ofSection_constant_smul_ofTwistedSection M d (schemeConstantMap f c) s

end

end SGPT.Foundations.Schemes
