import SGPT.Foundations.Schemes.BundleTensorLocalization
import SGPT.Foundations.Schemes.SchemeConstants
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.DirectSum.Algebra

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

variable {X : Scheme.{u}}

/-- The native section module, expressed over the actual global structure
ring so scalar inference retains the literal scheme section notation. -/
instance bundlePowerGlobalSectionsModule (L : X.Modules) (n : ℕ) :
    Module Γ(X, ⊤) (bundlePowerGlobalSections L n) :=
  bundleSectionsModule (bundleTensorPower L n) ⊤

set_option backward.isDefEq.respectTransparency false in
/-- The constructed open-site recovery isomorphism has the actual adjunction
counit as its forward map. -/
theorem bundleOverCounitIso_hom (U : X.Opens)
    (S : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    (bundleOverCounitIso U S).hom =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app S := by
  unfold bundleOverCounitIso
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse open comparison is the actual adjoint lift of the restricted
global sheafification unit. -/
theorem bundleOverSheafificationIso_inv (P : X.PresheafOfModules) (U : X.Opens) :
    (bundleOverSheafificationIso P U).inv =
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
        (bundleSheafificationOverMap P U) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U) := by
  unfold bundleOverSheafificationIso
  simp only [Iso.symm_inv, Iso.trans_hom, asIso_hom, bundleOverCounitIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison corresponds to the restricted unit under the
actual open-site sheafification adjunction. -/
theorem bundleOverSheafificationIso_inv_homEquiv (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
      (bundlePresheafOver P U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)
      (bundleOverSheafificationIso P U).inv = bundleSheafificationOverMap P U := by
  rw [bundleOverSheafificationIso_inv]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv (bundlePresheafOver P U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)
      |>.apply_symm_apply
      (bundleSheafificationOverMap P U)

set_option backward.isDefEq.respectTransparency false in
/-- The open comparison carries the restricted global unit to the local unit. -/
theorem bundleOverSheafificationIso_unit (P : X.PresheafOfModules) (U : X.Opens) :
    bundleSheafificationOverMap P U ≫ (bundleOverSheafificationIso P U).hom.val =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (bundlePresheafOver P U) := by
  have h := bundleOverSheafificationIso_inv_homEquiv P U
  rw [Adjunction.homEquiv_apply] at h
  rw [← h, Category.assoc]
  change _ ≫ (bundleOverSheafificationIso P U).inv.val ≫
    (bundleOverSheafificationIso P U).hom.val = _
  rw [← SheafOfModules.comp_val, Iso.inv_hom_id]
  rfl

local instance (U : X.Opens) :
    MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
  PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ X.sheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor-frame map before sheafification. -/
def tensorFramePresheafIso {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    bundlePresheafOver (bundleTensorPresheaf L N) U ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
  bundleOverTensorPresheafIso L N U ≪≫
    MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f) ≪≫
    MonoidalCategory.leftUnitor (SheafOfModules.unit (X.ringCatSheaf.over U)).val

set_option backward.isDefEq.respectTransparency false in
/-- The constructed tensor frame is the actual adjoint lift of its tensor
coefficient map, transported across open restriction. -/
theorem LocalBundleFrame.tensor_hom {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    (e.tensor f).hom =
      (bundleOverSheafificationIso (bundleTensorPresheaf L N) U).hom ≫
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
        (tensorFramePresheafIso e f).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  unfold LocalBundleFrame.tensor tensorFramePresheafIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, bundleOverCounitIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Applying the tensor frame to the actual sheafification unit recovers the
presheaf tensor coefficient morphism. -/
theorem LocalBundleFrame.tensor_unit {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    bundleSheafificationOverMap (bundleTensorPresheaf L N) U ≫ (e.tensor f).hom.val =
      (tensorFramePresheafIso e f).hom := by
  rw [LocalBundleFrame.tensor_hom]
  simp only [SheafOfModules.comp_val]
  rw [← Category.assoc, ← Category.assoc, bundleOverSheafificationIso_unit, Category.assoc]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
      (bundlePresheafOver (bundleTensorPresheaf L N) U)
      (SheafOfModules.unit (X.ringCatSheaf.over U)) |>.apply_symm_apply
        (tensorFramePresheafIso e f).hom

set_option backward.isDefEq.respectTransparency false in
/-- The actual presheaf tensor-frame map multiplies pure-tensor coefficients. -/
theorem tensorFramePresheafIso_tmul {L N : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) (i : V ⟶ U)
    (s : bundleSections L V) (t : bundleSections N V) :
    ((tensorFramePresheafIso e f).hom.app (op (Over.mk i))).hom
      (s ⊗ₜ[X.sheaf.obj.obj (op V)] t) = e.coefficients i s * f.coefficients i t := by
  change (MonoidalCategory.leftUnitor
    (ModuleCat.of (X.sheaf.obj.obj (op V)) (X.sheaf.obj.obj (op V)))).hom
      (e.coefficients i s ⊗ₜ[X.sheaf.obj.obj (op V)] f.coefficients i t) = _
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed local tensor frame multiplies coefficients of the actual
sheafified pure-tensor section. -/
theorem LocalBundleFrame.tensor_coefficients {L N : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) (i : V ⟶ U)
    (s : bundleSections L V) (t : bundleSections N V) :
    (e.tensor f).coefficients i (tensorSection L N V s t) =
      e.coefficients i s * f.coefficients i t := by
  have h := congrArg (fun q => (q.app (op (Over.mk i))).hom
    (s ⊗ₜ[X.sheaf.obj.obj (op V)] t)) (e.tensor_unit f)
  exact h.trans (tensorFramePresheafIso_tmul e f i s t)

/-- Tensor-frame transitions are the products of the actual transition units
on every common smaller open. -/
theorem localBundleFrameTransition_tensor {L N : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U)
    (e' : LocalBundleFrame L V) (f' : LocalBundleFrame N V) (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition (e.tensor f) (e'.tensor f') i j =
      localBundleFrameTransition e e' i j * localBundleFrameTransition f f' i j := by
  let s : bundleSections L W := (e.coefficients i).symm 1
  let t : bundleSections N W := (f.coefficients i).symm 1
  have h := localBundleFrameTransition_coefficients (e.tensor f) (e'.tensor f') i j
    (tensorSection L N W s t)
  rw [LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensor_coefficients,
    localBundleFrameTransition_coefficients e e' i j,
    localBundleFrameTransition_coefficients f f' i j] at h
  simp only [s, t, LinearEquiv.apply_symm_apply, mul_one] at h
  apply Units.ext
  exact h.symm

/-- The transition of the genuinely constructed `n`th power frame is the
`n`th power of the original transition unit. -/
theorem localBundleFrameTransition_tensorPower {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) (n : ℕ) :
    localBundleFrameTransition (e.tensorPower n) (f.tensorPower n) i j =
      localBundleFrameTransition e f i j ^ n := by
  induction n with
  | zero =>
      apply Units.ext
      simp [localBundleFrameTransition, LocalBundleFrame.tensorPower,
        LocalBundleFrame.coefficients, sectionFrameTransition, rankOneAutomorphismUnit]
      rfl
  | succ n ih =>
      change localBundleFrameTransition ((e.tensorPower n).tensor e)
        ((f.tensorPower n).tensor f) i j = _
      rw [localBundleFrameTransition_tensor, ih, pow_succ]

/-- Power-frame coefficients on overlaps transform by the derived transition
unit to the actual degree. -/
theorem LocalBundleFrame.tensorPower_coefficients_transition {L : X.Modules}
    {U V W : X.Opens} (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) (n : ℕ) (s : bundleSections (bundleTensorPower L n) W) :
    (f.tensorPower n).coefficients j s =
      (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) ^ n *
        (e.tensorPower n).coefficients i s := by
  rw [localBundleFrameTransition_coefficients,
    localBundleFrameTransition_tensorPower, Units.val_pow_eq_pow_val]

/-- Actual chart coefficients of a global section, using the coherent frame
of the indicated tensor power. -/
def atlasPowerGlobalCoefficients {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (i : a.I) (s : bundlePowerGlobalSections L n) : X.sheaf.obj.obj (op (a.opens i)) :=
  ((a.frame i).tensorPower n).coefficients (𝟙 _)
    ((bundleTensorPower L n).val.map (homOfLE le_top).op s)

/-- Global chart coefficients commute with genuine smaller-open restrictions. -/
theorem LocalBundleFrame.global_coefficients_restrict {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (n : ℕ) (i : V ⟶ U) (s : bundlePowerGlobalSections L n) :
    (e.tensorPower n).coefficients i
      ((bundleTensorPower L n).val.map (homOfLE le_top).op s) =
    X.sheaf.obj.map i.op ((e.tensorPower n).coefficients (𝟙 _)
      ((bundleTensorPower L n).val.map (homOfLE le_top).op s)) := by
  have h := (e.tensorPower n).coefficients_restrict (𝟙 U) i
    ((bundleTensorPower L n).val.map (homOfLE le_top).op s)
  have hi : (homOfLE (le_top : U ≤ ⊤)).op ≫ i.op =
      (homOfLE (le_top : V ≤ ⊤)).op := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hi] at h
  simpa only [Category.comp_id] using h

/-- Actual global sections are separated by their atlas coefficients. -/
theorem atlasPowerGlobalCoefficients_ext {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s t : bundlePowerGlobalSections L n)
    (h : ∀ i, atlasPowerGlobalCoefficients a n i s = atlasPowerGlobalCoefficients a n i t) :
    s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (bundleTensorPower L n).val.presheaf) (bundleTensorPower L n).isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  refine ⟨a.opens i, le_top, hi, ?_⟩
  exact (((a.frame i).tensorPower n).coefficients (𝟙 _)).injective (h i)

/-- Local multiplication is the inverse power frame applied to the actual
product of the two global coefficient functions. -/
def atlasPowerLocalProduct {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) (i : a.I) :
    bundleSections (bundleTensorPower L (m + n)) (a.opens i) :=
  (((a.frame i).tensorPower (m + n)).coefficients (𝟙 _)).symm
    (atlasPowerGlobalCoefficients a m i s * atlasPowerGlobalCoefficients a n i t)

/-- The actual global coefficient functions obey the power transition law
after restriction to every common smaller open. -/
theorem LocalBundleFrame.global_coefficients_transition {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    (n : ℕ) (s : bundlePowerGlobalSections L n) :
    X.sheaf.obj.map j.op ((f.tensorPower n).coefficients (𝟙 _)
      ((bundleTensorPower L n).val.map (homOfLE le_top).op s)) =
    (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) ^ n *
      X.sheaf.obj.map i.op ((e.tensorPower n).coefficients (𝟙 _)
        ((bundleTensorPower L n).val.map (homOfLE le_top).op s)) := by
  rw [← LocalBundleFrame.global_coefficients_restrict f n j s,
    ← LocalBundleFrame.global_coefficients_restrict e n i s]
  exact LocalBundleFrame.tensorPower_coefficients_transition e f i j n _

/-- Restricting a local product gives the corresponding restricted product
in the genuine power-frame coordinates. -/
theorem atlasPowerLocalProduct_coefficients_restrict {L : X.Modules}
    (a : LineBundleAtlas L) (m n : ℕ) (s : bundlePowerGlobalSections L m)
    (t : bundlePowerGlobalSections L n) (i : a.I) {W : X.Opens} (j : W ⟶ a.opens i) :
    ((a.frame i).tensorPower (m + n)).coefficients j
      ((bundleTensorPower L (m + n)).val.map j.op (atlasPowerLocalProduct a m n s t i)) =
    X.sheaf.obj.map j.op
      (atlasPowerGlobalCoefficients a m i s * atlasPowerGlobalCoefficients a n i t) := by
  have h := ((a.frame i).tensorPower (m + n)).coefficients_restrict (𝟙 _) j
    (atlasPowerLocalProduct a m n s t i)
  simpa only [Category.comp_id, atlasPowerLocalProduct, LinearEquiv.apply_symm_apply] using h

/-- Power transitions make the actual local coefficient products agree on
all pairwise overlaps, so they satisfy the sheaf gluing condition. -/
theorem atlasPowerLocalProduct_compatible {L : X.Modules} (a : LineBundleAtlas L)
    (m n : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) :
    TopCat.Presheaf.IsCompatible (bundleTensorPower L (m + n)).val.presheaf a.opens
      (atlasPowerLocalProduct a m n s t) := by
  intro i j
  let l : a.opens i ⊓ a.opens j ⟶ a.opens i := homOfLE inf_le_left
  let r : a.opens i ⊓ a.opens j ⟶ a.opens j := homOfLE inf_le_right
  let u : X.sheaf.obj.obj (op (a.opens i ⊓ a.opens j)) :=
    localBundleFrameTransition (a.frame i) (a.frame j) l r
  have hm := LocalBundleFrame.global_coefficients_transition (a.frame i) (a.frame j) l r m s
  have hn := LocalBundleFrame.global_coefficients_transition (a.frame i) (a.frame j) l r n t
  change X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients a m j s) =
    u ^ m * X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a m i s) at hm
  change X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients a n j t) =
    u ^ n * X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a n i t) at hn
  apply (((a.frame j).tensorPower (m + n)).coefficients r).injective
  calc
    ((a.frame j).tensorPower (m + n)).coefficients r
        ((bundleTensorPower L (m + n)).val.map l.op (atlasPowerLocalProduct a m n s t i)) =
        u ^ (m + n) * ((a.frame i).tensorPower (m + n)).coefficients l
          ((bundleTensorPower L (m + n)).val.map l.op (atlasPowerLocalProduct a m n s t i)) :=
      LocalBundleFrame.tensorPower_coefficients_transition (a.frame i) (a.frame j) l r _ _
    _ = u ^ (m + n) * X.sheaf.obj.map l.op
          (atlasPowerGlobalCoefficients a m i s * atlasPowerGlobalCoefficients a n i t) := by
      rw [atlasPowerLocalProduct_coefficients_restrict]
    _ = (u ^ m * X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a m i s)) *
          (u ^ n * X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a n i t)) := by
      rw [map_mul, pow_add]
      ring
    _ = X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients a m j s) *
          X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients a n j t) := by rw [hm, hn]
    _ = X.sheaf.obj.map r.op
          (atlasPowerGlobalCoefficients a m j s * atlasPowerGlobalCoefficients a n j t) :=
      (map_mul _ _ _).symm
    _ = ((a.frame j).tensorPower (m + n)).coefficients r
          ((bundleTensorPower L (m + n)).val.map r.op (atlasPowerLocalProduct a m n s t j)) :=
      (atlasPowerLocalProduct_coefficients_restrict a m n s t j r).symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual global multiplication exists uniquely by the sheaf condition. -/
theorem atlasPowerGlobalProduct_existsUnique {L : X.Modules} (a : LineBundleAtlas L)
    (m n : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) :
    ∃! z : bundlePowerGlobalSections L (m + n), ∀ i,
      (bundleTensorPower L (m + n)).val.map (homOfLE le_top).op z =
        atlasPowerLocalProduct a m n s t i := by
  have hcover : (⊤ : X.Opens) ≤ iSup a.opens := by
    intro x hx
    obtain ⟨i, hi⟩ := a.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let S : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(bundleTensorPower L (m + n)).val.presheaf, (bundleTensorPower L (m + n)).isSheaf⟩
  exact TopCat.Sheaf.existsUnique_gluing' S
    a.opens ⊤ (fun _ => homOfLE le_top) hcover
    (atlasPowerLocalProduct a m n s t) (atlasPowerLocalProduct_compatible a m n s t)

/-- Multiplication of actual global sections, chosen from their proved unique
sheaf gluing. -/
def atlasPowerGlobalMul {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) :
    bundlePowerGlobalSections L (m + n) :=
  Classical.choose (atlasPowerGlobalProduct_existsUnique a m n s t).exists

/-- The constructed global product restricts to the actual local products. -/
theorem atlasPowerGlobalMul_restrict {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) (i : a.I) :
    (bundleTensorPower L (m + n)).val.map (homOfLE le_top).op (atlasPowerGlobalMul a m n s t) =
      atlasPowerLocalProduct a m n s t i :=
  Classical.choose_spec (atlasPowerGlobalProduct_existsUnique a m n s t).exists i

/-- The global product has the actual products as all of its chart coefficients. -/
theorem atlasPowerGlobalMul_coefficients {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) (i : a.I) :
    atlasPowerGlobalCoefficients a (m + n) i (atlasPowerGlobalMul a m n s t) =
      atlasPowerGlobalCoefficients a m i s * atlasPowerGlobalCoefficients a n i t := by
  unfold atlasPowerGlobalCoefficients
  rw [atlasPowerGlobalMul_restrict]
  exact LinearEquiv.apply_symm_apply _ _

/-- The actual chart coefficient functions preserve addition. -/
theorem atlasPowerGlobalCoefficients_add {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (i : a.I) (s t : bundlePowerGlobalSections L n) :
    atlasPowerGlobalCoefficients a n i (s + t) =
      atlasPowerGlobalCoefficients a n i s + atlasPowerGlobalCoefficients a n i t := by
  simp [atlasPowerGlobalCoefficients]
  exact (((a.frame i).tensorPower n).coefficients (𝟙 _)).map_add _ _

/-- The actual chart coefficient functions preserve zero. -/
theorem atlasPowerGlobalCoefficients_zero {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (i : a.I) : atlasPowerGlobalCoefficients a n i 0 = 0 := by
  simp [atlasPowerGlobalCoefficients]
  exact (((a.frame i).tensorPower n).coefficients (𝟙 _)).map_zero

/-- The zero-degree frame is the actual structure-sheaf identity frame. -/
theorem LocalBundleFrame.tensorPower_zero_coefficients {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (s : bundleSections (bundleTensorPower L 0) V) :
    (e.tensorPower 0).coefficients i s = s := by
  rfl

/-- The actual structure-ring unit, as a global section of the zero power. -/
def bundlePowerGlobalOne (L : X.Modules) : bundlePowerGlobalSections L 0 :=
  (1 : X.sheaf.obj.obj (op ⊤))

set_option backward.isDefEq.respectTransparency false in
/-- The actual global unit has coefficient one on every chart. -/
theorem atlasPowerGlobalCoefficients_one {L : X.Modules} (a : LineBundleAtlas L) (i : a.I) :
    atlasPowerGlobalCoefficients a 0 i (bundlePowerGlobalOne L) = 1 := by
  exact (LocalBundleFrame.tensorPower_zero_coefficients (a.frame i) (𝟙 _)
    ((bundleTensorPower L 0).val.map (homOfLE le_top).op (bundlePowerGlobalOne L))).trans
    (X.sheaf.obj.map (homOfLE (le_top : a.opens i ≤ ⊤)).op).hom.map_one

/-- Equality of degrees and actual coefficients implies equality of the
homogeneous sections, including their dependent types. -/
theorem atlasPowerGlobalCoefficients_heq {L : X.Modules} (a : LineBundleAtlas L)
    {m n : ℕ} (h : m = n) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n)
    (hcoeff : ∀ i, atlasPowerGlobalCoefficients a m i s = atlasPowerGlobalCoefficients a n i t) :
    HEq s t := by
  cases h
  exact heq_of_eq (atlasPowerGlobalCoefficients_ext a m s t hcoeff)

theorem atlasPowerGlobalMul_zero_right {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) : atlasPowerGlobalMul a m n s 0 = 0 := by
  apply atlasPowerGlobalCoefficients_ext a (m + n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_zero, mul_zero]

theorem atlasPowerGlobalMul_zero_left {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (t : bundlePowerGlobalSections L n) : atlasPowerGlobalMul a m n 0 t = 0 := by
  apply atlasPowerGlobalCoefficients_ext a (m + n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_zero, zero_mul]

theorem atlasPowerGlobalMul_add_right {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t u : bundlePowerGlobalSections L n) :
    atlasPowerGlobalMul a m n s (t + u) =
      atlasPowerGlobalMul a m n s t + atlasPowerGlobalMul a m n s u := by
  apply atlasPowerGlobalCoefficients_ext a (m + n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_add, mul_add]

theorem atlasPowerGlobalMul_add_left {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s t : bundlePowerGlobalSections L m) (u : bundlePowerGlobalSections L n) :
    atlasPowerGlobalMul a m n (s + t) u =
      atlasPowerGlobalMul a m n s u + atlasPowerGlobalMul a m n t u := by
  apply atlasPowerGlobalCoefficients_ext a (m + n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_add, add_mul]

/-- Associativity is proved from actual coefficient multiplication, including
the necessary identification of tensor-power degrees. -/
theorem atlasPowerGlobalMul_assoc {L : X.Modules} (a : LineBundleAtlas L) (m n p : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n)
    (u : bundlePowerGlobalSections L p) :
    HEq (atlasPowerGlobalMul a (m + n) p (atlasPowerGlobalMul a m n s t) u)
      (atlasPowerGlobalMul a m (n + p) s (atlasPowerGlobalMul a n p t u)) := by
  apply atlasPowerGlobalCoefficients_heq a (Nat.add_assoc m n p)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, mul_assoc]

theorem atlasPowerGlobalMul_comm {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n) :
    HEq (atlasPowerGlobalMul a m n s t) (atlasPowerGlobalMul a n m t s) := by
  apply atlasPowerGlobalCoefficients_heq a (Nat.add_comm m n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, mul_comm]

theorem atlasPowerGlobalMul_one_left {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) :
    HEq (atlasPowerGlobalMul a 0 n (bundlePowerGlobalOne L) s) s := by
  apply atlasPowerGlobalCoefficients_heq a (Nat.zero_add n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_one, one_mul]

theorem atlasPowerGlobalMul_one_right {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) :
    HEq (atlasPowerGlobalMul a n 0 s (bundlePowerGlobalOne L)) s := by
  apply atlasPowerGlobalCoefficients_heq a (Nat.add_zero n)
  intro i
  simp only [atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_one, mul_one]

/-- The actual global tensor-power section spaces form a graded commutative
ring, with multiplication and every coherence law constructed above. -/
@[instance_reducible]
def atlasPowerGradedCommRing {L : X.Modules} (a : LineBundleAtlas L) :
    DirectSum.GCommRing (bundlePowerGlobalSections L) := by
  let : GradedMonoid.GOne (bundlePowerGlobalSections L) := ⟨bundlePowerGlobalOne L⟩
  let : GradedMonoid.GMul (bundlePowerGlobalSections L) :=
    ⟨fun {m n} => atlasPowerGlobalMul a m n⟩
  exact {
  mul {m n} := atlasPowerGlobalMul a m n
  one := bundlePowerGlobalOne L
  mul_zero := fun {m n} s => atlasPowerGlobalMul_zero_right a m n s
  zero_mul := fun {m n} t => atlasPowerGlobalMul_zero_left a m n t
  mul_add := fun {m n} s t u => atlasPowerGlobalMul_add_right a m n s t u
  add_mul := fun {m n} s t u => atlasPowerGlobalMul_add_left a m n s t u
  one_mul := by
    rintro ⟨n, s⟩
    exact Sigma.ext (Nat.zero_add n) (atlasPowerGlobalMul_one_left a n s)
  mul_one := by
    rintro ⟨n, s⟩
    exact Sigma.ext (Nat.add_zero n) (atlasPowerGlobalMul_one_right a n s)
  mul_assoc := by
    rintro ⟨m, s⟩ ⟨n, t⟩ ⟨p, u⟩
    exact Sigma.ext (Nat.add_assoc m n p) (atlasPowerGlobalMul_assoc a m n p s t u)
  mul_comm := by
    rintro ⟨m, s⟩ ⟨n, t⟩
    exact Sigma.ext (Nat.add_comm m n) (atlasPowerGlobalMul_comm a m n s t)
  natCast n := (n : X.sheaf.obj.obj (op ⊤))
  natCast_zero := (show ((0 : ℕ) : X.sheaf.obj.obj (op ⊤)) = 0 from Nat.cast_zero)
  natCast_succ n := (show ((n + 1 : ℕ) : X.sheaf.obj.obj (op ⊤)) =
    (n : X.sheaf.obj.obj (op ⊤)) + 1 from Nat.cast_add_one n)
  intCast z := (z : X.sheaf.obj.obj (op ⊤))
  intCast_ofNat n := (show ((n : ℤ) : X.sheaf.obj.obj (op ⊤)) =
    (n : X.sheaf.obj.obj (op ⊤)) from Int.cast_natCast n)
  intCast_negSucc_ofNat n := (show ((Int.negSucc n : ℤ) : X.sheaf.obj.obj (op ⊤)) =
    -((n + 1 : ℕ) : X.sheaf.obj.obj (op ⊤)) from Int.cast_negSucc n)
  }

/-- The actual direct sum of global sections of an intrinsic line bundle's
tensor powers. -/
def IntrinsicLineBundle.sectionRing (L : IntrinsicLineBundle X) : Type u :=
  ⨁ n : ℕ, bundlePowerGlobalSections L.sheaf n

/-- Its ring operations are induced by the proved global sheaf gluing. -/
instance intrinsicLineBundleSectionRingCommRing (L : IntrinsicLineBundle X) :
    CommRing L.sectionRing := by
  let := atlasPowerGradedCommRing L.atlas
  exact inferInstanceAs (CommRing (⨁ n : ℕ, bundlePowerGlobalSections L.sheaf n))

/-- The native homogeneous-degree inclusion into the actual section ring. -/
def IntrinsicLineBundle.ofSection (L : IntrinsicLineBundle X) (n : ℕ) :
    bundlePowerGlobalSections L.sheaf n →+ L.sectionRing :=
  DirectSum.of (bundlePowerGlobalSections L.sheaf) n

/-- Each actual section space embeds faithfully as its own degree. -/
theorem IntrinsicLineBundle.ofSection_injective (L : IntrinsicLineBundle X) (n : ℕ) :
    Function.Injective (L.ofSection n) :=
  DirectSum.of_injective (β := bundlePowerGlobalSections L.sheaf) n

/-- The ring product of homogeneous inclusions is precisely the constructed
global sheaf-gluing product. -/
theorem IntrinsicLineBundle.ofSection_mul (L : IntrinsicLineBundle X) (m n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf m) (t : bundlePowerGlobalSections L.sheaf n) :
    L.ofSection m s * L.ofSection n t =
      L.ofSection (m + n) (atlasPowerGlobalMul L.atlas m n s t) := by
  let := atlasPowerGradedCommRing L.atlas
  exact DirectSum.of_mul_of s t

theorem IntrinsicLineBundle.ofSection_one (L : IntrinsicLineBundle X) :
    L.ofSection 0 (bundlePowerGlobalOne L.sheaf) = 1 := by
  let := atlasPowerGradedCommRing L.atlas
  exact DirectSum.of_zero_one (bundlePowerGlobalSections L.sheaf)

/-- Degree-zero coefficients are the literal restrictions of regular functions. -/
theorem atlasPowerGlobalCoefficients_degree_zero {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) (r : X.sheaf.obj.obj (op ⊤)) :
    atlasPowerGlobalCoefficients a 0 i r = X.sheaf.obj.map (homOfLE le_top).op r :=
  LocalBundleFrame.tensorPower_zero_coefficients (a.frame i) (𝟙 _) _

/-- The constructed degree-zero product agrees with the actual global
structure-ring multiplication. -/
theorem atlasPowerGlobalMul_degree_zero {L : X.Modules} (a : LineBundleAtlas L)
    (r q : X.sheaf.obj.obj (op ⊤)) :
    atlasPowerGlobalMul a 0 0 r q = (r * q : X.sheaf.obj.obj (op ⊤)) := by
  apply atlasPowerGlobalCoefficients_ext a 0
  intro i
  calc
    atlasPowerGlobalCoefficients a 0 i (atlasPowerGlobalMul a 0 0 r q) =
        atlasPowerGlobalCoefficients a 0 i r * atlasPowerGlobalCoefficients a 0 i q :=
      atlasPowerGlobalMul_coefficients a 0 0 r q i
    _ = X.sheaf.obj.map (homOfLE le_top).op r * X.sheaf.obj.map (homOfLE le_top).op q :=
      congrArg₂ (· * ·) (atlasPowerGlobalCoefficients_degree_zero a i r)
        (atlasPowerGlobalCoefficients_degree_zero a i q)
    _ = X.sheaf.obj.map (homOfLE le_top).op (r * q) := (map_mul _ _ _).symm
    _ = atlasPowerGlobalCoefficients a 0 i (r * q) :=
      (atlasPowerGlobalCoefficients_degree_zero a i (r * q)).symm

/-- The literal degree-zero inclusion is a ring homomorphism from the actual
global structure ring. -/
def IntrinsicLineBundle.sectionRingConstants (L : IntrinsicLineBundle X) :
    Γ(X, ⊤) →+* L.sectionRing where
  toFun := L.ofSection 0
  map_zero' := (L.ofSection 0).map_zero
  map_add' := (L.ofSection 0).map_add
  map_one' := L.ofSection_one
  map_mul' r q := by
    exact ((L.ofSection_mul 0 0 r q).trans
      (congrArg (L.ofSection 0) (atlasPowerGlobalMul_degree_zero L.atlas r q))).symm

theorem IntrinsicLineBundle.sectionRingConstants_injective (L : IntrinsicLineBundle X) :
    Function.Injective L.sectionRingConstants :=
  L.ofSection_injective 0

/-- The structural field acts through its actual constant regular functions
and the actual degree-zero inclusion. -/
def IntrinsicLineBundle.sectionRingBaseMap {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) : K →+* L.sectionRing :=
  L.sectionRingConstants.comp (schemeConstantMap f)

/-- The actual section ring over the structural base field. -/
@[instance_reducible]
def IntrinsicLineBundle.sectionRingAlgebra {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) : Algebra K L.sectionRing :=
  (L.sectionRingBaseMap f).toAlgebra

/-- The constructed base map is literally the degree-zero constant-section map. -/
theorem IntrinsicLineBundle.sectionRingBaseMap_apply {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) (c : K) :
    L.sectionRingBaseMap f c = L.ofSection 0 (schemeConstantMap f c) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The natural structure-ring scalar action has its literal restricted
function as the multiplier in every chart coordinate. -/
theorem atlasPowerGlobalCoefficients_smul {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (i : a.I) (r : X.sheaf.obj.obj (op ⊤)) (s : bundlePowerGlobalSections L n) :
    atlasPowerGlobalCoefficients a n i (r • s) =
      X.sheaf.obj.map (homOfLE le_top).op r * atlasPowerGlobalCoefficients a n i s := by
  have h := (bundleTensorPower L n).val.map_smul (homOfLE (le_top : a.opens i ≤ ⊤)).op r s
  exact (congrArg (((a.frame i).tensorPower n).coefficients (𝟙 _)) h).trans
    ((((a.frame i).tensorPower n).coefficients (𝟙 _)).map_smul _ _)

/-- Multiplication by a degree-zero regular function is the actual natural
scalar action on the global section module. -/
theorem atlasPowerGlobalMul_regular_scalar {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (r : X.sheaf.obj.obj (op ⊤)) (s : bundlePowerGlobalSections L n) :
    HEq (atlasPowerGlobalMul a 0 n r s) (r • s) := by
  apply atlasPowerGlobalCoefficients_heq a (Nat.zero_add n)
  intro i
  calc
    atlasPowerGlobalCoefficients a (0 + n) i (atlasPowerGlobalMul a 0 n r s) =
        atlasPowerGlobalCoefficients a 0 i r * atlasPowerGlobalCoefficients a n i s :=
      atlasPowerGlobalMul_coefficients a 0 n r s i
    _ = X.sheaf.obj.map (homOfLE le_top).op r * atlasPowerGlobalCoefficients a n i s :=
      congrArg (· * atlasPowerGlobalCoefficients a n i s)
        (atlasPowerGlobalCoefficients_degree_zero a i r)
    _ = atlasPowerGlobalCoefficients a n i (r • s) :=
      (atlasPowerGlobalCoefficients_smul a n i r s).symm

/-- Native homogeneous inclusions preserve the actual regular-function
scalar multiplication via the constructed degree-zero ring inclusion. -/
theorem IntrinsicLineBundle.ofSection_constant_mul (L : IntrinsicLineBundle X) (n : ℕ)
    (r : Γ(X, ⊤)) (s : bundlePowerGlobalSections L.sheaf n) :
    L.ofSection 0 r * L.ofSection n s = L.ofSection n (r • s) := by
  calc
    L.ofSection 0 r * L.ofSection n s =
        L.ofSection (0 + n) (atlasPowerGlobalMul L.atlas 0 n r s) := L.ofSection_mul 0 n r s
    _ = L.ofSection n (r • s) :=
      DirectSum.of_eq_of_gradedMonoid_eq
        (Sigma.ext (Nat.zero_add n) (atlasPowerGlobalMul_regular_scalar L.atlas n r s))

/-- The structural base-field action on a homogeneous inclusion agrees with
the natural scalar action through the actual constant regular function. -/
theorem IntrinsicLineBundle.sectionRing_smul_ofSection {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) (n : ℕ) (c : K)
    (s : bundlePowerGlobalSections L.sheaf n) :
    letI := L.sectionRingAlgebra f
    c • L.ofSection n s = L.ofSection n ((schemeConstantMap f c) • s) := by
  let := L.sectionRingAlgebra f
  rw [Algebra.smul_def]
  exact L.ofSection_constant_mul n (schemeConstantMap f c) s

end

end SGPT.Foundations.Schemes
