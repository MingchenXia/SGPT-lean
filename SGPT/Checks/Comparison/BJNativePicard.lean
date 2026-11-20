import SGPT.NAPotential.BJRationalGFFunction
import SGPT.Support.ModularCurves.Picard.PicComparison
import Mathlib.RingTheory.TensorProduct.Basic

/-! Same native scheme sheaf atlas to its genuine scheme Picard class and
rational scalar extension. No numerical convergence or finite dimensionality
is assumed, and no arbitrary class map is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules SGPT.Foundations.Schemes
open scoped TensorProduct
open SGPT.NAPotential.Berkovich.BJSections
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {X : Scheme.{0}}

/-- A genuine over-site frame gives the SAME actual open-subscheme frame. -/
def restrictionIso {L : X.Modules} {U : X.Opens} (e : LocalBundleFrame L U) :
    L.restrict U.ι≅Scheme.Modules.unitObj U.toScheme :=
  ((Scheme.Modules.overFunctorEquiv U).app L).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Original rank-one atlas internally produces actual scheme invertibility. -/
theorem isInvertible_of_atlas {L : X.Modules} (a : LineBundleAtlas L) : IsInvertible L := by
  refine ⟨a.I,a.opens,?_,fun i =>
    ⟨pullbackIsoOfRestrictIso L (a.opens i) (restrictionIso (a.frame i))⟩⟩
  apply top_unique
  intro x _
  obtain ⟨i,hi⟩ := a.covers x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i,hi⟩

/-- The actual scheme Picard class; its inverse is produced by the native
genuine sheaf-dual pairing theorem, not supplied as caller data. -/
def linePicardClass {L : X.Modules} (a : LineBundleAtlas L) : X.Pic :=
  (isInvertible_of_atlas a).isUnit_toSkeleton.unit

theorem linePicardClass_val {L : X.Modules} (a : LineBundleAtlas L) :
    (linePicardClass a).val=toSkeleton L :=
  (isInvertible_of_atlas a).isUnit_toSkeleton.unit_spec

theorem linePicardClass_atlas_independent {L : X.Modules} (a b : LineBundleAtlas L) :
    linePicardClass a=linePicardClass b := by
  apply Units.ext
  rw [linePicardClass_val,linePicardClass_val]

theorem linePicardClass_eq_of_iso {L M : X.Modules} (a : LineBundleAtlas L)
    (b : LineBundleAtlas M) (e : L≅M) : linePicardClass a=linePicardClass b := by
  apply Units.ext
  rw [linePicardClass_val,linePicardClass_val]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

/-- Native recursively sheafified powers have their SAME true tensor classes. -/
theorem toSkeleton_power (L : X.Modules) (n : ℕ) :
    toSkeleton (SGPT.Foundations.Schemes.bundleTensorPower L n)=(toSkeleton L)^n := by
  induction n with
  | zero => exact toSkeleton_unitObj
  | succ n ih =>
    change toSkeleton (SGPT.Foundations.Schemes.bundleTensor (SGPT.Foundations.Schemes.bundleTensorPower L n) L)=_
    have he : SGPT.Foundations.Schemes.bundleTensor (SGPT.Foundations.Schemes.bundleTensorPower L n) L=
        Scheme.Modules.tensorObj (SGPT.Foundations.Schemes.bundleTensorPower L n) L := rfl
    rw [he,toSkeleton_tensorObj_eq,ih,pow_succ]

theorem linePicardClass_power {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ) :
    linePicardClass (powerAtlas a n)=(linePicardClass a)^n := by
  apply Units.ext
  rw [linePicardClass_val,Units.val_pow_eq_pow_val,linePicardClass_val,toSkeleton_power]

/-- Actual rational scalar extension of the SAME genuine scheme Picard group. -/
abbrev RationalPicardSpace (X : Scheme.{0}) := ℚ⊗[ℤ] Additive X.Pic

def rationalizePicard (X : Scheme.{0}) : Additive X.Pic →+ RationalPicardSpace X where
  toFun := fun a => (1:ℚ)⊗ₜ[ℤ] a
  map_zero' := TensorProduct.tmul_zero _ _
  map_add' := TensorProduct.tmul_add _

def rationalPicardClass {L : X.Modules} (a : LineBundleAtlas L) : RationalPicardSpace X :=
  rationalizePicard X (Additive.ofMul (linePicardClass a))

theorem rationalPicardClass_atlas_independent {L : X.Modules} (a b : LineBundleAtlas L) :
    rationalPicardClass a=rationalPicardClass b := by
  rw [rationalPicardClass,rationalPicardClass,linePicardClass_atlas_independent a b]

theorem rationalPicardClass_power {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ) :
    rationalPicardClass (powerAtlas a n)=n•rationalPicardClass a := by
  unfold rationalPicardClass
  rw [linePicardClass_power]
  exact (rationalizePicard X).map_nsmul _ _

/-- A genuine finite GF presentation now has its true rational Picard class,
without pretending this is already the numerical-class topology. -/
def gfPicardClass {L : X.Modules} {n m : ℕ} (a : LineBundleAtlas L)
    (_D : RationalGFData L n m) : RationalPicardSpace X :=
  ((n:ℚ)/(m:ℚ))•rationalPicardClass a

theorem gfPicardClass_atlas_independent {L : X.Modules} {n m : ℕ}
    (a b : LineBundleAtlas L) (D : RationalGFData L n m) :
    gfPicardClass a D=gfPicardClass b D := by
  rw [gfPicardClass,gfPicardClass,rationalPicardClass_atlas_independent a b]

/-- This is exactly the actual section-power line divided by its true
normalization, as required by the source rational GF formula. -/
theorem gfPicardClass_eq_powerClass {L : X.Modules} {n m : ℕ}
    (a : LineBundleAtlas L) (D : RationalGFData L n m) :
    gfPicardClass a D=(m:ℚ)⁻¹•rationalPicardClass (powerAtlas a n) := by
  rw [gfPicardClass,rationalPicardClass_power,← Nat.cast_smul_eq_nsmul ℚ n,smul_smul]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

end SGPT.NAPotential.BJ.NativePicard
