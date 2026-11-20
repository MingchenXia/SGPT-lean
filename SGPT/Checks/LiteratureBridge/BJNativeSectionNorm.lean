import SGPT.Checks.LiteratureBridge.BJNativeCenters
import SGPT.Checks.LiteratureBridge.BJNativePicard
import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeGlobalSectionModelNormIsometries
import SGPT.Foundations.PublishedEnvelope.Berkovich.SchemeLineLocalSectionEvaluation

/-! Actual original sections and true native model norms: whole coefficient
maps and a common genuine center-containing frame produce the dictionary
internally. Zero sections and every original support are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace SGPT.Support.PublishedModularCurves
open Scheme.Modules SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.Berkovich
open SGPT.Foundations.PublishedEnvelope.Berkovich.RelativeSchemeValuedPoint
open SGPT.Foundations.PublishedEnvelope.SchemeGlobalSectionModelNormIsometries

local instance (Y : Scheme.{0}) : ∀ U,IsMulCommutative (Y.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (Y.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

variable {X : Scheme.{0}}

/-- The actual whole-section morphism in the original over-site frame has
its literal original restricted regular coefficient, internally. -/
theorem sectionHom_over_comp_sourceFrame (M : X.Modules) (U : X.Opens)
    (e : SGPT.Foundations.Schemes.LocalBundleFrame M U) (s : Γ(M,⊤)) :
    (SchemeModuleGlobalSections.sectionHom M s).over U ≫ e.hom=
      (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        (e.coefficients (𝟙 U) (M.presheaf.map (homOfLE (le_top : U≤⊤)).op s))).asHom := by
  let r : Γ(X,U) := e.coefficients (𝟙 U) (M.presheaf.map (homOfLE (le_top : U≤⊤)).op s)
  apply (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
  change _=(SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
    ((SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm r)
  rw [Equiv.apply_symm_apply]
  change e.hom.val.app (op (Over.mk (𝟙 U)))
    ((SchemeModuleGlobalSections.sectionHom M s).val.app (op U) (show Γ(X,U) from 1))=r
  change e.coefficients (𝟙 U)
    ((1:Γ(X,U))•M.presheaf.map (homOfLE (le_top : U≤⊤)).op s)=r
  rw [one_smul]

/-- The actual section map evaluated on1 is the actual original section. -/
theorem sectionHom_source_value_one (M : X.Modules) (s : Γ(M,⊤)) :
    (SchemeModuleGlobalSections.sectionHom M s).val.app (op ⊤)
      (show Γ(X,⊤) from 1)=s := by
  change (1:Γ(X,⊤))•M.presheaf.map (homOfLE (le_top : (⊤:X.Opens)≤⊤)).op s=s
  rw [one_smul]
  change M.presheaf.map (𝟙 (op ⊤)) s=s
  rw [M.presheaf.map_id]
  rfl

/-- Genuine native restriction retains the SAME literal source coefficient;
no incoming coefficient/norm dictionary premise is used. -/
theorem localTrivializationCoefficient_eq_sourceCoefficient (M : X.Modules)
    (U : X.affineOpens) (e : SGPT.Foundations.Schemes.LocalBundleFrame M U.1) (s : Γ(M,⊤)) :
    localTrivializationCoefficient M U (restrictTrivializationOfOverIso M U.1 e) s=
      e.coefficients (𝟙 U.1) (M.presheaf.map (homOfLE (le_top : U.1≤⊤)).op s) := by
  let r : Γ(X,U.1) := e.coefficients (𝟙 U.1) (M.presheaf.map (homOfLE (le_top : U.1≤⊤)).op s)
  have hm := sectionHom_over_comp_sourceFrame M U.1 e s
  have ht := localTrivializationTopSection_unitHom_apply_one M U
    (SchemeModuleGlobalSections.sectionHom M s) e r hm
  rw [sectionHom_source_value_one] at ht
  unfold localTrivializationCoefficient
  rw [ht,affineOpenAmbientSection_topSection]

variable (p : X ⟶ Spec (.of ℂ)) [IsProper p]

/-- Actual native global-section model norm equals the exponential of the
actual original coefficient valuation, including all zero/polar cases. -/
theorem nativeGlobalSectionNorm_eq_sourceCoefficient (M : X.Modules)
    (hM : IsInvertible M) (v : BerkovichPoint p) (U : X.affineOpens)
    (hc : v.center∈U.1) (e : SGPT.Foundations.Schemes.LocalBundleFrame M U.1) (s : Γ(M,⊤)) :
    globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v) M hM s=
      expNegNN (v.sectionVal U.1 (v.support_specializes_center.mem_open U.1.isOpen hc)
        (e.coefficients (𝟙 U.1) (M.presheaf.map (homOfLE (le_top : U.1≤⊤)).op s))) := by
  have hr := SchemeLineSectionEvaluation.sectionHom_localScalar M U
    (restrictTrivializationOfOverIso M U.1 e) s
  rw [localTrivializationCoefficient_eq_sourceCoefficient] at hr
  have hn := modelLineNorm_fibreSection_eq_localEval Valuation.one_apply_le_one
    (pointEquiv p v) hM U.1 (nativeCenter_mem_affine_of_sourceCenter_mem p v U hc)
    (pullbackIsoOfRestrictIso M U.1 (restrictTrivializationOfOverIso M U.1 e))
    (SchemeModuleGlobalSections.sectionHom M s)
    (e.coefficients (𝟙 U.1) (M.presheaf.map (homOfLE (le_top : U.1≤⊤)).op s)) hr
  exact hn

/-- Intrinsic original power-section value gives the SAME true native
whole-section model norm, on EVERY original Berkovich point. -/
theorem nativeGlobalSectionNorm_eq_powerSectionValue {L : X.Modules}
    (a : LineBundleAtlas L) (n : ℕ) (s : bundlePowerGlobalSections L n)
    (v : BerkovichPoint p) :
    globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v) (bundleTensorPower L n)
      (isInvertible_of_atlas (powerAtlas a n)) s=expNegNN (powerSectionValue a n s v) := by
  let i := centerIndex a v
  obtain ⟨W,hW,hcW,hWU⟩ := exists_isAffineOpen_mem_and_subset
    (X:=X) (U:=a.opens i) (x:=v.center) (center_mem_open a v)
  let U : X.affineOpens := ⟨W,hW⟩
  let e : SGPT.Foundations.Schemes.LocalBundleFrame L W :=
    SheafOfModules.restrictOverTrivialization X.ringCatSheaf L (a.opens i) (a.frame i)
      (Over.mk (homOfLE hWU))
  have hn := nativeGlobalSectionNorm_eq_sourceCoefficient p (bundleTensorPower L n)
    (isInvertible_of_atlas (powerAtlas a n)) v U hcW (e.tensorPower n) s
  rw [powerSectionValue_eq_local a n s v e hcW]
  exact hn

end SGPT.NAPotential.BJ
