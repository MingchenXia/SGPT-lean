import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Foundations.Schemes.SchemeSubsetCechSections
import SGPT.Foundations.Schemes.NonemptySubsetCechComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme.{u}} {L : X.Modules}

/-- The original global section produces the actual evaluation sheaf map. -/
def sectionZeroSheafEvaluation (L : X.Modules) (s : Γ(L, ⊤)) :
    bundleDual L ⟶ SheafOfModules.unit X.ringCatSheaf where
  val := {
    app U := ModuleCat.ofHom
      (X := (bundleDual L).val.obj U)
      (Y := (SheafOfModules.unit X.ringCatSheaf).val.obj U)
      (sectionZeroEvaluation L s U.unop)
    naturality {U V} i := by
      apply ModuleCat.hom_ext
      ext α
      exact sectionZeroEvaluation_restrict L s (leOfHom i.unop) α }

/-- The actual evaluation component retains the original dual evaluation map. -/
theorem sectionZeroSheafEvaluation_app (L : X.Modules) (s : Γ(L, ⊤))
    (U : X.Opens) (α : Γ(bundleDual L, U)) :
    (sectionZeroSheafEvaluation L s).app U α = sectionZeroEvaluation L s U α := rfl

/-- The native structural pullback, as a morphism of actual scheme modules. -/
abbrev structureSheafPullbackMap {Y : Scheme.{u}} (f : Y ⟶ X) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- Actual structural pullback components are literally the original scheme map. -/
theorem structureSheafPullbackMap_app {Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) (r : Γ(X, U)) :
    (structureSheafPullbackMap f).app U r = f.app U r := rfl

/-- An actual sheaf morphism gives original global-ring-linear intersection maps. -/
def actualSchemeModuleSubsetMap {M N : X.Modules} (φ : M ⟶ N)
    {I : Type u} [LinearOrder I] (U : I → X.Opens) :
    actualSchemeModuleSubsetDiagram M U ⟶ actualSchemeModuleSubsetDiagram N U := by
  letI : ∀ V : X.Opens, Module Γ(X, ⊤) (bundleSections M V) :=
    fun V => localSectionsGlobalModule M V
  letI : ∀ V : X.Opens, Module Γ(X, ⊤) (bundleSections N V) :=
    fun V => localSectionsGlobalModule N V
  exact {
    app S := ModuleCat.ofHom {
      toFun := φ.val.app (.op (actualSchemeSubsetOpen U S))
      map_add' := (φ.val.app (.op (actualSchemeSubsetOpen U S))).hom.map_add
      map_smul' := by
        intro r x
        change φ.val.app (.op (actualSchemeSubsetOpen U S))
          (X.presheaf.map (actualSchemeSubsetOpen U S).leTop.op r • x) =
          X.presheaf.map (actualSchemeSubsetOpen U S).leTop.op r •
            φ.val.app (.op (actualSchemeSubsetOpen U S)) x
        exact (φ.val.app (.op (actualSchemeSubsetOpen U S))).hom.map_smul _ x }
    naturality {S T} h := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact PresheafOfModules.naturality_apply φ.val
        (homOfLE (actualSchemeSubsetOpen_antitone U (leOfHom h))).op x
  }

/-- Restriction to the given structural base action leaves actual components unchanged. -/
def actualSchemeModuleBaseSubsetMap {M N : X.Modules} (φ : M ⟶ N)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    actualSchemeModuleBaseSubsetDiagram M U c ⟶
      actualSchemeModuleBaseSubsetDiagram N U c :=
  Functor.whiskerRight (actualSchemeModuleSubsetMap φ U) (ModuleCat.restrictScalars c)

/-- The base-linear intersection map is literally the original sheaf component. -/
theorem actualSchemeModuleBaseSubsetMap_apply {M N : X.Modules} (φ : M ⟶ N)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (S : Finset I)
    (x : (actualSchemeModuleBaseSubsetDiagram M U c).obj S) :
    (actualSchemeModuleBaseSubsetMap φ U c).app S x =
      φ.val.app (.op (actualSchemeSubsetOpen U S)) x := rfl

/-- The original base-linear diagram map restricted to actual nonempty index subsets. -/
def actualSchemeModuleNonemptyBaseSubsetMap {M N : X.Modules} (φ : M ⟶ N)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram M U c) ⟶
      nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram N U c) :=
  Functor.whiskerLeft (nonemptySubsetInclusion I) (actualSchemeModuleBaseSubsetMap φ U c)


end
end SGPT.Foundations.Schemes
