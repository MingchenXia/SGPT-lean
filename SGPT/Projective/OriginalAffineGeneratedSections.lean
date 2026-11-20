import SGPT.Foundations.Schemes.AffineCoverModuleEpimorphism
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! Fresh generic source port of NativeGlobalGeneratingSections before its Fano consumers.
Same actual free evaluation and original affine spans; no Fano geometry imported.
Blueprint: original-affine-generated-sections.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace SGPT.Foundations.Schemes
variable {X : Scheme.{0}}

/-- SAME actual ordinary original section gives its original structure-module morphism. -/
def originalOrdinarySectionHom (F : X.Modules) (s : bundleSections F ⊤) :
    SheafOfModules.unit X.ringCatSheaf ⟶ F :=
  F.unitHomEquiv.symm (F.val.sectionsMk
    (fun U => F.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (fun {_ _} i => (F.val.map_comp_apply _ i s).symm))

/-- Its original local scalar action is the literal restricted original section. -/
theorem originalOrdinarySectionHom_app (F : X.Modules) (s : bundleSections F ⊤)
    (U : X.Opens) (r : Γ(X, U)) :
    (originalOrdinarySectionHom F s).val.app (.op U) r =
      r • F.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s := rfl

/-- The canonical free evaluation of the SAME original global sections and
index, formed from the genuine native unit-section/free-hom correspondences. -/
def originalAffineFamilyEvaluation (M : X.Modules) {I : Type} (s : I → Γ(M, ⊤)) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M :=
  M.freeHomEquiv.symm (fun i ↦ M.unitHomEquiv (originalOrdinarySectionHom M (s i)))

/-- Each literal native free generator evaluates to the EXACT original
restricted section, on every actual open and with its actual module action. -/
theorem originalAffineFamilyEvaluation_freeSection (M : X.Modules) {I : Type}
    (s : I → Γ(M, ⊤)) (i : I) (U : X.Opens) :
    (originalAffineFamilyEvaluation M s).val.app (.op U)
      ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (.op U)) =
        M.val.map U.leTop.op (s i) := by
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (fun b ↦ M.unitHomEquiv (originalOrdinarySectionHom M (s b))) i
  have hu := congrArg (fun z : M.sections ↦ z.val (.op U)) h
  change (originalAffineFamilyEvaluation M s).val.app (.op U)
    ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (.op U)) =
      (originalOrdinarySectionHom M (s i)).val.app (.op U) (1 : Γ(X, U)) at hu
  rw [originalOrdinarySectionHom_app, one_smul] at hu
  exact hu

/-- An actual span on a PARTICULAR open makes that evaluation component
surjective, by its linear range and literal native free generators. -/
theorem originalAffineFamilyEvaluation_surjective_of_span (M : X.Modules) {I : Type}
    (s : I → Γ(M, ⊤)) (U : X.Opens)
    (hspan : Submodule.span Γ(X, U) (Set.range (fun i ↦ M.val.map U.leTop.op (s i))) = ⊤) :
    Function.Surjective ((originalAffineFamilyEvaluation M s).val.app (.op U)) := by
  let l : bundleSections (SheafOfModules.free (R := X.ringCatSheaf) I) U →ₗ[Γ(X, U)]
      bundleSections M U := (originalAffineFamilyEvaluation M s).val.app (.op U) |>.hom
  have hr : Submodule.span Γ(X, U) (Set.range (fun i ↦ M.val.map U.leTop.op (s i))) ≤
      LinearMap.range l := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨(SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (.op U),
      originalAffineFamilyEvaluation_freeSection M s i U⟩
  rw [hspan] at hr
  exact LinearMap.range_eq_top.mp (top_unique hr)

/-- Genuine affine-cover spans of the SAME original global family PRODUCE
Epi of its canonical native free evaluation; no global right-exactness used. -/
theorem originalAffineFamilyEvaluation_epi_of_affine_cover (M : X.Modules) [M.IsQuasicoherent]
    {I : Type} (s : I → Γ(M, ⊤)) {J : Type} (U : J → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : ∀ x : X, ∃ j, x ∈ U j)
    (hspan : ∀ j, Submodule.span Γ(X, U j)
      (Set.range (fun i ↦ M.val.map (U j).leTop.op (s i))) = ⊤) :
    Epi (originalAffineFamilyEvaluation M s) :=
  moduleHom_epi_of_affine_cover (originalAffineFamilyEvaluation M s) U hU hcover
    (fun j ↦ originalAffineFamilyEvaluation_surjective_of_span M s (U j) (hspan j))

/-- ACTUAL native generating sections, keeping the ORIGINAL index and
compatible restrictions literally; the Epi field is PROVED from chart spans. -/
def originalGeneratingSectionsOfAffineCoverSpan (M : X.Modules) [M.IsQuasicoherent]
    {I : Type} (s : I → Γ(M, ⊤)) {J : Type} (U : J → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : ∀ x : X, ∃ j, x ∈ U j)
    (hspan : ∀ j, Submodule.span Γ(X, U j)
      (Set.range (fun i ↦ M.val.map (U j).leTop.op (s i))) = ⊤) : M.GeneratingSections where
  I := I
  s i := M.unitHomEquiv (originalOrdinarySectionHom M (s i))
  epi := originalAffineFamilyEvaluation_epi_of_affine_cover M s U hU hcover hspan

/-- Finite type here means the ACTUAL global generating family has the
same finite index; it is not merely local finite type of the target module. -/
instance originalGeneratingSectionsOfAffineCoverSpan_isFiniteType
    (M : X.Modules) [M.IsQuasicoherent] {I : Type} [Finite I] (s : I → Γ(M, ⊤))
    {J : Type} (U : J → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcover : ∀ x : X, ∃ j, x ∈ U j)
    (hspan : ∀ j, Submodule.span Γ(X, U j)
      (Set.range (fun i ↦ M.val.map (U j).leTop.op (s i))) = ⊤) :
    (originalGeneratingSectionsOfAffineCoverSpan M s U hU hcover hspan).IsFiniteType where
  finite := by change Finite I; infer_instance


end SGPT.Projective.NumEq.AlgebraicCurveDegree
