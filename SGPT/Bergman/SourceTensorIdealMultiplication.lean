import SGPT.Bergman.SourceMultiplierSectionSubsheaf
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealModuleStalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# TensorIdealMultiplication

The sheaf tensor product `O(E) ⊗ 𝓘` of module sheaves and its multiplication map to ideal-valued sections.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealModuleStalk

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The actual native module-sheaf category at the original concrete structure sheaf.
This specializes native category data; it is not a tensor/Gamma assumption. -/
instance structureModuleSheafCategory :
    Category (SheafOfModules.{0} (structureRingSheaf (n := n) (X := X))) :=
  SheafOfModules.instCategory

/-- The LITERAL O_X-module PRESHEAF tensor, using the original actual ideal-section module. -/
def literalTensorIdealPresheaf (A : GermIdeal n X) :
    PresheafOfModules.{0} (structureRingSheaf (n := n) (X := X)).presheaf :=
  PresheafOfModules.Monoidal.tensorObj (R := (structureSheaf (n := n) (X := X)).presheaf)
    (bundleSectionModulePresheaf (n := n) V) (actualIdealModulePresheaf A)

/-- The LITERAL actual O_X SHEAF tensor is the genuine module-sheafification of the actual presheaf tensor. -/
def literalTensorIdealSheaf (A : GermIdeal n X) :
    SheafOfModules.{0} (structureRingSheaf (n := n) (X := X)) :=
  (PresheafOfModules.sheafification.{0} (R := structureRingSheaf (n := n) (X := X)) (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)).obj
    (literalTensorIdealPresheaf (n := n) V A)

/-- Original ideal scalar sections multiply EVERY actual bundle section into the WHOLE original coefficient ideals. -/
theorem idealScalar_smul_mem (A : GermIdeal n X) (U : Opens X)
    (a : actualSectionIdeal A U) (s : OpenSections (n := n) V U) :
    a.val • s ∈ idealOpenSectionSubmodule (n := n) V A U := by
  intro e x hx
  rw [localFrameCoefficientGerm_smul]
  exact (actualWholeSheafStalkIdeal A x.val).mul_mem_right _ (a.property x.val x.property)

/-- Actual O(U)-bilinear multiplication, constructed on ALL real sections and ALL original ideal sections. -/
def tensorIdealMultiplicationBilinear (A : GermIdeal n X) (U : Opens X) :
    OpenSections (n := n) V U →ₗ[ScalarSections (n := n) U]
      actualSectionIdeal A U →ₗ[ScalarSections (n := n) U] idealOpenSectionSubmodule (n := n) V A U where
  toFun s := {
    toFun a := ⟨a.val • s, idealScalar_smul_mem (n := n) V A U a s⟩
    map_add' a b := by apply Subtype.ext; exact add_smul a.val b.val s
    map_smul' r a := by apply Subtype.ext; exact mul_smul r a.val s }
  map_add' s t := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact smul_add a.val s t
  map_smul' r s := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact smul_comm a.val r s

/-- The actual tensor universal property supplies the whole-tensor multiplication map. -/
def tensorIdealMultiplicationLinear (A : GermIdeal n X) (U : Opens X) :
    OpenSections (n := n) V U ⊗[ScalarSections (n := n) U] actualSectionIdeal A U →ₗ[ScalarSections (n := n) U]
      idealOpenSectionSubmodule (n := n) V A U :=
  TensorProduct.lift (tensorIdealMultiplicationBilinear (n := n) V A U)

/-- The SAME original pointwise multiplication formula on every actual pure tensor. -/
theorem tensorIdealMultiplicationLinear_tmul (A : GermIdeal n X) (U : Opens X)
    (s : OpenSections (n := n) V U) (a : actualSectionIdeal A U) :
    tensorIdealMultiplicationLinear (n := n) V A U (s ⊗ₜ[ScalarSections (n := n) U] a) =
      ⟨a.val • s, idealScalar_smul_mem (n := n) V A U a s⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual multiplication maps commute with ALL true original restrictions, as a genuine module-presheaf morphism. -/
def tensorIdealMultiplicationPresheaf (A : GermIdeal n X) :
    literalTensorIdealPresheaf (n := n) V A ⟶ idealBundleSectionModulePresheaf (n := n) V A where
  app U := ModuleCat.ofHom (R := ScalarSections (n := n) (unop U))
    (X := OpenSections (n := n) V (unop U) ⊗[ScalarSections (n := n) (unop U)] actualSectionIdeal A (unop U))
    (Y := ↥(idealOpenSectionSubmodule (n := n) V A (unop U)))
    (tensorIdealMultiplicationLinear (n := n) V A (unop U))
  naturality := by
    intro U W i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s a
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The TRUE universal sheafification map gives the actual forward SHEAF morphism, rather than an incoming Gamma certificate. -/
def tensorIdealMultiplicationSheaf (A : GermIdeal n X) :
    literalTensorIdealSheaf (n := n) V A ⟶ idealBundleSectionModuleSheaf (n := n) V A :=
  (PresheafOfModules.sheafificationHomEquiv (R := structureRingSheaf (n := n) (X := X)) (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)).symm
    (tensorIdealMultiplicationPresheaf (n := n) V A)

end SGPT.Bergman.MultiplierSectionsDraft
