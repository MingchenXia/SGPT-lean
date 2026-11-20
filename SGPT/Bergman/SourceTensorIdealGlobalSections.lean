import SGPT.Bergman.SourceTensorIdealIsomorphism
import SGPT.Bergman.SourceDegreeMultiplierIdeal

/-!
# TensorIdealGlobalSections

Global sections of the sheaf tensor product `O(E) ⊗ 𝓘` are the holomorphic sections whose coefficients lie in `𝓘`.

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

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- Literal GLOBAL sections of the true original tensor SHEAF on the whole original manifold. -/
abbrev TensorIdealGlobalSections (A : GermIdeal n X) :=
  (literalTensorIdealSheaf (n := n) V A).val.obj (op (⊤ : Opens X))

/-- The literal evaluated native module retains its original O(X)-action. -/
instance tensorIdealGammaScalarModule (A : GermIdeal n X) :
    Module (ScalarSections (n := n) (⊤ : Opens X)) (TensorIdealGlobalSections (n := n) V A) :=
  ((literalTensorIdealSheaf (n := n) V A).val.obj (op (⊤ : Opens X))).isModule

/-- Evaluation of the actual proved sheaf isomorphism on X gives the full original O(X)-linear equivalence. -/
def tensorIdealTopEquiv (A : GermIdeal n X) :
    TensorIdealGlobalSections (n := n) V A ≃ₗ[ScalarSections (n := n) (⊤ : Opens X)]
      ↥(idealOpenSectionSubmodule (n := n) V A ⊤) :=
  ((SheafOfModules.evaluation (R := structureRingSheaf (n := n) (X := X))
    (op (⊤ : Opens X))).mapIso (tensorIdealSheafIso (n := n) V A)).toLinearEquiv

/-- The genuine original constant-section algebra map supplies complex scalars on the literal Gamma space. -/
instance tensorIdealGammaComplexModule (A : GermIdeal n X) :
    Module ℂ (TensorIdealGlobalSections (n := n) V A) :=
  Module.compHom (TensorIdealGlobalSections (n := n) V A)
    (algebraMap ℂ (ScalarSections (n := n) (⊤ : Opens X)))

/-- Actual full original H0 submodule and the actual ideal-valued whole-manifold sections have BOTH maps. -/
def idealGlobalSectionEquiv (A : GermIdeal n X) :
    ↥(fullHolomorphicIdealSections (n := n) V A) ≃ₗ[ℂ]
      ↥(idealOpenSectionComplexSubmodule (n := n) V A ⊤) where
  toFun s := ⟨globalSectionSheafEquiv (n := n) V s.val, s.property⟩
  invFun s := ⟨(globalSectionSheafEquiv (n := n) V).symm s.val, by
    change globalSectionSheafEquiv (n := n) V ((globalSectionSheafEquiv (n := n) V).symm s.val) ∈
      idealOpenSectionComplexSubmodule (n := n) V A ⊤
    rw [LinearEquiv.apply_symm_apply]
    exact s.property⟩
  left_inv s := by apply Subtype.ext; exact (globalSectionSheafEquiv (n := n) V).symm_apply_apply s.val
  right_inv s := by apply Subtype.ext; exact (globalSectionSheafEquiv (n := n) V).apply_symm_apply s.val
  map_add' s t := by apply Subtype.ext; exact (globalSectionSheafEquiv (n := n) V).map_add s.val t.val
  map_smul' r s := by apply Subtype.ext; exact (globalSectionSheafEquiv (n := n) V).map_smul r s.val

/-- SAME original constant-section action, retaining the actual sheaf maps in BOTH directions. -/
def tensorIdealTopComplexEquiv (A : GermIdeal n X) :
    TensorIdealGlobalSections (n := n) V A ≃ₗ[ℂ]
      ↥(idealOpenSectionComplexSubmodule (n := n) V A ⊤) where
  toFun z := ⟨(tensorIdealTopEquiv (n := n) V A z).val, (tensorIdealTopEquiv (n := n) V A z).property⟩
  invFun z := (tensorIdealTopEquiv (n := n) V A).symm ⟨z.val, z.property⟩
  left_inv z := (tensorIdealTopEquiv (n := n) V A).symm_apply_apply z
  right_inv z := by
    apply Subtype.ext
    exact congrArg Subtype.val ((tensorIdealTopEquiv (n := n) V A).apply_symm_apply ⟨z.val, z.property⟩)
  map_add' z w := by
    apply Subtype.ext
    exact congrArg Subtype.val ((tensorIdealTopEquiv (n := n) V A).map_add z w)
  map_smul' r z := by
    apply Subtype.ext
    exact congrArg Subtype.val ((tensorIdealTopEquiv (n := n) V A).map_smul
      (algebraMap ℂ (ScalarSections (n := n) (⊤ : Opens X)) r) z)

/-- Literal Gamma(E tensor_O I) equals the ACTUAL full original H0 submodule,
with genuine inverse maps and complex linearity, not a finite-family or output certificate. -/
def tensorIdealGlobalSectionEquiv (A : GermIdeal n X) :
    TensorIdealGlobalSections (n := n) V A ≃ₗ[ℂ] ↥(fullHolomorphicIdealSections (n := n) V A) :=
  (tensorIdealTopComplexEquiv (n := n) V A).trans (idealGlobalSectionEquiv (n := n) V A).symm

/-- BOTH original coefficient-integrability directions on ALL original frames for literal degree k, including k=0. -/
theorem fullHolomorphicDegreeIdealSections_iff_original (k : ℕ) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (s : ContMDiffSection (𝓘(ℂ, ComplexModel n)) ℂ ∞ V) :
    s ∈ fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) k φ) ↔
      ∀ (e : OriginalFrame V) (x : X), x ∈ frameOpen V (⊤ : Opens X) e →
        (sourceDegreeMultiplierIdeal (n := n) k φ).mem x
          (sectionExtension (frameOpen V (⊤ : Opens X) e)
            (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s))) :=
  mem_idealOpenSectionSubmodule_iff_original (n := n) V _
    (sourceDegreeMultiplierIdeal_isCoherent k hφ) ⊤ (globalSectionSheafEquiv (n := n) V s)

end SGPT.Bergman.MultiplierSectionsDraft
