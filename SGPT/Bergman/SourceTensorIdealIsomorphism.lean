import SGPT.Bergman.SourceTensorIdealMultiplication
import SGPT.Bergman.SourceLocalTensorIdealFrames
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# TensorIdealIsomorphism

The multiplication map `O(E) ⊗ 𝓘 → 𝓘·O(E)` is an isomorphism of sheaves (locally injective and surjective).

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

/-- The actual original multiplication map IS the internally produced full local tensor equivalence. -/
theorem tensorIdealMultiplicationLinear_eq_local (A : GermIdeal n X) (U : Opens X)
    (e : OriginalFrame V) (he : (U : Set X) ⊆ e.val.baseSet) :
    tensorIdealMultiplicationLinear (n := n) V A U = (localTensorIdealEquiv (n := n) V A U e he).toLinearMap := by
  apply TensorProduct.ext'
  intro s a
  apply (idealFrameSectionEquiv (n := n) V A U e he).injective
  apply Subtype.ext
  change frameSectionEquiv (n := n) V U e.val he (a.val • s) =
    ((idealFrameSectionEquiv (n := n) V A U e he)
      (localTensorIdealEquiv (n := n) V A U e he (s ⊗ₜ[ScalarSections (n := n) U] a))).val
  simp only [localTensorIdealEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.lid_tmul]
  calc
    _ = a.val * frameSectionEquiv (n := n) V U e.val he s :=
      (frameSectionEquiv (n := n) V U e.val he).map_smul a.val s
    _ = _ := mul_comm _ _

/-- Actual true-frame geometry internally gives BOTH injectivity and surjectivity on the ENTIRE local tensor module. -/
theorem tensorIdealMultiplicationLinear_bijective_on_frame (A : GermIdeal n X) (U : Opens X)
    (e : OriginalFrame V) (he : (U : Set X) ⊆ e.val.baseSet) :
    Function.Bijective (tensorIdealMultiplicationLinear (n := n) V A U) := by
  rw [tensorIdealMultiplicationLinear_eq_local (n := n) V A U e he]
  exact (localTensorIdealEquiv (n := n) V A U e he).bijective

/-- Actual original preferred frames INTERNALLY supply a local preimage on a real original neighborhood. -/
instance tensorIdealMultiplication_locallySurjective (A : GermIdeal n X) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of X))
      (tensorIdealMultiplicationPresheaf (n := n) V A) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf (structureRingSheaf (n := n) (X := X)).presheaf).map
      (tensorIdealMultiplicationPresheaf (n := n) V A))).mpr
  intro U t x hx
  let e := preferredOriginalFrame V x
  let W : Opens X := frameOpen V U e
  have hWU : W ≤ U := inf_le_left
  have hWe : (W : Set X) ⊆ e.val.baseSet := fun _ hy => hy.2
  let tw := idealOpenSectionRestrict (n := n) V A hWU t
  obtain ⟨s, hs⟩ := (tensorIdealMultiplicationLinear_bijective_on_frame (n := n) V A W e hWe).surjective tw
  refine ⟨W, hWU, ⟨s, ?_⟩, ⟨hx, mem_baseSet_trivializationAt ℂ V x⟩⟩
  exact hs

/-- BOTH original restrictions agree on a genuine internally produced original frame neighborhood. -/
instance tensorIdealMultiplication_locallyInjective (A : GermIdeal n X) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of X))
      (tensorIdealMultiplicationPresheaf (n := n) V A) := by
  constructor
  intro U s t hst x hx
  let e := preferredOriginalFrame V x
  let W : Opens X := frameOpen V (unop U) e
  have hWU : W ≤ unop U := inf_le_left
  have hWe : (W : Set X) ⊆ e.val.baseSet := fun _ hy => hy.2
  let rho : U ⟶ op W := (homOfLE hWU).op
  have hh := (PresheafOfModules.naturality_apply (tensorIdealMultiplicationPresheaf (n := n) V A) rho s).trans
    ((congrArg (fun q => (idealBundleSectionModulePresheaf (n := n) V A).map rho q) hst).trans
      (PresheafOfModules.naturality_apply (tensorIdealMultiplicationPresheaf (n := n) V A) rho t).symm)
  refine ⟨W, homOfLE hWU, ?_, ⟨hx, mem_baseSet_trivializationAt ℂ V x⟩⟩
  exact (tensorIdealMultiplicationLinear_bijective_on_frame (n := n) V A W e hWe).injective hh

/-- The TRUE canonical sheafification unit, from its actual native universal Hom equivalence. -/
def tensorIdealSheafificationUnit (A : GermIdeal n X) :
    literalTensorIdealPresheaf (n := n) V A ⟶ (literalTensorIdealSheaf (n := n) V A).val :=
  PresheafOfModules.sheafificationHomEquiv (R := structureRingSheaf (n := n) (X := X))
    (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf) (𝟙 (literalTensorIdealSheaf (n := n) V A))

/-- The original-cover local bijection INTERNALLY produces the actual inverse module-presheaf morphism. -/
def tensorIdealInversePresheaf (A : GermIdeal n X) :
    (idealBundleSectionModuleSheaf (n := n) V A).val ⟶ (literalTensorIdealSheaf (n := n) V A).val :=
  (PresheafOfModules.homEquivOfIsLocallyBijective
    (J := Opens.grothendieckTopology (TopCat.of X))
    (f := tensorIdealMultiplicationPresheaf (n := n) V A)
    (hN := (literalTensorIdealSheaf (n := n) V A).isSheaf)).symm
      (tensorIdealSheafificationUnit (n := n) V A)

/-- The TRUE inverse SHEAF morphism, using the genuinely produced inverse restriction diagram. -/
def tensorIdealInverseSheaf (A : GermIdeal n X) :
    idealBundleSectionModuleSheaf (n := n) V A ⟶ literalTensorIdealSheaf (n := n) V A where
  val := tensorIdealInversePresheaf (n := n) V A

/-- The produced inverse is a REAL extension of the original local pure-tensor inverse. -/
theorem tensorIdealInversePresheaf_comp (A : GermIdeal n X) :
    tensorIdealMultiplicationPresheaf (n := n) V A ≫ tensorIdealInversePresheaf (n := n) V A =
      tensorIdealSheafificationUnit (n := n) V A :=
  (PresheafOfModules.homEquivOfIsLocallyBijective
    (J := Opens.grothendieckTopology (TopCat.of X))
    (f := tensorIdealMultiplicationPresheaf (n := n) V A)
    (hN := (literalTensorIdealSheaf (n := n) V A).isSheaf)).apply_symm_apply
      (tensorIdealSheafificationUnit (n := n) V A)

/-- The actual native universal Hom map has the literal original unit-composition formula. -/
theorem tensorIdealHomEquiv_apply (A : GermIdeal n X)
    (B : SheafOfModules.{0} (structureRingSheaf (n := n) (X := X)))
    (g : literalTensorIdealSheaf (n := n) V A ⟶ B) :
    PresheafOfModules.sheafificationHomEquiv (R := structureRingSheaf (n := n) (X := X))
        (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf) g =
      tensorIdealSheafificationUnit (n := n) V A ≫ g.val := rfl

/-- The TRUE forward sheaf morphism retains the original tensor multiplication through the actual canonical unit. -/
theorem tensorIdealMultiplicationSheaf_unit (A : GermIdeal n X) :
    tensorIdealSheafificationUnit (n := n) V A ≫ (tensorIdealMultiplicationSheaf (n := n) V A).val =
      tensorIdealMultiplicationPresheaf (n := n) V A := by
  have hu : PresheafOfModules.sheafificationHomEquiv
      (R := structureRingSheaf (n := n) (X := X))
      (P := literalTensorIdealPresheaf (n := n) V A)
      (F := idealBundleSectionModuleSheaf (n := n) V A)
      (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)
      (tensorIdealMultiplicationSheaf (n := n) V A) =
        tensorIdealMultiplicationPresheaf (n := n) V A :=
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureRingSheaf (n := n) (X := X))
      (P := literalTensorIdealPresheaf (n := n) V A)
      (F := idealBundleSectionModuleSheaf (n := n) V A)
      (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)).apply_symm_apply
        (tensorIdealMultiplicationPresheaf (n := n) V A)
  exact (tensorIdealHomEquiv_apply (n := n) V A
    (idealBundleSectionModuleSheaf (n := n) V A)
    (tensorIdealMultiplicationSheaf (n := n) V A)).symm.trans hu

set_option backward.isDefEq.respectTransparency false in
/-- The produced global tensor-to-ideal map followed by its produced inverse is the ACTUAL identity sheaf map. -/
theorem tensorIdealMultiplication_inverse (A : GermIdeal n X) :
    tensorIdealMultiplicationSheaf (n := n) V A ≫ tensorIdealInverseSheaf (n := n) V A =
      𝟙 (literalTensorIdealSheaf (n := n) V A) := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (R := structureRingSheaf (n := n) (X := X))
    (P := literalTensorIdealPresheaf (n := n) V A)
    (F := literalTensorIdealSheaf (n := n) V A)
    (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)).injective
  change tensorIdealSheafificationUnit (n := n) V A ≫
    ((tensorIdealMultiplicationSheaf (n := n) V A).val ≫ tensorIdealInversePresheaf (n := n) V A) =
      tensorIdealSheafificationUnit (n := n) V A
  rw [← Category.assoc, tensorIdealMultiplicationSheaf_unit]
  exact tensorIdealInversePresheaf_comp (n := n) V A

set_option backward.isDefEq.respectTransparency false in
/-- The produced inverse followed by the original multiplication is the ACTUAL identity on the entire ideal-valued section sheaf. -/
theorem tensorIdealInverse_multiplication (A : GermIdeal n X) :
    tensorIdealInverseSheaf (n := n) V A ≫ tensorIdealMultiplicationSheaf (n := n) V A =
      𝟙 (idealBundleSectionModuleSheaf (n := n) V A) := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (J := Opens.grothendieckTopology (TopCat.of X))
    (f := tensorIdealMultiplicationPresheaf (n := n) V A)
    (hN := (idealBundleSectionModuleSheaf (n := n) V A).isSheaf)).injective
  change tensorIdealMultiplicationPresheaf (n := n) V A ≫
    (tensorIdealInversePresheaf (n := n) V A ≫ (tensorIdealMultiplicationSheaf (n := n) V A).val) =
      tensorIdealMultiplicationPresheaf (n := n) V A ≫ 𝟙 _
  rw [← Category.assoc, tensorIdealInversePresheaf_comp,
    tensorIdealMultiplicationSheaf_unit, Category.comp_id]

/-- Literal sheaf tensor product of the original section sheaf and the original ideal sheaf,
with BOTH actual global inverse morphisms proved from true original-frame geometry. -/
def tensorIdealSheafIso (A : GermIdeal n X) :
    literalTensorIdealSheaf (n := n) V A ≅ idealBundleSectionModuleSheaf (n := n) V A where
  hom := tensorIdealMultiplicationSheaf (n := n) V A
  inv := tensorIdealInverseSheaf (n := n) V A
  hom_inv_id := tensorIdealMultiplication_inverse (n := n) V A
  inv_hom_id := tensorIdealInverse_multiplication (n := n) V A

end SGPT.Bergman.MultiplierSectionsDraft
