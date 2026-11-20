import SGPT.Bergman.SourceMultiplierSectionSubsheaf
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# LocalTensorIdealFrames

On a frame domain, the tensor product of the section module with an ideal module is the module of ideal-valued sections.

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

/-- On ANY original frame domain, one native ORIGINAL ideal-section condition is equivalent to ALL original coefficient conditions. -/
theorem mem_idealOpenSection_iff_frame (A : GermIdeal n X) (U : Opens X) (e : OriginalFrame V)
    (he : (U : Set X) ⊆ e.val.baseSet) (s : OpenSections (n := n) V U) :
    s ∈ idealOpenSectionSubmodule (n := n) V A U ↔
      frameCoefficientSection (n := n) V U e.val he s ∈ actualSectionIdeal A U := by
  constructor
  · intro hs x hx
    have hm := hs e ⟨x, hx⟩ (he hx)
    have hq := localFrameCoefficientGerm_eq_frame (n := n) V U e he s ⟨x, hx⟩ (he hx)
    exact Eq.mp (congrArg (fun z => z ∈ actualWholeSheafStalkIdeal A x) hq) hm
  · intro hs f x hx
    have hm : frameCoefficientGerm (n := n) V U e.val he s x ∈ actualWholeSheafStalkIdeal A x.val :=
      hs x.val x.property
    have hq := localFrameCoefficientGerm_eq_frame (n := n) V U e he s x (he x.property)
    have hm' : localFrameCoefficientGerm (n := n) V U e s x (he x.property) ∈
        actualWholeSheafStalkIdeal A x.val := hq.symm ▸ hm
    exact (localFrameCoefficientGerm_mem_iff (n := n) V A U e f s x (he x.property) hx).mp hm'

/-- Actual O(U)-linear local-frame isomorphism for the WHOLE original ideal modules, with BOTH full-space maps. -/
def idealFrameSectionEquiv (A : GermIdeal n X) (U : Opens X) (e : OriginalFrame V)
    (he : (U : Set X) ⊆ e.val.baseSet) :
    idealOpenSectionSubmodule (n := n) V A U ≃ₗ[ScalarSections (n := n) U] actualSectionIdeal A U where
  toFun s := ⟨frameSectionEquiv (n := n) V U e.val he s.val,
    (mem_idealOpenSection_iff_frame (n := n) V A U e he s.val).mp s.property⟩
  invFun a := ⟨(frameSectionEquiv (n := n) V U e.val he).symm a.val, by
    apply (mem_idealOpenSection_iff_frame (n := n) V A U e he _).mpr
    exact Eq.mpr (congrArg (fun z => z ∈ actualSectionIdeal A U)
      ((frameSectionEquiv (n := n) V U e.val he).apply_symm_apply a.val)) a.property⟩
  left_inv s := Subtype.ext ((frameSectionEquiv (n := n) V U e.val he).symm_apply_apply s.val)
  right_inv a := Subtype.ext ((frameSectionEquiv (n := n) V U e.val he).apply_symm_apply a.val)
  map_add' s t := Subtype.ext ((frameSectionEquiv (n := n) V U e.val he).map_add s.val t.val)
  map_smul' r s := Subtype.ext ((frameSectionEquiv (n := n) V U e.val he).map_smul r s.val)

/-- The literal O(U)-tensor is genuinely isomorphic to the original ideal-valued sections on EVERY real frame domain. -/
def localTensorIdealEquiv (A : GermIdeal n X) (U : Opens X) (e : OriginalFrame V)
    (he : (U : Set X) ⊆ e.val.baseSet) :
    OpenSections (n := n) V U ⊗[ScalarSections (n := n) U] actualSectionIdeal A U ≃ₗ[ScalarSections (n := n) U]
      idealOpenSectionSubmodule (n := n) V A U :=
  ((TensorProduct.congr (frameSectionEquiv (n := n) V U e.val he)
      (LinearEquiv.refl (ScalarSections (n := n) U) (actualSectionIdeal A U))).trans
    (TensorProduct.lid (ScalarSections (n := n) U) (actualSectionIdeal A U))).trans
      (idealFrameSectionEquiv (n := n) V A U e he).symm

/-- The actual local inverse is the ORIGINAL frame section tensor the SAME full original ideal coefficient. -/
theorem localTensorIdealEquiv_symm (A : GermIdeal n X) (U : Opens X) (e : OriginalFrame V)
    (he : (U : Set X) ⊆ e.val.baseSet) (s : idealOpenSectionSubmodule (n := n) V A U) :
    (localTensorIdealEquiv (n := n) V A U e he).symm s =
      (frameSectionEquiv (n := n) V U e.val he).symm 1 ⊗ₜ[ScalarSections (n := n) U]
        (idealFrameSectionEquiv (n := n) V A U e he) s := by
  simp [localTensorIdealEquiv, TensorProduct.lid_symm_apply, TensorProduct.congr_symm,
    TensorProduct.congr_tmul]

end SGPT.Bergman.MultiplierSectionsDraft
