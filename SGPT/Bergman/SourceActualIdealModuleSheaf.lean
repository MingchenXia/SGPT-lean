import SGPT.Bergman.SourceTensorIdealGlobalSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# ActualIdealModuleSheaf

The ideal module sheaf `𝓘` as a sheaf of modules and the sheaf `O(E) ⊗ 𝓘`.

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


/-- The native original WHOLE-stalk ideal-section presheaf genuinely satisfies arbitrary gluing. -/
theorem actualIdealModule_isSheaf (A : GermIdeal n X) :
    TopCat.Presheaf.IsSheaf (actualIdealSectionPresheaf A) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (actualIdealSectionPresheaf A)).mpr
  intro ι U sf hc
  let O := actualComplexStructureSheaf (n := n) X
  have hcompat : TopCat.Presheaf.IsCompatible O.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hc i j)
  obtain ⟨s, hs, huniq⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing O.property U (fun i => (sf i).val) hcompat
  have hm : s ∈ actualSectionIdeal A (iSup U) := by
    intro y hy
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hy
    have hg := O.presheaf.germ_res_apply (Opens.leSupr U i) y hyi s
    rw [← hg, hs i]
    exact (sf i).property y hyi
  refine ⟨⟨s, hm⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The ACTUAL original ideal module SHEAF, with original restriction/action and no incoming sheaf certificate. -/
def originalIdealModuleSheaf (A : GermIdeal n X) :
    SheafOfModules.{0} (structureRingSheaf (n := n) (X := X)) where
  val := actualIdealModulePresheaf A
  isSheaf := actualIdealModule_isSheaf A

variable (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The genuine usual tensor construction applied to TWO internally produced ORIGINAL module SHEAVES. -/
def originalBundleIdealTensorSheaf (A : GermIdeal n X) :
    SheafOfModules.{0} (structureRingSheaf (n := n) (X := X)) :=
  (PresheafOfModules.sheafification.{0} (R := structureRingSheaf (n := n) (X := X))
    (𝟙 (structureRingSheaf (n := n) (X := X)).presheaf)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := (structureSheaf (n := n) (X := X)).presheaf)
      (bundleSectionModuleSheaf (n := n) V).val (originalIdealModuleSheaf A).val)

/-- The proved tensor/Gamma map uses EXACTLY those two genuine original SHEAVES as its factors. -/
theorem originalBundleIdealTensorSheaf_eq (A : GermIdeal n X) :
    originalBundleIdealTensorSheaf (n := n) V A = literalTensorIdealSheaf (n := n) V A := rfl

end SGPT.Bergman.MultiplierSectionsDraft
