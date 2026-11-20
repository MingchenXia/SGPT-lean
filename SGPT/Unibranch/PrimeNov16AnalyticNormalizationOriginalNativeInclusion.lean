import SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominatorGraph

/-! Actual full original identity embedding between original models in nested opens.
Blueprint: prime-nov16-analytic-normalization-original-native-inclusion.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeInclusion
open SourceReducedComplexSpace
variable {n : ℕ} (U V : Opens (ComplexModel n)) {C : Set U} {D : Set V}
  (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D)
  (hUV : U ≤ V) (hCD : ∀ c : C,(⟨c.val.val,hUV c.val.property⟩ : V) ∈ D)

def nativeInclusion : sourceReducedComplexSpaceModel U C hC ⟶
    sourceReducedComplexSpaceModel V D hD :=
  analyticModelMorphism hC hD id contDiff_id.contDiffOn (fun _ hz => hUV hz) hCD

theorem nativeInclusion_point (c : C) :
    ((nativeInclusion U V hC hD hUV hCD).hom.left.base c).val.val=c.val.val := rfl

theorem nativeInclusion_embedding :
    Topology.IsEmbedding (nativeInclusion U V hC hD hUV hCD).hom.left.base := by
  let f : C → D := (nativeInclusion U V hC hD hUV hCD).hom.left.base
  have he : (fun d : D => d.val.val) ∘ f=(fun c : C => c.val.val) := rfl
  have hv : Topology.IsEmbedding (fun c : C => c.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  exact Topology.IsEmbedding.of_comp
    (nativeInclusion U V hC hD hUV hCD).hom.left.base.hom.continuous
    (continuous_subtype_val.comp continuous_subtype_val)
    (show Topology.IsEmbedding ((fun d : D => d.val.val) ∘ f) from he.symm ▸ hv)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeInclusion
