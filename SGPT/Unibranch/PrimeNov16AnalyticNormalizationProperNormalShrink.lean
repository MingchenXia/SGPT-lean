import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalLocus
import Mathlib.Topology.LocalAtTarget

/-! Actual properness deletes the WHOLE nonnormal image and retains EVERY full original fibre point.
Blueprint: prime-nov16-analytic-normalization-proper-normal-shrink.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationProperNormalShrink
open PrimeNov16AnalyticNormalizationOriginalNormalLocus HironakaActualAnalyticSubspace

section Topological
variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] (f : S → T)

omit [TopologicalSpace S] [TopologicalSpace T] in
theorem actual_restricted_fibre_image (U : Set T) (u : U) :
    (Subtype.val : (f ⁻¹' U) → S) '' ((U.restrictPreimage f) ⁻¹' {u})=f ⁻¹' {u.val} := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change (U.restrictPreimage f) q=u at hq
    exact congrArg Subtype.val hq
  · intro hp
    change f p=u.val at hp
    refine ⟨⟨p,?_⟩,?_,rfl⟩
    · change f p ∈ U
      rw [hp]
      exact u.property
    · exact Subtype.ext hp

theorem actual_proper_restrict_preimage (hf : IsProperMap f) (U : Set T) :
    IsProperMap (U.restrictPreimage f) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf.continuous.restrictPreimage,hf.isClosedMap.restrictPreimage U,?_⟩
  intro u
  apply Subtype.isCompact_iff.mpr
  rw [actual_restricted_fibre_image]
  exact hf.isCompact_preimage isCompact_singleton

omit [TopologicalSpace S] [TopologicalSpace T] in
theorem actual_finite_restrict_preimage
    (hfinite : ∀ y : T,(f ⁻¹' {y}).Finite) (U : Set T) (u : U) :
    ((U.restrictPreimage f) ⁻¹' {u}).Finite := by
  apply Set.Finite.of_finite_image
  · rw [actual_restricted_fibre_image]
    exact hfinite u.val
  · exact Subtype.val_injective.injOn
end Topological

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def originalNormalLocus (C : Set M) : Set C :=
  {p | IsDomain ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier ∧
    IsIntegrallyClosed ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier}

theorem isOpen_originalNormalLocus (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C) :
    IsOpen (originalNormalLocus (n := n) C) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  let := hp.1
  let := hp.2
  obtain ⟨U,hU,hpU,_hUN,hNormal⟩ := exists_original_normal_locus_open C hC p
    (show (univ : Set M) ∈ 𝓝 p.val from univ_mem)
  exact mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hpU)
    (fun q hq => hNormal q hq)

theorem exists_actual_proper_finite_normal_full_preimage {T : Type*} [TopologicalSpace T]
    (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C) (f : C → T)
    (hf : IsProperMap f) (hfinite : ∀ y : T,(f ⁻¹' {y}).Finite) (b : T)
    (hcentral : ∀ p : C,f p=b → p ∈ originalNormalLocus (n := n) C)
    {N : Set T} (hN : N ∈ 𝓝 b) :
    ∃ U : Set T,IsOpen U ∧ b ∈ U ∧ U ⊆ N ∧ IsProperMap (U.restrictPreimage f) ∧
      (∀ u : U,((U.restrictPreimage f) ⁻¹' {u}).Finite) ∧
      ∀ p : C,f p ∈ U → p ∈ originalNormalLocus (n := n) C := by
  have hclosed := hf.isClosedMap ((originalNormalLocus (n := n) C)ᶜ) (isOpen_originalNormalLocus (n := n) C hC).isClosed_compl
  have hb : b ∉ f '' ((originalNormalLocus (n := n) C)ᶜ) := by
    rintro ⟨p,hp,hpb⟩
    exact hp (hcentral p hpb)
  obtain ⟨V,hVN,hV,hbV⟩ := mem_nhds_iff.mp hN
  let U := V ∩ (f '' ((originalNormalLocus (n := n) C)ᶜ))ᶜ
  refine ⟨U,hV.inter hclosed.isOpen_compl,⟨hbV,hb⟩,fun _y hy => hVN hy.1,
    actual_proper_restrict_preimage f hf U,actual_finite_restrict_preimage f hfinite U,?_⟩
  intro p hp
  by_contra hbad
  exact hp.2 ⟨p,hbad,rfl⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationProperNormalShrink
