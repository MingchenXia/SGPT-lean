import SGPT.Unibranch.HironakaG10FlatNilpotentCriterion

/-! # The first tensor obstruction as an ideal-intersection condition -/
set_option autoImplicit false
open TensorProduct
namespace SGPT.Unibranch.HironakaG10FlatIntersectionCriterion

/-- If a submodule of a flat module meets `I N` only in `I K`, then the
  ideal-tensor map for its quotient is injective. This is the global
  section-relation condition needed by the nilpotent flatness criterion. -/
theorem ideal_tensor_quotient_injective_of_intersection
    {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N] [Module.Flat A N]
    (I : Ideal A) (K : Submodule A N)
    (hinter : K ⊓ I • (⊤ : Submodule A N) ≤ I • K) :
    Function.Injective (I.subtype.rTensor (N ⧸ K)) := by
  let μ : I ⊗[A] N →ₗ[A] N := (TensorProduct.lid A N).toLinearMap.comp (I.subtype.rTensor N)
  have hμ : Function.Injective μ := (TensorProduct.lid A N).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
  have hμmem (z : I ⊗[A] N) : μ z ∈ I • (⊤ : Submodule A N) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      change (a : A) • x ∈ I • (⊤ : Submodule A N)
      exact Submodule.smul_mem_smul a.property trivial
    | add x y hx hy =>
      simpa only [map_add] using (I • (⊤ : Submodule A N)).add_mem hx hy
  have hpre : I • K ≤ LinearMap.range (μ.comp (K.subtype.lTensor I)) := by
    rw [Submodule.smul_le]
    intro a ha x hx
    refine ⟨⟨a,ha⟩ ⊗ₜ[A] ⟨x,hx⟩, ?_⟩
    rfl
  have hcomm (z : I ⊗[A] N) : K.mkQ (μ z) =
      (TensorProduct.lid A (N ⧸ K)) ((I.subtype.rTensor (N ⧸ K)) ((K.mkQ.lTensor I) z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [μ]
    | add x y hx hy =>
      simp only [map_add]
      rw [hx,hy]
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro t ht
    have ht0 : (I.subtype.rTensor (N ⧸ K)) t = 0 := ht
    obtain ⟨z,rfl⟩ := K.mkQ.lTensor_surjective I (Submodule.mkQ_surjective K) t
    have hK : μ z ∈ K := by
      rw [← Submodule.ker_mkQ K]
      change K.mkQ (μ z) = 0
      rw [hcomm,ht0]
      simp
    obtain ⟨w,hw⟩ := hpre (hinter ⟨hK,hμmem z⟩)
    have hz : z = (K.subtype.lTensor I) w := hμ hw.symm
    change K.mkQ.lTensor I z = 0
    rw [hz]
    have hzero : K.mkQ ∘ₗ K.subtype = 0 := LinearMap.exact_subtype_mkQ K |>.linearMap_comp_eq_zero
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero]
    simp
  · exact bot_le

end SGPT.Unibranch.HironakaG10FlatIntersectionCriterion
