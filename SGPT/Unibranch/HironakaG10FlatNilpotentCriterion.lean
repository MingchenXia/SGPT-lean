import SGPT.Unibranch.HironakaG10FlatArtinianProjection
import Mathlib.RingTheory.LocalRing.Module

/-! # Flatness criterion for nilpotent parameter thickenings -/
set_option autoImplicit false
namespace SGPT.Unibranch.HironakaG10FlatNilpotentCriterion
open SGPT.Unibranch.HironakaG10FlatArtinianProjection

/-- For a nilpotent ideal, a flat presentation which is injective on the
  special fibre has flat cokernel as soon as the first ideal-tensor map is
  injective. Neither the presentation nor the cokernel need be finite. -/
theorem flat_of_nilpotent_minimal_presentation
    {A P M : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module.Flat A P]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) (f : P →ₗ[A] M)
    (hfsurj : Function.Surjective f)
    (hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A P))
    (hTor : Function.Injective (I.subtype.rTensor M)) : Module.Flat A M := by
  let K := LinearMap.ker f
  have hinj : Function.Injective (K.subtype.lTensor (A ⧸ I)) := by
    exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
      (LinearMap.exact_subtype_ker_map f) hfsurj hTor
      (Module.Flat.lTensor_preserves_injective_linearMap K.subtype Subtype.val_injective)
  have hsmall : (⊤ : Submodule A K) ≤ I • (⊤ : Submodule A K) := by
    intro x _
    have hx : (1 : A ⧸ I) ⊗ₜ[A] (x : P) = 0 := by
      have : (x : P) ∈ LinearMap.ker (TensorProduct.mk A (A ⧸ I) P 1) := by
        rw [LinearMap.ker_tensorProductMk]
        exact hmin x.property
      exact this
    have hx' : (1 : A ⧸ I) ⊗ₜ[A] x = 0 := by
      apply hinj
      simpa using hx
    have : x ∈ LinearMap.ker (TensorProduct.mk A (A ⧸ I) K 1) := hx'
    rwa [LinearMap.ker_tensorProductMk] at this
  have hK : (⊤ : Submodule A K) ≤ ⊥ := by
    apply le_of_le_sup_smul_of_nilpotent I ⊤ ⊥ hnil
    simpa using hsmall
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro x hx
      have : (⟨x,hx⟩ : K) = 0 := hK (show (⟨x,hx⟩ : K) ∈ ⊤ from trivial)
      exact congrArg Subtype.val this
    · exact bot_le
  let e := LinearEquiv.ofBijective f ⟨hf,hfsurj⟩
  exact (Module.Flat.equiv_iff e).mp inferInstance

end SGPT.Unibranch.HironakaG10FlatNilpotentCriterion

namespace SGPT.Unibranch.HironakaG10FlatNilpotentCriterion
open SGPT.Unibranch.HironakaG10FlatArtinianProjection
open TensorProduct

/-- Over a local ring with nilpotent maximal ideal, the usual first tensor
  criterion for flatness holds for arbitrary modules. -/
theorem flat_of_maximalIdeal_rTensor_injective_of_nilpotent
    {A M : Type*} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    (hnil : ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n = ⊥)
    (hTor : Function.Injective ((IsLocalRing.maximalIdeal A).subtype.rTensor M)) :
    Module.Flat A M := by
  classical
  let I := IsLocalRing.maximalIdeal A
  let k := A ⧸ I
  letI : Field k := Ideal.Quotient.field I
  let b := Module.Free.chooseBasis k (k ⊗[A] M)
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[A] M)
  have hmk : Function.Surjective (TensorProduct.mk A k M 1) :=
    TensorProduct.mk_surjective A M k Ideal.Quotient.mk_surjective
  choose v hv using fun i : ι => hmk (b i)
  let f : (ι →₀ A) →ₗ[A] M := Finsupp.linearCombination A v
  let e : (k ⊗[A] (ι →₀ A)) ≃ₗ[k] (k ⊗[A] M) :=
    (TensorProduct.finsuppScalarRight A k k ι).trans b.repr.symm
  have he : f.lTensor k = e.toLinearMap.restrictScalars A := by
    ext a z
    change a ⊗ₜ[A] f (Finsupp.single z 1) = e (a ⊗ₜ[A] Finsupp.single z 1)
    simp only [f, Finsupp.linearCombination_single, one_smul, e, LinearEquiv.trans_apply]
    rw [TensorProduct.finsuppScalarRight_apply_tmul]
    rw [Finsupp.sum_single_index (by simp)]
    simp only [one_smul, b.repr_symm_single, ← hv z]
    change a ⊗ₜ[A] v z = a • ((1 : k) ⊗ₜ[A] v z)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have heinj : Function.Injective (f.lTensor k) := he ▸ e.injective
  have hesurj : Function.Surjective (f.lTensor k) := he ▸ e.surjective
  have hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A (ι →₀ A)) := by
    intro x hx
    rw [← LinearMap.ker_tensorProductMk]
    change (1 : k) ⊗ₜ[A] x = 0
    apply heinj
    have hx0 : f x = 0 := hx
    simp [hx0]
  have hfsurj : Function.Surjective f := by
    have hgen : (⊤ : Submodule A M) ≤ LinearMap.range f ⊔ I • (⊤ : Submodule A M) := by
      intro x _
      obtain ⟨z,hz⟩ := hesurj ((1 : k) ⊗ₜ[A] x)
      obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective A (ι →₀ A) k Ideal.Quotient.mk_surjective z
      apply Submodule.mem_sup.mpr
      refine ⟨f y, ⟨y,rfl⟩, x - f y, ?_, by simp⟩
      rw [← LinearMap.ker_tensorProductMk]
      change (1 : k) ⊗ₜ[A] (x - f y) = 0
      simp only [TensorProduct.tmul_sub, sub_eq_zero]
      simpa using hz.symm
    have htop := le_of_le_sup_smul_of_nilpotent I (⊤ : Submodule A M)
      (LinearMap.range f) hnil hgen
    exact LinearMap.range_eq_top.mp (top_le_iff.mp htop)
  exact flat_of_nilpotent_minimal_presentation I hnil f hfsurj hmin hTor

end SGPT.Unibranch.HironakaG10FlatNilpotentCriterion
