import SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorProductTransport
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image

/-!
# Actual pure eigenblocks and genuine exterior preservation

Every wrong-cardinality eigenspace block is used. The complete signed
normalized wedge preserves the sum of actual holomorphic degrees by the
internally proved disjoint-slot cardinality identity. No real span or
usual-class equality is asserted in this module.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorPreservation

open NaturalComplexBidegreeTransport NaturalComplexExteriorProductTransport

def pureEigenblockSpace (n d r : ℕ) :
    Submodule ℂ (complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) where
  carrier := {F | ∀ (S : Finset (Fin d)), S.card ≠ r →
    ∀ v, (∀ j, j ∈ S → extendedJ n (v j) = Complex.I • v j) →
      (∀ j, j ∉ S → extendedJ n (v j) = -Complex.I • v j) → F v = 0}
  zero_mem' := by
    intro S hS v hp hm
    rfl
  add_mem' := by
    intro F G hF hG S hS v hp hm
    simp only [AlternatingMap.add_apply, hF S hS v hp hm, hG S hS v hp hm, add_zero]
  smul_mem' := by
    intro c F hF S hS v hp hm
    simp only [AlternatingMap.smul_apply, hF S hS v hp hm, smul_zero]

theorem mem_pureEigenblockSpace_iff_bidegree {n r s : ℕ}
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ) :
    F ∈ pureEigenblockSpace n (r + s) r ↔ IsPureBidegree r s F :=
  (isPureBidegree_iff_eigenblocks F).symm

theorem domDomCongr_mem_pureEigenblockSpace {n d e r : ℕ}
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ)
    (hF : F ∈ pureEigenblockSpace n d r) (ι : Fin d ≃ Fin e) :
    F.domDomCongr ι ∈ pureEigenblockSpace n e r := by
  classical
  intro S hS v hp hm
  change F (v ∘ ι) = 0
  apply hF (S.map ι.symm.toEmbedding) (by simpa using hS) (v ∘ ι)
  · intro j hj
    apply hp (ι j)
    simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hj
  · intro j hj
    apply hm (ι j)
    simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hj

private theorem split_card {d e t : ℕ} (S : Finset (Fin t))
    (ι : Fin d ⊕ Fin e ≃ Fin t) :
    ((Finset.univ : Finset (Fin d)).filter (fun i => ι (Sum.inl i) ∈ S)).card +
      ((Finset.univ : Finset (Fin e)).filter (fun i => ι (Sum.inr i) ∈ S)).card = S.card := by
  classical
  let h := Equiv.subtypeEquiv ι (p := fun z => ι z ∈ S)
    (q := fun j => j ∈ S) (fun _ => Iff.rfl)
  have hc := Fintype.card_congr (h.symm.trans (Equiv.subtypeSum))
  simpa only [Fintype.card_sum, Fintype.card_subtype, Finset.filter_mem_eq_inter,
    Finset.univ_inter] using hc.symm

theorem complexWedge_mem_pureEigenblockSpace {n d e r s : ℕ}
    (A : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin e]→ₗ[ℂ] ℂ)
    (hA : A ∈ pureEigenblockSpace n d r) (hB : B ∈ pureEigenblockSpace n e s) :
    complexWedge A B ∈ pureEigenblockSpace n (d + e) (r + s) := by
  classical
  intro S hS v hp hm
  simp only [complexWedge, AlternatingMap.domDomCongr_apply, complexWedgeSum_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro σ _
  let ι : Fin d ⊕ Fin e ≃ Fin (d + e) := σ.trans finSumFinEquiv
  let SL : Finset (Fin d) := Finset.univ.filter fun j => ι (Sum.inl j) ∈ S
  let SR : Finset (Fin e) := Finset.univ.filter fun j => ι (Sum.inr j) ∈ S
  have hc : SL.card + SR.card = S.card := split_card S ι
  by_cases hL : SL.card = r
  · have hR : SR.card ≠ s := by omega
    have hz := hB SR hR ((v ∘ finSumFinEquiv) ∘ σ ∘ Sum.inr)
      (by
        intro j hj
        apply hp (ι (Sum.inr j))
        simpa [SR] using hj)
      (by
        intro j hj
        apply hm (ι (Sum.inr j))
        simpa [SR] using hj)
    simp only [hz, mul_zero]
  · have hz := hA SL hL ((v ∘ finSumFinEquiv) ∘ σ ∘ Sum.inl)
      (by
        intro j hj
        apply hp (ι (Sum.inl j))
        simpa [SL] using hj)
      (by
        intro j hj
        apply hm (ι (Sum.inl j))
        simpa [SL] using hj)
    simp only [hz, zero_mul, mul_zero]

end SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorPreservation
