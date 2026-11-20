import SGPT.Foundations.Analysis.Pending.NaturalComplexBidegreeTransport
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Faithful complex extension of actual real alternating tensors

The extension is constructed from the actual real coordinate basis and its
tensor base change, then alternatized and normalized by the nonzero factorial.
No caller extension, type-equivalence or cone-span certificate is assumed.
The equality of all usual real `(p,p)` tensors with the strongly-positive
product span is a separate, still open polarization theorem.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalRealAlternatingComplexification

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open scoped TensorProduct

private def scalarMonomial {n d : ℕ} (w : Fin d → Fin (n * 2)) :
    MultilinearMap ℂ (fun _ : Fin d => NaturalComplexBidegreeTransport.complexification n) ℂ :=
  (MultilinearMap.mkPiRing ℂ (Fin d) (1 : ℂ)).compLinearMap
    (fun j => ((coordinateRealBasis n).baseChange ℂ).coord (w j))

private def coordinateMultilinear {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    MultilinearMap ℂ (fun _ : Fin d => NaturalComplexBidegreeTransport.complexification n) ℂ :=
  ∑ w : Fin d → Fin (n * 2),
    (A (fun j => coordinateRealBasis n (w j)) : ℂ) • scalarMonomial w

private theorem scalarMonomial_basis {n d : ℕ}
    (w v : Fin d → Fin (n * 2)) :
    scalarMonomial w (fun j => (coordinateRealBasis n).baseChange ℂ (v j)) =
      if w = v then 1 else 0 := by
  classical
  by_cases h : w = v
  · subst v
    simp only [scalarMonomial, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiRing_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finset.prod_const_one, one_smul, ite_true]
  · have hj : ∃ j, v j ≠ w j := by
      by_contra hn
      apply h
      funext j
      exact (not_ne_iff.mp (not_exists.mp hn j)).symm
    obtain ⟨j, hj⟩ := hj
    simp only [scalarMonomial, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiRing_apply, Module.Basis.coord_apply, smul_eq_mul, mul_one,
      if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg hj]

private theorem coordinateMultilinear_basis {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (v : Fin d → Fin (n * 2)) :
    coordinateMultilinear A (fun j => (coordinateRealBasis n).baseChange ℂ (v j)) =
      (A (fun j => coordinateRealBasis n (v j)) : ℂ) := by
  classical
  simp only [coordinateMultilinear, _root_.sum_apply, _root_.smul_apply,
    scalarMonomial_basis, smul_eq_mul]
  simp

private def restrictMulti {n d : ℕ}
    (F : MultilinearMap ℂ (fun _ : Fin d => NaturalComplexBidegreeTransport.complexification n) ℂ) :
    MultilinearMap ℝ (fun _ : Fin d => ComplexModel n) ℂ :=
  (F.restrictScalars ℝ).compLinearMap (fun _ => NaturalComplexBidegreeTransport.realEmbedding n)

private theorem coordinateMultilinear_realEmbedding {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (v : Fin d → ComplexModel n) :
    coordinateMultilinear A (fun j => NaturalComplexBidegreeTransport.realEmbedding n (v j)) = (A v : ℂ) := by
  have h : restrictMulti (coordinateMultilinear A) =
      Complex.ofRealCLM.toLinearMap.compMultilinearMap A.toMultilinearMap := by
    apply Module.Basis.ext_multilinear (fun _ => coordinateRealBasis n)
    intro w
    simpa [restrictMulti, NaturalComplexBidegreeTransport.realEmbedding, Module.Basis.baseChange_apply] using
      coordinateMultilinear_basis A w
  exact congrArg (fun F => F v) h

def complexify {n d : ℕ} (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    NaturalComplexBidegreeTransport.complexification n [⋀^Fin d]→ₗ[ℂ] ℂ :=
  (d.factorial : ℂ)⁻¹ • MultilinearMap.alternatization (coordinateMultilinear A)

theorem complexify_realEmbedding {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (v : Fin d → ComplexModel n) :
    complexify A (fun j => NaturalComplexBidegreeTransport.realEmbedding n (v j)) = (A v : ℂ) := by
  classical
  let A' := Complex.ofRealCLM.toLinearMap.compAlternatingMap A
  have h : MultilinearMap.alternatization (coordinateMultilinear A)
      (fun j => NaturalComplexBidegreeTransport.realEmbedding n (v j)) =
      MultilinearMap.alternatization A'.toMultilinearMap v := by
    simp only [MultilinearMap.alternatization_apply]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    exact coordinateMultilinear_realEmbedding A (v ∘ σ)
  change (d.factorial : ℂ)⁻¹ •
    (MultilinearMap.alternatization (coordinateMultilinear A)
      (fun j => NaturalComplexBidegreeTransport.realEmbedding n (v j))) = (A v : ℂ)
  rw [h, AlternatingMap.coe_alternatization]
  simp [A', Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, Nat.factorial_ne_zero]

theorem complexify_unique {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ)
    (F : NaturalComplexBidegreeTransport.complexification n [⋀^Fin d]→ₗ[ℂ] ℂ)
    (hF : ∀ v, F (fun j => NaturalComplexBidegreeTransport.realEmbedding n (v j)) = (A v : ℂ)) :
    F = complexify A := by
  apply AlternatingMap.coe_multilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (coordinateRealBasis n).baseChange ℂ)
  intro w
  simpa [Module.Basis.baseChange_apply, NaturalComplexBidegreeTransport.realEmbedding] using
    (hF (fun j => coordinateRealBasis n (w j))).trans
      (complexify_realEmbedding A (fun j => coordinateRealBasis n (w j))).symm

theorem complexify_injective (n d : ℕ) :
    Function.Injective (complexify (n := n) (d := d)) := by
  intro A B h
  ext v
  apply Complex.ofReal_injective
  rw [← complexify_realEmbedding A v, ← complexify_realEmbedding B v, h]

theorem complexify_compLinearMap {m n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ)
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n) :
    complexify (A.compLinearMap L) = (complexify A).compLinearMap (L.baseChange ℂ) := by
  symm
  apply complexify_unique
  intro v
  simpa [AlternatingMap.compLinearMap_apply, NaturalComplexBidegreeTransport.realEmbedding] using
    complexify_realEmbedding A (fun j => L (v j))

def IsPureRealPP {n : ℕ} (p : ℕ)
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) : Prop :=
  NaturalComplexBidegreeTransport.IsPureBidegree p p (complexify A)

theorem isPureRealPP_iff_eigenblocks {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) :
    IsPureRealPP p A ↔
      ∀ (S : Finset (Fin (p + p))), S.card ≠ p →
        ∀ v, (∀ j, j ∈ S → NaturalComplexBidegreeTransport.extendedJ n (v j) = Complex.I • v j) →
          (∀ j, j ∉ S → NaturalComplexBidegreeTransport.extendedJ n (v j) = -Complex.I • v j) →
          complexify A v = 0 :=
  NaturalComplexBidegreeTransport.isPureBidegree_iff_eigenblocks (complexify A)

theorem isPureRealPP_compLinearMap {m n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ)
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v)
    (hA : IsPureRealPP p A) : IsPureRealPP p (A.compLinearMap L) := by
  unfold IsPureRealPP
  rw [complexify_compLinearMap]
  exact NaturalComplexBidegreeTransport.isPureBidegree_comp (complexify A) L hL hA

end SGPT.Foundations.Analysis.Pending.NaturalRealAlternatingComplexification
