import SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorExpansion
import SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorProductTransport

/-!
# Genuine complex exterior coordinate generator factorization

Signed alternatization commutes with actual finite slot equivalences. The
actual complex exterior product of two coordinate generators is exactly
the generator of their concatenated word, and every coordinate-word
permutation has its actual sign. No higher-degree real cone-span equality
or cohomological theorem is asserted.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorGeneratorProducts

open NaturalComplexBidegreeTransport NaturalComplexCoordinateEigenbasis
open NaturalComplexPureExteriorExpansion NaturalComplexExteriorProductTransport

theorem alternatization_domDomCongr {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (F : MultilinearMap ℂ (fun _ : ι => complexification n) ℂ) :
    (MultilinearMap.alternatization F).domDomCongr e =
      MultilinearMap.alternatization (F.domDomCongr e) := by
  classical
  ext v
  simp only [AlternatingMap.domDomCongr_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  apply Fintype.sum_equiv e.permCongr
  intro σ
  simp

def concatWord {n p q : ℕ} (a : Fin p → Fin 2 × Fin n)
    (b : Fin q → Fin 2 × Fin n) : Fin (p + q) → Fin 2 × Fin n :=
  fun i => Sum.elim a b (finSumFinEquiv.symm i)

private theorem concat_multilinear {n p q : ℕ}
    (a : Fin p → Fin 2 × Fin n) (b : Fin q → Fin 2 × Fin n) :
    ((TensorProduct.lid ℂ ℂ).toLinearMap.compMultilinearMap
      (MultilinearMap.domCoprod (coordinateMonomial a) (coordinateMonomial b))).domDomCongr
        finSumFinEquiv = coordinateMonomial (concatWord a b) := by
  classical
  ext v
  simp only [MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domCoprod_apply, coordinateMonomial,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one]
  calc
    (∏ i : Fin p, eigenCovector (a i) (v (finSumFinEquiv (Sum.inl i)))) *
        (∏ j : Fin q, eigenCovector (b j) (v (finSumFinEquiv (Sum.inr j)))) =
        ∏ s : Fin p ⊕ Fin q, eigenCovector (Sum.elim a b s) (v (finSumFinEquiv s)) := by
      rw [Fintype.prod_sum_type]
      rfl
    _ = ∏ i : Fin (p + q), eigenCovector (concatWord a b i) (v i) := by
      apply Fintype.prod_equiv finSumFinEquiv
      intro s
      simp [concatWord]

theorem exteriorMonomial_complexWedge {n p q : ℕ}
    (a : Fin p → Fin 2 × Fin n) (b : Fin q → Fin 2 × Fin n) :
    complexWedge (exteriorMonomial a) (exteriorMonomial b) =
      exteriorMonomial (concatWord a b) := by
  rw [complexWedge_eq_domCoprod]
  simp only [exteriorMonomial]
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization,
    alternatization_domDomCongr, concat_multilinear]

private theorem coordinateMonomial_word_perm {n d : ℕ}
    (a : Fin d → Fin 2 × Fin n) (σ : Equiv.Perm (Fin d)) :
    coordinateMonomial (a ∘ σ) = (coordinateMonomial a).domDomCongr σ.symm := by
  classical
  ext v
  simp only [coordinateMonomial, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, MultilinearMap.domDomCongr_apply, smul_eq_mul, mul_one]
  apply Fintype.prod_equiv σ
  intro i
  change eigenCovector (a (σ i)) (v i) = eigenCovector (a (σ i)) (v (σ.symm (σ i)))
  rw [Equiv.symm_apply_apply]

theorem exteriorMonomial_word_perm {n d : ℕ}
    (a : Fin d → Fin 2 × Fin n) (σ : Equiv.Perm (Fin d)) :
    exteriorMonomial (a ∘ σ) = Equiv.Perm.sign σ • exteriorMonomial a := by
  simp only [exteriorMonomial, coordinateMonomial_word_perm]
  rw [← alternatization_domDomCongr, AlternatingMap.domDomCongr_perm,
    Equiv.Perm.sign_symm]

end SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorGeneratorProducts
