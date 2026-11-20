import SGPT.Foundations.Analysis.Pending.NaturalComplexPureWordPairing
import SGPT.Foundations.Analysis.Pending.NaturalComplexPositiveProductSpanStep

/-!
# Genuine usual pure (p,p) inclusion in the original real formSpan

Actual pure coordinate words are internally paired and factored by the
proved normalized exterior product. Faithful slot transport and unique
complexification reflection yield the original real span inclusion.
The reverse preservation theorem and full equality remain separate.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalPurePPPositiveSpanInclusion

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open NaturalComplexCoordinateEigenbasis NaturalComplexPureExteriorExpansion
open NaturalComplexExteriorGeneratorProducts NaturalComplexPureWordPairing
open NaturalComplexPositiveProductSpanStep NaturalComplexifiedRealSpan
open NaturalComplexOneOneRealComponents NaturalComplexExteriorProductTransport

theorem zero_mem_complexFormSpan {n : ℕ}
    (F : complexification n [⋀^Fin 0]→ₗ[ℂ] ℂ) :
    F ∈ complexFormSpan n 0 := by
  let v₀ : Fin 0 → ComplexModel n := isEmptyElim
  let c : ℂ := F (fun j => realEmbedding n (v₀ j))
  have hF : F = c • realExtension n 0 coordinateWedgeUnit := by
    ext v
    have hv : v = fun j => realEmbedding n (v₀ j) := Subsingleton.elim _ _
    rw [hv]
    have hu : (coordinateWedgeUnit : StronglyPositiveForms.RealForm n 0) v₀ = 1 := rfl
    simp only [AlternatingMap.smul_apply, realExtension_realEmbedding, hu,
      Complex.ofReal_one, smul_eq_mul, mul_one]
    rfl
  rw [hF]
  exact (complexFormSpan n 0).smul_mem c (unit_mem_complexFormSpan n)

theorem pairedWord_mem_complexFormSpan {n p : ℕ} (j k : Fin p → Fin n) :
    exteriorMonomial (pairedWord j k) ∈ complexFormSpan n p := by
  induction p with
  | zero => exact zero_mem_complexFormSpan _
  | succ p ih =>
    rw [pairedWord_succ, ← exteriorMonomial_complexWedge]
    exact complexWedge_mem_complexFormSpan _ _
      (ih (fun r => j r.castSucc) (fun r => k r.castSucc))
      (mixedGenerator_mem_complexFormSpan (j (Fin.last p)) (k (Fin.last p)))

theorem pureWord_mem_complexFormSpan {n p : ℕ}
    (a : Fin (2 * p) → Fin 2 × Fin n) (ha : (holomorphicSlots a).card = p) :
    exteriorMonomial a ∈ complexFormSpan n p := by
  obtain ⟨j, k, σ, hσ⟩ := exists_pairedWord_permutation a ha
  have ht : pairedWord j k ∘ σ.symm = a := by
    rw [← hσ]
    funext i
    simp
  rw [← ht, exteriorMonomial_word_perm, Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact (complexFormSpan n p).smul_mem _ (pairedWord_mem_complexFormSpan j k)

theorem holomorphicSlots_card_domCongr {n d e : ℕ}
    (a : Fin d → Fin 2 × Fin n) (ι : Fin d ≃ Fin e) :
    (holomorphicSlots (a ∘ ι.symm)).card = (holomorphicSlots a).card := by
  classical
  have he : {i : Fin d // (a i).1 = 0} ≃
      {j : Fin e // ((a ∘ ι.symm) j).1 = 0} :=
    Equiv.subtypeEquiv ι (by intro i; simp)
  simpa only [Fintype.card_subtype, holomorphicSlots] using (Fintype.card_congr he).symm

private theorem pure_coefficient_zero_twice {n p : ℕ}
    (F : complexification n [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ)
    (hF : IsPureBidegree p p (F.domDomCongr (finCongr (two_mul p))))
    (a : Fin (2 * p) → Fin 2 × Fin n) (ha : (holomorphicSlots a).card ≠ p) :
    F (fun j => eigenVector (a j)) = 0 := by
  let e : Fin (2 * p) ≃ Fin (p + p) := finCongr (two_mul p)
  have hz := pure_coefficient_eq_zero (F.domDomCongr e) hF (a ∘ e.symm)
    (by rw [holomorphicSlots_card_domCongr]; exact ha)
  simpa only [AlternatingMap.domDomCongr_apply, Function.comp_def,
    Equiv.symm_apply_apply] using hz

theorem pure_mem_complexFormSpan {n p : ℕ}
    (F : complexification n [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ)
    (hF : IsPureBidegree p p (F.domDomCongr (finCongr (two_mul p)))) :
    F ∈ complexFormSpan n p := by
  classical
  rw [alternating_eq_exterior_sum F]
  apply (complexFormSpan n p).smul_mem
  apply (complexFormSpan n p).sum_mem
  intro a _
  by_cases ha : (holomorphicSlots a).card = p
  · exact (complexFormSpan n p).smul_mem _ (pureWord_mem_complexFormSpan a ha)
  · rw [pure_coefficient_zero_twice F hF a ha, zero_smul]
    exact (complexFormSpan n p).zero_mem

theorem complexify_domDomCongr {n d e : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (ι : Fin d ≃ Fin e) :
    complexify (A.domDomCongr ι) = (complexify A).domDomCongr ι := by
  symm
  apply complexify_unique
  intro v
  simpa only [AlternatingMap.domDomCongr_apply, Function.comp_def] using
    complexify_realEmbedding A (v ∘ ι)

theorem formSpan_mem_of_pureRealPP {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ)
    (hA : IsPureRealPP p (A.toAlternatingMap.domDomCongr (finCongr (two_mul p)))) :
    A ∈ LocalProductCurrents.formSpan n p := by
  unfold IsPureRealPP at hA
  rw [complexify_domDomCongr] at hA
  have hF : realExtension n (2 * p) A ∈ complexFormSpan n p :=
    pure_mem_complexFormSpan _ hA
  exact (realExtension_mem_complexSpan_iff (LocalProductCurrents.formSpan n p) A).mp hF

end SGPT.Foundations.Analysis.Pending.NaturalPurePPPositiveSpanInclusion
