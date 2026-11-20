import SGPT.Foundations.Analysis.Pending.NaturalComplexCoordinateEigenbasis

/-!
# Genuine pure-bidegree exterior coordinate expansion

Actual covector monomials are alternatized with their literal permutation
signs. Every actual alternating form has its internally derived coordinate
expansion with precisely the inverse factorial. Pure bidegree internally
kills every wrong holomorphic-slot coefficient, and alternation kills
repeated coordinate words. No positive-product-span or usual-class theorem
is asserted.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorExpansion

open NaturalComplexBidegreeTransport NaturalComplexCoordinateEigenbasis

def exteriorMonomial {n d : ℕ} (a : Fin d → Fin 2 × Fin n) :
    complexification n [⋀^Fin d]→ₗ[ℂ] ℂ :=
  MultilinearMap.alternatization (coordinateMonomial a)

private theorem alternatization_smul {n d : ℕ} (c : ℂ)
    (F : MultilinearMap ℂ (fun _ : Fin d => complexification n) ℂ) :
    MultilinearMap.alternatization (c • F) = c • MultilinearMap.alternatization F := by
  classical
  ext v
  simp only [AlternatingMap.smul_apply, MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    _root_.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact smul_comm _ _ _

theorem alternating_eq_exterior_sum {n d : ℕ}
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) :
    F = (d.factorial : ℂ)⁻¹ •
      ∑ a : Fin d → Fin 2 × Fin n,
        F (fun j => eigenVector (a j)) • exteriorMonomial a := by
  classical
  have h := congrArg MultilinearMap.alternatization
    (multilinear_eq_coordinate_sum F.toMultilinearMap)
  rw [AlternatingMap.coe_alternatization] at h
  simp only [Fintype.card_fin, map_sum, alternatization_smul] at h
  calc
    F = (d.factorial : ℂ)⁻¹ • (d.factorial • F) := by
      ext v
      simp [AlternatingMap.smul_apply, nsmul_eq_mul, smul_eq_mul, Nat.factorial_ne_zero]
    _ = _ := by rw [h]; rfl

def holomorphicSlots {n d : ℕ} (a : Fin d → Fin 2 × Fin n) : Finset (Fin d) :=
  Finset.univ.filter fun j => (a j).1 = 0

theorem pure_coefficient_eq_zero {n r s : ℕ}
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ)
    (hF : IsPureBidegree r s F) (a : Fin (r + s) → Fin 2 × Fin n)
    (ha : (holomorphicSlots a).card ≠ r) :
    F (fun j => eigenVector (a j)) = 0 := by
  apply (isPureBidegree_iff_eigenblocks F).mp hF (holomorphicSlots a) ha
  · intro j hj
    have hp : (a j).1 = 0 := by simpa [holomorphicSlots] using hj
    simpa [hp] using eigenVector_extendedJ (a j)
  · intro j hj
    have hm : (a j).1 ≠ 0 := by simpa [holomorphicSlots] using hj
    simpa [hm] using eigenVector_extendedJ (a j)

theorem pure_eq_exterior_sum {n r s : ℕ}
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ)
    (hF : IsPureBidegree r s F) :
    F = ((r + s).factorial : ℂ)⁻¹ •
      ∑ a ∈ (Finset.univ : Finset (Fin (r + s) → Fin 2 × Fin n)).filter
          (fun a => (holomorphicSlots a).card = r),
        F (fun j => eigenVector (a j)) • exteriorMonomial a := by
  classical
  calc
    F = ((r + s).factorial : ℂ)⁻¹ •
        ∑ a : Fin (r + s) → Fin 2 × Fin n,
          F (fun j => eigenVector (a j)) • exteriorMonomial a := alternating_eq_exterior_sum F
    _ = _ := by
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (holomorphicSlots a).card = r
      · simp [ha]
      · simp [ha, pure_coefficient_eq_zero F hF a ha]

theorem coefficient_eq_zero_of_not_injective {n d : ℕ}
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ)
    (a : Fin d → Fin 2 × Fin n) (ha : ¬Function.Injective a) :
    F (fun j => eigenVector (a j)) = 0 := by
  apply F.map_eq_zero_of_not_injective
  intro hv
  apply ha
  intro i j hij
  exact hv (congrArg eigenVector hij)

end SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorExpansion
