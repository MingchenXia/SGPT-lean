import SGPT.Foundations.Analysis.Pending.WeightedTruncationNormalThreshold
import SGPT.Foundations.Analysis.Pending.SNCHolomorphicTestNecessity

set_option autoImplicit false

/-! # Original full coordinate orders inherit the strict truncation threshold -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.TruncatedIntegrabilityFullCoordinateOrders

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

private theorem near_product {n : ℕ} (s : Finset (Fin n)) (d : Fin n → ℕ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun z : ComplexModel n => ∏ i ∈ s, z i ^ d i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using
      eventually_differentiableAt_const (E := ComplexModel n) (1 : ℂ)
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        eventually_differentiableAt_mul
          (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (d i)) ih

private theorem mk_product {n : ℕ} (s : Finset (Fin n)) (d : Fin n → ℕ) :
    HolGerm.mk (fun z : ComplexModel n => ∏ i ∈ s, z i ^ d i) (near_product s d) =
      ∏ i ∈ s, HolGerm.mk (fun z : ComplexModel n => z i)
        (eventually_differentiableAt_coordinate i) ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact (HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)).trans
        (HolGerm.mk_one (E := ComplexModel n))
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      rw [HolGerm.mk_mul (fun z : ComplexModel n => z i ^ d i)
        (fun z : ComplexModel n => ∏ j ∈ s, z j ^ d j)
        (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate i) (d i))
        (near_product s d), HolGerm.mk_pow, ih]

/-- Genuine original factorizations and residual nondivisibility internally
bound the normal exponent by the actual full coordinate order. -/
theorem normal_exponent_le_full_coordinate_order {n : ℕ} (j : Fin n)
    (d : Fin n → ℕ) {b : ℕ} {F H G : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (hG : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ G z)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ i : Fin n, z i ^ d i)
    (hnormal : F =ᶠ[𝓝 0] fun z => z j ^ b * G z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) : b ≤ d j := by
  classical
  let t : HolGerm (ComplexModel n) := HolGerm.mk (fun z : ComplexModel n => z j)
    (eventually_differentiableAt_coordinate j)
  let P : HolGerm (ComplexModel n) := ∏ i ∈ (Finset.univ : Finset (Fin n)).erase j,
    HolGerm.mk (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i) ^ d i
  let R : HolGerm (ComplexModel n) := HolGerm.mk H hH * P
  have ht : Prime t := HolomorphicCoordinatePrime.prime_coordinate_germ j
  have hnotP : ¬t ∣ P := by
    apply ht.not_dvd_finsetProd
    intro i hi hdiv
    exact SNCHolomorphicTestNecessity.coordinate_germ_not_dvd_of_ne
      (Finset.mem_erase.mp hi).1 (ht.dvd_of_dvd_pow hdiv)
  have hnotR : ¬t ∣ R := ht.not_dvd_mul hnot hnotP
  have hfull : HolGerm.mk F hF = t ^ d j * R := by
    calc
      _ = HolGerm.mk (fun z : ComplexModel n => H z * ∏ i : Fin n, z i ^ d i)
          (eventually_differentiableAt_mul hH (near_product Finset.univ d)) :=
        HolGerm.mk_eq_mk_iff.mpr heq
      _ = HolGerm.mk H hH * ∏ i : Fin n,
          HolGerm.mk (fun z : ComplexModel n => z i)
            (eventually_differentiableAt_coordinate i) ^ d i := by
        rw [HolGerm.mk_mul H (fun z : ComplexModel n => ∏ i, z i ^ d i)
          hH (near_product Finset.univ d), mk_product]
      _ = _ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        dsimp only [t, P, R]
        ring
  have hbdiv : t ^ b ∣ HolGerm.mk F hF := by
    refine ⟨HolGerm.mk G hG, ?_⟩
    calc
      _ = HolGerm.mk (fun z : ComplexModel n => z j ^ b * G z)
          (eventually_differentiableAt_mul
            (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) b) hG) :=
        HolGerm.mk_eq_mk_iff.mpr hnormal
      _ = _ := by
        rw [HolGerm.mk_mul (fun z : ComplexModel n => z j ^ b) G
          (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) b) hG,
          HolGerm.mk_pow (fun z : ComplexModel n => z j)
            (eventually_differentiableAt_coordinate j) b]
  by_contra hn
  have hdb : d j + 1 ≤ b := Nat.succ_le_of_lt (lt_of_not_ge hn)
  obtain ⟨S, hS⟩ := (pow_dvd_pow t hdb).trans hbdiv
  rw [hfull, pow_succ, mul_assoc] at hS
  have hRS : R = t * S := mul_left_cancel₀ (pow_ne_zero _ ht.ne_zero) hS
  exact hnotR ⟨S, hRS⟩

/-- The original function supplies its complete coordinate orders; actual
truncation integrals internally give the last-coordinate strict threshold. -/
theorem exists_full_coordinate_factorization_with_last_threshold {m : ℕ} (A : ℕ) {q : ℝ}
    {F : ComplexModel (m + 2) → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z ≠ 0)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {HolGerm.mk (fun z : ComplexModel (m + 2) => z (Fin.last (m + 1)))
          (eventually_differentiableAt_coordinate (Fin.last (m + 1))) ^ A} ⊔
        (Ideal.span (Set.range fun i : Fin (m + 2) => HolGerm.mk
          (fun z : ComplexModel (m + 2) => z i) (eventually_differentiableAt_coordinate i))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    ∃ (d : Fin (m + 2) → ℕ) (H : ComplexModel (m + 2) → ℂ)
      (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ H z),
      (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), H z ≠ 0) ∧
      F =ᶠ[𝓝 0] (fun z => H z * ∏ i : Fin (m + 2), z i ^ d i) ∧
      (∀ i, ¬HolGerm.mk (fun z : ComplexModel (m + 2) => z i)
        (eventually_differentiableAt_coordinate i) ∣ HolGerm.mk H hH) ∧
      ∀ q' : ℝ, q' < q → q' * (A : ℝ) < (d (Fin.last (m + 1)) : ℝ) + 1 := by
  obtain ⟨d, H, hH, hHne, heq, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
  obtain ⟨b, G, hG, hnormal, _hfreq, hthreshold⟩ :=
    WeightedTruncationNormalThreshold.exists_normal_factor_with_strict_threshold A hF hne htrunc
  have hbd := normal_exponent_le_full_coordinate_order (Fin.last (m + 1)) d
    hF hH hG heq hnormal (hnot (Fin.last (m + 1)))
  refine ⟨d, H, hH, hHne, heq, hnot, ?_⟩
  intro q' hq'
  have hbdR : (b : ℝ) ≤ (d (Fin.last (m + 1)) : ℝ) := by exact_mod_cast hbd
  exact (hthreshold q' hq').trans_le (add_le_add hbdR le_rfl)

end
end SGPT.Foundations.Analysis.Pending.TruncatedIntegrabilityFullCoordinateOrders
