import SGPT.PSH.OriginalPrimeFactorization
import SGPT.PSH.CartierLogarithmicRemainder

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff


private theorem coe_mul_finite_sum {ι : Type*} (s : Finset ι) (f : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ s, f i) = ∑ i ∈ s, (c : EReal) * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

/-- The ORIGINAL nonzero function and arbitrary original bounded remainder
produce one actual prime open set carrying a literal logarithmic formula
and ONE finite bound on the ENTIRE SAME open set, with every pole retained. -/
theorem exists_common_open_prime_logarithmic_remainder {m : ℕ}
    (f : ComplexModel (m + 1) → ℂ) (hf : OkaRelationSheaf.HolAt f 0)
    (hF : HolGerm.mk f hf ≠ 0)
    (N : Set (ComplexModel (m + 1))) (hN : N ∈ 𝓝 0)
    (c : ℚ) (hc : 0 < c) (u : ComplexModel (m + 1) → EReal)
    (R : ComplexModel (m + 1) → ℝ) (hR : BoundedRealGermAt R 0)
    (hu : u =ᶠ[𝓝 0] fun z => ((c : ℝ) : EReal) * logNormSq (f z) + (R z : EReal)) :
    ∃ Ω : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ Ω ∧
      (Ω : Set (ComplexModel (m + 1))) ⊆ N ∧
      ∃ (r : ℕ) (q : Fin r → ComplexModel (m + 1) → ℂ)
        (hq : ∀ i, OkaRelationSheaf.HolAt (q i) 0) (a : Fin r → ℕ)
        (V : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) Ω)
        (b : ComplexModel (m + 1) → ℝ) (C : ℝ),
        (∀ i, Prime (HolGerm.mk (q i) (hq i))) ∧
        (∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j)) ∧
        (∀ i, 0 < a i ∧ a i = multiplicity (HolGerm.mk (q i) (hq i)) (HolGerm.mk f hf) ∧
          0 < c * (a i : ℚ) ∧ (V i).carrier = {y : Ω | q i y = 0} ∧ (V i).dim = m ∧
          (∀ y : Ω, HolomorphicAt (m + 1) (fun z : Ω => q i z) y) ∧
          (vanishingIdeal (n := m + 1) (V i).carrier).IsInvertible ∧
          ∀ (y : Ω) (d : Ω → ℂ),
            (vanishingIdeal (n := m + 1) (V i).carrier).mem y d ↔
              IsInSpanAt (n := m + 1) (· = fun z : Ω => q i z) y d) ∧
        0 ≤ C ∧ (∀ z ∈ Ω, |b z| ≤ C) ∧
        (∀ z ∈ Ω, u z = (∑ i, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) *
          logNormSq (q i z)) + (b z : EReal)) ∧
        ∀ y : Ω, f y = 0 ↔ ∃ i, y ∈ (V i).carrier := by
  classical
  obtain ⟨r, q, hq, a, v, hv, hprime, hnot, hmult, hv0, hvnon, hfactor⟩ :=
    exists_original_distinct_prime_factorization f hf hF
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlogcont : ContinuousAt (fun z => Real.log (‖v z‖ ^ 2)) 0 :=
    (hv.self_of_nhds.continuousAt.norm.pow 2).log
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0))
  let b : ComplexModel (m + 1) → ℝ := fun z => R z + (c : ℝ) * Real.log (‖v z‖ ^ 2)
  have hb : BoundedRealGermAt b 0 :=
    hR.add (boundedRealGermAt_of_continuousAt (continuousAt_const.mul hlogcont))
  obtain ⟨C, hC, hbC⟩ := hb
  let N' : Set (ComplexModel (m + 1)) := {z | z ∈ N ∧ OkaRelationSheaf.HolAt v z ∧
    v z ≠ 0 ∧ f z = (∏ i, q i z ^ a i) * v z ∧ |b z| ≤ C ∧
    u z = ((c : ℝ) : EReal) * logNormSq (f z) + (R z : EReal)}
  have hN' : N' ∈ 𝓝 0 := by
    filter_upwards [hN, OkaRelationSheaf.HolAt.eventually hv, hvnon, hfactor, hbC, hu]
      with z hz hhol hne hfac hbz huz
    exact ⟨hz, hhol, hne, hfac, hbz, huz⟩
  obtain ⟨Ω, h0Ω, hΩN', V, hV⟩ := exists_common_open_prime_carriers q hq hprime hnot N' hN'
  refine ⟨Ω, h0Ω, fun z hz => (hΩN' hz).1, r, q, hq, a, V, b, C,
    hprime, hnot, ?_, hC, fun z hz => (hΩN' hz).2.2.2.2.1, ?_, ?_⟩
  · intro i
    exact ⟨(hmult i).1, (hmult i).2, mul_pos hc (by exact_mod_cast (hmult i).1), hV i⟩
  · intro z hz
    have h := hΩN' hz
    rw [h.2.2.2.2.2, h.2.2.2.1, logNormSq_geometric_product, logNormSq_of_ne_zero h.2.2.1,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top (c : ℝ)),
      coe_mul_finite_sum _ _ hcR.le]
    have hsum : (∑ i : Fin r, ((c : ℝ) : EReal) *
        (((a i : ℝ) : EReal) * logNormSq (q i z))) =
        ∑ i : Fin r, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (q i z) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← EReal.coe_mul]
      congr 2
      norm_cast
    rw [hsum]
    dsimp only [b]
    rw [EReal.coe_add, EReal.coe_mul]
    ac_rfl
  · intro y
    rw [(hΩN' y.2).2.2.2.1, mul_eq_zero,
      or_iff_left (hΩN' y.2).2.2.1, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨i, _, hi⟩
      refine ⟨i, ?_⟩
      rw [(hV i).1]
      exact eq_zero_of_pow_eq_zero hi
    · rintro ⟨i, hi⟩
      rw [(hV i).1] at hi
      exact ⟨i, Finset.mem_univ i, by rw [hi, zero_pow (hmult i).1.ne']⟩

#print axioms exists_common_open_prime_logarithmic_remainder
end SGPT.PSH
