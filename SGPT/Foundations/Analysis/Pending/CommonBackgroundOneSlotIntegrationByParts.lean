import SGPT.Foundations.Analysis.Pending.CanonicalAffineMixedPolynomials

set_option autoImplicit false

/-!
# Actual common-background singular one-slot integration by parts

Lu, arXiv:2005.04264v1, Theorem 1.2. Recover the first affine
coefficient from the actual positive diagonal identity and actual mixed
polynomial expansions, then use actual slot symmetry and cancel the dimension.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.CommonBackgroundOneSlotIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open NonPluripolarMixedCutoffs DeepCoincidenceIntegrationByParts GlobalMultilinearExpansion
open CanonicalAffineMixedPolynomials PositiveAffineDiagonalIntegrationByParts
open BinarySlotPolynomialCoefficients PolynomialCoefficientRecovery

noncomputable section

/-- The first coefficient on the left equals the constant coefficient before
multiplication by the affine parameter on the right. -/
theorem first_coefficient_eq_zero_coefficient {G H : Type*} [Fintype G] [Fintype H]
    (k : G → ℕ) (l : H → ℕ) (d : G → ℝ) (e : H → ℝ) (N0 : ℕ)
    (h : ∀ N : ℕ, N0 ≤ N → (∑ g, (N : ℝ) ^ k g * d g) =
      (N : ℝ) * ∑ z, (N : ℝ) ^ l z * e z) :
    (∑ g with k g = 1, d g) = ∑ z with l z = 0, e z := by
  classical
  let degree : G ⊕ H → ℕ := Sum.elim k (fun z => l z + 1)
  let coeff : G ⊕ H → ℝ := Sum.elim d (fun z => -e z)
  have hz (N : ℕ) (hN : N0 ≤ N) : ∑ z, (N : ℝ) ^ degree z * coeff z = 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ g, (N : ℝ) ^ k g * d g) + (∑ z, (N : ℝ) ^ (l z + 1) * (-e z)) = 0
    have hr : (∑ z, (N : ℝ) ^ (l z + 1) * (-e z)) =
        -((N : ℝ) * ∑ z, (N : ℝ) ^ l z * e z) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [pow_succ]
      ring
    rw [hr]
    exact sub_eq_zero.mpr (h N hN)
  have hc := sum_coeff_eq_zero_of_forall_nat_ge degree coeff N0 hz 1
  rw [Finset.sum_filter, Fintype.sum_sum_type] at hc
  change (∑ g, if k g = 1 then d g else 0) +
    (∑ z, if l z + 1 = 1 then -e z else 0) = 0 at hc
  have hr : (∑ z, if l z + 1 = 1 then -e z else 0) =
      -(∑ z, if l z = 0 then e z else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : l z = 0
    · simp [hz]
    · simp [hz]
  rw [hr] at hc
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sub_eq_zero.mp hc

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- Every actual first diagonal coefficient is the original reference one-slot measure. -/
theorem globalMixedMeasure_oneSlotChoice {theta : ClosedRealOneOneForm n M}
    {a phi : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hphi : IsThetaPshPotential theta.val phi) (k : Fin n)
    (hs : ∀ i, ThetaPlurisubharmonic theta.val (binaryPotentialTuple (oneSlotChoice k) a phi i)) :
    globalMixedMeasure (fun _ => theta) (binaryPotentialTuple (oneSlotChoice k) a phi) hs =
      binaryMixedMeasure theta hphi.1 hphi.1 ha.1 (fun _ => false) k := by
  refine globalMixedMeasure_congr rfl ?_ _ _
  funext i
  by_cases hi : i = k
  · subst hi
    simp [binaryPotentialTuple, oneSlotChoice]
  · simp [binaryPotentialTuple, oneSlotChoice, hi]

omit [BorelSpace M] in
/-- Every actual constant affine coefficient retains the original distinguished current. -/
theorem globalMixedMeasure_affineChoicePot_zero {theta : ClosedRealOneOneForm n M}
    {a b phi r : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hb : IsThetaPshPotential theta.val b) (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential theta.val r) (sigma : Fin n → Bool) (k : Fin n) :
    globalMixedMeasure (fun _ => theta)
      (fun i => affineChoicePot sigma k a b phi r (i, false))
      (fun i => (isThetaPshPotential_affineChoicePot ha hb hphi hr sigma k (i, false)).1) =
      binaryMixedMeasure theta hphi.1 hphi.1 hr.1 (fun _ => false) k := by
  refine globalMixedMeasure_congr rfl ?_ _ _
  funext i
  by_cases hi : i = k
  · subst hi
    simp [affineChoicePot]
  · simp [affineChoicePot, binaryPotentialTuple, hi]

/-- Slot symmetry identifies the actual reference one-slot measures. -/
theorem binaryMixedMeasure_reference_slot_eq {theta : ClosedRealOneOneForm n M}
    {r phi : M → EReal} (hr : IsThetaPshPotential theta.val r)
    (hphi : IsThetaPshPotential theta.val phi) (i k : Fin n) :
    binaryMixedMeasure theta hphi.1 hphi.1 hr.1 (fun _ => false) i =
      binaryMixedMeasure theta hphi.1 hphi.1 hr.1 (fun _ => false) k := by
  classical
  have h := GlobalSlotPerm.globalMixedMeasure_perm
    (thetaPlurisubharmonic_binaryUpdatedTuple theta hphi.1 hphi.1 hr.1 (fun _ => false) i)
    (Equiv.swap i k)
  have hpot : (fun j => Function.update (binaryPotentialTuple (fun _ => false) phi phi) i r
      (Equiv.swap i k j)) = Function.update (binaryPotentialTuple (fun _ => false) phi phi) k r := by
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hne : Equiv.swap i k j ≠ i := by
        intro he
        apply hjk
        apply (Equiv.swap i k).injective
        simpa using he
      simp [Function.update_of_ne hjk, Function.update_of_ne hne, binaryPotentialTuple]
  exact h.symm.trans (globalMixedMeasure_congr rfl hpot _ _)

/-- The actual first affine coefficient gives the sum of original reference
one-slot integrals on both sides, with no polynomial or IBP premise. -/
theorem sum_integral_sub_reference_slot_symm (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {a b p q phi : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (hphi : IsThetaPshPotential theta.val phi)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ) :
    (∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂binaryMixedMeasure theta hphi.1 hphi.1 ha.1 (fun _ => false) k) -
       (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂binaryMixedMeasure theta hphi.1 hphi.1 hb.1 (fun _ => false) k))) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta hphi.1 hphi.1 hp.1 (fun _ => false) k) -
       (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta hphi.1 hphi.1 hq.1 (fun _ => false) k)) := by
  classical
  have hbin (r : M → EReal) (hr : IsThetaPshPotential theta.val r) (g : Fin n → Bool) :
      ∀ i, ThetaPlurisubharmonic theta.val (binaryPotentialTuple g r phi i) := by
    intro i
    unfold binaryPotentialTuple
    split
    · exact hr.1
    · exact hphi.1
  let lcoeff (r : M → EReal) (hr : IsThetaPshPotential theta.val r) (g : Fin n → Bool) : ℝ :=
    ∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (binaryPotentialTuple g r phi) (hbin r hr g)
  let left (g : Fin n → Bool) : ℝ := lcoeff a ha g - lcoeff b hb g
  let rcoeff (r : M → EReal) (hr : IsThetaPshPotential theta.val r)
      (k : Fin n) (g : Fin n → Bool) : ℝ :=
    ∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂globalMixedMeasure (fun _ => theta)
        (fun i => affineChoicePot (stepSelector k) k a b phi r (i, g i))
        (fun i => (isThetaPshPotential_affineChoicePot ha hb hphi hr (stepSelector k) k (i, g i)).1)
  let right (z : Fin n × (Fin n → Bool)) : ℝ :=
    if z.2 z.1 = false then rcoeff p hp z.1 z.2 - rcoeff q hq z.1 z.2 else 0
  have hpoly (N : ℕ) (hN : 1 ≤ N) :
      (∑ g, (N : ℝ) ^ binaryDegree g * left g) =
      (N : ℝ) * ∑ z : Fin n × (Fin n → Bool), (N : ℝ) ^ binaryDegree z.2 * right z := by
    have ht : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h := diagonal_integral_sub_eq_mul_sum_positiveAffine omega ha hb hp hq hphi hab hpq ht
    have hleft :
        ((∫ x, canonicalERealDiffToReal (p x) (q x)
          ∂globalMixedMeasure (fun _ => ((N : ℝ) + 1) • theta)
            (fun _ => PositiveCombinationCanonicalWeights.positiveCombination (N : ℝ) 1 a phi)
            (fun _ => (isThetaPshPotential_positiveAffine ha hphi ht).1)) -
         (∫ x, canonicalERealDiffToReal (p x) (q x)
          ∂globalMixedMeasure (fun _ => ((N : ℝ) + 1) • theta)
            (fun _ => PositiveCombinationCanonicalWeights.positiveCombination (N : ℝ) 1 b phi)
            (fun _ => (isThetaPshPotential_positiveAffine hb hphi ht).1))) =
        ∑ g, (N : ℝ) ^ binaryDegree g * left g := by
      refine (congrArg₂ (fun x y : ℝ => x - y)
        (integral_canonicalDiff_positiveAffine_diagonal omega hp hq hpq ha hphi ht)
        (integral_canonicalDiff_positiveAffine_diagonal omega hp hq hpq hb hphi ht)).trans ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      change (N : ℝ) ^ binaryDegree g * lcoeff a ha g -
        (N : ℝ) ^ binaryDegree g * lcoeff b hb g =
        (N : ℝ) ^ binaryDegree g * (lcoeff a ha g - lcoeff b hb g)
      ring
    have hright :
        (∑ k : Fin n,
          ((∫ x, canonicalERealDiffToReal (a x) (b x)
            ∂affineBinaryMixedMeasure ha hb hphi hp ht (stepSelector k) k) -
           (∫ x, canonicalERealDiffToReal (a x) (b x)
            ∂affineBinaryMixedMeasure ha hb hphi hq ht (stepSelector k) k))) =
        ∑ z : Fin n × (Fin n → Bool), (N : ℝ) ^ binaryDegree z.2 * right z := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc
        _ = (∑ g with g k = false, (N : ℝ) ^ binaryDegree g * rcoeff p hp k g) -
            (∑ g with g k = false, (N : ℝ) ^ binaryDegree g * rcoeff q hq k g) :=
          congrArg₂ (fun x y : ℝ => x - y)
            (integral_canonicalDiff_affineBinaryMixedMeasure omega ha hb hab ha hb hphi hp ht
              (stepSelector k) k)
            (integral_canonicalDiff_affineBinaryMixedMeasure omega ha hb hab ha hb hphi hq ht
              (stepSelector k) k)
        _ = _ := by
          rw [← Finset.sum_sub_distrib, Finset.sum_filter]
          refine Finset.sum_congr rfl fun g _ => ?_
          change (if g k = false then
              (N : ℝ) ^ binaryDegree g * rcoeff p hp k g -
                (N : ℝ) ^ binaryDegree g * rcoeff q hq k g else 0) =
            (N : ℝ) ^ binaryDegree g *
              (if g k = false then rcoeff p hp k g - rcoeff q hq k g else 0)
          by_cases hg : g k = false
          · simp only [hg, if_true, mul_sub]
          · simp [hg]
    exact hleft.symm.trans (h.trans (congrArg (fun x : ℝ => (N : ℝ) * x) hright))
  have hc := first_coefficient_eq_zero_coefficient binaryDegree
    (fun z : Fin n × (Fin n → Bool) => binaryDegree z.2) left right 1 hpoly
  rw [sum_binary_degree_one] at hc
  have hl : (∑ i : Fin n, left (oneSlotChoice i)) =
      ∑ i : Fin n,
        ((∫ x, canonicalERealDiffToReal (p x) (q x)
          ∂binaryMixedMeasure theta hphi.1 hphi.1 ha.1 (fun _ => false) i) -
         (∫ x, canonicalERealDiffToReal (p x) (q x)
          ∂binaryMixedMeasure theta hphi.1 hphi.1 hb.1 (fun _ => false) i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg₂ (fun x y : ℝ => x - y)
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
        (globalMixedMeasure_oneSlotChoice ha hphi i (hbin a ha (oneSlotChoice i))))
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
        (globalMixedMeasure_oneSlotChoice hb hphi i (hbin b hb (oneSlotChoice i))))
  have hr : (∑ z : Fin n × (Fin n → Bool) with binaryDegree z.2 = 0, right z) =
      ∑ k : Fin n,
        ((∫ x, canonicalERealDiffToReal (a x) (b x)
          ∂binaryMixedMeasure theta hphi.1 hphi.1 hp.1 (fun _ => false) k) -
         (∫ x, canonicalERealDiffToReal (a x) (b x)
          ∂binaryMixedMeasure theta hphi.1 hphi.1 hq.1 (fun _ => false) k)) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, sum_binary_degree_zero]
    exact congrArg₂ (fun x y : ℝ => x - y)
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
        (globalMixedMeasure_affineChoicePot_zero ha hb hphi hp (stepSelector k) k))
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
        (globalMixedMeasure_affineChoicePot_zero ha hb hphi hq (stepSelector k) k))
  exact hl.symm.trans (hc.trans hr)

/-- Actual common-background singular one-slot integration by parts. -/
theorem integral_sub_reference_slot_symm (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {a b p q phi : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (hphi : IsThetaPshPotential theta.val phi)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ)
    (i0 : Fin n) :
    ((∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂binaryMixedMeasure theta hphi.1 hphi.1 ha.1 (fun _ => false) i0) -
     (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂binaryMixedMeasure theta hphi.1 hphi.1 hb.1 (fun _ => false) i0)) =
    (∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂binaryMixedMeasure theta hphi.1 hphi.1 hp.1 (fun _ => false) i0) -
    (∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂binaryMixedMeasure theta hphi.1 hphi.1 hq.1 (fun _ => false) i0) := by
  have h := sum_integral_sub_reference_slot_symm omega ha hb hp hq hphi hab hpq
  have hl := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
    congrArg₂ (fun x y : ℝ => x - y)
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
        (binaryMixedMeasure_reference_slot_eq ha hphi i i0))
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
        (binaryMixedMeasure_reference_slot_eq hb hphi i i0))
  have hr := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
    congrArg₂ (fun x y : ℝ => x - y)
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
        (binaryMixedMeasure_reference_slot_eq hp hphi i i0))
      (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
        (binaryMixedMeasure_reference_slot_eq hq hphi i i0))
  have hscaled := hl.symm.trans (h.trans hr)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hscaled
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have hi := i0.isLt; omega)
  exact mul_left_cancel₀ hn hscaled

end

end SGPT.Foundations.Analysis.Pending.CommonBackgroundOneSlotIntegrationByParts
