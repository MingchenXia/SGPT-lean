import SGPT.Toric.GlobalTropicalLegendreGap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Lipschitz
import SGPT.Convex.MixedAlexandrovPolynomial
import SGPT.Toric.GlobalTropicalMixedEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

noncomputable section

namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {n : ℕ}

/-- The literal interpolation on the closed time interval. The nonnegative
weights outside that interval only totalize this private definition. -/
private def legendreInterpolation (f g : RealConvexFunction E) (t : ℝ) :
    RealConvexFunction E :=
  finiteConvexWeightedSum ![f, g] ![Real.toNNReal t, Real.toNNReal (1 - t)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem legendreInterpolation_val (f g : RealConvexFunction E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    (legendreInterpolation f g t).val x = (1 - t) * g.val x + t * f.val x := by
  simp only [legendreInterpolation, finiteConvexWeightedSum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.coe_toNNReal _ ht.1,
    Real.coe_toNNReal _ (sub_nonneg.mpr ht.2)]
  ring

private def legendreEndpointTuple (f g : RealConvexFunction E) (k : ℕ) :
    Fin n → RealConvexFunction E := fun i => if (i : ℕ) < k then f else g

private def legendreBernsteinWeight (n k : ℕ) (t : ℝ) : ℝ :=
  (n.choose k : ℝ) * t ^ k * (1 - t) ^ (n - k)

/-- A binary slot map is its actual finite set of first-function slots. -/
private def legendreBinarySubsetEquiv (n : ℕ) :
    (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun a := Finset.univ.filter (fun i => a i = 0)
  invFun S i := if i ∈ S then 0 else 1
  left_inv a := by
    funext i
    have hi : a i = 0 ∨ a i = 1 := by omega
    rcases hi with hi | hi <;> simp [hi]
  right_inv S := by
    ext i
    simp

/-- The actual binary tuple is a permutation of the initial-block tuple.
The permutation is manufactured from the two finite partitions. -/
private theorem legendreEndpointTuple_subset (b : OrthonormalBasis (Fin n) ℝ E)
    (f g : RealConvexFunction E) (S : Finset (Fin n)) :
    mixedAlexandrovMeasure μ b (fun i => if i ∈ S then f else g) =
      mixedAlexandrovMeasure μ b (legendreEndpointTuple f g S.card) := by
  classical
  let p : Fin n → Prop := fun i => (i : ℕ) < S.card
  let q : Fin n → Prop := fun i => i ∈ S
  have hcard : Fintype.card {i : Fin n // p i} = Fintype.card {i : Fin n // q i} := by
    simp only [p, q, Fintype.card_subtype, Fin.card_filter_val_lt,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Nat.min_eq_right
    simpa only [Fintype.card_fin] using S.card_le_univ
  let ep : {i : Fin n // p i} ≃ {i : Fin n // q i} := Fintype.equivOfCardEq hcard
  have hcardc : Fintype.card {i : Fin n // ¬p i} =
      Fintype.card {i : Fin n // ¬q i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard]
  let en : {i : Fin n // ¬p i} ≃ {i : Fin n // ¬q i} := Fintype.equivOfCardEq hcardc
  let τ : Equiv.Perm (Fin n) := Equiv.subtypeCongr ep en
  have hτ (i : Fin n) : q (τ i) ↔ p i := by
    by_cases hi : p i
    · have he : τ i = (ep ⟨i, hi⟩ : Fin n) := by
        simp [τ, Equiv.subtypeCongr, hi]
      rw [he]
      exact iff_of_true (ep ⟨i, hi⟩).2 hi
    · have he : τ i = (en ⟨i, hi⟩ : Fin n) := by
        simp [τ, Equiv.subtypeCongr, hi]
      rw [he]
      exact iff_of_false (en ⟨i, hi⟩).2 hi
  have heq : (fun i => if τ i ∈ S then f else g) =
      legendreEndpointTuple f g S.card := by
    funext i
    change (if q (τ i) then f else g) = if p i then f else g
    simp only [hτ i]
  rw [← mixedAlexandrovMeasure_perm μ b (fun i => if i ∈ S then f else g) τ,
    heq]

/-- Group the genuine mother polynomial by the actual number of first slots. -/
private theorem legendreInterpolation_measure (b : OrthonormalBasis (Fin n) ℝ E)
    (f g : RealConvexFunction E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    alexandrovMeasure (innerₗ E) μ (fun x => ((legendreInterpolation f g t).val x : EReal)) =
      ∑ k : Fin (n + 1), Real.toNNReal (legendreBernsteinWeight n k t) •
        mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k) := by
  classical
  let c : Fin 2 → ℝ≥0 := ![Real.toNNReal t, Real.toNNReal (1 - t)]
  let A : (Fin n → Fin 2) → Measure E := fun a =>
    (∏ i, c (a i)) • mixedAlexandrovMeasure μ b (fun i => (![f, g] : Fin 2 → _) (a i))
  have hprod (S : Finset (Fin n)) :
      (∏ i : Fin n, c (if i ∈ S then 0 else 1)) =
        (Real.toNNReal t) ^ S.card * (Real.toNNReal (1 - t)) ^ (n - S.card) := by
    simp only [apply_ite, c, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : (Finset.univ.filter (fun i : Fin n => i ∉ S)).card = n - S.card := by
      rw [Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff,
        Finset.card_compl, Fintype.card_fin]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const, hc]
  have hA (S : Finset (Fin n)) :
      A ((legendreBinarySubsetEquiv n).symm S) =
        ((Real.toNNReal t) ^ S.card * (Real.toNNReal (1 - t)) ^ (n - S.card)) •
          mixedAlexandrovMeasure μ b (legendreEndpointTuple f g S.card) := by
    have hInv : (legendreBinarySubsetEquiv n).symm S =
        (fun i : Fin n => if i ∈ S then 0 else 1) := rfl
    rw [hInv]
    dsimp only [A]
    have hTuple : (fun i : Fin n => (![f, g] : Fin 2 → RealConvexFunction E)
        (if i ∈ S then 0 else 1)) = (fun i => if i ∈ S then f else g) := by
      funext i
      split_ifs <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hprod, hTuple, legendreEndpointTuple_subset μ b f g S]
  have hsum : (∑ a : Fin n → Fin 2, A a) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((Real.toNNReal t) ^ S.card * (Real.toNNReal (1 - t)) ^ (n - S.card)) •
          mixedAlexandrovMeasure μ b (legendreEndpointTuple f g S.card) := by
    calc
      (∑ a : Fin n → Fin 2, A a) = ∑ S : Finset (Fin n),
          A ((legendreBinarySubsetEquiv n).symm S) :=
        ((legendreBinarySubsetEquiv n).symm.sum_comp A).symm
      _ = _ := by
        simp_rw [hA]
        rw [Finset.powerset_univ]
  change (alexandrovMeasure (innerₗ E) μ
    (fun x => ((finiteConvexWeightedSum ![f, g] c).val x : EReal))) = _
  rw [alexandrovMeasure_finiteConvexWeightedSum μ b ![f, g] c]
  change (∑ a, A a) = _
  rw [hsum, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_powersetCard (k : ℕ) (Finset.univ : Finset (Fin n))
    (fun j : ℕ =>
      ((Real.toNNReal t) ^ j * (Real.toNNReal (1 - t)) ^ (n - j)) •
        mixedAlexandrovMeasure μ b (legendreEndpointTuple f g j))]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul]
  congr 1
  apply NNReal.eq
  have hw : 0 ≤ legendreBernsteinWeight n k t :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
      (pow_nonneg (sub_nonneg.mpr ht.2) _)
  rw [Real.coe_toNNReal _ hw]
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
    Real.coe_toNNReal _ ht.1, Real.coe_toNNReal _ (sub_nonneg.mpr ht.2),
    Finset.card_univ, Fintype.card_fin, legendreBernsteinWeight]
  ring

/-- Actual beta integral, proved by elementary integration by parts.
This is independent of all measures and includes zero exponents. -/
private theorem legendreBeta_integral (a b : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b) =
      (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  induction b generalizing a with
  | zero =>
      simp only [pow_zero, mul_one, integral_pow, one_pow,
        zero_pow (Nat.succ_ne_zero a), sub_zero, Nat.add_zero,
        Nat.factorial_zero, Nat.cast_one, mul_one, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add]
      field_simp
  | succ b ih =>
      have ha : (a + 1 : ℝ) ≠ 0 := by positivity
      have hdU (t : ℝ) : HasDerivAt (fun t : ℝ => (1 - t) ^ (b + 1))
          (-((b + 1 : ℝ) * (1 - t) ^ b)) t := by
        convert ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow (b + 1) using 1 <;>
          first | rfl | (simp only [Pi.sub_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; ring)
      have hdV (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ (a + 1) / (a + 1))
          (t ^ a) t := by
        convert ((hasDerivAt_id t).pow (a + 1)).div_const (a + 1 : ℝ) using 1 <;>
          first | rfl | (simp only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; field_simp)
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (u := fun t => (1 - t) ^ (b + 1)) (v := fun t => t ^ (a + 1) / (a + 1))
        (u' := fun t => -((b + 1 : ℝ) * (1 - t) ^ b)) (v' := fun t => t ^ a)
        (by fun_prop) (by fun_prop) (fun t _ => hdU t) (fun t _ => hdV t)
        ((by fun_prop : Continuous (fun t : ℝ => -((b + 1 : ℝ) * (1 - t) ^ b))).intervalIntegrable 0 1)
        ((by fun_prop : Continuous (fun t : ℝ => t ^ a)).intervalIntegrable 0 1)
      have hrec : (∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ (b + 1)) =
          ((b + 1 : ℝ) / (a + 1)) * (∫ t in (0 : ℝ)..1, t ^ (a + 1) * (1 - t) ^ b) := by
        have hfun (t : ℝ) : -((b + 1 : ℝ) * (1 - t) ^ b) * (t ^ (a + 1) / (a + 1)) =
            -((b + 1 : ℝ) / (a + 1)) * (t ^ (a + 1) * (1 - t) ^ b) := by ring
        simp_rw [hfun] at hibp
        have hL : (fun t : ℝ => (1 - t) ^ (b + 1) * t ^ a) =
            (fun t : ℝ => t ^ a * (1 - t) ^ (b + 1)) := by
          funext t
          ring
        rw [hL] at hibp
        simpa only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero b),
          zero_pow (Nat.succ_ne_zero a), zero_div, zero_mul, mul_zero,
          one_pow, intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
          zero_sub, neg_mul, neg_neg] using hibp
      rw [hrec, ih]
      have hidx : a + (b + 1) + 1 = (a + 1) + b + 1 := by omega
      rw [hidx, Nat.factorial_succ a, Nat.factorial_succ b]
      push_cast
      field_simp

private theorem legendreBernstein_integral (k : Fin (n + 1)) :
    (∫ t in (0 : ℝ)..1, legendreBernsteinWeight n k t) = (n + 1 : ℝ)⁻¹ := by
  simp only [legendreBernsteinWeight, mul_assoc, intervalIntegral.integral_const_mul,
    legendreBeta_integral]
  have hkn : (k : ℕ) ≤ n := by omega
  have hi : (k : ℕ) + (n - k) + 1 = n + 1 := by omega
  rw [hi, Nat.factorial_succ]
  have hc : (n.choose k : ℝ) * ((k : ℕ).factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hc]

/-- The time average is manufactured from the SAME actual mixed measures.
Endpoint signed L1 is the natural hypothesis; no polynomial or integral
identity is supplied by the caller. -/
theorem integral_interpolation_alexandrov_eq_endpoint_average
    (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E)
    (a : E → ℝ) (_ha : Measurable a)
    (hi : ∀ k : Fin (n + 1), Integrable a
      (mixedAlexandrovMeasure μ b (fun i : Fin n => if (i : ℕ) < (k : ℕ) then f else g))) :
    (∀ t ∈ Icc (0 : ℝ) 1,
      alexandrovMeasure (innerₗ E) μ (fun x => ((finiteConvexWeightedSum ![f, g]
          ![Real.toNNReal t, Real.toNNReal (1 - t)]).val x : EReal)) =
        ∑ k : Fin (n + 1), Real.toNNReal ((n.choose (k : ℕ) : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - k)) •
          mixedAlexandrovMeasure μ b (fun i : Fin n => if (i : ℕ) < (k : ℕ) then f else g) ∧
      Integrable a (alexandrovMeasure (innerₗ E) μ
        (fun x => ((finiteConvexWeightedSum ![f, g]
          ![Real.toNNReal t, Real.toNNReal (1 - t)]).val x : EReal)))) ∧
    IntervalIntegrable (fun t => ∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
      (fun x => ((finiteConvexWeightedSum ![f, g]
          ![Real.toNNReal t, Real.toNNReal (1 - t)]).val x : EReal))) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
      (fun x => ((finiteConvexWeightedSum ![f, g]
          ![Real.toNNReal t, Real.toNNReal (1 - t)]).val x : EReal))) =
      (n + 1 : ℝ)⁻¹ * ∑ k : Fin (n + 1),
        ∫ x, a x ∂mixedAlexandrovMeasure μ b (fun i : Fin n => if (i : ℕ) < (k : ℕ) then f else g) := by
  classical
  change (∀ t ∈ Icc (0 : ℝ) 1,
      alexandrovMeasure (innerₗ E) μ (fun x => ((legendreInterpolation f g t).val x : EReal)) =
        ∑ k : Fin (n + 1), Real.toNNReal (legendreBernsteinWeight n k t) •
          mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k) ∧
      Integrable a (alexandrovMeasure (innerₗ E) μ
        (fun x => ((legendreInterpolation f g t).val x : EReal)))) ∧
    IntervalIntegrable (fun t => ∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
      (fun x => ((legendreInterpolation f g t).val x : EReal))) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
      (fun x => ((legendreInterpolation f g t).val x : EReal))) =
      (n + 1 : ℝ)⁻¹ * ∑ k : Fin (n + 1),
        ∫ x, a x ∂mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k)

  let J : Fin (n + 1) → ℝ := fun k =>
    ∫ x, a x ∂mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k)
  have hw (k : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ legendreBernsteinWeight n k t := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
      (pow_nonneg (sub_nonneg.mpr ht.2) _)
  have hm t (ht : t ∈ Icc (0 : ℝ) 1) := legendreInterpolation_measure μ b f g ht
  have hs t (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable a (alexandrovMeasure (innerₗ E) μ
        (fun x => ((legendreInterpolation f g t).val x : EReal))) := by
    rw [hm t ht]
    exact integrable_finsetSum_measure.mpr (fun k _ => (hi k).smul_measure_nnreal)
  have he t (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
        (fun x => ((legendreInterpolation f g t).val x : EReal))) =
      ∑ k : Fin (n + 1), legendreBernsteinWeight n k t * J k := by
    rw [hm t ht]
    rw [integral_finsetSum_measure
      (μ := fun k : Fin (n + 1) => Real.toNNReal (legendreBernsteinWeight n k t) •
        mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k))
      (s := Finset.univ) (fun k _ => (hi k).smul_measure_nnreal)]
    simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (hw _ ht), J]
  have hp : Continuous (fun t => ∑ k : Fin (n + 1), legendreBernsteinWeight n k t * J k) := by
    apply continuous_finsetSum
    intro k _
    unfold legendreBernsteinWeight
    fun_prop
  have heI : ∀ t ∈ uIcc (0 : ℝ) 1,
      (∫ x, a x ∂alexandrovMeasure (innerₗ E) μ
        (fun x => ((legendreInterpolation f g t).val x : EReal))) =
      ∑ k : Fin (n + 1), legendreBernsteinWeight n k t * J k := by
    simpa only [uIcc_of_le zero_le_one] using he
  have hki (k : Fin (n + 1)) : IntervalIntegrable
      (fun t => legendreBernsteinWeight n k t * J k) volume 0 1 := by
    unfold legendreBernsteinWeight
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (n.choose (k : ℕ) : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - k) * J k)).intervalIntegrable 0 1
  refine ⟨fun t ht => ⟨hm t ht, hs t ht⟩,
    (hp.intervalIntegrable 0 1).congr (fun t ht => (heI t (uIoc_subset_uIcc ht)).symm), ?_⟩
  rw [intervalIntegral.integral_congr heI,
    intervalIntegral.integral_finsetSum (fun k _ => hki k)]
  simp_rw [intervalIntegral.integral_mul_const, legendreBernstein_integral]
  rw [← Finset.mul_sum]

section FullClassInterpolation
omit [MeasurableSpace E] [BorelSpace E]

/-- Closure equality and genuine full affine span produce pointwise ordinary
interior equality; this is stronger than the existing almost-everywhere readback. -/
private theorem legendreInterior_eq_of_closure {C P : Set E}
    (hC : Convex ℝ C) (hP : Convex ℝ P) (hcl : closure C = P)
    (hi : (interior P).Nonempty) : interior C = interior P := by
  have hAP : P ⊆ (affineSpan ℝ C : Set E) := by
    rw [← hcl]
    exact closure_minimal (subset_affineSpan ℝ C)
      (AffineSubspace.closed_of_finiteDimensional _)
  have hspan : affineSpan ℝ P ≤ affineSpan ℝ C := affineSpan_le.mpr hAP
  have hPspan := hP.interior_nonempty_iff_affineSpan_eq_top.mp hi
  rw [hPspan] at hspan
  have hCspan : affineSpan ℝ C = ⊤ := top_le_iff.mp hspan
  have hCi := hC.interior_nonempty_iff_affineSpan_eq_top.mpr hCspan
  rw [← hC.interior_closure_eq_interior_of_nonempty_interior hCi, hcl]

/-- The actual FullMassClass closure condition supplies finite endpoint
conjugates at every ordinary interior point, without an a.e. premise. -/
private theorem legendreInterior_conjugate_of_fullMassClass {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    interior (effectiveDomain (conjugate (innerₗ E) (fun x => (f.val x : EReal)))) =
      interior P := by
  have hraw : closure (rawSubgradientImage (innerₗ E)
      (fun x => (f.val x : EReal))) = P :=
    hf.2.resolve_left (Set.nonempty_iff_ne_empty.mp hi)
  have hcl : closure (effectiveDomain (conjugate (innerₗ E)
      (fun x => (f.val x : EReal)))) = P := by
    rw [← closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate
      (innerₗ E) hf.1.1
      (lowerSemicontinuous_of_isClosedConvex
        (isClosedConvex_of_mem_growthClass (innerₗ E) hP hne hf.1))]
    exact hraw
  exact legendreInterior_eq_of_closure
    (convex_effectiveDomain (isConvex_conjugate (innerₗ E) _)) hconv hcl hi

/-- The SAME finite interpolation inherits the actual support-growth bound,
with its real constant manufactured from the two original constants. -/
private theorem legendreInterpolation_growth {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ GrowthClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ GrowthClass (innerₗ E) P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => ((legendreInterpolation f g t).val x : EReal)) ∈
      GrowthClass (innerₗ E) P := by
  obtain ⟨Cf, hCf⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  obtain ⟨Cg, hCg⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hg.2
  refine ⟨isProper_coe_of_convexOn (legendreInterpolation f g t).property, ?_⟩
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨(1 - t) * Cg + t * Cf, fun x => ?_⟩
  obtain ⟨r, hr⟩ := exists_real_support_value (innerₗ E) hP hne x
  have hfx : f.val x ≤ r + Cf := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hr, ← EReal.coe_add] using hCf x
  have hgx : g.val x ≤ r + Cg := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hr, ← EReal.coe_add] using hCg x
  rw [legendreInterpolation_val f g ht, hr, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  calc
    (1 - t) * g.val x + t * f.val x ≤
        (1 - t) * (r + Cg) + t * (r + Cf) :=
      add_le_add (mul_le_mul_of_nonneg_left hgx (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hfx ht.1)
    _ = r + ((1 - t) * Cg + t * Cf) := by ring

/-- The endpoint Fenchel minorants give a finite actual interpolation conjugate
at every interior point. No maximizer or conjugate value is supplied as input. -/
private theorem legendreInterpolation_conjugate_finite {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {p : E} (hp : p ∈ interior P) :
    p ∈ effectiveDomain (conjugate (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal))) := by
  have hi : (interior P).Nonempty := ⟨p, hp⟩
  have hpF : p ∈ effectiveDomain (conjugate (innerₗ E) (fun x => (f.val x : EReal))) := by
    apply interior_subset
    rwa [legendreInterior_conjugate_of_fullMassClass hP hne hconv hi f hf]
  have hpG : p ∈ effectiveDomain (conjugate (innerₗ E) (fun x => (g.val x : EReal))) := by
    apply interior_subset
    rwa [legendreInterior_conjugate_of_fullMassClass hP hne hconv hi g hg]
  let Fp := (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal
  let Gp := (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal
  have hF : conjugate (innerₗ E) (fun x => (f.val x : EReal)) p = (Fp : EReal) :=
    (EReal.coe_toReal (ne_of_lt hpF)
      ((isProper_conjugate_of_isContPerfPair (innerₗ E) hf.1.1).2.2 p)).symm
  have hG : conjugate (innerₗ E) (fun x => (g.val x : EReal)) p = (Gp : EReal) :=
    (EReal.coe_toReal (ne_of_lt hpG)
      ((isProper_conjugate_of_isContPerfPair (innerₗ E) hg.1.1).2.2 p)).symm
  have hbound : conjugate (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal)) p ≤
      (((1 - t) * Gp + t * Fp : ℝ) : EReal) := by
    apply (conjugate_le_coe_iff _ _ _ _).mpr
    intro x
    have hfx : (innerₗ E) x p - Fp ≤ f.val x :=
      EReal.coe_le_coe_iff.mp ((conjugate_le_coe_iff _ _ _ _).mp hF.le x)
    have hgx : (innerₗ E) x p - Gp ≤ g.val x :=
      EReal.coe_le_coe_iff.mp ((conjugate_le_coe_iff _ _ _ _).mp hG.le x)
    rw [legendreInterpolation_val f g ht]
    apply EReal.coe_le_coe_iff.mpr
    calc
      (innerₗ E) x p - ((1 - t) * Gp + t * Fp) =
          (1 - t) * ((innerₗ E) x p - Gp) + t * ((innerₗ E) x p - Fp) := by ring
      _ ≤ (1 - t) * g.val x + t * f.val x :=
        add_le_add (mul_le_mul_of_nonneg_left hgx (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hfx ht.1)
  exact hbound.trans_lt (EReal.coe_lt_top _)

/-- The original FullMassClass is derived for every time, including its literal
empty ordinary-interior branch. -/
private theorem legendreInterpolation_fullMassClass {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => ((legendreInterpolation f g t).val x : EReal)) ∈
      FullMassClass (innerₗ E) P := by
  have htGrowth := legendreInterpolation_growth hP hne f g hf.1 hg.1 ht
  refine ⟨htGrowth, ?_⟩
  by_cases hi : interior P = ∅
  · exact Or.inl hi
  · apply Or.inr
    have hInt : interior P ⊆ effectiveDomain (conjugate (innerₗ E)
        (fun x => ((legendreInterpolation f g t).val x : EReal))) :=
      fun p hp => legendreInterpolation_conjugate_finite hP hne hconv f g hf hg ht hp
    have hDom : effectiveDomain (conjugate (innerₗ E)
        (fun x => ((legendreInterpolation f g t).val x : EReal))) ⊆ P := by
      intro p hp
      by_contra hout
      have htop := conjugate_eq_top_of_singularityLE_support (innerₗ E)
        hP hconv htGrowth.1 htGrowth.2 hout
      exact (ne_of_lt hp) htop
    rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate
      (innerₗ E) htGrowth.1
      (lowerSemicontinuous_of_isClosedConvex
        (isClosedConvex_of_mem_growthClass (innerₗ E) hP hne htGrowth))]
    apply subset_antisymm (closure_minimal hDom hP.isClosed)
    have hclInt : closure (interior P) = P := by
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior
        (Set.nonempty_iff_ne_empty.mpr hi), hP.isClosed.closure_eq]
    rw [← hclInt]
    exact closure_mono hInt

/-- A true compact thickening inside the original body makes both endpoint
conjugates uniformly bounded; Fenchel then supplies uniform primal coercivity. -/
private theorem legendreInterpolation_uniform_coercive {P K : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hK : IsCompact K) (hKI : K ⊆ interior P) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∀ x : E,
      ε * ‖x‖ - C ≤ (legendreInterpolation f g t).val x - (innerₗ E) x p := by
  by_cases hKe : K = ∅
  · refine ⟨1, 0, zero_lt_one, ?_⟩
    intro t ht p hp
    simp only [hKe, mem_empty_iff_false] at hp
  have hKn := Set.nonempty_iff_ne_empty.mpr hKe
  have hi := hKn.mono hKI
  obtain ⟨ε, hε, hthick⟩ := hK.exists_cthickening_subset_open isOpen_interior hKI
  let A := Metric.cthickening ε K
  have hA : IsCompact A := hK.cthickening
  have hAI : A ⊆ interior P := hthick
  have hFD := legendreInterior_conjugate_of_fullMassClass hP hne hconv hi f hf
  have hGD := legendreInterior_conjugate_of_fullMassClass hP hne hconv hi g hg
  have hFc : ContinuousOn (fun p => (conjugate (innerₗ E)
      (fun x => (f.val x : EReal)) p).toReal) A := by
    apply ((convexOn_toReal_effectiveDomain
      (isProper_conjugate_of_isContPerfPair (innerₗ E) hf.1.1)).continuousOn_interior).mono
    rwa [hFD]
  have hGc : ContinuousOn (fun p => (conjugate (innerₗ E)
      (fun x => (g.val x : EReal)) p).toReal) A := by
    apply ((convexOn_toReal_effectiveDomain
      (isProper_conjugate_of_isContPerfPair (innerₗ E) hg.1.1)).continuousOn_interior).mono
    rwa [hGD]
  obtain ⟨Cf, hCf⟩ := hA.bddAbove_image hFc
  obtain ⟨Cg, hCg⟩ := hA.bddAbove_image hGc
  let C := max Cf Cg
  have hFupper (q : E) (hq : q ∈ A) :
      conjugate (innerₗ E) (fun x => (f.val x : EReal)) q ≤ (C : EReal) := by
    have hqD : q ∈ effectiveDomain (conjugate (innerₗ E)
        (fun x => (f.val x : EReal))) := interior_subset (by rw [hFD]; exact hAI hq)
    rw [← EReal.coe_toReal (ne_of_lt hqD)
      ((isProper_conjugate_of_isContPerfPair (innerₗ E) hf.1.1).2.2 q)]
    exact EReal.coe_le_coe_iff.mpr ((hCf ⟨q, hq, rfl⟩).trans (le_max_left _ _))
  have hGupper (q : E) (hq : q ∈ A) :
      conjugate (innerₗ E) (fun x => (g.val x : EReal)) q ≤ (C : EReal) := by
    have hqD : q ∈ effectiveDomain (conjugate (innerₗ E)
        (fun x => (g.val x : EReal))) := interior_subset (by rw [hGD]; exact hAI hq)
    rw [← EReal.coe_toReal (ne_of_lt hqD)
      ((isProper_conjugate_of_isContPerfPair (innerₗ E) hg.1.1).2.2 q)]
    exact EReal.coe_le_coe_iff.mpr ((hCg ⟨q, hq, rfl⟩).trans (le_max_right _ _))
  have hpoint (F : RealConvexFunction E)
      (hupper : ∀ q ∈ A, conjugate (innerₗ E) (fun x => (F.val x : EReal)) q ≤ (C : EReal))
      (p : E) (hp : p ∈ K) (x : E) : ε * ‖x‖ - C ≤ F.val x - (innerₗ E) x p := by
    by_cases hx : x = 0
    · have hminor := (conjugate_le_coe_iff _ _ _ _).mp
        (hupper p (Metric.self_subset_cthickening K hp)) 0
      have hminor' := EReal.coe_le_coe_iff.mp hminor
      simpa only [hx, norm_zero, mul_zero, map_zero, LinearMap.zero_apply,
        sub_zero, zero_sub] using hminor'
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let q := p + (ε / ‖x‖) • x
      have hdist : dist q p ≤ ε := by
        dsimp [q]
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hε.le (norm_nonneg _))]
        exact (div_mul_cancel₀ _ hnorm).le
      have hq : q ∈ A := Metric.mem_cthickening_of_dist_le q p ε K hp hdist
      have hinner : (innerₗ E) x q = (innerₗ E) x p + ε * ‖x‖ := by
        dsimp [q]
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
          pow_two, ← mul_assoc, div_mul_cancel₀ _ hnorm]
      have hminor := EReal.coe_le_coe_iff.mp
        ((conjugate_le_coe_iff _ _ _ _).mp (hupper q hq) x)
      rw [hinner] at hminor
      linarith
  refine ⟨ε, C, hε, fun t ht p hp x => ?_⟩
  rw [legendreInterpolation_val f g ht]
  have hFx := hpoint f hFupper p hp x
  have hGx := hpoint g hGupper p hp x
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hFx),
    mul_nonneg ht' (sub_nonneg.mpr hGx)]

/-- The accepted relative-interior subgradient producer manufactures an actual
primal point attaining the literal conjugate, for each time and moment point. -/
private theorem legendreInterpolation_attains {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {p : E} (hp : p ∈ interior P) :
    ∃ x : E, conjugate (innerₗ E)
      (fun y => ((legendreInterpolation f g t).val y : EReal)) p =
        (((innerₗ E) x p - (legendreInterpolation f g t).val x : ℝ) : EReal) := by
  have hfull := legendreInterpolation_fullMassClass hP hne hconv f g hf hg ht
  have hInt := legendreInterior_conjugate_of_fullMassClass hP hne hconv
    ⟨p, hp⟩ (legendreInterpolation f g t) hfull
  have hpD : p ∈ intrinsicInterior ℝ (effectiveDomain (conjugate (innerₗ E)
      (fun y => ((legendreInterpolation f g t).val y : EReal)))) := by
    apply interior_subset_intrinsicInterior
    rwa [hInt]
  have hraw := intrinsicInterior_effectiveDomain_conjugate_subset_rawSubgradientImage
    (innerₗ E) hfull.1.1
    (lowerSemicontinuous_of_isClosedConvex
      (isClosedConvex_of_mem_growthClass (innerₗ E) hP hne hfull.1)) hpD
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hraw
  refine ⟨x, ?_⟩
  rw [rawSubdifferential_eq_subdifferential_of_isProper (innerₗ E) hfull.1.1] at hx
  have hxD : x ∈ effectiveDomain (fun y => ((legendreInterpolation f g t).val y : EReal)) :=
    EReal.coe_lt_top _
  simpa only [← EReal.coe_sub] using
    (mem_subdifferential_iff_fenchel (innerₗ E) hfull.1.1 hxD).mp hx

/-- Every actual optimizer lies in one compact ball, uniformly in both the
closed time interval and the supplied compact interior moment window. -/
private theorem legendreInterpolation_compact_attainers {P K : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hK : IsCompact K) (hKI : K ⊆ interior P) :
    ∃ ε C R : ℝ, 0 < ε ∧ 0 ≤ R ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∀ x : E,
        ε * ‖x‖ - C ≤ (legendreInterpolation f g t).val x - (innerₗ E) x p) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K,
        ∃ x : E, ‖x‖ ≤ R ∧ conjugate (innerₗ E)
          (fun y => ((legendreInterpolation f g t).val y : EReal)) p =
            (((innerₗ E) x p - (legendreInterpolation f g t).val x : ℝ) : EReal)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∀ x : E,
        conjugate (innerₗ E) (fun y => ((legendreInterpolation f g t).val y : EReal)) p =
          (((innerₗ E) x p - (legendreInterpolation f g t).val x : ℝ) : EReal) → ‖x‖ ≤ R) := by
  obtain ⟨ε, C, hε, hcoer⟩ :=
    legendreInterpolation_uniform_coercive hP hne hconv f g hf hg hK hKI
  let M := max (f.val 0) (g.val 0)
  let R := max 0 ((C + M) / ε)
  have hR : 0 ≤ R := le_max_left _ _
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (legendreInterpolation f g t).val 0 ≤ M := by
    rw [legendreInterpolation_val f g ht]
    calc
      (1 - t) * g.val 0 + t * f.val 0 ≤ (1 - t) * M + t * M :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ht.1)
      _ = M := by ring
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : E) (hp : p ∈ K) (x : E)
      (hx : conjugate (innerₗ E)
        (fun y => ((legendreInterpolation f g t).val y : EReal)) p =
          (((innerₗ E) x p - (legendreInterpolation f g t).val x : ℝ) : EReal)) : ‖x‖ ≤ R := by
    have hlower : (-(legendreInterpolation f g t).val 0 : ℝ) ≤
        (innerₗ E) x p - (legendreInterpolation f g t).val x := by
      have h := le_iSup (fun y : E => ((innerₗ E) y p : EReal) -
        ((legendreInterpolation f g t).val y : EReal)) 0
      change ((innerₗ E) 0 p : EReal) - ((legendreInterpolation f g t).val 0 : EReal) ≤
        conjugate (innerₗ E) (fun y => ((legendreInterpolation f g t).val y : EReal)) p at h
      rw [hx, map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub,
        ← EReal.coe_neg, EReal.coe_le_coe_iff] at h
      exact h
    have hnum : ‖x‖ * ε ≤ C + M := by
      nlinarith [hcoer t ht p hp x, hzero t ht]
    exact ((le_div_iff₀ hε).mpr hnum).trans (le_max_right _ _)
  refine ⟨ε, C, R, hε, hR, hcoer, ?_, hbound⟩
  intro t ht p hp
  obtain ⟨x, hx⟩ := legendreInterpolation_attains hP hne hconv f g hf hg ht (hKI hp)
  exact ⟨x, hbound t ht p hp x hx, hx⟩

/-- Compact actual optimizers make the conjugate path Lipschitz for each fixed
interior moment point. This does not take an uncountable intersection of null sets. -/
private theorem legendreInterpolation_conjugate_lipschitz {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (p : E) (hp : p ∈ interior P) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun t => (conjugate (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal)) p).toReal) (Icc (0 : ℝ) 1) := by
  obtain ⟨ε, C, R, _, hR, _, hAtt, _⟩ := legendreInterpolation_compact_attainers
    hP hne hconv f g hf hg isCompact_singleton
    (by intro q hq; rcases mem_singleton_iff.mp hq with rfl; exact hp)
  have hfcont : Continuous f.val := continuousOn_univ.mp (f.property.continuousOn isOpen_univ)
  have hgcont : Continuous g.val := continuousOn_univ.mp (g.property.continuousOn isOpen_univ)
  have hbcont : Continuous (fun x => |f.val x - g.val x|) := (hfcont.sub hgcont).abs
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) R).bddAbove_image hbcont.continuousOn
  let D := max 0 B
  have hD : 0 ≤ D := le_max_left _ _
  have hgap (x : E) (hx : ‖x‖ ≤ R) : |f.val x - g.val x| ≤ D := by
    apply (hB ⟨x, ?_, rfl⟩).trans (le_max_right _ _)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  refine ⟨Real.toNNReal D, LipschitzOnWith.of_le_add_mul' D ?_⟩
  intro t ht s hs
  obtain ⟨xt, hxt, htouchT⟩ := hAtt t ht p (mem_singleton p)
  obtain ⟨xs, _, htouchS⟩ := hAtt s hs p (mem_singleton p)
  have hminor : (innerₗ E) xt p - (legendreInterpolation f g s).val xt ≤
      (innerₗ E) xs p - (legendreInterpolation f g s).val xs := by
    have h := le_iSup (fun y : E => ((innerₗ E) y p : EReal) -
      ((legendreInterpolation f g s).val y : EReal)) xt
    change ((innerₗ E) xt p : EReal) - ((legendreInterpolation f g s).val xt : EReal) ≤
      conjugate (innerₗ E) (fun y => ((legendreInterpolation f g s).val y : EReal)) p at h
    rw [htouchS, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    exact h
  have hrealT := congrArg EReal.toReal htouchT
  have hrealS := congrArg EReal.toReal htouchS
  simp only [EReal.toReal_coe] at hrealT hrealS
  rw [hrealT, hrealS]
  have hdiff : (legendreInterpolation f g s).val xt - (legendreInterpolation f g t).val xt =
      (s - t) * (f.val xt - g.val xt) := by
    rw [legendreInterpolation_val f g hs, legendreInterpolation_val f g ht]
    ring
  have hdiffBound : (legendreInterpolation f g s).val xt - (legendreInterpolation f g t).val xt ≤
      D * dist t s := by
    rw [hdiff]
    calc
      (s - t) * (f.val xt - g.val xt) ≤ |(s - t) * (f.val xt - g.val xt)| := le_abs_self _
      _ = |s - t| * |f.val xt - g.val xt| := abs_mul _ _
      _ ≤ |s - t| * D := mul_le_mul_of_nonneg_left (hgap xt hxt) (abs_nonneg _)
      _ = D * dist t s := by rw [Real.dist_eq, abs_sub_comm]; ring
  linarith

/-- The original full-mass condition, actual compact argmax windows and true
Lipschitz time paths are all produced internally from the two endpoint classes. -/
theorem fullMassClass_interpolation_and_compact_conjugate_argmax {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    let F := fun t : ℝ => finiteConvexWeightedSum ![f, g]
      ![Real.toNNReal t, Real.toNNReal (1 - t)]
    (∀ t ∈ Icc (0 : ℝ) 1,
      (fun x => ((F t).val x : EReal)) ∈ FullMassClass (innerₗ E) P) ∧
    (∀ K : Set E, IsCompact K → K ⊆ interior P →
      ∃ ε C R : ℝ, 0 < ε ∧ 0 ≤ R ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∀ x : E,
          ε * ‖x‖ - C ≤ (F t).val x - (innerₗ E) x p) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∃ x : E, ‖x‖ ≤ R ∧
          conjugate (innerₗ E) (fun y => ((F t).val y : EReal)) p =
            (((innerₗ E) x p - (F t).val x : ℝ) : EReal)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, ∀ x : E,
          conjugate (innerₗ E) (fun y => ((F t).val y : EReal)) p =
            (((innerₗ E) x p - (F t).val x : ℝ) : EReal) → ‖x‖ ≤ R)) ∧
    (∀ p ∈ interior P, ∃ L : ℝ≥0, LipschitzOnWith L
      (fun t => (conjugate (innerₗ E) (fun x => ((F t).val x : EReal)) p).toReal)
      (Icc (0 : ℝ) 1)) := by
  dsimp only
  exact ⟨fun t ht => legendreInterpolation_fullMassClass hP hne hconv f g hf hg ht,
    fun K hK hKI => legendreInterpolation_compact_attainers hP hne hconv f g hf hg hK hKI,
    fun p hp => legendreInterpolation_conjugate_lipschitz hP hne hconv f g hf hg p hp⟩

end FullClassInterpolation

section JointLegendreInterpolation

/-- One literal supremum in the joint time and moment variables. Outside the
closed time interval this definition is total, and its epigraph is still convex. -/
private def legendreJointConjugate (f g : RealConvexFunction E) (z : ℝ × E) : EReal :=
  ⨆ x : E, (((innerₗ E) x z.2 - g.val x - z.1 * (f.val x - g.val x) : ℝ) : EReal)

private def legendreJointSlope (f g : RealConvexFunction E) (x : E) :
    (ℝ × E) →ₗ[ℝ] ℝ :=
  ((innerₗ E) x).comp (LinearMap.snd ℝ ℝ E) -
    (f.val x - g.val x) • LinearMap.fst ℝ ℝ E

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem legendreJointConjugate_eq (f g : RealConvexFunction E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : E) :
    legendreJointConjugate f g (t, p) = conjugate (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal)) p := by
  unfold legendreJointConjugate conjugate
  apply congrArg (fun a : E → EReal => ⨆ x, a x)
  funext x
  change (((innerₗ E) x p - g.val x - t * (f.val x - g.val x) : ℝ) : EReal) =
    ((innerₗ E) x p : EReal) - ((legendreInterpolation f g t).val x : EReal)
  rw [legendreInterpolation_val f g ht, ← EReal.coe_sub]
  apply congrArg (fun a : ℝ => (a : EReal))
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every term is a genuine affine functional on the normed product. No
inner-product structure on the product is imposed or identified by convention. -/
private theorem legendreJointConjugate_convex (f g : RealConvexFunction E) :
    IsConvex (legendreJointConjugate f g) := by
  apply isConvex_iSup
  intro x
  convert isConvex_affine (legendreJointSlope f g x) (-g.val x) using 1
  funext z
  simp only [legendreJointSlope, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul]
  congr 1
  ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem legendreJointConjugate_lowerSemicontinuous
    (f g : RealConvexFunction E) : LowerSemicontinuous (legendreJointConjugate f g) := by
  apply lowerSemicontinuous_iSup
  intro x
  have hcont : Continuous (fun z : ℝ × E =>
      (legendreJointSlope f g x) z + (-g.val x)) :=
    (legendreJointSlope f g x).continuous_of_finiteDimensional.add continuous_const
  convert (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous using 1
  funext z
  simp only [legendreJointSlope, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul]
  congr 1
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- A genuine interior point of the actual body provides a finite point of the
joint supremum. The zero primal test rules out bottom everywhere. -/
private theorem legendreJointConjugate_proper {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    IsProper (legendreJointConjugate f g) := by
  obtain ⟨p, hp⟩ := hi
  refine ⟨legendreJointConjugate_convex f g, ⟨(0, p), ?_⟩, ?_⟩
  · change legendreJointConjugate f g (0, p) < ⊤
    rw [legendreJointConjugate_eq f g ⟨le_rfl, zero_le_one⟩]
    exact legendreInterpolation_conjugate_finite hP hne hconv f g hf hg
      ⟨le_rfl, zero_le_one⟩ hp
  · intro z
    have h := le_iSup (fun x : E =>
      (((innerₗ E) x z.2 - g.val x - z.1 * (f.val x - g.val x) : ℝ) : EReal)) 0
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le h)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem legendreJointConjugate_interior {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    (Ioo (0 : ℝ) 1 ×ˢ interior P) ⊆
      interior (effectiveDomain (legendreJointConjugate f g)) := by
  apply interior_maximal ?_ (isOpen_Ioo.prod isOpen_interior)
  intro z hz
  change legendreJointConjugate f g (z.1, z.2) < ⊤
  rw [legendreJointConjugate_eq f g ⟨hz.1.1.le, hz.1.2.le⟩]
  exact legendreInterpolation_conjugate_finite hP hne hconv f g hf hg
    ⟨hz.1.1.le, hz.1.2.le⟩ hz.2

omit [MeasurableSpace E] [BorelSpace E] in
/-- An actual attaining primal point supplies a joint raw subgradient. This
reads back the supremum directly at every joint point, even where it is infinite. -/
private theorem legendreJointSlope_mem_rawSubdifferential
    (f g : RealConvexFunction E) (z : ℝ × E) (x : E)
    (hx : legendreJointConjugate f g z =
      (((innerₗ E) x z.2 - g.val x - z.1 * (f.val x - g.val x) : ℝ) : EReal)) :
    (legendreJointSlope f g x).toContinuousLinearMap ∈
      rawSubdifferential continuousDualPairing (legendreJointConjugate f g) z := by
  intro y
  rw [hx]
  change _ + (((legendreJointSlope f g x) (y - z) : ℝ) : EReal) ≤ _
  rw [← EReal.coe_add]
  have heq : (innerₗ E) x z.2 - g.val x - z.1 * (f.val x - g.val x) +
      (legendreJointSlope f g x) (y - z) =
      (innerₗ E) x y.2 - g.val x - y.1 * (f.val x - g.val x) := by
    simp only [legendreJointSlope, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      map_sub, smul_eq_mul]
    ring
  rw [heq]
  exact le_iSup (fun q : E =>
    (((innerₗ E) q y.2 - g.val q - y.1 * (f.val q - g.val q) : ℝ) : EReal)) x

omit [MeasurableSpace E] [BorelSpace E] in
/-- At a joint differentiability point the SAME actual optimizer determines
both derivative components. This is a pointwise producer, not an a.e. premise. -/
private theorem legendreJointDerivative_eq_optimizer {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {p : E} (hp : p ∈ interior P)
    (hd : DifferentiableAt ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p)) :
    ∃ x : E,
      conjugate (innerₗ E) (fun q => ((legendreInterpolation f g t).val q : EReal)) p =
        (((innerₗ E) x p - (legendreInterpolation f g t).val x : ℝ) : EReal) ∧
      fderiv ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p) =
        (legendreJointSlope f g x).toContinuousLinearMap := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨x, hx⟩ := legendreInterpolation_attains hP hne hconv f g hf hg ht' hp
  have hxJoint : legendreJointConjugate f g (t, p) =
      (((innerₗ E) x p - g.val x - t * (f.val x - g.val x) : ℝ) : EReal) := by
    rw [legendreJointConjugate_eq f g ht', hx, legendreInterpolation_val f g ht']
    congr 1
    ring
  have hj := legendreJointConjugate_proper hP hne hconv ⟨p, hp⟩ f g hf hg
  have hInt : (t, p) ∈ interior (effectiveDomain (legendreJointConjugate f g)) :=
    legendreJointConjugate_interior hP hne hconv f g hf hg
      (show (t, p) ∈ Ioo (0 : ℝ) 1 ×ˢ interior P from ⟨ht, hp⟩)
  exact ⟨x, hx, (eq_derivative_of_mem_rawSubdifferential hj hInt hd.hasFDerivAt
    (legendreJointSlope_mem_rawSubdifferential f g (t, p) x hxJoint)).symm⟩

/-- A measurable total representative of the actual moment derivative. The
genuine perfect-pairing equivalence turns that derivative into a primal vector. -/
private def legendreJointOptimizer (f g : RealConvexFunction E) (z : ℝ × E) : E :=
  (innerₗ E).toContPerfPair.toContinuousLinearEquiv.symm
    ((fderiv ℝ (fun y => (legendreJointConjugate f g y).toReal) z).comp
      (ContinuousLinearMap.inr ℝ ℝ E))

private theorem legendreJointOptimizer_measurable (f g : RealConvexFunction E) :
    Measurable (legendreJointOptimizer f g) := by
  apply (innerₗ E).toContPerfPair.toContinuousLinearEquiv.symm.continuous.measurable.comp
  exact ((ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip
    (ContinuousLinearMap.inr ℝ ℝ E)).continuous.measurable.comp
      (measurable_fderiv ℝ (fun z => (legendreJointConjugate f g z).toReal))

/-- One product-measure differentiability theorem manufactures both the
actual optimizer and its time derivative simultaneously. No uncountable
intersection of time-indexed exceptional sets is taken. -/
private theorem legendreJointOptimizer_ae {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    ∀ᵐ z ∂((volume : Measure ℝ).prod μ),
      z ∈ Ioo (0 : ℝ) 1 ×ˢ interior P →
        conjugate (innerₗ E)
          (fun q => ((legendreInterpolation f g z.1).val q : EReal)) z.2 =
            (((innerₗ E) (legendreJointOptimizer f g z) z.2 -
              (legendreInterpolation f g z.1).val (legendreJointOptimizer f g z) : ℝ) : EReal) ∧
        fderiv ℝ (fun y => (legendreJointConjugate f g y).toReal) z (1, 0) =
          -(f.val (legendreJointOptimizer f g z) - g.val (legendreJointOptimizer f g z)) := by
  have hdiff := ae_differentiableAt_toReal_of_isProper
    (μ := (volume : Measure ℝ).prod μ)
    (legendreJointConjugate_proper hP hne hconv hi f g hf hg)
  filter_upwards [hdiff] with z hz
  intro hzI
  have hd := hz (legendreJointConjugate_interior hP hne hconv f g hf hg hzI)
  obtain ⟨x, hx, hL⟩ := legendreJointDerivative_eq_optimizer hP hne hconv f g hf hg
    hzI.1 hzI.2 hd
  have he : (innerₗ E).toContPerfPair.toContinuousLinearEquiv x =
      (fderiv ℝ (fun y => (legendreJointConjugate f g y).toReal) z).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
    rw [hL]
    ext q
    simp only [LinearEquiv.coe_toContinuousLinearEquiv',
      LinearMap.toContPerfPair_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, LinearMap.coe_toContinuousLinearMap',
      legendreJointSlope, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      smul_eq_mul, mul_zero, sub_zero]
  have hxX : x = legendreJointOptimizer f g z := by
    apply (innerₗ E).toContPerfPair.toContinuousLinearEquiv.injective
    simpa only [legendreJointOptimizer, ContinuousLinearEquiv.apply_symm_apply] using he
  subst x
  refine ⟨hx, ?_⟩
  rw [hL]
  simp only [LinearMap.coe_toContinuousLinearMap', legendreJointSlope,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_zero, smul_eq_mul,
    mul_one, zero_sub]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual moment derivative of the joint supremum is exactly the accepted
conjugate-gradient map at that time. This identifies SAME measures and maps. -/
private theorem legendreJointOptimizer_eq_gradient
    (f g : RealConvexFunction E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {p : E}
    (hd : DifferentiableAt ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p)) :
    legendreJointOptimizer f g (t, p) = conjugateGradient (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal)) p := by
  have hmoment := hd.hasFDerivAt.comp p (hasFDerivAt_prodMk_right t p)
  have hmoment' : HasFDerivAt
      (fun q => (conjugate (innerₗ E)
        (fun x => ((legendreInterpolation f g t).val x : EReal)) q).toReal)
      ((fderiv ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)) p := by
    simpa only [Function.comp_def, legendreJointConjugate_eq f g ht] using hmoment
  unfold legendreJointOptimizer conjugateGradient
  rw [hmoment'.fderiv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A true one-dimensional derivative follows by composing the joint derivative
with the time line; equality of the conjugates is used on an actual neighbourhood. -/
private theorem legendreJoint_hasDerivAt_time
    (f g : RealConvexFunction E) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {p : E}
    (hd : DifferentiableAt ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p)) :
    HasDerivAt
      (fun s => (conjugate (innerₗ E)
        (fun x => ((legendreInterpolation f g s).val x : EReal)) p).toReal)
      (fderiv ℝ (fun z => (legendreJointConjugate f g z).toReal) (t, p) (1, 0)) t := by
  have hline := (hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t p)).hasDerivAt
  apply hline.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  change (conjugate (innerₗ E)
    (fun x => ((legendreInterpolation f g s).val x : EReal)) p).toReal =
      (legendreJointConjugate f g (s, p)).toReal
  rw [legendreJointConjugate_eq f g ⟨hs.1.le, hs.2.le⟩]

/-- Product a.e. differentiability simultaneously identifies the accepted moment
map and the actual time derivative. There is ONE product-null exceptional set. -/
private theorem legendreJoint_gradient_and_time_derivative_ae {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    ∀ᵐ z ∂((volume : Measure ℝ).prod μ),
      z ∈ Ioo (0 : ℝ) 1 ×ˢ interior P →
        legendreJointOptimizer f g z = conjugateGradient (innerₗ E)
          (fun x => ((legendreInterpolation f g z.1).val x : EReal)) z.2 ∧
        HasDerivAt
          (fun s => (conjugate (innerₗ E)
            (fun x => ((legendreInterpolation f g s).val x : EReal)) z.2).toReal)
          (-(f.val (legendreJointOptimizer f g z) -
              g.val (legendreJointOptimizer f g z))) z.1 := by
  have hdiff := ae_differentiableAt_toReal_of_isProper
    (μ := (volume : Measure ℝ).prod μ)
    (legendreJointConjugate_proper hP hne hconv hi f g hf hg)
  filter_upwards [hdiff, legendreJointOptimizer_ae μ hP hne hconv hi f g hf hg] with z hz hval
  intro hzI
  have hd := hz (legendreJointConjugate_interior hP hne hconv f g hf hg hzI)
  refine ⟨legendreJointOptimizer_eq_gradient f g ⟨hzI.1.1.le, hzI.1.2.le⟩ hd, ?_⟩
  simpa only [(hval hzI).2] using legendreJoint_hasDerivAt_time f g hzI.1 hd

/-- The actual full-mass gradient pushforward transfers the supplied endpoint
L1 hypotheses to the genuine measurable gradient at every interpolation time. -/
private theorem legendreInterpolation_gradient_integrable {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (ha : ∀ k : Fin (n + 1), Integrable (fun x => f.val x - g.val x)
      (mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => f.val (conjugateGradient (innerₗ E)
      (fun x => ((legendreInterpolation f g t).val x : EReal)) p) -
      g.val (conjugateGradient (innerₗ E)
        (fun x => ((legendreInterpolation f g t).val x : EReal)) p)) (μ.restrict P) := by
  have hfc : Continuous f.val := continuousOn_univ.mp (f.property.continuousOn isOpen_univ)
  have hgc : Continuous g.val := continuousOn_univ.mp (g.property.continuousOn isOpen_univ)
  have hma := ((integral_interpolation_alexandrov_eq_endpoint_average μ b f g
    (fun x => f.val x - g.val x) (hfc.sub hgc).measurable ha).1 t ht).2
  change Integrable (fun x => f.val x - g.val x)
    (alexandrovMeasure (innerₗ E) μ
      (fun x => ((legendreInterpolation f g t).val x : EReal))) at hma
  rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass (innerₗ E)
    hP hne hconv (legendreInterpolation_fullMassClass hP hne hconv f g hf hg ht)] at hma
  have hmap := (integrable_smul_measure (by positivity) (by simp)).mp hma
  exact hmap.comp_measurable (measurable_conjugateGradient (innerₗ E) _)

/-- Restriction to the original compact body removes only its genuine Haar-null
frontier, so the one joint derivative exceptional set supplies product readbacks. -/
private theorem legendreJoint_ae_on_original_product {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    ∀ᵐ z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μ.restrict P)),
      z.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2 ∈ interior P ∧
      legendreJointOptimizer f g z = conjugateGradient (innerₗ E)
        (fun x => ((legendreInterpolation f g z.1).val x : EReal)) z.2 ∧
      HasDerivAt
        (fun t => (conjugate (innerₗ E)
          (fun x => ((legendreInterpolation f g t).val x : EReal)) z.2).toReal)
        (-(f.val (legendreJointOptimizer f g z) -
            g.val (legendreJointOptimizer f g z))) z.1 := by
  have hp : ∀ᵐ p ∂μ.restrict P, p ∈ interior P := by
    filter_upwards [ae_restrict_mem hP.measurableSet,
      ae_restrict_of_ae (interior_ae_eq_of_null_frontier (hconv.addHaar_frontier μ))]
      with p hp heq
    exact heq.symm.mp hp
  have htime : ∀ᵐ z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μ.restrict P)),
      z.1 ∈ Ioo (0 : ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem measurableSet_Ioo)
  have hmoment : ∀ᵐ z ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μ.restrict P)),
      z.2 ∈ interior P := Measure.quasiMeasurePreserving_snd.ae hp
  have hj := ae_restrict_of_ae (s := Ioo (0 : ℝ) 1 ×ˢ P)
    (legendreJoint_gradient_and_time_derivative_ae μ hP hne hconv hi f g hf hg)
  rw [← Measure.prod_restrict] at hj
  filter_upwards [htime, hmoment, hj] with z ht hp hz
  exact ⟨ht, hp, (hz ⟨ht, hp⟩).1, (hz ⟨ht, hp⟩).2⟩

/-- Polynomial time integration and the true gradient pushforward manufacture
product L1 of the measurable gap. No Fubini or L1 certificate is an input. -/
private theorem legendreJoint_gap_product_integrable {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (b : OrthonormalBasis (Fin n) ℝ E)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (ha : ∀ k : Fin (n + 1), Integrable (fun x => f.val x - g.val x)
      (mixedAlexandrovMeasure μ b (legendreEndpointTuple f g k))) :
    Integrable (fun z => f.val (legendreJointOptimizer f g z) -
      g.val (legendreJointOptimizer f g z))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μ.restrict P)) ∧
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      (∫ p in P, f.val (legendreJointOptimizer f g (t, p)) -
        g.val (legendreJointOptimizer f g (t, p)) ∂μ) =
        ((Module.finrank ℝ E).factorial : ℝ)⁻¹ *
          ∫ x, f.val x - g.val x ∂alexandrovMeasure (innerₗ E) μ
            (fun x => ((legendreInterpolation f g t).val x : EReal)) := by
  let H : ℝ × E → ℝ := fun z => f.val (legendreJointOptimizer f g z) -
    g.val (legendreJointOptimizer f g z)
  have hfc : Continuous f.val := continuousOn_univ.mp (f.property.continuousOn isOpen_univ)
  have hgc : Continuous g.val := continuousOn_univ.mp (g.property.continuousOn isOpen_univ)
  have hmeas : Measurable H := (hfc.sub hgc).measurable.comp
    (legendreJointOptimizer_measurable f g)
  have hs := Measure.ae_ae_of_ae_prod (legendreJoint_ae_on_original_product μ
    hP hne hconv hi f g hf hg)
  have hgradAE : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      (fun p => H (t, p)) =ᵐ[μ.restrict P] fun p =>
        f.val (conjugateGradient (innerₗ E)
          (fun x => ((legendreInterpolation f g t).val x : EReal)) p) -
        g.val (conjugateGradient (innerₗ E)
          (fun x => ((legendreInterpolation f g t).val x : EReal)) p) := by
    filter_upwards [hs] with t ht
    filter_upwards [ht] with p hp
    dsimp only [H]
    rw [hp.2.2.1]
  have hfac : ((Module.finrank ℝ E).factorial : ℝ) ≠ 0 := by positivity
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      (∫ p in P, ‖H (t, p)‖ ∂μ) = ((Module.finrank ℝ E).factorial : ℝ)⁻¹ *
        ∫ x, |f.val x - g.val x| ∂alexandrovMeasure (innerₗ E) μ
          (fun x => ((legendreInterpolation f g t).val x : EReal)) := by
    filter_upwards [hgradAE, ae_restrict_mem measurableSet_Ioo] with t ht htime
    rw [integral_congr_ae (ht.mono fun p hp => congrArg norm hp)]
    have hh := integral_alexandrovMeasure_of_mem_fullMassClass (innerₗ E) (ν := μ) hP hne hconv
      (legendreInterpolation_fullMassClass hP hne hconv f g hf hg ⟨htime.1.le, htime.2.le⟩)
      (hfc.sub hgc).abs.measurable
    simp only [Pi.sub_apply] at hh
    simp only [Real.norm_eq_abs] at *
    rw [hh, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]
  have hiAbs := (integral_interpolation_alexandrov_eq_endpoint_average μ b f g
    (fun x => |f.val x - g.val x|) (hfc.sub hgc).abs.measurable
    (fun k => (ha k).abs)).2.1
  have hiTime : Integrable
      (fun t => ((Module.finrank ℝ E).factorial : ℝ)⁻¹ *
        ∫ x, |f.val x - g.val x| ∂alexandrovMeasure (innerₗ E) μ
          (fun x => ((legendreInterpolation f g t).val x : EReal)))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hiAbs).const_mul _
  have hL1 : Integrable H ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μ.restrict P)) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hgradAE, ae_restrict_mem measurableSet_Ioo] with t ht htime
      exact (legendreInterpolation_gradient_integrable μ hP hne hconv b f g hf hg ha
        ⟨htime.1.le, htime.2.le⟩).congr ht.symm
    · exact hiTime.congr (hnorm.mono fun _ ht => ht.symm)
  refine ⟨hL1, ?_⟩
  filter_upwards [hgradAE, ae_restrict_mem measurableSet_Ioo] with t ht htime
  rw [integral_congr_ae ht]
  have hh := integral_alexandrovMeasure_of_mem_fullMassClass (innerₗ E) (ν := μ) hP hne hconv
    (legendreInterpolation_fullMassClass hP hne hconv f g hf hg ⟨htime.1.le, htime.2.le⟩)
    (hfc.sub hgc).measurable
  simp only [Pi.sub_apply] at hh
  rw [hh, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

/-- Absolute continuity follows from the actual compact optimizer bounds, and
its FTC turns the manufactured product derivative into the literal endpoint gap. -/
private theorem legendreJoint_time_integral_eq_gap_ae {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (hi : (interior P).Nonempty) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    ∀ᵐ p ∂μ.restrict P,
      (∫ t in Ioo (0 : ℝ) 1, f.val (legendreJointOptimizer f g (t, p)) -
          g.val (legendreJointOptimizer f g (t, p))) =
        (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal -
        (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal := by
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (legendreJoint_ae_on_original_product μ hP hne hconv hi f g hf hg)
  have hpTime := Measure.ae_ae_of_ae_prod hswap
  have hpInt : ∀ᵐ p ∂μ.restrict P, p ∈ interior P := by
    filter_upwards [ae_restrict_mem hP.measurableSet,
      ae_restrict_of_ae (interior_ae_eq_of_null_frontier (hconv.addHaar_frontier μ))]
      with p hp heq
    exact heq.symm.mp hp
  filter_upwards [hpTime, hpInt] with p htime hp
  let C : ℝ → ℝ := fun t => (conjugate (innerₗ E)
    (fun x => ((legendreInterpolation f g t).val x : EReal)) p).toReal
  obtain ⟨L, hL⟩ := legendreInterpolation_conjugate_lipschitz hP hne hconv f g hf hg p hp
  have hAC : AbsolutelyContinuousOnInterval C 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hL
  have hd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      deriv C t = -(f.val (legendreJointOptimizer f g (t, p)) -
        g.val (legendreJointOptimizer f g (t, p))) := by
    filter_upwards [htime] with t ht
    exact ht.2.2.2.deriv
  have hzero : C 0 = (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal := by
    dsimp only [C]
    congr 2
    funext x
    rw [legendreInterpolation_val f g ⟨le_rfl, zero_le_one⟩]
    simp
  have hone : C 1 = (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal := by
    dsimp only [C]
    congr 2
    funext x
    rw [legendreInterpolation_val f g ⟨zero_le_one, le_rfl⟩]
    simp
  calc
    (∫ t in Ioo (0 : ℝ) 1, f.val (legendreJointOptimizer f g (t, p)) -
      g.val (legendreJointOptimizer f g (t, p))) = -∫ t in Ioo (0 : ℝ) 1, deriv C t := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [hd] with t ht
        rw [ht, neg_neg]
    _ = -(∫ t in (0 : ℝ)..1, deriv C t) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    _ = C 0 - C 1 := by rw [hAC.integral_deriv_eq_sub]; ring
    _ = _ := by rw [hzero, hone]

/-- The actual original Haar finite-value statement is produced from both
full-mass domains, before using toReal or any integration convention. -/
private theorem legendreEndpoint_conjugates_finite_ae {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P) :
    ∀ᵐ p ∂μ.restrict P,
      conjugate (innerₗ E) (fun x => (f.val x : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ E) (fun x => (f.val x : EReal)) p ≠ ⊥ ∧
      conjugate (innerₗ E) (fun x => (g.val x : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ E) (fun x => (g.val x : EReal)) p ≠ ⊥ := by
  have hfd := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    (innerₗ E) (ν := μ) hP hne hconv hf
  have hgd := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    (innerₗ E) (ν := μ) hP hne hconv hg
  filter_upwards [ae_restrict_mem hP.measurableSet,
    ae_restrict_of_ae hfd, ae_restrict_of_ae hgd] with p hp hfp hgp
  have hpF : p ∈ interior (effectiveDomain (conjugate (innerₗ E)
      (fun x => (f.val x : EReal)))) := by
    change (p ∈ interior (effectiveDomain (conjugate (innerₗ E)
      (fun x => (f.val x : EReal))))) = (p ∈ P) at hfp
    exact hfp.symm.mp hp
  have hpG : p ∈ interior (effectiveDomain (conjugate (innerₗ E)
      (fun x => (g.val x : EReal)))) := by
    change (p ∈ interior (effectiveDomain (conjugate (innerₗ E)
      (fun x => (g.val x : EReal))))) = (p ∈ P) at hgp
    exact hgp.symm.mp hp
  have hpFD : p ∈ effectiveDomain (conjugate (innerₗ E)
    (fun x => (f.val x : EReal))) := interior_subset hpF
  have hpGD : p ∈ effectiveDomain (conjugate (innerₗ E)
    (fun x => (g.val x : EReal))) := interior_subset hpG
  exact ⟨ne_of_lt hpFD,
    (isProper_conjugate_of_isContPerfPair (innerₗ E) hf.1.1).2.2 p,
    ne_of_lt hpGD,
    (isProper_conjugate_of_isContPerfPair (innerₗ E) hg.1.1).2.2 p⟩

/-- The signed Legendre integral follows from genuine product derivatives,
manufactured product L1, one-dimensional FTC and the actual mixed time average.
Only the natural endpoint L1 hypotheses are supplied. -/
theorem integral_conjugate_gap_eq_mixed_endpoint_integrals {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (b : OrthonormalBasis (Fin n) ℝ E) (f g : RealConvexFunction E)
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (hg : (fun x => (g.val x : EReal)) ∈ FullMassClass (innerₗ E) P)
    (ha : ∀ k : Fin (n + 1), Integrable (fun x => f.val x - g.val x)
      (mixedAlexandrovMeasure μ b (fun i => if (i : ℕ) < (k : ℕ) then f else g))) :
    (∀ᵐ p ∂μ.restrict P,
      conjugate (innerₗ E) (fun x => (f.val x : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ E) (fun x => (f.val x : EReal)) p ≠ ⊥ ∧
      conjugate (innerₗ E) (fun x => (g.val x : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ E) (fun x => (g.val x : EReal)) p ≠ ⊥) ∧
    Integrable (fun p =>
      (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal -
        (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal) (μ.restrict P) ∧
    (∫ p in P, (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal -
        (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal ∂μ) =
      (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ))⁻¹ *
        ∑ k : Fin (n + 1), ∫ x, f.val x - g.val x
          ∂mixedAlexandrovMeasure μ b (fun i => if (i : ℕ) < (k : ℕ) then f else g) := by
  have hfc : Continuous f.val := continuousOn_univ.mp (f.property.continuousOn isOpen_univ)
  have hgc : Continuous g.val := continuousOn_univ.mp (g.property.continuousOn isOpen_univ)
  have havg := integral_interpolation_alexandrov_eq_endpoint_average μ b f g
    (fun x => f.val x - g.val x) (hfc.sub hgc).measurable ha
  have hdim : Module.finrank ℝ E = n := by
    simpa using Module.finrank_eq_card_basis b.toBasis
  refine ⟨legendreEndpoint_conjugates_finite_ae μ hP hne hconv f g hf hg, ?_⟩
  by_cases hi : (interior P).Nonempty
  · obtain ⟨hL1, hread⟩ := legendreJoint_gap_product_integrable μ hP hne hconv hi
      b f g hf hg ha
    have htime := legendreJoint_time_integral_eq_gap_ae μ hP hne hconv hi f g hf hg
    refine ⟨hL1.integral_prod_right.congr htime, ?_⟩
    calc
      (∫ p in P, (conjugate (innerₗ E) (fun x => (g.val x : EReal)) p).toReal -
        (conjugate (innerₗ E) (fun x => (f.val x : EReal)) p).toReal ∂μ) =
          ∫ p in P, (∫ t in Ioo (0 : ℝ) 1,
            f.val (legendreJointOptimizer f g (t, p)) -
              g.val (legendreJointOptimizer f g (t, p))) ∂μ := integral_congr_ae (htime.mono fun _ hp => hp.symm)
      _ = ∫ t in Ioo (0 : ℝ) 1, ∫ p in P,
          f.val (legendreJointOptimizer f g (t, p)) -
            g.val (legendreJointOptimizer f g (t, p)) ∂μ :=
              (integral_integral_swap hL1).symm
      _ = ∫ t in Ioo (0 : ℝ) 1, ((Module.finrank ℝ E).factorial : ℝ)⁻¹ *
          ∫ x, f.val x - g.val x ∂alexandrovMeasure (innerₗ E) μ
            (fun x => ((legendreInterpolation f g t).val x : EReal)) := integral_congr_ae hread
      _ = ((Module.finrank ℝ E).factorial : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..1, ∫ x, f.val x - g.val x ∂alexandrovMeasure (innerₗ E) μ
            (fun x => ((legendreInterpolation f g t).val x : EReal)) := by
          rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
            integral_Ioc_eq_integral_Ioo]
      _ = _ := by
        simp only [legendreInterpolation]
        rw [havg.2.2, hdim, Nat.cast_add, Nat.cast_one, mul_inv_rev]
        ring
  · have hiEmpty : interior P = ∅ := not_nonempty_iff_eq_empty.mp hi
    have hnull : μ P = 0 := by
      rw [← measure_interior_of_null_frontier (hconv.addHaar_frontier μ), hiEmpty,
        measure_empty]
    have hrestrict : μ.restrict P = 0 := Measure.restrict_eq_zero.mpr hnull
    have hMAzero t (ht : t ∈ Icc (0 : ℝ) 1) :
        alexandrovMeasure (innerₗ E) μ
          (fun x => ((legendreInterpolation f g t).val x : EReal)) = 0 := by
      rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass (innerₗ E)
        hP hne hconv (legendreInterpolation_fullMassClass hP hne hconv f g hf hg ht),
        hrestrict, Measure.map_zero, smul_zero]
    have hmeanZero : (∫ t in (0 : ℝ)..1, ∫ x, f.val x - g.val x
        ∂alexandrovMeasure (innerₗ E) μ
          (fun x => ((legendreInterpolation f g t).val x : EReal))) = 0 := by
      calc
        (∫ t in (0 : ℝ)..1, ∫ x, f.val x - g.val x
          ∂alexandrovMeasure (innerₗ E) μ
            (fun x => ((legendreInterpolation f g t).val x : EReal))) =
              ∫ t in (0 : ℝ)..1, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro t ht
                dsimp only
                rw [hMAzero t (by simpa only [uIcc_of_le zero_le_one] using ht)]
                simp
        _ = 0 := by simp
    have hsumZero : (∑ k : Fin (n + 1), ∫ x, f.val x - g.val x
        ∂mixedAlexandrovMeasure μ b (fun i => if (i : ℕ) < (k : ℕ) then f else g)) = 0 := by
      have hh := havg.2.2.symm.trans hmeanZero
      exact (mul_eq_zero.mp hh).resolve_left (by positivity)
    constructor
    · rw [hrestrict]
      exact integrable_zero_measure
    · rw [hrestrict]
      simp only [integral_zero_measure, hsumZero, mul_zero]

end JointLegendreInterpolation

end SGPT.Convex

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open RelativeEnergy RelativeDarvasDistance RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
  {hφ : IsModelPotential θ φ} {r : ComplexModel n → ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ E
local notation "D" => tropicalSmoothDomain n

/-- Native relative E1 internally supplies the two actual real full-mass classes
and every mixed L1 endpoint. The real Legendre integral and the accepted cocycle
then give the literal energy difference with the single original factorial. -/
theorem energy_sub_eq_factorial_conjugate_gap_integral
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e D r) (f₀ f g : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) D)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal))))) :
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal =
      (n.factorial : ℝ) * ∫ p in closure (rawSubgradientImage B
        (fun a => (f₀.val a : EReal))),
        (conjugate B (fun a => (g.val a : EReal)) p).toReal -
          (conjugate B (fun a => (f.val a : EReal)) p).toReal := by
  let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
  obtain ⟨hne, hconv, _, hF⟩ := fullMassClass_of_nativeRelativeFullMass_tropical_chart
    hu.1 e hD hr f₀ f h₀ hf hψ hpole hP
  obtain ⟨_, _, _, hG⟩ := fullMassClass_of_nativeRelativeFullMass_tropical_chart
    hv.1 e hD hr f₀ g h₀ hg hψ hpole hP
  have hL1 k := integrable_tropical_endpoint_gap_mixedAlexandrov
    omega hu hv e hD hr f g hf hg hψ hpole k
  have hreal := (integral_conjugate_gap_eq_mixed_endpoint_integrals
    (volume : Measure E) hP hne hconv (EuclideanSpace.basisFun (Fin n) ℝ)
    f g hF hG hL1).2.2
  have hnative := energy_sub_eq_tropicalMixedAlexandrov_integrals
    omega hu hv e hD hr f g hf hg hψ hpole
  have hcoef : ((((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ))) ≠ 0 := by positivity
  have hmul := congrArg (fun a : ℝ => (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ)) * a) hreal
  rw [← mul_assoc, mul_inv_cancel₀ hcoef, one_mul] at hmul
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hnp
  calc
    ((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) =
        ∑ k : Fin (n + 1), ∫ a, f.val a - g.val a
          ∂mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
            (fun i => if i.val < k.val then f else g) := hnative
    _ = ((n : ℝ) + 1) * ((n.factorial : ℝ) * ∫ p in P,
        (conjugate B (fun a => (g.val a : EReal)) p).toReal -
          (conjugate B (fun a => (f.val a : EReal)) p).toReal) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul.symm

end SGPT.Toric
