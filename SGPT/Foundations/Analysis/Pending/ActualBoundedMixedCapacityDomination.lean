import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

set_option autoImplicit false

/-! # Actual fixed-box capacity control of independent bounded mixed slots

Independent finite-summand adaptation of Lu, Lemma 4.1 Step 1.2, providing
the uniform capacity control needed for the bounded Xing input in DDL 2.2.
The actual original forms need not be semipositive or big. An internally
produced semipositive zero slot makes the weighted background exactly omega,
including n=0, and actual finite-constant invariance retains the original
mixed measure. Unbounded capacity lower semicontinuity remains separate.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityDomination

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalMultilinearExpansion
  MixedSummandCapacityDomination ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A finite bound in independent arbitrary closed backgrounds produces one
finite positive domination constant for the original actual Kähler capacity. -/
theorem exists_uniform_capacity_bound
    (omega : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : Fin n → M → EReal)
      (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      (∀ i x, ((-B : ℝ) : EReal) ≤ u i x ∧ u i x ≤ (B : EReal)) →
      ∀ E : Set M, globalMixedMeasure θ u (fun i => (hu i).1) E ≤
        ENNReal.ofReal K * thetaCapacity omega.form (fun _ => 0) E := by
  classical
  let Θ : ClosedRealOneOneForm n M := ∑ i, θ i
  obtain ⟨A, hA, hγ⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-Θ)
  let γ : ClosedRealOneOneForm n M := -Θ + A • omega.form
  let α : Fin (n + 1) → ClosedRealOneOneForm n M := Fin.snoc θ γ
  let a : Fin (n + 1) → ℝ := fun _ => A⁻¹
  have ha : ∀ i, 0 < a i := fun _ => inv_pos.mpr hA
  have hsum : ∑ i, α i = Θ + γ := by
    rw [Fin.sum_univ_castSucc]
    simp only [α, Fin.snoc_castSucc, Fin.snoc_last]
    rfl
  have hform : sumForm Finset.univ a α = omega.form := by
    simp only [sumForm, a]
    rw [← Finset.smul_sum, hsum]
    have he : Θ + γ = A • omega.form := by dsimp [γ]; abel
    rw [he, smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
  let C : ℝ := 1 + 2 * B * (n + 1) * A⁻¹
  have hC : 1 ≤ C := by
    have hn : 0 ≤ 2 * B * (n + 1) * A⁻¹ := by positivity
    dsimp [C]
    linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨A ^ n * C ^ n, mul_pos (pow_pos hA _) (pow_pos hCpos _), ?_⟩
  intro u hu hb E
  let f : Fin (n + 1) → M → EReal :=
    Fin.snoc (fun i x => u i x - (B : EReal)) (fun _ => 0)
  have hf : ∀ i, IsThetaPshPotential (α i).val (f i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [α, f, Fin.snoc_last] using
        (LocalPotentials.isThetaPshPotential_zero_iff γ).mpr hγ
    · simpa only [α, f, Fin.snoc_castSucc] using (hu j).sub_const B
  have hbox : ∀ i x, ((-2 * B : ℝ) : EReal) ≤ f i x ∧ f i x ≤ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro x
      simp only [f, Fin.snoc_last]
      exact ⟨EReal.coe_nonpos.mpr (by nlinarith), le_rfl⟩
    · intro x
      simp only [f, Fin.snoc_castSucc]
      have hl : (((-B - B : ℝ)) : EReal) ≤ u j x - (B : EReal) := by
        rw [EReal.coe_sub]
        change ((-B : ℝ) : EReal) + -(B : EReal) ≤ u j x + -(B : EReal)
        exact add_le_add (hb j x).1 le_rfl
      have he : -B - B = -2 * B := by ring
      exact ⟨by simpa only [he] using hl, EReal.sub_nonpos.mpr (hb j x).2⟩
  have hupper : sumPot Finset.univ a f ≤ (fun _ => 0) := by
    intro x
    have hh := sumPot_mono (T := Finset.univ) ha (fun i y => (hbox i y).2) x
    simpa [sumPot] using hh
  have hlower : ∀ x, (0 : EReal) ≤ sumPot Finset.univ a f x + (C : EReal) := by
    intro x
    have hh := sumPot_mono (T := Finset.univ) ha (fun i y => (hbox i y).1) x
    have hconst : sumPot Finset.univ a (fun _ _ => ((-2 * B : ℝ) : EReal)) x =
        ((-2 * B * (n + 1) * A⁻¹ : ℝ) : EReal) := by
      simp only [sumPot, a, ← EReal.coe_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← EReal.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [hconst] at hh
    have he : ((-2 * B * (n + 1) * A⁻¹ : ℝ) : EReal) + (C : EReal) = 1 := by
      rw [← EReal.coe_add]
      have heR : -2 * B * (n + 1) * A⁻¹ + C = 1 := by dsimp [C]; ring
      rw [heR, EReal.coe_one]
    exact zero_le_one.trans (by simpa only [he] using add_le_add hh (le_refl (C : EReal)))
  have hzero : IsThetaPshPotential (sumForm Finset.univ a α).val (fun _ => 0) := by
    rw [hform]
    exact (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have h := selectedMixedMeasure_apply_le_thetaCapacity Finset.univ_nonempty ha hf
    Fin.castSucc (fun _ => Finset.mem_univ _) hzero hC hupper hlower E
  have hF : (fun j : Fin n => α (Fin.castSucc j)) = θ := by
    funext j; simp only [α, Fin.snoc_castSucc]
  have hP : (fun j : Fin n => f (Fin.castSucc j)) = fun j x => u j x - (B : EReal) := by
    funext j x; simp only [f, Fin.snoc_castSucc]
  have hmeasure : globalMixedMeasure (fun j => α (Fin.castSucc j))
      (fun j => f (Fin.castSucc j)) (fun j => (hf (Fin.castSucc j)).1) =
        globalMixedMeasure θ u (fun j => (hu j).1) := by
    rw [GlobalDiagonalScaling.globalMixedMeasure_congr hF hP _
      (fun j => FirstPass.GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hu j).1 B)]
    exact GlobalMeasureInvariance.globalMixedMeasure_sub_const (fun j => (hu j).1) (fun _ => B)
  simp only [a, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hform, hmeasure] at h
  have hcancel : ENNReal.ofReal (A ^ n) * ENNReal.ofReal ((A⁻¹) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hA.le _), ← mul_pow, mul_inv_cancel₀ hA.ne', one_pow]
    exact ENNReal.ofReal_one
  calc
    _ = ENNReal.ofReal (A ^ n) * (ENNReal.ofReal ((A⁻¹) ^ n) *
        globalMixedMeasure θ u (fun i => (hu i).1) E) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal (A ^ n) *
        (ENNReal.ofReal (C ^ n) * thetaCapacity omega.form (fun _ => 0) E) :=
      mul_le_mul_of_nonneg_left h zero_le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hA.le _)]

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityDomination
