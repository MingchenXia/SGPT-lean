import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass

set_option autoImplicit false

/-! # Actual independent mixed masses controlled by admissible barriers

SGPT PDF0236 Step 2: genuine admissible diagonal mass gaps internally
produce PSH barriers and the quantitative independent mixed-mass bound.
The measure domination is an explicit independent-slot adaptation of
positive multilinearity. No mixed-mass continuity or barrier is assumed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedMassAdmissibleBarrier

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
  ThetaPshConvexCombination GlobalMixedMassMonotone ConvexCombEnvelopeMass DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual independent convex mixed measures dominate their all-first term,
with the product of the genuine slot weights, on every set. -/
theorem globalMixedMeasure_convexComb_le {θ : Fin n → ClosedRealOneOneForm n M}
    {u v : Fin n → M → EReal} (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i)) {t : Fin n → ℝ}
    (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i < 1) (S : Set M) :
    ENNReal.ofReal (∏ i, t i) * globalMixedMeasure θ u (fun i => (hu i).1) S ≤
      globalMixedMeasure θ (fun i => convexComb (t i) (u i) (v i))
        (fun i => (isThetaPshPotential_convexComb (hu i) (hv i) (ht0 i) (ht1 i)).1) S := by
  classical
  let w : Fin n → M → EReal := fun i => convexComb (t i) (u i) (v i)
  have hw (i : Fin n) : ThetaPlurisubharmonic (θ i).val (w i) :=
    (isThetaPshPotential_convexComb (hu i) (hv i) (ht0 i) (ht1 i)).1
  let x : ℕ → Fin n → M → EReal := fun m i => if i.val < m then w i else u i
  let c : ℕ → Fin n → ℝ := fun m i => if i.val < m then t i else 1
  have hx (m : ℕ) (i : Fin n) : ThetaPlurisubharmonic (θ i).val (x m i) := by
    dsimp only [x]
    split_ifs
    · exact hw i
    · exact (hu i).1
  have step : ∀ m, m ≤ n → ∀ S : Set M,
      ENNReal.ofReal (∏ i, c m i) * globalMixedMeasure θ u (fun i => (hu i).1) S ≤
        globalMixedMeasure θ (x m) (hx m) S := by
    intro m
    induction m with
    | zero =>
      intro _ S
      have e : x 0 = u := by funext i; simp [x]
      simp only [c, Nat.not_lt_zero, if_false, Finset.prod_const_one,
        ENNReal.ofReal_one, one_mul]
      exact (congrArg (fun μ : Measure M => μ S)
        (globalMixedMeasure_congr rfl e (hx 0) (fun i => (hu i).1))).symm.le
    | succ m ih =>
      intro hm S
      have hmn : m < n := hm
      let k : Fin n := ⟨m, hmn⟩
      have e1 : x (m + 1) = Function.update (x m) k (w k) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp [x, k]
        · rw [Function.update_of_ne hi]
          have him : i.val ≠ m := fun he => hi (Fin.ext he)
          simp only [x]
          split_ifs <;> first | rfl | omega
      have e2 : Function.update (x m) k (u k) = x m := by
        funext i
        by_cases hi : i = k
        · subst hi; simp [x, k]
        · rw [Function.update_of_ne hi]
      have eθ : Function.update θ k (θ k) = θ := Function.update_eq_self k θ
      have hθ : θ k = (t k) • θ k + (1 - t k) • θ k := by
        rw [← add_smul, add_sub_cancel, one_smul]
      have hc' : ∀ i, ThetaPlurisubharmonic (θ i).val
          (Function.update (x m) k
            (fun p => (t k : EReal) * u k p + ((1 - t k : ℝ) : EReal) * v k p) i) := by
        change ∀ i, ThetaPlurisubharmonic (θ i).val (Function.update (x m) k (w k) i)
        rw [← e1]
        exact hx (m + 1)
      have ha' : ∀ i, ThetaPlurisubharmonic (Function.update θ k (θ k) i).val
          (Function.update (x m) k (u k) i) := by
        rw [eθ, e2]
        exact hx m
      have hb' : ∀ i, ThetaPlurisubharmonic (Function.update θ k (θ k) i).val
          (Function.update (x m) k (v k) i) := by
        intro i
        rw [eθ]
        by_cases hi : i = k
        · subst hi; rw [Function.update_self]; exact (hv k).1
        · rw [Function.update_of_ne hi]; exact hx m i
      have hpoleu := globalMixedMeasure_pole_null_of_nondegenerate hb' (hu k)
      have hpolev := globalMixedMeasure_pole_null_of_nondegenerate ha' (hv k)
      have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul
        k (ht0 k) (sub_pos.mpr (ht1 k)) hθ hc' ha' hb' hpoleu hpolev
      have hA : globalMixedMeasure (Function.update θ k (θ k))
          (Function.update (x m) k (u k)) ha' = globalMixedMeasure θ (x m) (hx m) :=
        globalMixedMeasure_congr eθ e2 _ _
      have hC : globalMixedMeasure θ (x (m + 1)) (hx (m + 1)) =
          globalMixedMeasure θ (Function.update (x m) k
            (fun p => (t k : EReal) * u k p + ((1 - t k : ℝ) : EReal) * v k p)) hc' :=
        globalMixedMeasure_congr rfl e1 _ _
      have ec1 : c m = Function.update (c m) k 1 :=
        (Function.update_eq_self_iff.mpr (by simp [c, k])).symm
      have ec2 : c (m + 1) = Function.update (c m) k (t k) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp [c, k]
        · rw [Function.update_of_ne hi]
          have him : i.val ≠ m := fun he => hi (Fin.ext he)
          simp only [c]
          split_ifs <;> first | rfl | omega
      have hprod : (∏ i, c (m + 1) i) = t k * ∏ i, c m i := by
        rw [ec2, Finset.prod_update_of_mem (Finset.mem_univ k)]
        conv_rhs => rw [ec1, Finset.prod_update_of_mem (Finset.mem_univ k)]
        simp only [one_mul]
      rw [hC, hlin, hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      calc
        ENNReal.ofReal (∏ i, c (m + 1) i) * globalMixedMeasure θ u (fun i => (hu i).1) S =
            ENNReal.ofReal (t k) * (ENNReal.ofReal (∏ i, c m i) *
              globalMixedMeasure θ u (fun i => (hu i).1) S) := by
          rw [hprod, ENNReal.ofReal_mul (ht0 k).le, mul_assoc]
        _ ≤ ENNReal.ofReal (t k) * globalMixedMeasure θ (x m) (hx m) S := by
          gcongr
          exact ih (Nat.le_of_succ_le hm) S
        _ ≤ _ := le_self_add
  have e : x n = w := by funext i; simp [x, i.isLt]
  have hprod : (∏ i, c n i) = ∏ i, t i := by
    apply Finset.prod_congr rfl
    intro i _
    simp [c, i.isLt]
  have h := step n le_rfl S
  rwa [hprod, globalMixedMeasure_congr rfl e (hx n) hw] at h

/-- Natural admissible diagonal mass gaps internally produce all PSH barriers
and control the actual independent mixed mass by their product coefficient. -/
theorem globalMixedMass_le_of_admissibleWeights [ConnectedSpace M]
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {φ ψ : Fin n → M → EReal} (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (hψ : ∀ i, IsThetaPshPotential (θ i).val (ψ i))
    (hle : ∀ i, φ i ≤ ψ i)
    (hpos : ∀ i, 0 < diagonalPotentialMass (θ i) (φ i) (hφ i))
    {b : Fin n → ℝ}
    (hb : ∀ i, IsAdmissibleWeight n (diagonalPotentialMass (θ i) (φ i) (hφ i))
      (diagonalPotentialMass (θ i) (ψ i) (hψ i)) (b i)) :
    ENNReal.ofReal (∏ i, (1 - (b i)⁻¹)) *
        MixedMass.globalMixedMass θ ψ (fun i => (hψ i).1) ≤
      MixedMass.globalMixedMass θ φ (fun i => (hφ i).1) := by
  classical
  choose ρ hρ hbar using fun i =>
    exists_thetaPsh_convexCombBarrier omega (θ i) (hφ i) (hψ i) (hle i) (hpos i) (hb i)
  have ht0 (i : Fin n) : 0 < 1 - (b i)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (hb i).one_lt)
  have ht1 (i : Fin n) : 1 - (b i)⁻¹ < 1 :=
    sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans (hb i).one_lt))
  have hW (i : Fin n) : IsThetaPshPotential (θ i).val
      (convexComb (1 - (b i)⁻¹) (ψ i) (ρ i)) :=
    isThetaPshPotential_convexComb (hψ i) (hρ i) (ht0 i) (ht1 i)
  have hWle (i : Fin n) : convexComb (1 - (b i)⁻¹) (ψ i) (ρ i) ≤ φ i := by
    rw [convexComb_symm (1 - (b i)⁻¹) (ψ i) (ρ i), sub_sub_cancel]
    exact hbar i
  exact (globalMixedMeasure_convexComb_le hψ hρ ht0 ht1 univ).trans
    (globalMixedMass_mono_of_isThetaPshPotential omega hW hφ
      (fun i => MoreSingularOn.of_le fun x _ => hWle i x))

end

end SGPT.Foundations.Analysis.Pending.ActualMixedMassAdmissibleBarrier
