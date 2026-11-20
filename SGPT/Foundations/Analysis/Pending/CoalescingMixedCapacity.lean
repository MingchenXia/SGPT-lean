import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# One actual common reference for Lu's coalescing mixed products

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2. Include the zero potential as
one of five equally weighted genuine potentials. The reference is the fixed
sum `(a+b+p+q)/5`; actual max approximations lie in uniform pointwise boxes.
This supplies actual selected mixed-measure domination with a constant
independent of epsilon. Zero-reference comparison and ordinary weak
convergence are separate producers.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CoalescingMixedCapacity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar ThetaCapacity
open GlobalMultilinearExpansion MixedSummandCapacityDomination NonPluripolarPoleCoalescing

noncomputable section

/-- Four actual potentials and the fifth, zero potential. -/
def fivePotentialFamily {X : Type*} (a b p q : X → EReal) : Fin 5 → X → EReal :=
  ![a, b, p, q, fun _ => 0]

/-- The fixed reference used for all actual approximants. -/
def commonReference {X : Type*} (a b p q : X → EReal) : X → EReal :=
  sumPot Finset.univ (fun _ : Fin 5 => (1 / 5 : ℝ)) (fivePotentialFamily a b p q)

/-- Lu's two actual maxima, the two fixed lower potentials, and zero. -/
def coalescingPotentialFamily {X : Type*} (eps : ℝ) (a b p q : X → EReal) :
    Fin 5 → X → EReal :=
  fivePotentialFamily a (poleCoalescingApprox eps a b) p (poleCoalescingApprox eps p q)

/-- The finite-family reference is exactly the source's four-potential average. -/
theorem commonReference_apply {X : Type*} (a b p q : X → EReal) (x : X) :
    commonReference a b p q x = ((1 / 5 : ℝ) : EReal) * (a x + b x + p x + q x) := by
  have hdist := EReal.left_distrib_of_nonneg_of_ne_top
    (x := ((1 / 5 : ℝ) : EReal)) (by norm_num) (by simp)
  simp_rw [hdist]
  simp [commonReference, sumPot, fivePotentialFamily, Fin.sum_univ_succ]
  abel

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The five equally weighted background forms sum to the original form. -/
theorem sumForm_five_eq (theta : ClosedRealOneOneForm n M) :
    sumForm Finset.univ (fun _ : Fin 5 => (1 / 5 : ℝ)) (fun _ => theta) = theta := by
  rw [sumForm, ← Finset.sum_smul]
  norm_num

/-- All five fixed slots are genuine potentials. -/
theorem isThetaPshPotential_fivePotentialFamily {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q) :
    ∀ i, IsThetaPshPotential theta.val (fivePotentialFamily a b p q i) := by
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff theta).mpr hsemi
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hp
  · exact hq
  · exact hzero

/-- The common reference is genuine, including local nondegeneracy. -/
theorem isThetaPshPotential_commonReference {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q) :
    IsThetaPshPotential theta.val (commonReference a b p q) := by
  have h := isThetaPshPotential_sumPot Finset.univ_nonempty
    (fun _ : Fin 5 => (by norm_num : (0 : ℝ) < 1 / 5))
    (isThetaPshPotential_fivePotentialFamily hsemi ha hb hp hq)
  simpa only [sumForm_five_eq, commonReference] using h

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Every actual moving slot is in its fixed pointwise box of width `B`. -/
theorem coalescingPotentialFamily_box {a b p q : M → EReal} {B eps : ℝ}
    (hB : 0 ≤ B) (heps : 0 ≤ eps) (hab : a ≤ b) (hpq : p ≤ q)
    (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal)) :
    (∀ i, coalescingPotentialFamily eps a b p q i ≤ fivePotentialFamily a b p q i) ∧
    (∀ i x, fivePotentialFamily a b p q i x ≤
      coalescingPotentialFamily eps a b p q i x + (B : EReal)) := by
  have hself : ∀ v : M → EReal, ∀ x, v x ≤ v x + (B : EReal) := by
    intro v x
    simpa only [add_zero] using add_le_add (le_refl (v x)) (EReal.coe_nonneg.mpr hB)
  constructor
  · intro i x
    fin_cases i
    · exact le_rfl
    · exact (poleCoalescingApprox_bounds heps hab hb0 hba x).2.1
    · exact le_rfl
    · exact (poleCoalescingApprox_bounds heps hpq hq0 hqp x).2.1
    · exact le_rfl
  · intro i x
    fin_cases i
    · exact hself a x
    · exact (hba x).trans (add_le_add (le_max_left _ _) le_rfl)
    · exact hself p x
    · exact (hqp x).trans (add_le_add (le_max_left _ _) le_rfl)
    · exact hself (fun _ => 0) x

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual coalescing slots have the original Kähler curvature whenever
the scaling stays in its given curvature margin. -/
theorem isThetaPshPotential_coalescingPotentialFamily_of_margin
    (omega : KahlerBackground n M) {lam eps : ℝ} (hlam : lam ≤ 1)
    (heps : 0 < eps) (hscaled : (1 + eps) * lam ≤ 1) {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q) :
    ∀ i, IsThetaPshPotential omega.form.val (coalescingPotentialFamily eps a b p q i) := by
  have lift {u : M → EReal} (hu : IsThetaPshPotential (lam • omega.form).val u) :
      IsThetaPshPotential omega.form.val u := by
    simpa only [one_smul] using isThetaPshPotential_smul_kahler_mono omega hlam hu
  have hbe : IsThetaPshPotential omega.form.val (poleCoalescingApprox eps a b) := by
    simpa only [one_smul] using
      isThetaPshPotential_poleCoalescingApprox omega heps hlam hscaled ha hb
  have hqe : IsThetaPshPotential omega.form.val (poleCoalescingApprox eps p q) := by
    simpa only [one_smul] using
      isThetaPshPotential_poleCoalescingApprox omega heps hlam hscaled hp hq
  exact isThetaPshPotential_fivePotentialFamily omega.isSemipositive (lift ha) hbe (lift hp) hqe

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every member of the explicit strict-margin sequence is a genuine
potential for the original Kähler background. -/
theorem isThetaPshPotential_coalescingSequenceFamily
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q) (k : ℕ) :
    ∀ i, IsThetaPshPotential omega.form.val
      (coalescingPotentialFamily (strictKahlerParameter lam k) a b p q i) := by
  obtain ⟨hpos, -, -, hscaled⟩ := strictKahlerParameter_spec hlam hlam1
  exact isThetaPshPotential_coalescingPotentialFamily_of_margin omega hlam1.le (hpos k)
    ((hscaled k).trans (by linarith)) ha hb hp hq

/-- Actual coalescing mixed products are uniformly controlled by one fixed
relative capacity, for every slot selector and every set. -/
theorem mixedMeasure_apply_le_commonCapacity {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    {B eps : ℝ} (hB : 0 ≤ B) (heps : 0 ≤ eps)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal))
    (hbep : IsThetaPshPotential theta.val (poleCoalescingApprox eps a b))
    (hqep : IsThetaPshPotential theta.val (poleCoalescingApprox eps p q))
    (s : Fin n → Fin 5) (E : Set M) :
    globalMixedMeasure (fun _ => theta) (fun j => coalescingPotentialFamily eps a b p q (s j))
      (fun j => (isThetaPshPotential_fivePotentialFamily hsemi ha hbep hp hqep (s j)).1) E ≤
    ENNReal.ofReal ((5 * (B + 1)) ^ n) * thetaCapacity theta (commonReference a b p q) E := by
  obtain ⟨hgf, hfg⟩ := coalescingPotentialFamily_box hB heps hab hpq hb0 hq0 hba hqp
  have hBC : ∑ i : Fin 5, (1 / 5 : ℝ) * B ≤ B + 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have h := selectedMixedMeasure_apply_le_capacity_of_box Finset.univ_nonempty
    (fun _ : Fin 5 => (by norm_num : (0 : ℝ) < 1 / 5))
    (isThetaPshPotential_fivePotentialFamily hsemi ha hb hp hq)
    (isThetaPshPotential_fivePotentialFamily hsemi ha hbep hp hqep)
    hgf hfg (by linarith : 1 ≤ B + 1) hBC s (fun _ => Finset.mem_univ _) E
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, sumForm_five_eq] at h
  have hcancel : ENNReal.ofReal ((5 : ℝ) ^ n) * ENNReal.ofReal ((1 / 5 : ℝ) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num) _), ← mul_pow]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ENNReal.ofReal ((5 : ℝ) ^ n) from zero_le)
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  calc _ ≤ ENNReal.ofReal ((5 : ℝ) ^ n) *
        (ENNReal.ofReal ((B + 1) ^ n) * thetaCapacity theta (commonReference a b p q) E) := hscaled
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num) _), ← mul_pow]

/-- The curvature margin itself produces all genuine max slots needed for
the actual common-capacity bound. -/
theorem mixedMeasure_apply_le_commonCapacity_of_margin
    (omega : KahlerBackground n M) {lam eps : ℝ} (hlam : lam ≤ 1)
    (heps : 0 < eps) (hscaled : (1 + eps) * lam ≤ 1) {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    {B : ℝ} (hB : 0 ≤ B) (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal))
    (s : Fin n → Fin 5) (E : Set M) :
    globalMixedMeasure (fun _ => omega.form)
      (fun j => coalescingPotentialFamily eps a b p q (s j))
      (fun j => (isThetaPshPotential_coalescingPotentialFamily_of_margin
        omega hlam heps hscaled ha hb hp hq (s j)).1) E ≤
    ENNReal.ofReal ((5 * (B + 1)) ^ n) *
      thetaCapacity omega.form (commonReference a b p q) E := by
  have lift {u : M → EReal} (hu : IsThetaPshPotential (lam • omega.form).val u) :
      IsThetaPshPotential omega.form.val u := by
    simpa only [one_smul] using isThetaPshPotential_smul_kahler_mono omega hlam hu
  have hf := isThetaPshPotential_coalescingPotentialFamily_of_margin
    omega hlam heps hscaled ha hb hp hq
  exact mixedMeasure_apply_le_commonCapacity omega.isSemipositive
    (lift ha) (lift hb) (lift hp) (lift hq) hB heps.le hab hpq hb0 hq0 hba hqp (hf 1) (hf 3) s E

/-- Uniform domination of the actual explicit coalescing sequence, including
all binary mixed terms and its diagonal endpoints via slot selection. -/
theorem mixedMeasure_sequence_apply_le_commonCapacity
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    {B : ℝ} (hB : 0 ≤ B) (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal))
    (k : ℕ) (s : Fin n → Fin 5) (E : Set M) :
    globalMixedMeasure (fun _ => omega.form)
      (fun j => coalescingPotentialFamily (strictKahlerParameter lam k) a b p q (s j))
      (fun j => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq k (s j)).1) E ≤
    ENNReal.ofReal ((5 * (B + 1)) ^ n) *
      thetaCapacity omega.form (commonReference a b p q) E := by
  obtain ⟨hpos, -, -, hscaled⟩ := strictKahlerParameter_spec hlam hlam1
  exact mixedMeasure_apply_le_commonCapacity_of_margin omega hlam1.le (hpos k)
    ((hscaled k).trans (by linarith)) ha hb hp hq hB hab hpq hb0 hq0 hba hqp s E

end

end SGPT.Foundations.Analysis.Pending.CoalescingMixedCapacity
