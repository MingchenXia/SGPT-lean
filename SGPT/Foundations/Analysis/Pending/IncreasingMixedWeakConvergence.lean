import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalWeakConvergence
import SGPT.Foundations.Analysis.Pending.MixedProductIntegralPolarization
import SGPT.Foundations.Analysis.Pending.CoalescingMixedCapacity

set_option autoImplicit false

/-!
# Actual increasing mixed weak convergence with a bounded gap

Apply actual diagonal weak convergence to each genuine subset sum, then
pass limits in the actual signed test-integral polarization identity.
This produces ordinary mixed weak convergence for the coalescing family
in Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingMixedWeakConvergence

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open GlobalMultilinearExpansion MixedSummandCapacityDomination
open IncreasingDiagonalWeakConvergence MixedProductIntegralPolarization
open NonPluripolarPoleCoalescing CoalescingMixedCapacity

noncomputable section

/-- Finite sums of sequences with nonpositive extended-real limits converge,
including limits at poles. Addition is continuous below positive infinity. -/
theorem tendsto_finsetSum_ereal_of_nonpos {iota : Type*} (S : Finset iota)
    {f : iota → ℕ → EReal} {v : iota → EReal}
    (hlim : ∀ i, Tendsto (f i) atTop (𝓝 (v i))) (hv0 : ∀ i, v i ≤ 0) :
    Tendsto (fun j => ∑ i ∈ S, f i j) atTop (𝓝 (∑ i ∈ S, v i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact tendsto_const_nhds
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hvi : v i ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hv0 i)
    have hvS : (∑ k ∈ S, v k) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (Finset.sum_nonpos fun k _ => hv0 k)
    exact (EReal.continuousAt_add (p := (v i, ∑ k ∈ S, v k))
      (Or.inl hvi) (Or.inr hvS)).tendsto.comp ((hlim i).prodMk_nhds ih)

/-- The actual moving family increases when its positive parameters decrease. -/
theorem coalescingPotentialFamily_monotone {X : Type*} {eps : ℕ → ℝ}
    (hpos : ∀ j, 0 < eps j) (hanti : Antitone eps) {a b p q : X → EReal}
    (hb0 : b ≤ 0) (hq0 : q ≤ 0) :
    ∀ i, Monotone (fun j => coalescingPotentialFamily (eps j) a b p q i) := by
  intro i j k hjk x
  fin_cases i
  · exact le_rfl
  · exact poleCoalescingApprox_antitone hb0 (hpos k) (hpos j) (hanti hjk) x
  · exact le_rfl
  · exact poleCoalescingApprox_antitone hq0 (hpos k) (hpos j) (hanti hjk) x
  · exact le_rfl

/-- The actual moving family converges pointwise to its original family,
including the common pole values. -/
theorem tendsto_coalescingPotentialFamily {X : Type*} {eps : ℕ → ℝ}
    (hpos : ∀ j, 0 < eps j) (hlim : Tendsto eps atTop (𝓝 0)) {a b p q : X → EReal}
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0) :
    ∀ i x, Tendsto (fun j => coalescingPotentialFamily (eps j) a b p q i x) atTop
      (𝓝 (fivePotentialFamily a b p q i x)) := by
  intro i x
  fin_cases i
  · exact tendsto_const_nhds
  · exact tendsto_poleCoalescingApprox hpos hlim hab hb0 x
  · exact tendsto_const_nhds
  · exact tendsto_poleCoalescingApprox hpos hlim hpq hq0 x
  · exact tendsto_const_nhds

/-- All five original slots inherit the source's nonpositive normalization. -/
theorem fivePotentialFamily_le_zero {X : Type*} {a b p q : X → EReal}
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0) :
    ∀ i, fivePotentialFamily a b p q i ≤ 0 := by
  intro i
  fin_cases i
  · exact hab.trans hb0
  · exact hb0
  · exact hpq.trans hq0
  · exact hq0
  · exact le_rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual subset form in a common background is its cardinal multiple. -/
theorem sumForm_const_eq_card_smul (theta : ClosedRealOneOneForm n M)
    (S : Finset (Fin n)) :
    sumForm S (fun _ => 1) (fun _ => theta) = (S.card : ℝ) • theta := by
  rw [sumForm, ← Finset.sum_smul]
  simp

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every common-background subset form is semipositive. -/
theorem sumForm_const_isSemipositive {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) (S : Finset (Fin n)) :
    (sumForm S (fun _ => 1) (fun _ => theta)).val.IsSemipositive := by
  rw [sumForm_const_eq_card_smul]
  exact KahlerDomination.isSemipositive_smul hsemi (Nat.cast_nonneg _)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- The actual subset sum inherits the uniform gap, multiplied by its cardinal. -/
theorem subsetSum_boundedGap {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    {B : ℝ} (hgap : ∀ j i x, v i x ≤ u j i x + (B : EReal))
    (S : Finset (Fin n)) (j : ℕ) (x : M) :
    sumPot S (fun _ => 1) v x ≤ sumPot S (fun _ => 1) (u j) x +
      (((S.card : ℝ) * B : ℝ) : EReal) := by
  have h := sumPot_mono (T := S) (fun _ : Fin n => one_pos)
    (fun i x => hgap j i x) x
  rw [sumPot_add_const (fun _ : Fin n => one_pos)] at h
  simpa only [one_mul, Finset.sum_const, nsmul_eq_mul] using h

/-- Every actual partial-sum diagonal product has an ordinary test-integral
limit, with its genuine regularity, semipositivity and mass gap produced. -/
theorem tendsto_integral_diagonal_subsetSum
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential theta.val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential theta.val (v i)) (hv0 : ∀ i, v i ≤ 0)
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x)))
    {B : ℝ} (hB : 0 ≤ B) (hgap : ∀ j i x, v i x ≤ u j i x + (B : EReal))
    (S : Finset (Fin n)) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂(diagonalPotentialMeasure
      (sumForm S (fun _ => 1) (fun _ => theta)) (sumPot S (fun _ => 1) (u j))
        (isThetaPshPotential_subsetSum (hu j) S))) atTop
      (𝓝 (∫ x, chi x ∂(diagonalPotentialMeasure
        (sumForm S (fun _ => 1) (fun _ => theta)) (sumPot S (fun _ => 1) v)
          (isThetaPshPotential_subsetSum hv S)))) := by
  apply tendsto_integral_diagonal_of_monotone_of_boundedGap omega
    (sumForm_const_isSemipositive hsemi S) (fun j => isThetaPshPotential_subsetSum (hu j) S)
    (fun i j hij => sumPot_mono (fun _ => one_pos) (fun k => hmono k hij))
    (isThetaPshPotential_subsetSum hv S) _
    (mul_nonneg (Nat.cast_nonneg S.card) hB) (subsetSum_boundedGap hgap S) chi
  intro x
  simpa only [sumPot, EReal.coe_one, one_mul] using
    tendsto_finsetSum_ereal_of_nonpos S (fun i => hlim i x) (fun i => hv0 i x)

/-- Actual mixed continuous-test integrals converge by finite polarization.
No weak-convergence conclusion or mass-equality conclusion is a premise. -/
theorem tendsto_integral_mixed_of_monotone_of_boundedGap
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential theta.val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential theta.val (v i)) (hv0 : ∀ i, v i ≤ 0)
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x)))
    {B : ℝ} (hB : 0 ≤ B) (hgap : ∀ j i x, v i x ≤ u j i x + (B : EReal))
    (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂(globalMixedMeasure (fun _ => theta) (u j)
      (fun i => (hu j i).1))) atTop
      (𝓝 (∫ x, chi x ∂(globalMixedMeasure (fun _ => theta) v (fun i => (hv i).1)))) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n))) fun S _ =>
    (tendsto_const_nhds (x := (-1 : ℝ) ^ (n - S.card))).mul
      (tendsto_integral_diagonal_subsetSum omega hsemi hu hmono hv hv0 hlim hB hgap S chi)
  have hj := fun j => integral_mixed_eq_signed_diagonal_subsetSum omega (hu j) chi
  have hvtest := integral_mixed_eq_signed_diagonal_subsetSum omega hv chi
  have hfaclim : Tendsto (fun j => (n.factorial : ℝ) *
      ∫ x, chi x ∂(globalMixedMeasure (fun _ => theta) (u j) (fun i => (hu j i).1)))
      atTop (𝓝 ((n.factorial : ℝ) *
        ∫ x, chi x ∂(globalMixedMeasure (fun _ => theta) v (fun i => (hv i).1)))) := by
    simpa only [hj, hvtest] using hsum
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa only [inv_mul_cancel_left₀ hfac] using
    (tendsto_const_nhds (x := (n.factorial : ℝ)⁻¹)).mul hfaclim

/-- The actual common-background mixed product with its produced finite mass. -/
def finiteMixedMeasure (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential theta.val (u i)) : FiniteMeasure M :=
  ⟨globalMixedMeasure (fun _ => theta) u (fun i => (hu i).1),
    globalMixedMeasure_isFiniteMeasure omega (fun i => (hu i).1)⟩

/-- The actual increasing mixed products converge in the native weak topology. -/
theorem weakTendsto_mixed_of_monotone_of_boundedGap
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential theta.val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential theta.val (v i)) (hv0 : ∀ i, v i ≤ 0)
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x)))
    {B : ℝ} (hB : 0 ≤ B) (hgap : ∀ j i x, v i x ≤ u j i x + (B : EReal)) :
    Tendsto (fun j => finiteMixedMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteMixedMeasure omega theta v hv)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro chi
  exact tendsto_integral_mixed_of_monotone_of_boundedGap omega hsemi hu hmono hv hv0 hlim
    hB hgap chi.toContinuousMap

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual original five-potential endpoint is genuine for the Kähler form. -/
theorem isThetaPshPotential_originalFamily_kahler
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : lam ≤ 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q) :
    ∀ i, IsThetaPshPotential omega.form.val (fivePotentialFamily a b p q i) := by
  have lift {u : M → EReal} (hu : IsThetaPshPotential (lam • omega.form).val u) :
      IsThetaPshPotential omega.form.val u := by
    simpa only [one_smul] using isThetaPshPotential_smul_kahler_mono omega hlam hu
  exact isThetaPshPotential_fivePotentialFamily omega.isSemipositive
    (lift ha) (lift hb) (lift hp) (lift hq)

/-- Every selected actual mixed strict-schedule product converges weakly to
its original endpoint, with no measure convergence or domination premise. -/
theorem weakTendsto_coalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (selector : Fin n → Fin 5) :
    Tendsto (fun j => finiteMixedMeasure omega omega.form
      (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
      (fun i => isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
        (selector i))) atTop
      (𝓝 (finiteMixedMeasure omega omega.form
        (fun i => fivePotentialFamily a b p q (selector i))
        (fun i => isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
          (selector i)))) := by
  obtain ⟨hpos, hanti, hlim, -⟩ := strictKahlerParameter_spec hlam hlam1
  exact weakTendsto_mixed_of_monotone_of_boundedGap omega omega.isSemipositive
    (fun j i => isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
      (selector i))
    (fun i => coalescingPotentialFamily_monotone hpos hanti hb0 hq0 (selector i))
    (fun i => isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq (selector i))
    (fun i => fivePotentialFamily_le_zero hab hpq hb0 hq0 (selector i))
    (fun i => tendsto_coalescingPotentialFamily hpos hlim hab hpq hb0 hq0 (selector i))
    hB (fun j i x =>
      (coalescingPotentialFamily_box hB (hpos j).le hab hpq hb0 hq0 hba hqp).2 (selector i) x)

/-- Ordinary continuous-test convergence for the full actual mixed sequence. -/
theorem tendsto_integral_coalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (selector : Fin n → Fin 5) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂(globalMixedMeasure (fun _ => omega.form)
      (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
      (fun i => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
        (selector i)).1))) atTop
      (𝓝 (∫ x, chi x ∂(globalMixedMeasure (fun _ => omega.form)
        (fun i => fivePotentialFamily a b p q (selector i))
        (fun i => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
          (selector i)).1)))) :=
  (FiniteMeasure.continuous_integral_continuousMap chi).tendsto _ |>.comp
    (weakTendsto_coalescingSequence omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0 hB hba hqp
      selector)

end

end SGPT.Foundations.Analysis.Pending.IncreasingMixedWeakConvergence
