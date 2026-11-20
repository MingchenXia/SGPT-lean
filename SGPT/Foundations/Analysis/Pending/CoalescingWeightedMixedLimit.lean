import SGPT.Foundations.Analysis.Pending.IncreasingMixedWeakConvergence
import SGPT.Foundations.Analysis.Pending.StrictReferenceCapacityComparison
import SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity

set_option autoImplicit false

/-!
# Actual weighted coalescing mixed-product limits

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2 and Theorem 2.5.
All capacity, ordinary weak convergence, and signed-weight inputs are produced
for the actual strict-curvature family. The resulting limit has no convergence
or domination hypothesis. Its two source weights are exported for every actual
slot selector.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.CoalescingWeightedMixedLimit

open FirstPass FirstPass.PositiveClasses RelativeEnergyIntegrability
open GlobalNonPluripolar GlobalSlotComparison
open NonPluripolarPoleCoalescing CoalescingMixedCapacity
open IncreasingMixedWeakConvergence StrictReferenceCapacityComparison
open PoleCoalescingCapacity CapacityWeightedConvergence ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Lu 2.5 applied to the actual mixed strict-curvature sequence and an actual
coalescing weight. Every convergence and capacity input is produced. -/
theorem tendsto_integral_coalescingWeight_mixed
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (selector : Fin n → Fin 5)
    {r t : M → EReal} (hr : IsThetaPshPotential omega.form.val r)
    (ht : IsThetaPshPotential omega.form.val t)
    (hrt : r ≤ t) (ht0 : t ≤ 0) {D : ℝ} (hD : 0 ≤ D)
    (htr : ∀ x, t x ≤ r x + (D : EReal)) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * canonicalERealDiffToReal (r x)
      (poleCoalescingApprox (strictKahlerParameter lam j) r t x)
      ∂(globalMixedMeasure (fun _ => omega.form)
        (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
        (fun i => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
          (selector i)).1))) atTop
      (𝓝 (∫ x, chi x * canonicalERealDiffToReal (r x) (t x)
        ∂(globalMixedMeasure (fun _ => omega.form)
          (fun i => fivePotentialFamily a b p q (selector i))
          (fun i => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
            (selector i)).1)))) := by
  obtain ⟨hpos, -, hlim, -⟩ := strictKahlerParameter_spec hlam hlam1
  have htype : SameSingularityTypeOn r t univ :=
    ⟨MoreSingularOn.of_le fun x _ => hrt x, ⟨D, fun x _ => htr x⟩⟩
  exact tendsto_integral_mul_of_weakTendsto
    (mu := fun j => finiteMixedMeasure omega omega.form
      (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
      (fun i => isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
        (selector i)))
    (nu := finiteMixedMeasure omega omega.form
      (fun i => fivePotentialFamily a b p q (selector i))
      (fun i => isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
        (selector i)))
    (uniformCapacityControl_coalescingSequence omega hlam hlam1 ha hb hp hq hB hab hpq hb0 hq0
      hba hqp selector)
    (weakTendsto_coalescingSequence omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0 hB hba hqp
      selector)
    (fun j => measurable_coalescingWeight (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hr.1) (GlobalSlotComparison.ThetaPlurisubharmonic.measurable ht.1)
      (strictKahlerParameter lam j))
    (measurable_canonicalWeight (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hr.1) (GlobalSlotComparison.ThetaPlurisubharmonic.measurable ht.1))
    (quasiContinuousFor_canonicalWeight omega omega.isSemipositive hr ht (hrt.trans ht0) ht0
      htype)
    hD (fun j => abs_canonicalDiff_poleCoalescingApprox_le hD (hpos j).le hrt ht0 htr)
    (abs_canonicalDiff_le_of_orderGap hD hrt ht0 htr)
    (fun delta hdelta => tendsto_thetaCapacity_coalescingWeight_gap omega omega.isSemipositive
      ht hrt ht0 htr hpos hlim hdelta) chi

/-- The actual first source weight has the weighted limit against every
selected actual mixed coalescing product. -/
theorem tendsto_integral_firstWeight_mixed
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (selector : Fin n → Fin 5) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * canonicalERealDiffToReal (a x)
      (poleCoalescingApprox (strictKahlerParameter lam j) a b x)
      ∂(globalMixedMeasure (fun _ => omega.form)
        (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
        (fun i => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
          (selector i)).1))) atTop
      (𝓝 (∫ x, chi x * canonicalERealDiffToReal (a x) (b x)
        ∂(globalMixedMeasure (fun _ => omega.form)
          (fun i => fivePotentialFamily a b p q (selector i))
          (fun i => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
            (selector i)).1)))) := by
  have hf := isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
  exact tendsto_integral_coalescingWeight_mixed omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0
    hB hba hqp selector (hf 0) (hf 1) hab hb0 hB hba chi

/-- The actual second source weight has the weighted limit against every
selected actual mixed coalescing product. -/
theorem tendsto_integral_secondWeight_mixed
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (selector : Fin n → Fin 5) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * canonicalERealDiffToReal (p x)
      (poleCoalescingApprox (strictKahlerParameter lam j) p q x)
      ∂(globalMixedMeasure (fun _ => omega.form)
        (fun i => coalescingPotentialFamily (strictKahlerParameter lam j) a b p q (selector i))
        (fun i => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
          (selector i)).1))) atTop
      (𝓝 (∫ x, chi x * canonicalERealDiffToReal (p x) (q x)
        ∂(globalMixedMeasure (fun _ => omega.form)
          (fun i => fivePotentialFamily a b p q (selector i))
          (fun i => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
            (selector i)).1)))) := by
  have hf := isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
  exact tendsto_integral_coalescingWeight_mixed omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0
    hB hba hqp selector (hf 2) (hf 3) hpq hq0 hB hqp chi

end

end SGPT.Foundations.Analysis.Pending.CoalescingWeightedMixedLimit
