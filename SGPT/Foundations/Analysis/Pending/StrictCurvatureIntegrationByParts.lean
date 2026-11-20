import SGPT.Foundations.Analysis.Pending.CoalescingWeightedMixedLimit
import SGPT.Foundations.Analysis.Pending.DeepCoincidenceIntegrationByParts

set_option autoImplicit false

/-!
# Strict-curvature singular diagonal integration by parts

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2, for normalized ordered
pairs with a strict Kähler curvature margin. Produce deep coincidence
at every actual parameter and pass the actual weighted mixed limits.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.StrictCurvatureIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open RelativeEnergyIntegrability NonPluripolarMixedCutoffs
open NonPluripolarPoleCoalescing CoalescingMixedCapacity
open IncreasingMixedWeakConvergence CoalescingWeightedMixedLimit
open DeepCoincidenceIntegrationByParts

noncomputable section

/-- Select a distinguished labelled family slot, and the first two family
slots according to the binary choice everywhere else. -/
def binaryFamilySelector {n : ℕ} (sigma : Fin n → Bool) (i0 : Fin n)
    (r : Fin 5) (i : Fin n) : Fin 5 :=
  if i = i0 then r else if sigma i then 0 else 1

/-- The interval bound identifies the precise deep region required by the
singular cutoff IBP theorem. -/
theorem eqOn_poleCoalescingApprox_deep {X : Type*} {u v : X → EReal}
    {B eps : ℝ} (heps : 0 < eps) (huv : u ≤ v) (hv0 : v ≤ 0)
    (hgap : ∀ x, v x ≤ u x + (B : EReal)) :
    EqOn u (poleCoalescingApprox eps u v)
      {x | min (u x) (poleCoalescingApprox eps u v x) < ((-(B + B / eps) : ℝ) : EReal)} := by
  intro x hx
  have hlow : u x ≤ poleCoalescingApprox eps u v x := le_max_left _ _
  change min (u x) (poleCoalescingApprox eps u v x) < ((-(B + B / eps) : ℝ) : EReal) at hx
  rw [min_eq_left hlow] at hx
  exact (poleCoalescingApprox_eq_of_deep_sublevel heps huv hv0 hgap hx.le).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- The actual selected family measure is exactly the actual binary updated
mixed measure, for any five-potential family. -/
theorem binaryMixedMeasure_eq_selectedFamily
    (theta : ClosedRealOneOneForm n M) (f : Fin 5 → M → EReal)
    (hf : ∀ r, ThetaPlurisubharmonic theta.val (f r))
    (sigma : Fin n → Bool) (i0 : Fin n) (r : Fin 5) :
    binaryMixedMeasure theta (hf 0) (hf 1) (hf r) sigma i0 =
      globalMixedMeasure (fun _ => theta)
        (fun i => f (binaryFamilySelector sigma i0 r i))
        (fun i => hf (binaryFamilySelector sigma i0 r i)) := by
  apply UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
  funext i
  by_cases hi : i = i0
  · subst hi
    simp [binaryFamilySelector]
  · simp only [Function.update_of_ne hi, binaryFamilySelector, if_neg hi,
      binaryPotentialTuple]
    split <;> rfl

/-- Every actual binary updated product has the coalescing first-weight limit;
all five labelled distinguished slots are allowed. -/
theorem tendsto_binary_integral_firstWeight
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal))
    (sigma : Fin n → Bool) (i0 : Fin n) (r : Fin 5) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (a x)
      (poleCoalescingApprox (strictKahlerParameter lam j) a b x)
      ∂binaryMixedMeasure omega.form
        (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 0).1
        (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 1).1
        (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j r).1
        sigma i0) atTop
      (𝓝 (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure omega.form
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 0).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 1).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq r).1
          sigma i0)) := by
  have h := tendsto_integral_firstWeight_mixed omega hlam hlam1 ha hb hp hq
    hab hpq hb0 hq0 hB hba hqp (binaryFamilySelector sigma i0 r)
    (ContinuousMap.const M (1 : ℝ))
  have hseq (j : ℕ) := binaryMixedMeasure_eq_selectedFamily omega.form
    (coalescingPotentialFamily (strictKahlerParameter lam j) a b p q)
    (fun s => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j s).1)
    sigma i0 r
  have hend := binaryMixedMeasure_eq_selectedFamily omega.form (fivePotentialFamily a b p q)
    (fun s => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq s).1)
    sigma i0 r
  simpa only [ContinuousMap.const_apply, one_mul, ← hseq, ← hend] using h

/-- At every actual strict parameter both pairs satisfy the deep-coincident
IBP, with their coincidence and same-type inputs produced explicitly. -/
theorem diagonal_integral_coalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) (j : ℕ) :
    (∫ x, canonicalERealDiffToReal (p x)
      (poleCoalescingApprox (strictKahlerParameter lam j) p q x)
      ∂globalMixedMeasure (fun _ => omega.form) (fun _ => a)
        (fun _ => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 0).1)) -
    (∫ x, canonicalERealDiffToReal (p x)
      (poleCoalescingApprox (strictKahlerParameter lam j) p q x)
      ∂globalMixedMeasure (fun _ => omega.form)
        (fun _ => poleCoalescingApprox (strictKahlerParameter lam j) a b)
        (fun _ => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 1).1)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x)
        (poleCoalescingApprox (strictKahlerParameter lam j) a b x)
        ∂binaryMixedMeasure omega.form
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 0).1
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 1).1
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 2).1
          (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x)
        (poleCoalescingApprox (strictKahlerParameter lam j) a b x)
        ∂binaryMixedMeasure omega.form
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 0).1
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 1).1
          (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j 3).1
          (stepSelector k) k)) := by
  obtain ⟨hpos, -, -, -⟩ := strictKahlerParameter_spec hlam hlam1
  have hf := isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq j
  exact diagonal_integral_sub_eq_sum_of_deepCoincidence omega omega.form omega.isSemipositive
    (hf 0).1 (hf 1).1 (hf 2).1 (hf 3).1
    (sameSingularityType_poleCoalescingApprox (hpos j).le hab hb0 hba).symm
    (sameSingularityType_poleCoalescingApprox (hpos j).le hpq hq0 hqp).symm
    (eqOn_poleCoalescingApprox_deep (hpos j) hab hb0 hba)
    (eqOn_poleCoalescingApprox_deep (hpos j) hpq hq0 hqp)

/-- The original strict-curvature singular diagonal IBP. Actual coalescing
identities and their produced weighted limits remove all deep-coincidence
assumptions; no IBP or convergence certificate is a premise. -/
theorem diagonal_integral_sub_eq_sum_of_strictCurvature
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (hqp : ∀ x, q x ≤ p x + (B : EReal)) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => omega.form) (fun _ => a)
        (fun _ => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 0).1)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => omega.form) (fun _ => b)
        (fun _ => (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 1).1)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure omega.form
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 0).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 1).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 2).1
          (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure omega.form
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 0).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 1).1
          (isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq 3).1
          (stepSelector k) k)) := by
  have hleftA := tendsto_integral_secondWeight_mixed omega hlam hlam1 ha hb hp hq
    hab hpq hb0 hq0 hB hba hqp (fun _ => 0) (ContinuousMap.const M (1 : ℝ))
  have hleftB := tendsto_integral_secondWeight_mixed omega hlam hlam1 ha hb hp hq
    hab hpq hb0 hq0 hB hba hqp (fun _ => 1) (ContinuousMap.const M (1 : ℝ))
  simp only [ContinuousMap.const_apply, one_mul] at hleftA hleftB
  have hright := tendsto_finsetSum Finset.univ (fun k _ =>
    (tendsto_binary_integral_firstWeight omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0
      hB hba hqp (stepSelector k) k 2).sub
    (tendsto_binary_integral_firstWeight omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0
      hB hba hqp (stepSelector k) k 3))
  exact tendsto_nhds_unique (hleftA.sub hleftB)
    (hright.congr' (Eventually.of_forall fun j =>
      (diagonal_integral_coalescingSequence omega hlam hlam1 ha hb hp hq hab hpq hb0 hq0
        hba hqp j).symm))

end

end SGPT.Foundations.Analysis.Pending.StrictCurvatureIntegrationByParts
