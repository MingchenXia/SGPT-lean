import SGPT.Foundations.Analysis.Pending.NonPluripolarMixedCutoffs
import SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts

/-!
# Diagonal integration by parts for pairs equal near their poles

Lu, Lemma 4.1 Step 1.1: telescope the genuine bounded slotwise
formula, then take the actual diagonal and weighted mixed cutoff
limits. The target is the deep-coincident singular identity;
removing coincidence by capacity-controlled approximation is separate.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.DeepCoincidenceIntegrationByParts

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar
open NonPluripolarCutoffCancellation NonPluripolarCutoffLimits NonPluripolarMixedCutoffs
open RelativeEnergyIntegrability

noncomputable section

/-- The binary choice of the first `k` slots used in the diagonal telescoping sum. -/
def stepSelector {n : ℕ} (k : Fin n) (i : Fin n) : Bool := decide (i.val < k.val)

/-- The actual prefix tuple, with the first `j` slots filled by `a`. -/
def prefixPotentialTuple {n : ℕ} {X : Type*} (j : ℕ) (a b : X → EReal)
    (i : Fin n) : X → EReal := if i.val < j then a else b

/-- Real telescoping on a finite interval, including the empty interval. -/
theorem sum_fin_successive_sub {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ k : Fin n, (f k.succ - f k.castSucc)) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  linarith

/-- The successor prefix inserts `a` in precisely the distinguished slot. -/
theorem prefixPotentialTuple_succ {n : ℕ} {X : Type*} (k : Fin n) (a b : X → EReal) :
    prefixPotentialTuple (k.val + 1) a b =
      Function.update (binaryPotentialTuple (stepSelector k) a b) k a := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [prefixPotentialTuple]
  · rw [Function.update_of_ne hi]
    have hne : i.val ≠ k.val := fun h => hi (Fin.ext h)
    have heq : i.val < k.val + 1 ↔ i.val < k.val := by omega
    simp [prefixPotentialTuple, binaryPotentialTuple, stepSelector, heq]

/-- The current prefix inserts `b` in that same slot. -/
theorem prefixPotentialTuple_current {n : ℕ} {X : Type*} (k : Fin n) (a b : X → EReal) :
    prefixPotentialTuple k.val a b =
      Function.update (binaryPotentialTuple (stepSelector k) a b) k b := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [prefixPotentialTuple]
  · rw [Function.update_of_ne hi]
    simp [prefixPotentialTuple, binaryPotentialTuple, stepSelector]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The prefix tuple consists of actual raw PSH slots. -/
theorem thetaPlurisubharmonic_prefixPotentialTuple
    (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b) (j : ℕ) :
    ∀ i : Fin n, ThetaPlurisubharmonic theta.val (prefixPotentialTuple j a b i) := by
  intro i
  unfold prefixPotentialTuple
  split
  · exact ha
  · exact hb

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Actual cutoff commutes with the binary tuple and distinguished-slot selection. -/
theorem binaryMixedCutoffMeasure_eq_truncated
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b r : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hr : ThetaPlurisubharmonic theta.val r)
    (sigma : Fin n → Bool) (i0 : Fin n) (t : ℝ) :
    binaryMixedCutoffMeasure theta htheta ha hb hr sigma i0 t =
      binaryMixedMeasure theta (thetaPlurisubharmonic_canonicalTruncation htheta ha t)
        (thetaPlurisubharmonic_canonicalTruncation htheta hb t)
        (thetaPlurisubharmonic_canonicalTruncation htheta hr t) sigma i0 := by
  apply UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
  funext i x
  by_cases hi : i = i0
  · subst hi
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hi, binaryPotentialTuple]
    split <;> rfl

private theorem canonicalDiff_eq_sub_of_bounded {X : Type*} {a b : X → EReal}
    (ha : IsBoundedPotential a) (hb : IsBoundedPotential b) (x : X) :
    canonicalERealDiffToReal (a x) (b x) = (a x).toReal - (b x).toReal :=
  canonicalDiff_eq_sub_toReal (ha.ne_top x) (hb.ne_top x)
    (iff_of_false (ha.ne_bot x) (hb.ne_bot x))

/-- Actual bounded one-slot IBP with the exact signed integrands used by the
cutoff limits and the actual binary mixed measures. -/
theorem bounded_binaryMixedMeasure_integral_sub_symm
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {a b p q : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hp : ThetaPlurisubharmonic theta.val p)
    (hq : ThetaPlurisubharmonic theta.val q) (hab : IsBoundedPotential a)
    (hbb : IsBoundedPotential b) (hpb : IsBoundedPotential p) (hqb : IsBoundedPotential q)
    (sigma : Fin n → Bool) (i0 : Fin n) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂binaryMixedMeasure theta ha hb ha sigma i0) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂binaryMixedMeasure theta ha hb hb sigma i0) =
    (∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂binaryMixedMeasure theta ha hb hp sigma i0) -
    (∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂binaryMixedMeasure theta ha hb hq sigma i0) := by
  have hw : ∀ i, IsBoundedPotential (binaryPotentialTuple sigma a b i) := by
    intro i
    unfold binaryPotentialTuple
    split
    · exact hab
    · exact hbb
  have hforms : Function.update (fun _ : Fin n => theta) i0 theta = fun _ => theta := by
    funext i
    by_cases hi : i = i0
    · subst hi
      simp
    · simp only [Function.update_of_ne hi]
  have hca : ∀ i, ThetaPlurisubharmonic
      (Function.update (fun _ : Fin n => theta) i0 theta i).val
      (Function.update (binaryPotentialTuple sigma a b) i0 a i) := by
    rw [hforms]
    exact thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb ha sigma i0
  have hcb : ∀ i, ThetaPlurisubharmonic
      (Function.update (fun _ : Fin n => theta) i0 theta i).val
      (Function.update (binaryPotentialTuple sigma a b) i0 b i) := by
    rw [hforms]
    exact thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hb sigma i0
  have h := BoundedIntegrationByParts.integral_sub_symm omega hw i0 hpb hqb hab hbb
    (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hp sigma i0)
    (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hq sigma i0) hca hcb
  simp_rw [canonicalDiff_eq_sub_of_bounded hpb hqb,
    canonicalDiff_eq_sub_of_bounded hab hbb]
  simpa only [binaryMixedMeasure, hforms] using h

/-- The actual prefix mixed measure used in diagonal telescoping. -/
def prefixMixedMeasure (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (j : ℕ) : Measure M :=
  globalMixedMeasure (fun _ => theta) (prefixPotentialTuple j a b)
    (thetaPlurisubharmonic_prefixPotentialTuple theta ha hb j)

omit [BorelSpace M] in
/-- Successive actual prefix measures identify the binary `a`-slot measures. -/
theorem prefixMixedMeasure_succ (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (k : Fin n) :
    prefixMixedMeasure theta ha hb (k.val + 1) =
      binaryMixedMeasure theta ha hb ha (stepSelector k) k :=
  UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple (prefixPotentialTuple_succ k a b) _ _

omit [BorelSpace M] in
/-- Current actual prefix measures identify the binary `b`-slot measures. -/
theorem prefixMixedMeasure_current (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (k : Fin n) :
    prefixMixedMeasure theta ha hb k.val =
      binaryMixedMeasure theta ha hb hb (stepSelector k) k :=
  UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple (prefixPotentialTuple_current k a b) _ _

/-- The genuine bounded diagonal IBP formula follows by actual slotwise
measure identities and finite telescoping, also in dimension zero. -/
theorem bounded_diagonal_integral_sub_eq_sum
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {a b p q : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hp : ThetaPlurisubharmonic theta.val p)
    (hq : ThetaPlurisubharmonic theta.val q) (hab : IsBoundedPotential a)
    (hbb : IsBoundedPotential b) (hpb : IsBoundedPotential p) (hqb : IsBoundedPotential q) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hp (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hq (stepSelector k) k)) := by
  let f : Fin (n + 1) → ℝ := fun j =>
    ∫ x, canonicalERealDiffToReal (p x) (q x) ∂prefixMixedMeasure theta ha hb j.val
  have h0 : prefixMixedMeasure theta ha hb 0 =
      globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb) := by
    apply UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
    funext i
    simp [prefixPotentialTuple]
  have hn : prefixMixedMeasure theta ha hb n =
      globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha) := by
    apply UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
    funext i
    simp [prefixPotentialTuple, i.isLt]
  have hstep (k : Fin n) : f k.succ - f k.castSucc =
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hp (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hq (stepSelector k) k) := by
    change (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂prefixMixedMeasure theta ha hb (k.val + 1)) -
      (∫ x, canonicalERealDiffToReal (p x) (q x) ∂prefixMixedMeasure theta ha hb k.val) = _
    rw [prefixMixedMeasure_succ theta ha hb k, prefixMixedMeasure_current theta ha hb k]
    exact bounded_binaryMixedMeasure_integral_sub_symm omega theta ha hb hp hq
      hab hbb hpb hqb (stepSelector k) k
  calc
    _ = f (Fin.last n) - f 0 := by
      change _ = (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂prefixMixedMeasure theta ha hb n) -
        (∫ x, canonicalERealDiffToReal (p x) (q x) ∂prefixMixedMeasure theta ha hb 0)
      rw [hn, h0]
    _ = ∑ k : Fin n, (f k.succ - f k.castSucc) := (sum_fin_successive_sub f).symm
    _ = _ := Finset.sum_congr rfl fun k _ => hstep k

/-- Lu's actual deep-coincident singular diagonal IBP identity. The proof
uses genuine bounded IBP and the two proved cutoff limits; it assumes no
singular integration-by-parts or varying-measure convergence certificate. -/
theorem diagonal_integral_sub_eq_sum_of_deepCoincidence
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (htheta : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hp : ThetaPlurisubharmonic theta.val p) (hq : ThetaPlurisubharmonic theta.val q)
    (habtype : SameSingularityTypeOn a b univ) (hpqtype : SameSingularityTypeOn p q univ)
    {C : ℝ} (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    (hpq : EqOn p q {x | min (p x) (q x) < ((-C : ℝ) : EReal)}) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hp (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hq (stepSelector k) k)) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let _ := hM
    simp only [integral_of_isEmpty, sub_self, Finset.sum_const_zero]
  · let _ := hM
    have hT : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hleft := tendsto_globalDiagonalTruncation_integral_canonicalDiff_sub
      omega theta htheta ha hb hp hq hpqtype hab hT
    have hright := tendsto_finsetSum Finset.univ (fun k _ =>
      tendsto_binaryMixedCutoffMeasure_integral_sub omega theta htheta ha hb hp hq
        (stepSelector k) k habtype hab hpq hT)
    have hbounded (j : ℕ) :
        (∫ x, canonicalERealDiffToReal (canonicalTruncation (j : ℝ) p x)
          (canonicalTruncation (j : ℝ) q x)
          ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation (j : ℝ) a)
            (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha (j : ℝ))) -
        (∫ x, canonicalERealDiffToReal (canonicalTruncation (j : ℝ) p x)
          (canonicalTruncation (j : ℝ) q x)
          ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation (j : ℝ) b)
            (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta hb (j : ℝ))) =
        ∑ k : Fin n,
          ((∫ x, canonicalERealDiffToReal (canonicalTruncation (j : ℝ) a x)
            (canonicalTruncation (j : ℝ) b x)
            ∂binaryMixedCutoffMeasure theta htheta ha hb hp (stepSelector k) k (j : ℝ)) -
          (∫ x, canonicalERealDiffToReal (canonicalTruncation (j : ℝ) a x)
            (canonicalTruncation (j : ℝ) b x)
            ∂binaryMixedCutoffMeasure theta htheta ha hb hq (stepSelector k) k (j : ℝ))) := by
      have h := bounded_diagonal_integral_sub_eq_sum omega theta
        (thetaPlurisubharmonic_canonicalTruncation htheta ha (j : ℝ))
        (thetaPlurisubharmonic_canonicalTruncation htheta hb (j : ℝ))
        (thetaPlurisubharmonic_canonicalTruncation htheta hp (j : ℝ))
        (thetaPlurisubharmonic_canonicalTruncation htheta hq (j : ℝ))
        (isBoundedPotential_max_const ha (-(j : ℝ)))
        (isBoundedPotential_max_const hb (-(j : ℝ)))
        (isBoundedPotential_max_const hp (-(j : ℝ)))
        (isBoundedPotential_max_const hq (-(j : ℝ)))
      simp_rw [← binaryMixedCutoffMeasure_eq_truncated theta htheta ha hb hp,
        ← binaryMixedCutoffMeasure_eq_truncated theta htheta ha hb hq] at h
      exact h
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun j => (hbounded j).symm))

end

end SGPT.Foundations.Analysis.Pending.DeepCoincidenceIntegrationByParts
