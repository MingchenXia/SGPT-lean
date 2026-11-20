import SGPT.Foundations.Analysis.Pending.StrictCurvatureIntegrationByParts
import SGPT.Foundations.Analysis.Pending.CanonicalWeightConstantShift

set_option autoImplicit false

/-!
# Strict-curvature diagonal IBP for arbitrary genuine same-type pairs

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2, normalization removal.
Produce actual finite ordered nonpositive translates, then cancel actual
constant corrections using same-type mixed masses and pole-nullity.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SameTypeStrictIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open RelativeEnergyIntegrability NonPluripolarMixedCutoffs
open NonPluripolarPoleCoalescing CoalescingMixedCapacity IncreasingMixedWeakConvergence
open DeepCoincidenceIntegrationByParts StrictCurvatureIntegrationByParts
open CanonicalWeightConstantShift GlobalMeasureInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Produce finite translations of an actual same-type pair with the exact
ordered, nonpositive and nonnegative bounded-gap hypotheses required by the
strict coalescing IBP, including the empty manifold. -/
theorem exists_ordered_nonpositive_sub_consts
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ) :
    ∃ c d B : ℝ, 0 ≤ B ∧
      (fun x => u x - (c : EReal)) ≤ (fun x => v x - (d : EReal)) ∧
      (fun x => v x - (d : EReal)) ≤ 0 ∧
      ∀ x, v x - (d : EReal) ≤ (u x - (c : EReal)) + (B : EReal) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let _ := hM
    refine ⟨0, 0, 0, le_refl 0, ?_, ?_, ?_⟩ <;> intro x <;> exact isEmptyElim x
  · let _ := hM
    obtain ⟨K, hK⟩ := htype.1
    obtain ⟨L, hL⟩ := htype.2
    obtain ⟨T, hT⟩ := hv.exists_global_upper_bound
    have hpoint : ∀ x, u x - ((K + T : ℝ) : EReal) ≤ v x - (T : EReal) ∧
        v x - (T : EReal) ≤ u x - ((K + T : ℝ) : EReal) + ((max 0 (K + L) : ℝ) : EReal) := by
      intro x
      by_cases hux : u x = ⊥
      · have hvx := (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp hux
        simp [hux, hvx]
      · have hvx : v x ≠ ⊥ := fun h => hux ((sameSingularityTypeOn_eq_bot_iff htype
          (mem_univ x)).mpr h)
        have huc := EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hux
        have hvc := EReal.coe_toReal (hv.1.quasiPlurisubharmonic.ne_top x) hvx
        have hKx := hK x (mem_univ x)
        have hLx := hL x (mem_univ x)
        rw [← huc, ← hvc, ← EReal.coe_add, EReal.coe_le_coe_iff] at hKx hLx
        rw [← huc, ← hvc]
        simp only [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
        constructor <;> linarith [le_max_right (0 : ℝ) (K + L)]
    exact ⟨K + T, T, max 0 (K + L), le_max_left _ _, fun x => (hpoint x).1,
      sub_const_nonpositive_of_le hT, fun x => (hpoint x).2⟩

omit [CompactSpace M] in
/-- A binary updated tuple is genuine when each actual input potential is. -/
theorem isThetaPshPotential_binaryUpdatedTuple
    (theta : ClosedRealOneOneForm n M) {a b r : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hr : IsThetaPshPotential theta.val r) (sigma : Fin n → Bool) (i0 : Fin n) :
    ∀ i, IsThetaPshPotential theta.val (Function.update (binaryPotentialTuple sigma a b) i0 r i) := by
  intro i
  by_cases hi : i = i0
  · subst hi
    simpa only [Function.update_self] using hr
  · rw [Function.update_of_ne hi]
    unfold binaryPotentialTuple
    split
    · exact ha
    · exact hb

variable [MeasurableSpace M] [BorelSpace M]

/-- Actual same-type distinguished binary measures cancel the canonical
weight's independent finite shift correction. -/
theorem integral_sub_canonicalDiff_sub_consts_binaryMixedMeasure
    (omega : KahlerBackground n M) {alpha beta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential alpha u)
    (hv : IsThetaPshPotential beta v) (huv : SameSingularityTypeOn u v univ)
    (theta : ClosedRealOneOneForm n M) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (hpq : SameSingularityTypeOn p q univ) (sigma : Fin n → Bool) (i0 : Fin n) (c d : ℝ) :
    (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal))
      ∂binaryMixedMeasure theta ha.1 hb.1 hp.1 sigma i0) -
    (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (v x - (d : EReal))
      ∂binaryMixedMeasure theta ha.1 hb.1 hq.1 sigma i0) =
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂binaryMixedMeasure theta ha.1 hb.1 hp.1 sigma i0) -
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂binaryMixedMeasure theta ha.1 hb.1 hq.1 sigma i0) := by
  classical
  have htypes : ∀ i, SameSingularityTypeOn
      (Function.update (binaryPotentialTuple sigma a b) i0 p i)
      (Function.update (binaryPotentialTuple sigma a b) i0 q i) univ := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simpa only [Function.update_self] using hpq
    · simp only [Function.update_of_ne hi]
      exact SameSingularityTypeOn.refl _ univ
  exact integral_sub_canonicalDiff_sub_consts_of_sameTypeTuples omega hu hv huv
    (isThetaPshPotential_binaryUpdatedTuple theta ha hb hp sigma i0)
    (isThetaPshPotential_binaryUpdatedTuple theta ha hb hq sigma i0) htypes c d

/-- Arbitrary genuine same-type pairs satisfy strict-curvature diagonal IBP.
Finite normalized translates and actual mass-cancelled shift identities remove
all order, nonpositivity, bounded-gap and coincidence premises. -/
theorem diagonal_integral_sub_eq_sum_of_sameType_strictCurvature
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    (habtype : SameSingularityTypeOn a b univ) (hpqtype : SameSingularityTypeOn p q univ) :
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
  obtain ⟨ca, cb, B, hB, hab, hb0, hba⟩ := exists_ordered_nonpositive_sub_consts ha hb habtype
  obtain ⟨cp, cq, D, hD, hpq, hq0, hqp⟩ := exists_ordered_nonpositive_sub_consts hp hq hpqtype
  have hba' : ∀ x, b x - (cb : EReal) ≤ a x - (ca : EReal) + ((max B D : ℝ) : EReal) :=
    fun x => (hba x).trans (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr (le_max_left B D)))
  have hqp' : ∀ x, q x - (cq : EReal) ≤ p x - (cp : EReal) + ((max B D : ℝ) : EReal) :=
    fun x => (hqp x).trans (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr (le_max_right B D)))
  have hnorm := diagonal_integral_sub_eq_sum_of_strictCurvature omega hlam hlam1
    (ha.sub_const ca) (hb.sub_const cb) (hp.sub_const cp) (hq.sub_const cq)
    hab hpq hb0 hq0 (hB.trans (le_max_left B D)) hba' hqp'
  have hf := isThetaPshPotential_originalFamily_kahler omega hlam1.le ha hb hp hq
  change
    (∫ x, canonicalERealDiffToReal (p x - (cp : EReal)) (q x - (cq : EReal))
      ∂globalMixedMeasure (fun _ => omega.form) (fun _ x => a x - (ca : EReal))
        (fun _ => GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 0).1 ca)) -
    (∫ x, canonicalERealDiffToReal (p x - (cp : EReal)) (q x - (cq : EReal))
      ∂globalMixedMeasure (fun _ => omega.form) (fun _ x => b x - (cb : EReal))
        (fun _ => GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 1).1 cb)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x - (ca : EReal)) (b x - (cb : EReal))
        ∂binaryMixedMeasure omega.form
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 0).1 ca)
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 1).1 cb)
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 2).1 cp)
          (stepSelector k) k) -
      (∫ x, canonicalERealDiffToReal (a x - (ca : EReal)) (b x - (cb : EReal))
        ∂binaryMixedMeasure omega.form
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 0).1 ca)
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 1).1 cb)
          (GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const (hf 3).1 cq)
          (stepSelector k) k)) at hnorm
  have hmeasureA := globalMixedMeasure_sub_const (θ := fun _ => omega.form) (u := fun _ => a)
    (fun _ => (hf 0).1) (fun _ => ca)
  have hmeasureB := globalMixedMeasure_sub_const (θ := fun _ => omega.form) (u := fun _ => b)
    (fun _ => (hf 1).1) (fun _ => cb)
  have hmeasureP (k : Fin n) := binaryMixedMeasure_sub_consts omega.form
    (hf 0).1 (hf 1).1 (hf 2).1 (stepSelector k) k ca cb cp
  have hmeasureQ (k : Fin n) := binaryMixedMeasure_sub_consts omega.form
    (hf 0).1 (hf 1).1 (hf 3).1 (stepSelector k) k ca cb cq
  rw [hmeasureA, hmeasureB] at hnorm
  simp_rw [hmeasureP, hmeasureQ] at hnorm
  have hleft := integral_sub_canonicalDiff_sub_consts_of_sameTypeTuples
    (u := p) (v := q) (s := fun _ => a) (t := fun _ => b) omega (hf 2) (hf 3)
    hpqtype (fun _ => hf 0) (fun _ => hf 1) (fun _ => habtype) cp cq
  have hright (k : Fin n) := integral_sub_canonicalDiff_sub_consts_binaryMixedMeasure
    (u := a) (v := b) (a := a) (b := b) (p := p) (q := q) omega (hf 0) (hf 1) habtype omega.form (hf 0) (hf 1) (hf 2) (hf 3) hpqtype
    (stepSelector k) k ca cb
  rw [hleft] at hnorm
  exact hnorm.trans (Finset.sum_congr rfl fun k _ => hright k)

end

end SGPT.Foundations.Analysis.Pending.SameTypeStrictIntegrationByParts
