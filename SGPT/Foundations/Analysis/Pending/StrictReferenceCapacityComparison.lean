import SGPT.Foundations.Analysis.Pending.CoalescingMixedCapacity
import SGPT.Foundations.Analysis.Pending.ThetaCapacitySublevel
import SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffCancellation
import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence

set_option autoImplicit false

/-!
# Direct capacity comparison for a reference with a scaling margin

The strict-reference case used in Lu, arXiv:2005.04264v1, Lemma 4.1
Step 1.2. A genuine scaled reference gives uniform relative-capacity tail
decay, and actual truncation locality bounds the remaining capacity by
zero-reference capacity. The actual four-potential average has the needed
scaling margin because its fifth zero slot retains positive weight.
This does not assert the general model-envelope capacity comparison.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.StrictReferenceCapacityComparison

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open ThetaCapacity ThetaCapacitySublevel CoalescingMixedCapacity
open GlobalMultilinearExpansion MixedSummandCapacityDomination
open NonPluripolarCutoffCancellation CapacityWeightedConvergence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A genuine scaling margin produces arbitrarily small relative-capacity
deep tails of the reference itself; its poles are treated separately. -/
theorem exists_thetaCapacity_deepSublevel_lt
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {V : M → EReal} (hV : IsThetaPshPotential theta.val V) (hV0 : V ≤ 0)
    {c : ℝ} (hc : 1 < c)
    (hcV : IsThetaPshPotential theta.val (fun x => (c : EReal) * V x))
    {eta : ℝ≥0∞} (heta : 0 < eta) :
    ∃ k : ℝ, 0 ≤ k ∧ thetaCapacity theta V {x | V x < ((-k : ℝ) : EReal)} < eta := by
  have hc0 : 0 < c := by linarith
  have hscale : (fun x => (c : EReal) * V x) ≤ V := by
    intro x
    change (c : EReal) * V x ≤ V x
    induction hval : V x using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hc0]
    | top => have h := hV0 x; simp [hval] at h
    | coe v =>
      rw [← EReal.coe_mul]
      apply EReal.coe_le_coe_iff.mpr
      have hv : v ≤ 0 := by simpa [hval] using hV0 x
      nlinarith
  obtain ⟨j, hj⟩ := ((tendsto_thetaCapacity_sublevel omega hV hcV hscale).eventually_lt_const heta).exists
  let k : ℝ := (j : ℝ) / (c - 1) + 1
  have hcm : 0 < c - 1 := by linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hkd : k * (c - 1) = (j : ℝ) + (c - 1) := by
    dsimp [k]
    rw [add_mul, div_mul_cancel₀ _ hcm.ne']
    ring
  have hpoles : thetaCapacity theta V {x | V x = ⊥} = 0 :=
    thetaCapacity_eq_zero_of_manifoldLocallyPluripolar V
      (quasiPsh_poles_manifoldLocallyPluripolar hV.quasiPshPotential)
  refine ⟨k, hk, lt_of_le_of_lt ?_ hj⟩
  calc thetaCapacity theta V {x | V x < ((-k : ℝ) : EReal)}
      ≤ thetaCapacity theta V
        ({x | (c : EReal) * V x < V x + ((-(j : ℝ) : ℝ) : EReal)} ∪ {x | V x = ⊥}) := by
        apply thetaCapacity_mono
        intro x hx
        by_cases hb : V x = ⊥
        · exact Or.inr hb
        · have ht := hV.1.quasiPlurisubharmonic.ne_top x
          obtain ⟨v, hv⟩ : ∃ v : ℝ, V x = (v : EReal) :=
            ⟨(V x).toReal, (EReal.coe_toReal ht hb).symm⟩
          left
          change (c : EReal) * V x < V x + ((-(j : ℝ) : ℝ) : EReal)
          rw [hv, ← EReal.coe_mul, ← EReal.coe_add]
          apply EReal.coe_lt_coe_iff.mpr
          have hxv : v < -k := by
            apply EReal.coe_lt_coe_iff.mp
            change V x < ((-k : ℝ) : EReal) at hx
            rwa [hv] at hx
          nlinarith
    _ ≤ thetaCapacity theta V
        {x | (c : EReal) * V x < V x + ((-(j : ℝ) : ℝ) : EReal)} +
        thetaCapacity theta V {x | V x = ⊥} := thetaCapacity_union_le _ _ _ _
    _ = _ := by rw [hpoles, add_zero]

/-- Actual truncation locality bounds relative capacity by its deep tail and
a finite multiple of zero-reference capacity. This holds on every set. -/
theorem thetaCapacity_le_deepSublevel_add_zero
    {theta : ClosedRealOneOneForm n M} (hsemi : theta.val.IsSemipositive)
    {V : M → EReal} (hV0 : V ≤ 0) {k : ℝ} (hk : 0 ≤ k) (E : Set M) :
    thetaCapacity theta V E ≤ thetaCapacity theta V {x | V x < ((-k : ℝ) : EReal)} +
      ENNReal.ofReal ((k + 2) ^ n) * thetaCapacity theta (fun _ => 0) E := by
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff theta).mpr hsemi
  apply thetaCapacity_le_of_forall
  intro u hu huV hVu
  let D : Set M := {x | V x < ((-k : ℝ) : EReal)}
  let W : Set M := E ∩ Dᶜ
  let t : ℝ := k + 2
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hconst : IsThetaPshPotential theta.val (fun _ => ((-t : ℝ) : EReal)) := by
    simpa only [zero_add] using hzero.add_const (-t)
  have hcut : IsThetaPshPotential theta.val (canonicalTruncation t u) :=
    IsThetaPshPotential.max hu hconst
  have hcut0 : canonicalTruncation t u ≤ (fun _ => 0) := by
    intro x
    exact max_le ((huV x).trans (hV0 x)) (EReal.coe_nonpos.mpr (by linarith))
  have hcutlower : ∀ x, (0 : EReal) ≤ canonicalTruncation t u x + (t : EReal) := by
    intro x
    calc (0 : EReal) = ((-t : ℝ) : EReal) + (t : EReal) := by
          rw [← EReal.coe_add]; simp
      _ ≤ canonicalTruncation t u x + (t : EReal) := add_le_add (le_max_right _ _) le_rfl
  have hsub : W ⊆ {x | ((-t : ℝ) : EReal) < u x} := by
    intro x hx
    have hVk : ((-k : ℝ) : EReal) ≤ V x := not_lt.mp hx.2
    have hbound := hVk.trans (hVu x)
    have hubot : u x ≠ ⊥ := by
      intro hb
      rw [hb, EReal.bot_add] at hbound
      exact EReal.coe_ne_bot _ (le_bot_iff.mp hbound)
    obtain ⟨v, hv⟩ : ∃ v : ℝ, u x = (v : EReal) :=
      ⟨(u x).toReal, (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hubot).symm⟩
    change ((-t : ℝ) : EReal) < u x
    rw [hv]
    apply EReal.coe_lt_coe_iff.mpr
    rw [hv, ← EReal.coe_one, ← EReal.coe_add] at hbound
    have hvk := EReal.coe_le_coe_iff.mp hbound
    dsimp [t]
    linarith
  have hloc : (diagonalPotentialMeasure theta (canonicalTruncation t u) hcut).restrict
      {x | ((-t : ℝ) : EReal) < u x} =
      (diagonalPotentialMeasure theta u hu).restrict {x | ((-t : ℝ) : EReal) < u x} :=
    globalDiagonalTruncation_restrict_strict_eq theta hsemi hu.1 t
  have hgood : diagonalPotentialMeasure theta u hu W ≤
      diagonalPotentialMeasure theta (canonicalTruncation t u) hcut E := by
    calc _ = ((diagonalPotentialMeasure theta u hu).restrict
          {x | ((-t : ℝ) : EReal) < u x}) W := (Measure.restrict_eq_self _ hsub).symm
      _ = ((diagonalPotentialMeasure theta (canonicalTruncation t u) hcut).restrict
          {x | ((-t : ℝ) : EReal) < u x}) W := by rw [hloc]
      _ = diagonalPotentialMeasure theta (canonicalTruncation t u) hcut W :=
        Measure.restrict_eq_self _ hsub
      _ ≤ _ := measure_mono inter_subset_left
  have hsplit : E ⊆ D ∪ W := by
    intro x hx
    by_cases hD : x ∈ D
    · exact Or.inl hD
    · exact Or.inr ⟨hx, hD⟩
  calc diagonalPotentialMeasure theta u hu E
      ≤ diagonalPotentialMeasure theta u hu (D ∪ W) := measure_mono hsplit
    _ ≤ diagonalPotentialMeasure theta u hu D + diagonalPotentialMeasure theta u hu W :=
      measure_union_le D W
    _ ≤ thetaCapacity theta V D + diagonalPotentialMeasure theta (canonicalTruncation t u) hcut E :=
      add_le_add (diagonalPotentialMeasure_le_thetaCapacity hu huV hVu D) hgood
    _ ≤ _ := add_le_add le_rfl
      (diagonalPotentialMeasure_le_thetaCapacity_of_bounds hzero hcut ht hcut0 hcutlower E)

/-- Relative capacity is uniformly small when zero-reference capacity is
small, produced by the actual scaling margin and truncation estimates. -/
theorem exists_pos_capacity_lt_imp_relative_le
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {V : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hV0 : V ≤ 0)
    {c : ℝ} (hc : 1 < c)
    (hcV : IsThetaPshPotential theta.val (fun x => (c : EReal) * V x))
    {r : ℝ} (hr : 0 < r) :
    ∃ eta : ℝ≥0∞, 0 < eta ∧ ∀ E : Set M,
      thetaCapacity theta (fun _ => 0) E < eta → thetaCapacity theta V E ≤ ENNReal.ofReal r := by
  obtain ⟨k, hk, htail⟩ := exists_thetaCapacity_deepSublevel_lt omega hV hV0 hc hcV
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < r / 2))
  let L : ℝ := (k + 2) ^ n
  have hL : 0 < L := pow_pos (by linarith) _
  have hsmall : 0 < r / (2 * L) := div_pos hr (mul_pos (by norm_num) hL)
  refine ⟨ENNReal.ofReal (r / (2 * L)), ENNReal.ofReal_pos.mpr hsmall, ?_⟩
  intro E hE
  have hcan : L * (r / (2 * L)) = r / 2 := by
    field_simp
  calc thetaCapacity theta V E
      ≤ thetaCapacity theta V {x | V x < ((-k : ℝ) : EReal)} +
        ENNReal.ofReal L * thetaCapacity theta (fun _ => 0) E :=
      thetaCapacity_le_deepSublevel_add_zero hsemi hV0 hk E
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal L * ENNReal.ofReal (r / (2 * L)) := by
      exact add_le_add htail.le (mul_le_mul_of_nonneg_left hE.le zero_le)
    _ = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul hL.le, hcan,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ r / 2) (by linarith : 0 ≤ r / 2)]
      congr 1
      ring

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- The actual four-potential reference is nonpositive whenever its four
original potentials are nonpositive. -/
theorem commonReference_le_zero {a b p q : M → EReal}
    (ha0 : a ≤ 0) (hb0 : b ≤ 0) (hp0 : p ≤ 0) (hq0 : q ≤ 0) :
    commonReference a b p q ≤ 0 := by
  intro x
  change commonReference a b p q x ≤ (0 : EReal)
  rw [commonReference_apply]
  have hsum : a x + b x + p x + q x ≤ 0 := by
    simpa only [Pi.zero_apply, zero_add, add_zero] using
      add_le_add (add_le_add (add_le_add (ha0 x) (hb0 x)) (hp0 x)) (hq0 x)
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hsum
    (by norm_num : (0 : EReal) ≤ ((1 / 5 : ℝ) : EReal))

/-- The spare zero slot keeps the actual scaled reference genuine. -/
def boostedWeight : Fin 5 → ℝ := ![6 / 25, 6 / 25, 6 / 25, 6 / 25, 1 / 25]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual common reference has a scaling margin of `6/5`: all five
weights, including that of zero, remain strictly positive. -/
theorem isThetaPshPotential_scaled_commonReference {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q) :
    IsThetaPshPotential theta.val (fun x => ((6 / 5 : ℝ) : EReal) * commonReference a b p q x) := by
  have hw : ∀ i, 0 < boostedWeight i := by
    intro i
    fin_cases i <;> norm_num [boostedWeight]
  have hform : sumForm Finset.univ boostedWeight (fun _ => theta) = theta := by
    rw [sumForm, ← Finset.sum_smul]
    norm_num [boostedWeight, Fin.sum_univ_succ]
  have hpot : sumPot Finset.univ boostedWeight (fivePotentialFamily a b p q) =
      fun x => ((6 / 5 : ℝ) : EReal) * commonReference a b p q x := by
    funext x
    rw [commonReference_apply, ← mul_assoc, ← EReal.coe_mul]
    norm_num
    have hdist := EReal.left_distrib_of_nonneg_of_ne_top
      (x := ((6 / 25 : ℝ) : EReal)) (by norm_num) (by simp)
    simp_rw [hdist]
    simp [sumPot, boostedWeight, fivePotentialFamily, Fin.sum_univ_succ]
    abel
  have h := isThetaPshPotential_sumPot Finset.univ_nonempty hw
    (isThetaPshPotential_fivePotentialFamily hsemi ha hb hp hq)
  rwa [hform, hpot] at h

/-- The actual four-potential common reference has the proved comparison
with zero-reference capacity, without an assumed capacity modulus. -/
theorem exists_pos_capacity_lt_imp_commonReference_le
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (ha0 : a ≤ 0) (hb0 : b ≤ 0) (hp0 : p ≤ 0) (hq0 : q ≤ 0) {r : ℝ} (hr : 0 < r) :
    ∃ eta : ℝ≥0∞, 0 < eta ∧ ∀ E : Set M,
      thetaCapacity theta (fun _ => 0) E < eta →
        thetaCapacity theta (commonReference a b p q) E ≤ ENNReal.ofReal r :=
  exists_pos_capacity_lt_imp_relative_le omega hsemi
    (isThetaPshPotential_commonReference hsemi ha hb hp hq)
    (commonReference_le_zero ha0 hb0 hp0 hq0) (by norm_num : (1 : ℝ) < 6 / 5)
    (isThetaPshPotential_scaled_commonReference hsemi ha hb hp hq) hr

/-- A fixed finite nonnegative multiple of strict-reference capacity produces
uniform small-set control over zero-reference capacity for actual measures. -/
theorem uniformCapacityControl_of_strictReference
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {V : M → EReal}
    (hV : IsThetaPshPotential theta.val V) (hV0 : V ≤ 0)
    {c : ℝ} (hc : 1 < c)
    (hcV : IsThetaPshPotential theta.val (fun x => (c : EReal) * V x))
    {mu : ℕ → Measure M} {nu : Measure M} {L : ℝ} (hL : 0 ≤ L)
    (hmu : ∀ j E, mu j E ≤ ENNReal.ofReal L * thetaCapacity theta V E)
    (hnu : ∀ E, nu E ≤ ENNReal.ofReal L * thetaCapacity theta V E) :
    UniformCapacityControl (thetaCapacity theta (fun _ => 0)) mu nu := by
  rcases hL.eq_or_lt' with rfl | hL
  · intro r hr
    refine ⟨1, by simp, fun E _ _ => ⟨fun j => ?_, ?_⟩⟩
    · have h : mu j E ≤ 0 := by simpa only [ENNReal.ofReal_zero, zero_mul] using hmu j E
      exact h.trans zero_le
    · have h : nu E ≤ 0 := by simpa only [ENNReal.ofReal_zero, zero_mul] using hnu E
      exact h.trans zero_le
  intro r hr
  obtain ⟨eta, heta, hsmall⟩ := exists_pos_capacity_lt_imp_relative_le omega hsemi hV hV0 hc hcV
    (div_pos hr hL)
  refine ⟨eta, heta, fun E _ hE => ?_⟩
  have hcan : L * (r / L) = r := by field_simp
  have hbound : ENNReal.ofReal L * thetaCapacity theta V E ≤ ENNReal.ofReal r := by
    calc _ ≤ ENNReal.ofReal L * ENNReal.ofReal (r / L) := by
            exact mul_le_mul_of_nonneg_left (hsmall E hE) zero_le
      _ = _ := by rw [← ENNReal.ofReal_mul hL.le, hcan]
  exact ⟨fun j => (hmu j E).trans hbound, (hnu E).trans hbound⟩

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- At parameter zero the actual ordered max family is the original family. -/
theorem coalescingPotentialFamily_zero_of_order {a b p q : M → EReal}
    (hab : a ≤ b) (hpq : p ≤ q) :
    coalescingPotentialFamily 0 a b p q = fivePotentialFamily a b p q := by
  have hb : NonPluripolarPoleCoalescing.poleCoalescingApprox 0 a b = b := by
    funext x
    simp only [NonPluripolarPoleCoalescing.poleCoalescingApprox, add_zero,
      EReal.coe_one, one_mul, max_eq_right (hab x)]
  have hq : NonPluripolarPoleCoalescing.poleCoalescingApprox 0 p q = q := by
    funext x
    simp only [NonPluripolarPoleCoalescing.poleCoalescingApprox, add_zero,
      EReal.coe_one, one_mul, max_eq_right (hpq x)]
  rw [coalescingPotentialFamily, hb, hq]

/-- The actual coalescing mixed measures and their original mixed endpoint
have uniform small-set control for zero-reference capacity. -/
theorem uniformCapacityControl_coalescingMixed
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    {B : ℝ} (hB : 0 ≤ B) (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal))
    {eps : ℕ → ℝ} (heps : ∀ j, 0 ≤ eps j)
    (hbe : ∀ j, IsThetaPshPotential theta.val (NonPluripolarPoleCoalescing.poleCoalescingApprox (eps j) a b))
    (hqe : ∀ j, IsThetaPshPotential theta.val (NonPluripolarPoleCoalescing.poleCoalescingApprox (eps j) p q))
    (s : Fin n → Fin 5) :
    UniformCapacityControl (thetaCapacity theta (fun _ => 0))
      (fun k => globalMixedMeasure (fun _ => theta)
        (fun j => coalescingPotentialFamily (eps k) a b p q (s j))
        (fun j => (isThetaPshPotential_fivePotentialFamily hsemi ha (hbe k) hp (hqe k) (s j)).1))
      (globalMixedMeasure (fun _ => theta) (fun j => fivePotentialFamily a b p q (s j))
        (fun j => (isThetaPshPotential_fivePotentialFamily hsemi ha hb hp hq (s j)).1)) := by
  have hV := isThetaPshPotential_commonReference hsemi ha hb hp hq
  have hV0 := commonReference_le_zero (hab.trans hb0) hb0 (hpq.trans hq0) hq0
  apply uniformCapacityControl_of_strictReference omega hsemi hV hV0
    (by norm_num : (1 : ℝ) < 6 / 5)
    (isThetaPshPotential_scaled_commonReference hsemi ha hb hp hq)
    (L := (5 * (B + 1)) ^ n) (by positivity)
  · intro k E
    exact mixedMeasure_apply_le_commonCapacity hsemi ha hb hp hq hB (heps k)
      hab hpq hb0 hq0 hba hqp (hbe k) (hqe k) s E
  · intro E
    have h := coalescingPotentialFamily_zero_of_order hab hpq
    have hbzero : IsThetaPshPotential theta.val (NonPluripolarPoleCoalescing.poleCoalescingApprox 0 a b) := by
      have heq := congrFun h (1 : Fin 5)
      change NonPluripolarPoleCoalescing.poleCoalescingApprox 0 a b = b at heq
      rw [heq]
      exact hb
    have hqzero : IsThetaPshPotential theta.val (NonPluripolarPoleCoalescing.poleCoalescingApprox 0 p q) := by
      have heq := congrFun h (3 : Fin 5)
      change NonPluripolarPoleCoalescing.poleCoalescingApprox 0 p q = q at heq
      rw [heq]
      exact hq
    simpa only [h] using mixedMeasure_apply_le_commonCapacity hsemi ha hb hp hq hB
      (le_refl (0 : ℝ)) hab hpq hb0 hq0 hba hqp hbzero hqzero s E

/-- The complete actual strict-margin sequence satisfies uniform control by
zero-reference capacity; no measure-domination or convergence premise is used. -/
theorem uniformCapacityControl_coalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hp : IsThetaPshPotential (lam • omega.form).val p)
    (hq : IsThetaPshPotential (lam • omega.form).val q)
    {B : ℝ} (hB : 0 ≤ B) (hab : a ≤ b) (hpq : p ≤ q) (hb0 : b ≤ 0) (hq0 : q ≤ 0)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (hqp : ∀ x, q x ≤ p x + (B : EReal))
    (s : Fin n → Fin 5) :
    UniformCapacityControl (thetaCapacity omega.form (fun _ => 0))
      (fun k => globalMixedMeasure (fun _ => omega.form)
        (fun j => coalescingPotentialFamily (NonPluripolarPoleCoalescing.strictKahlerParameter lam k) a b p q (s j))
        (fun j => (isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq k (s j)).1))
      (globalMixedMeasure (fun _ => omega.form) (fun j => fivePotentialFamily a b p q (s j))
        (fun j => (isThetaPshPotential_fivePotentialFamily omega.isSemipositive
          (by simpa only [one_smul] using NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono omega hlam1.le ha)
          (by simpa only [one_smul] using NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono omega hlam1.le hb)
          (by simpa only [one_smul] using NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono omega hlam1.le hp)
          (by simpa only [one_smul] using NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono omega hlam1.le hq) (s j)).1)) := by
  have lift {u : M → EReal} (hu : IsThetaPshPotential (lam • omega.form).val u) :
      IsThetaPshPotential omega.form.val u := by
    simpa only [one_smul] using NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono omega hlam1.le hu
  obtain ⟨hpos, -, -, -⟩ := NonPluripolarPoleCoalescing.strictKahlerParameter_spec hlam hlam1
  exact uniformCapacityControl_coalescingMixed omega omega.isSemipositive
    (lift ha) (lift hb) (lift hp) (lift hq) hB hab hpq hb0 hq0 hba hqp
    (fun k => (hpos k).le)
    (fun k => isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq k 1)
    (fun k => isThetaPshPotential_coalescingSequenceFamily omega hlam hlam1 ha hb hp hq k 3) s

end

end SGPT.Foundations.Analysis.Pending.StrictReferenceCapacityComparison
