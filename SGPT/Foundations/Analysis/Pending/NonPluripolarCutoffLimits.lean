import SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffCancellation
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability

/-!
# Signed diagonal cutoff limits under actual non-pluripolar measures

The left-hand cutoff limit in Lu, Lemma 4.1 Step 1.1. Actual deep
mass cancellation replaces varying measures by fixed restrictions;
the canonical truncated differences are uniformly dominated and
converge at finite values and common poles. The active diagonal pole
sets are null in positive dimension; dimension zero is handled by
the equality of the empty-tuples' actual measures.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffLimits

open FirstPass FirstPass.PositiveClasses RelativeEnergyIntegrability
open NonPluripolarCutoffCancellation GlobalNonPluripolar BoundedGlobalProduct

noncomputable section

private theorem max_coe_coe (r c : ℝ) : max (r : EReal) (c : EReal) = (max r c : ℝ) := by
  by_cases h : r ≤ c
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
  · rw [max_eq_left (le_of_not_ge h),
      max_eq_left (EReal.coe_le_coe_iff.mpr (le_of_not_ge h))]

/-- A common real cutoff contracts the canonical signed difference,
including the common pole where both truncated values coincide. -/
theorem abs_canonicalDiff_canonicalTruncation_le {X : Type*} {p q : X → EReal}
    (hp : ∀ x, p x ≠ ⊤) (hq : ∀ x, q x ≠ ⊤)
    (hpole : ∀ x, p x = ⊥ ↔ q x = ⊥) (t : ℝ) (x : X) :
    |canonicalERealDiffToReal (canonicalTruncation t p x) (canonicalTruncation t q x)| ≤
      |canonicalERealDiffToReal (p x) (q x)| := by
  by_cases hpb : p x = ⊥
  · have hqb := (hpole x).mp hpb
    simp [canonicalTruncation, hpb, hqb]
  · have hqb : q x ≠ ⊥ := fun h => hpb ((hpole x).mpr h)
    unfold canonicalTruncation
    rw [← EReal.coe_toReal (hp x) hpb, ← EReal.coe_toReal (hq x) hqb,
      max_coe_coe, max_coe_coe, canonicalERealDiffToReal_coe_coe,
      canonicalERealDiffToReal_coe_coe]
    exact abs_max_sub_max_le_abs _ _ _

/-- Cutoff signed differences converge at every point for any real levels
tending to positive infinity, including the common poles. -/
theorem tendsto_canonicalDiff_canonicalTruncation {X : Type*} {p q : X → EReal}
    (hp : ∀ x, p x ≠ ⊤) (hq : ∀ x, q x ≠ ⊤)
    (hpole : ∀ x, p x = ⊥ ↔ q x = ⊥) {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) (x : X) :
    Tendsto (fun k => canonicalERealDiffToReal
      (canonicalTruncation (T k) p x) (canonicalTruncation (T k) q x)) atTop
      (𝓝 (canonicalERealDiffToReal (p x) (q x))) := by
  by_cases hpb : p x = ⊥
  · have hqb := (hpole x).mp hpb
    simp [canonicalTruncation, hpb, hqb]
  · have hqb : q x ≠ ⊥ := fun h => hpb ((hpole x).mpr h)
    have hevent : ∀ᶠ k in atTop,
        canonicalERealDiffToReal (canonicalTruncation (T k) p x)
          (canonicalTruncation (T k) q x) = canonicalERealDiffToReal (p x) (q x) := by
      filter_upwards [(tendsto_atTop.1 hT) (max (-(p x).toReal) (-(q x).toReal))]
        with k hk
      have hpk : ((-T k : ℝ) : EReal) ≤ p x := by
        rw [← EReal.coe_toReal (hp x) hpb]
        exact EReal.coe_le_coe_iff.mpr (by linarith [le_max_left (-(p x).toReal) (-(q x).toReal)])
      have hqk : ((-T k : ℝ) : EReal) ≤ q x := by
        rw [← EReal.coe_toReal (hq x) hqb]
        exact EReal.coe_le_coe_iff.mpr (by linarith [le_max_right (-(p x).toReal) (-(q x).toReal)])
      simp only [canonicalTruncation, max_eq_left hpk, max_eq_left hqk]
    exact tendsto_const_nhds.congr' (hevent.mono fun k hk => hk.symm)

/-- The signed cutoff weights are genuine integrable functions under every
finite measure, with one bound independent of the cutoff level. -/
theorem integrable_canonicalDiff_canonicalTruncation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {p q : X → EReal} (hpm : Measurable p) (hqm : Measurable q)
    (hp : ∀ x, p x ≠ ⊤) (hq : ∀ x, q x ≠ ⊤)
    (hpq : SameSingularityTypeOn p q univ) (t : ℝ) :
    Integrable (fun x => canonicalERealDiffToReal
      (canonicalTruncation t p x) (canonicalTruncation t q x)) μ := by
  obtain ⟨B, _, hB⟩ := exists_abs_canonicalDiff_le_of_sameSingularityType hpq hp hq
  have hm : Measurable (fun x => canonicalERealDiffToReal
      (canonicalTruncation t p x) (canonicalTruncation t q x)) :=
    measurable_canonicalERealDiffToReal.comp
    ((hpm.max measurable_const).prodMk (hqm.max measurable_const))
  exact (integrable_const B).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_canonicalDiff_canonicalTruncation_le hp hq
        (fun x => sameSingularityTypeOn_eq_bot_iff hpq (mem_univ x)) t x).trans (hB x))

/-- Dominated convergence under a fixed finite measure after removal of
its null pole locus. This lemma makes no assertion about varying measures. -/
theorem tendsto_setIntegral_canonicalDiff_canonicalTruncation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {p q a : X → EReal} (hpm : Measurable p) (hqm : Measurable q)
    (ham : Measurable a) (hp : ∀ x, p x ≠ ⊤) (hq : ∀ x, q x ≠ ⊤)
    (ha : ∀ x, a x ≠ ⊤) (hpq : SameSingularityTypeOn p q univ)
    (hnull : μ {x | a x = ⊥} = 0) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun k => ∫ x in {x | ((-T k : ℝ) : EReal) < a x},
      canonicalERealDiffToReal (canonicalTruncation (T k) p x)
        (canonicalTruncation (T k) q x) ∂μ) atTop
      (𝓝 (∫ x, canonicalERealDiffToReal (p x) (q x) ∂μ)) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_canonicalDiff_le_of_sameSingularityType hpq hp hq
  have hSm (k : ℕ) : MeasurableSet {x | ((-T k : ℝ) : EReal) < a x} :=
    measurableSet_lt measurable_const ham
  simp_rw [← integral_indicator (hSm _)]
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro k
    exact (measurable_canonicalERealDiffToReal.comp
      ((hpm.max measurable_const).prodMk (hqm.max measurable_const))).aestronglyMeasurable.indicator
        (hSm k)
  · exact integrable_const B
  · intro k
    exact Eventually.of_forall fun x => by
      by_cases hx : ((-T k : ℝ) : EReal) < a x
      · rw [indicator_of_mem (show x ∈ {x | ((-T k : ℝ) : EReal) < a x} from hx),
          Real.norm_eq_abs]
        exact (abs_canonicalDiff_canonicalTruncation_le hp hq
          (fun x => sameSingularityTypeOn_eq_bot_iff hpq (mem_univ x)) (T k) x).trans (hB x)
      · rw [indicator_of_notMem (show x ∉ {x | ((-T k : ℝ) : EReal) < a x} from hx),
          norm_zero]
        exact hB0
  · have hae : ∀ᵐ x ∂μ, a x ≠ ⊥ := by
      apply ae_iff.mpr
      simpa only [not_not] using hnull
    filter_upwards [hae] with x hax
    have hevent : ∀ᶠ k in atTop, ((-T k : ℝ) : EReal) < a x := by
      filter_upwards [(tendsto_atTop.1 hT) (-(a x).toReal + 1)] with k hk
      rw [← EReal.coe_toReal (ha x) hax]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    apply (tendsto_canonicalDiff_canonicalTruncation hp hq
      (fun x => sameSingularityTypeOn_eq_bot_iff hpq (mem_univ x)) hT x).congr'
    exact hevent.mono fun k hk =>
      (indicator_of_mem (show x ∈ {x | ((-T k : ℝ) : EReal) < a x} from hk)
        (fun y => canonicalERealDiffToReal (canonicalTruncation (T k) p y)
          (canonicalTruncation (T k) q y))).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual signed cutoff-integral convergence for a deep-coincident diagonal
pair. The varying measures are eliminated by proved cutoff cancellation;
their convergence is never assumed. No bounded model or positive dimension. -/
theorem tendsto_globalDiagonalTruncation_integral_canonicalDiff_sub
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (htheta : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hp : ThetaPlurisubharmonic theta.val p) (hq : ThetaPlurisubharmonic theta.val q)
    (hpq : SameSingularityTypeOn p q univ) {C : ℝ}
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun k =>
      (∫ x, canonicalERealDiffToReal (canonicalTruncation (T k) p x)
        (canonicalTruncation (T k) q x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation (T k) a)
          (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha (T k))) -
      (∫ x, canonicalERealDiffToReal (canonicalTruncation (T k) p x)
        (canonicalTruncation (T k) q x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation (T k) b)
          (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta hb (T k)))) atTop
      (𝓝 ((∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)) -
      (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb)))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hμ {r s : M → EReal} (hr : ThetaPlurisubharmonic theta.val r)
        (hs : ThetaPlurisubharmonic theta.val s) :
        globalMixedMeasure (fun _ : Fin 0 => theta) (fun _ => r) (fun _ => hr) =
          globalMixedMeasure (fun _ : Fin 0 => theta) (fun _ => s) (fun _ => hs) := by
      apply UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
      funext i
      exact Fin.elim0 i
    have hμt (k : ℕ) := hμ (thetaPlurisubharmonic_canonicalTruncation htheta ha (T k))
      (thetaPlurisubharmonic_canonicalTruncation htheta hb (T k))
    simp_rw [hμt, hμ ha hb, sub_self]
    exact tendsto_const_nhds
  · let := globalMixedMeasure_isFiniteMeasure omega (fun _ : Fin n => ha)
    let := globalMixedMeasure_isFiniteMeasure omega (fun _ : Fin n => hb)
    have hpm := hp.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have hqm := hq.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have ham := ha.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have hpoles : {x | a x = ⊥} = {x | b x = ⊥} := by
      ext x
      constructor
      · intro hx
        have heq := hab (show min (a x) (b x) < ((-C : ℝ) : EReal) by
          simpa only [show a x = ⊥ from hx, min_bot_left] using EReal.bot_lt_coe (-C))
        change b x = ⊥
        rw [← heq]
        exact hx
      · intro hx
        have heq := hab (show min (a x) (b x) < ((-C : ℝ) : EReal) by
          simpa only [show b x = ⊥ from hx, min_bot_right] using EReal.bot_lt_coe (-C))
        change a x = ⊥
        rw [heq]
        exact hx
    have hnulla : globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)
        {x | a x = ⊥} = 0 :=
      GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => ha) ⟨0, hn⟩
    have hnullb : globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb)
        {x | a x = ⊥} = 0 := by
      rw [hpoles]
      exact GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => hb) ⟨0, hn⟩
    have hleft := tendsto_setIntegral_canonicalDiff_canonicalTruncation hpm hqm ham
      hp.quasiPlurisubharmonic.ne_top hq.quasiPlurisubharmonic.ne_top
      ha.quasiPlurisubharmonic.ne_top hpq hnulla hT
    have hright := tendsto_setIntegral_canonicalDiff_canonicalTruncation hpm hqm ham
      hp.quasiPlurisubharmonic.ne_top hq.quasiPlurisubharmonic.ne_top
      ha.quasiPlurisubharmonic.ne_top hpq hnullb hT
    apply (hleft.sub hright).congr'
    filter_upwards [(tendsto_atTop.1 hT) (C + 1)] with k hk
    have hCk : C < T k := by linarith
    let := globalMixedMeasure_isFiniteMeasure omega
      (fun _ : Fin n => thetaPlurisubharmonic_canonicalTruncation htheta ha (T k))
    let := globalMixedMeasure_isFiniteMeasure omega
      (fun _ : Fin n => thetaPlurisubharmonic_canonicalTruncation htheta hb (T k))
    exact (globalDiagonalTruncation_integral_sub_eq theta htheta ha hb hCk hab
      (integrable_canonicalDiff_canonicalTruncation hpm hqm
        hp.quasiPlurisubharmonic.ne_top hq.quasiPlurisubharmonic.ne_top hpq (T k))
      (integrable_canonicalDiff_canonicalTruncation hpm hqm
        hp.quasiPlurisubharmonic.ne_top hq.quasiPlurisubharmonic.ne_top hpq (T k))).symm

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffLimits
