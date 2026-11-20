import SGPT.Foundations.Analysis.Pending.GlobalOpenLocality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual cutoff-mass cancellation for pairs agreeing near their poles

Lu, Lemma 4.1 Step 1.1: ordinary-open coincidence gives equality of
actual truncated measures on the closed deep sublevel, including its
boundary. Global max locality then transfers the remaining signed
integrals to fixed original measures on the strict superlevel.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffCancellation

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar
open GlobalOpenLocality GlobalMaxLocality

noncomputable section

/-- Truncation at the real lower level `-t`, with the original poles allowed. -/
def canonicalTruncation {X : Type*} (t : ℝ) (a : X → EReal) (x : X) : EReal :=
  max (a x) ((-t : ℝ) : EReal)

/-- Deep coincidence identifies the closed sublevels, including their boundaries. -/
theorem closedSublevel_eq_of_deepCoincidence {X : Type*} {a b : X → EReal}
    {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)}) :
    {x | a x ≤ ((-t : ℝ) : EReal)} = {x | b x ≤ ((-t : ℝ) : EReal)} := by
  have hlevel : ((-t : ℝ) : EReal) < ((-C : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (neg_lt_neg hCt)
  ext x
  constructor
  · intro hx
    have heq := hab ((min_le_left _ _).trans_lt (hx.trans_lt hlevel))
    change b x ≤ ((-t : ℝ) : EReal)
    rw [← heq]
    exact hx
  · intro hx
    have heq := hab ((min_le_right _ _).trans_lt (hx.trans_lt hlevel))
    change a x ≤ ((-t : ℝ) : EReal)
    rw [heq]
    exact hx

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The deep coincidence region is an actual ordinary open set. -/
theorem deepCoincidence_isOpen {alpha beta : SmoothRealForm n M 2}
    {a b : M → EReal} (ha : ThetaPlurisubharmonic alpha a)
    (hb : ThetaPlurisubharmonic beta b) (C : ℝ) :
    IsOpen {x | min (a x) (b x) < ((-C : ℝ) : EReal)} := by
  have hopen (u : M → EReal) (hu : UpperSemicontinuous u) :
      IsOpen {x | u x < ((-C : ℝ) : EReal)} := by
    rw [isOpen_iff_mem_nhds]
    exact fun x hx => hu x _ hx
  have hset : {x | min (a x) (b x) < ((-C : ℝ) : EReal)} =
      {x | a x < ((-C : ℝ) : EReal)} ∪ {x | b x < ((-C : ℝ) : EReal)} := by
    ext x
    change min (a x) (b x) < ((-C : ℝ) : EReal) ↔
      a x < ((-C : ℝ) : EReal) ∨ b x < ((-C : ℝ) : EReal)
    exact min_lt_iff
  rw [hset]
  exact (hopen a ha.quasiPlurisubharmonic.upperSemicontinuous).union
    (hopen b hb.quasiPlurisubharmonic.upperSemicontinuous)

/-- A semipositive background produces the raw PSH property of the actual cutoff. -/
theorem thetaPlurisubharmonic_canonicalTruncation {theta : ClosedRealOneOneForm n M}
    (htheta : theta.val.IsSemipositive) {a : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (t : ℝ) :
    ThetaPlurisubharmonic theta.val (canonicalTruncation t a) :=
  thetaPlurisubharmonic_max_const htheta ha (-t)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual diagonal cutoff measures have identical deep-sublevel mass. -/
theorem globalDiagonalTruncation_restrict_deep_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)}) :
    (globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation t a)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha t)).restrict
        {x | a x ≤ ((-t : ℝ) : EReal)} =
      (globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation t b)
        (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta hb t)).restrict
          {x | a x ≤ ((-t : ℝ) : EReal)} := by
  apply globalMixedMeasure_restrict_eq_on_subset _ _ (deepCoincidence_isOpen ha hb C)
  · intro i x hx
    simp only [canonicalTruncation, hab hx]
  · intro x hx
    exact (min_le_left _ _).trans_lt
      (hx.trans_lt (EReal.coe_lt_coe_iff.mpr (neg_lt_neg hCt)))

/-- The same boundary cancellation holds for an actual one-slot mixed change. -/
theorem globalMixedTruncation_update_restrict_deep_eq
    {theta : Fin n → ClosedRealOneOneForm n M} (s : Fin n → M → EReal) (i0 : Fin n)
    {a b : M → EReal} (ha : ThetaPlurisubharmonic (theta i0).val a)
    (hb : ThetaPlurisubharmonic (theta i0).val b) {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    (hsa : ∀ i, ThetaPlurisubharmonic (theta i).val
      (Function.update s i0 (canonicalTruncation t a) i))
    (hsb : ∀ i, ThetaPlurisubharmonic (theta i).val
      (Function.update s i0 (canonicalTruncation t b) i)) :
    (globalMixedMeasure theta (Function.update s i0 (canonicalTruncation t a)) hsa).restrict
      {x | a x ≤ ((-t : ℝ) : EReal)} =
    (globalMixedMeasure theta (Function.update s i0 (canonicalTruncation t b)) hsb).restrict
      {x | a x ≤ ((-t : ℝ) : EReal)} := by
  have hloc := globalMixedMeasure_update_restrict_eq_of_eqOn s i0 hsa hsb
    (deepCoincidence_isOpen ha hb C)
    (show EqOn (canonicalTruncation t a) (canonicalTruncation t b)
      {x | min (a x) (b x) < ((-C : ℝ) : EReal)} from
      fun x hx => by simp only [canonicalTruncation, hab hx])
  have hsub : {x | a x ≤ ((-t : ℝ) : EReal)} ⊆
      {x | min (a x) (b x) < ((-C : ℝ) : EReal)} := fun x hx =>
    (min_le_left _ _).trans_lt
      (hx.trans_lt (EReal.coe_lt_coe_iff.mpr (neg_lt_neg hCt)))
  exact (Measure.restrict_restrict_of_subset hsub).symm.trans
    ((congrArg (fun μ : Measure M => μ.restrict {x | a x ≤ ((-t : ℝ) : EReal)})
      hloc).trans (Measure.restrict_restrict_of_subset hsub))

/-- Away from the cutoff the actual diagonal measure is the original one.
The proof also handles the empty tuple in dimension zero. -/
theorem globalDiagonalTruncation_restrict_strict_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a : M → EReal} (ha : ThetaPlurisubharmonic theta.val a) (t : ℝ) :
    (globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation t a)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha t)).restrict
        {x | ((-t : ℝ) : EReal) < a x} =
      (globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)).restrict
        {x | ((-t : ℝ) : EReal) < a x} := by
  have hloc := globalMixedMeasure_restrict_max_eq (fun _ : Fin n => ha)
    (fun _ : Fin n => thetaPlurisubharmonic_const theta htheta (-t))
    (fun _ : Fin n => thetaPlurisubharmonic_canonicalTruncation htheta ha t)
  have hsub : {x | ((-t : ℝ) : EReal) < a x} ⊆
      {x | ∀ _ : Fin n, ((-t : ℝ) : EReal) < a x} := fun _ hx _ => hx
  exact (Measure.restrict_restrict_of_subset hsub).symm.trans
    ((congrArg (fun μ : Measure M => μ.restrict {x | ((-t : ℝ) : EReal) < a x})
      hloc).trans (Measure.restrict_restrict_of_subset hsub))

/-- Deep-sublevel equality genuinely removes both cutoff measures from the
signed integral difference, leaving restrictions of the fixed original measures. -/
theorem globalDiagonalTruncation_integral_sub_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    {F : M → ℝ}
    (hFa : Integrable F (globalMixedMeasure (fun _ => theta)
      (fun _ => canonicalTruncation t a)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha t)))
    (hFb : Integrable F (globalMixedMeasure (fun _ => theta)
      (fun _ => canonicalTruncation t b)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta hb t))) :
    (∫ x, F x ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation t a)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta ha t)) -
    (∫ x, F x ∂globalMixedMeasure (fun _ => theta) (fun _ => canonicalTruncation t b)
      (fun _ => thetaPlurisubharmonic_canonicalTruncation htheta hb t)) =
    (∫ x in {x | ((-t : ℝ) : EReal) < a x}, F x
      ∂globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha)) -
    (∫ x in {x | ((-t : ℝ) : EReal) < a x}, F x
      ∂globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb)) := by
  have hS : MeasurableSet {x | ((-t : ℝ) : EReal) < a x} :=
    measurableSet_lt measurable_const ha.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hcompl : {x | ((-t : ℝ) : EReal) < a x}ᶜ =
      {x | a x ≤ ((-t : ℝ) : EReal)} := by ext x; simp
  have hS' : {x | ((-t : ℝ) : EReal) < a x} =
      {x | ((-t : ℝ) : EReal) < b x} := by
    have hE := closedSublevel_eq_of_deepCoincidence hCt hab
    ext x
    have hx := Set.ext_iff.mp hE x
    simpa only [mem_ofPred_eq, not_le] using not_congr hx
  rw [← integral_add_compl hS hFa, ← integral_add_compl hS hFb, hcompl,
    globalDiagonalTruncation_restrict_deep_eq theta htheta ha hb hCt hab,
    globalDiagonalTruncation_restrict_strict_eq theta htheta ha t,
    hS', globalDiagonalTruncation_restrict_strict_eq theta htheta hb t]
  ring

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffCancellation
