import SGPT.Foundations.Analysis.Pending.NonPluripolarCutoffLimits

/-!
# Actual weighted mixed cutoff terms for deep-coincident pairs

Lu, Lemma 4.1 Step 1.1: the signed cutoff weight vanishes on its
own deep sublevel, while a one-slot cutoff measure difference
cancels on the second pair's deep sublevel. Their intersection
lies in the actual common strict locality locus of every slot.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarMixedCutoffs

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar
open GlobalOpenLocality GlobalMaxLocality NonPluripolarCutoffCancellation
open NonPluripolarCutoffLimits RelativeEnergyIntegrability

noncomputable section

/-- A deep-coincident pair has an exact indicator formula for its cutoff weight. -/
theorem canonicalTruncatedDiff_eq_indicator {X : Type*} {a b : X → EReal}
    {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)}) :
    (fun x => canonicalERealDiffToReal (canonicalTruncation t a x)
      (canonicalTruncation t b x)) =
    {x | ((-t : ℝ) : EReal) < a x}.indicator
      (fun x => canonicalERealDiffToReal (a x) (b x)) := by
  have hE := closedSublevel_eq_of_deepCoincidence hCt hab
  funext x
  have hxE := Set.ext_iff.mp hE x
  change a x ≤ ((-t : ℝ) : EReal) ↔ b x ≤ ((-t : ℝ) : EReal) at hxE
  by_cases hx : ((-t : ℝ) : EReal) < a x
  · have hbx : ((-t : ℝ) : EReal) < b x := by
      simpa only [not_le] using (not_congr hxE).mp (not_le.mpr hx)
    rw [indicator_of_mem (show x ∈ {x | ((-t : ℝ) : EReal) < a x} from hx)]
    simp only [canonicalTruncation, max_eq_left hx.le, max_eq_left hbx.le]
  · have hax : a x ≤ ((-t : ℝ) : EReal) := le_of_not_gt hx
    have hbx := hxE.mp hax
    rw [indicator_of_notMem (show x ∉ {x | ((-t : ℝ) : EReal) < a x} from hx)]
    simp only [canonicalTruncation, max_eq_right hax, max_eq_right hbx,
      canonicalERealDiffToReal_self]

/-- The exact indicator identity restricts every weighted integral to the
common strict superlevel, with the original corrected difference there. -/
theorem setIntegral_canonicalTruncatedDiff_eq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {a b : X → EReal}
    (ham : Measurable a) {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)}) (S : Set X) :
    (∫ x in S, canonicalERealDiffToReal (canonicalTruncation t a x)
      (canonicalTruncation t b x) ∂μ) =
    ∫ x in S ∩ {x | ((-t : ℝ) : EReal) < a x},
      canonicalERealDiffToReal (a x) (b x) ∂μ := by
  rw [canonicalTruncatedDiff_eq_indicator hCt hab,
    setIntegral_indicator (measurableSet_lt measurable_const ham)]

/-- Actual tuples choosing one of two potentials in each slot. -/
def binaryPotentialTuple {n : ℕ} {X : Type*} (sigma : Fin n → Bool)
    (a b : X → EReal) (i : Fin n) : X → EReal := if sigma i then a else b

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Raw PSH closure for the actual mixed tuple with one distinguished slot. -/
theorem thetaPlurisubharmonic_binaryUpdatedTuple
    (theta : ClosedRealOneOneForm n M) {a b r : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hr : ThetaPlurisubharmonic theta.val r) (sigma : Fin n → Bool) (i0 : Fin n) :
    ∀ i, ThetaPlurisubharmonic theta.val (Function.update (binaryPotentialTuple sigma a b) i0 r i) := by
  intro i
  by_cases hi : i = i0
  · subst hi
    simpa using hr
  · simp only [Function.update_of_ne hi, binaryPotentialTuple]
    split
    · exact ha
    · exact hb

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual mixed measure with a distinguished slot and binary remaining slots. -/
def binaryMixedMeasure (theta : ClosedRealOneOneForm n M) {a b r : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hr : ThetaPlurisubharmonic theta.val r) (sigma : Fin n → Bool) (i0 : Fin n) : Measure M :=
  globalMixedMeasure (fun _ => theta) (Function.update (binaryPotentialTuple sigma a b) i0 r)
    (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hr sigma i0)

/-- Its actual canonical cutoff measure, truncating every slot. -/
def binaryMixedCutoffMeasure (theta : ClosedRealOneOneForm n M)
    (htheta : theta.val.IsSemipositive) {a b r : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hr : ThetaPlurisubharmonic theta.val r) (sigma : Fin n → Bool) (i0 : Fin n) (t : ℝ) :
    Measure M :=
  globalMixedMeasure (fun _ => theta)
    (fun i => canonicalTruncation t (Function.update (binaryPotentialTuple sigma a b) i0 r i))
    (fun i => thetaPlurisubharmonic_canonicalTruncation htheta
      (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hr sigma i0 i) t)

/-- Actual strict restoration on any set lying above all three slot obstacles. -/
theorem binaryMixedCutoffMeasure_restrict_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b r : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hr : ThetaPlurisubharmonic theta.val r)
    (sigma : Fin n → Bool) (i0 : Fin n) (t : ℝ) {S : Set M}
    (hS : ∀ x ∈ S, ((-t : ℝ) : EReal) < a x ∧
      ((-t : ℝ) : EReal) < b x ∧ ((-t : ℝ) : EReal) < r x) :
    (binaryMixedCutoffMeasure theta htheta ha hb hr sigma i0 t).restrict S =
      (binaryMixedMeasure theta ha hb hr sigma i0).restrict S := by
  have hloc := globalMixedMeasure_restrict_max_eq
    (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hr sigma i0)
    (fun _ => thetaPlurisubharmonic_const theta htheta (-t))
    (fun i => thetaPlurisubharmonic_canonicalTruncation htheta
      (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hr sigma i0 i) t)
  have hsub : S ⊆ {x | ∀ i, ((-t : ℝ) : EReal) <
      Function.update (binaryPotentialTuple sigma a b) i0 r i x} := by
    intro x hx i
    obtain ⟨hax, hbx, hrx⟩ := hS x hx
    by_cases hi : i = i0
    · subst hi
      simpa using hrx
    · simp only [Function.update_of_ne hi, binaryPotentialTuple]
      split
      · exact hax
      · exact hbx
  exact (Measure.restrict_restrict_of_subset hsub).symm.trans
    ((congrArg (fun μ : Measure M => μ.restrict S) hloc).trans
      (Measure.restrict_restrict_of_subset hsub))

/-- Actual one-slot deep cancellation with every remaining slot also truncated. -/
theorem binaryMixedCutoffMeasure_restrict_deep_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b p q : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hp : ThetaPlurisubharmonic theta.val p)
    (hq : ThetaPlurisubharmonic theta.val q) (sigma : Fin n → Bool) (i0 : Fin n)
    {C t : ℝ} (hCt : C < t)
    (hpq : EqOn p q {x | min (p x) (q x) < ((-C : ℝ) : EReal)}) :
    (binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 t).restrict
      {x | p x ≤ ((-t : ℝ) : EReal)} =
    (binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 t).restrict
      {x | p x ≤ ((-t : ℝ) : EReal)} := by
  apply globalMixedMeasure_restrict_eq_on_subset _ _ (deepCoincidence_isOpen hp hq C)
  · intro i x hx
    by_cases hi : i = i0
    · subst hi
      simp [canonicalTruncation, hpq hx]
    · simp only [canonicalTruncation, Function.update_of_ne hi]
  · intro x hx
    exact (min_le_left _ _).trans_lt
      (hx.trans_lt (EReal.coe_lt_coe_iff.mpr (neg_lt_neg hCt)))

/-- The two actual mixed cutoff integrals reduce to restrictions of fixed
original mixed measures. The real weight's own deep part vanishes identically. -/
theorem binaryMixedCutoffMeasure_integral_sub_eq
    (theta : ClosedRealOneOneForm n M) (htheta : theta.val.IsSemipositive)
    {a b p q : M → EReal} (ha : ThetaPlurisubharmonic theta.val a)
    (hb : ThetaPlurisubharmonic theta.val b) (hp : ThetaPlurisubharmonic theta.val p)
    (hq : ThetaPlurisubharmonic theta.val q) (sigma : Fin n → Bool) (i0 : Fin n)
    {C t : ℝ} (hCt : C < t)
    (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    (hpq : EqOn p q {x | min (p x) (q x) < ((-C : ℝ) : EReal)})
    (hFp : Integrable (fun x => canonicalERealDiffToReal (canonicalTruncation t a x)
      (canonicalTruncation t b x)) (binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 t))
    (hFq : Integrable (fun x => canonicalERealDiffToReal (canonicalTruncation t a x)
      (canonicalTruncation t b x)) (binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 t)) :
    (∫ x, canonicalERealDiffToReal (canonicalTruncation t a x) (canonicalTruncation t b x)
      ∂binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 t) -
    (∫ x, canonicalERealDiffToReal (canonicalTruncation t a x) (canonicalTruncation t b x)
      ∂binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 t) =
    (∫ x in {x | ((-t : ℝ) : EReal) < p x},
      canonicalERealDiffToReal (canonicalTruncation t a x) (canonicalTruncation t b x)
      ∂binaryMixedMeasure theta ha hb hp sigma i0) -
    (∫ x in {x | ((-t : ℝ) : EReal) < p x},
      canonicalERealDiffToReal (canonicalTruncation t a x) (canonicalTruncation t b x)
      ∂binaryMixedMeasure theta ha hb hq sigma i0) := by
  let Sa : Set M := {x | ((-t : ℝ) : EReal) < a x}
  let Sp : Set M := {x | ((-t : ℝ) : EReal) < p x}
  have hSa : MeasurableSet Sa := measurableSet_lt measurable_const
    ha.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hSp : MeasurableSet Sp := measurableSet_lt measurable_const
    hp.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hcompl : Spᶜ = {x | p x ≤ ((-t : ℝ) : EReal)} := by ext x; simp [Sp]
  have hEa := closedSublevel_eq_of_deepCoincidence hCt hab
  have hEp := closedSublevel_eq_of_deepCoincidence hCt hpq
  have hIb (x : M) (hx : x ∈ Sp ∩ Sa) : ((-t : ℝ) : EReal) < b x := by
    have hxE := Set.ext_iff.mp hEa x
    change a x ≤ ((-t : ℝ) : EReal) ↔ b x ≤ ((-t : ℝ) : EReal) at hxE
    exact not_le.mp ((not_congr hxE).mp (not_le.mpr hx.2))
  have hIq (x : M) (hx : x ∈ Sp ∩ Sa) : ((-t : ℝ) : EReal) < q x := by
    have hxE := Set.ext_iff.mp hEp x
    change p x ≤ ((-t : ℝ) : EReal) ↔ q x ≤ ((-t : ℝ) : EReal) at hxE
    exact not_le.mp ((not_congr hxE).mp (not_le.mpr hx.1))
  have hrestp := binaryMixedCutoffMeasure_restrict_eq theta htheta ha hb hp sigma i0 t
    (S := Sp ∩ Sa) (fun x hx => ⟨hx.2, hIb x hx, hx.1⟩)
  have hrestq := binaryMixedCutoffMeasure_restrict_eq theta htheta ha hb hq sigma i0 t
    (S := Sp ∩ Sa) (fun x hx => ⟨hx.2, hIb x hx, hIq x hx⟩)
  have hF := canonicalTruncatedDiff_eq_indicator hCt hab
  have htrans (r : M → EReal) (hr : ThetaPlurisubharmonic theta.val r)
      (hrest : (binaryMixedCutoffMeasure theta htheta ha hb hr sigma i0 t).restrict (Sp ∩ Sa) =
        (binaryMixedMeasure theta ha hb hr sigma i0).restrict (Sp ∩ Sa)) :
      (∫ x in Sp, canonicalERealDiffToReal (canonicalTruncation t a x)
        (canonicalTruncation t b x) ∂binaryMixedCutoffMeasure theta htheta ha hb hr sigma i0 t) =
      (∫ x in Sp, canonicalERealDiffToReal (canonicalTruncation t a x)
        (canonicalTruncation t b x) ∂binaryMixedMeasure theta ha hb hr sigma i0) := by
    rw [hF, setIntegral_indicator hSa, setIntegral_indicator hSa, hrest]
  have hdeep : (binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 t).restrict Spᶜ =
      (binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 t).restrict Spᶜ := by
    rw [hcompl]
    exact binaryMixedCutoffMeasure_restrict_deep_eq theta htheta ha hb hp hq sigma i0 hCt hpq
  change _ = (∫ x in Sp, _ ∂_) - (∫ x in Sp, _ ∂_)
  rw [← integral_add_compl hSp hFp, ← integral_add_compl hSp hFq, hdeep,
    htrans p hp hrestp, htrans q hq hrestq]
  ring

/-- The actual weighted mixed cutoff difference converges by genuine pole
nullity, finite mass, cancellation and fixed-measure domination. -/
theorem tendsto_binaryMixedCutoffMeasure_integral_sub
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (htheta : theta.val.IsSemipositive) {a b p q : M → EReal}
    (ha : ThetaPlurisubharmonic theta.val a) (hb : ThetaPlurisubharmonic theta.val b)
    (hp : ThetaPlurisubharmonic theta.val p) (hq : ThetaPlurisubharmonic theta.val q)
    (sigma : Fin n → Bool) (i0 : Fin n) (habtype : SameSingularityTypeOn a b univ)
    {C : ℝ} (hab : EqOn a b {x | min (a x) (b x) < ((-C : ℝ) : EReal)})
    (hpq : EqOn p q {x | min (p x) (q x) < ((-C : ℝ) : EReal)})
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun k =>
      (∫ x, canonicalERealDiffToReal (canonicalTruncation (T k) a x)
        (canonicalTruncation (T k) b x)
        ∂binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 (T k)) -
      (∫ x, canonicalERealDiffToReal (canonicalTruncation (T k) a x)
        (canonicalTruncation (T k) b x)
        ∂binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 (T k))) atTop
      (𝓝 ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hp sigma i0) -
      (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha hb hq sigma i0))) := by
  let : IsFiniteMeasure (binaryMixedMeasure theta ha hb hp sigma i0) :=
    globalMixedMeasure_isFiniteMeasure omega
      (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hp sigma i0)
  let : IsFiniteMeasure (binaryMixedMeasure theta ha hb hq sigma i0) :=
    globalMixedMeasure_isFiniteMeasure omega
      (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hq sigma i0)
  have ham := ha.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hbm := hb.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hpm := hp.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hpoles : {x | p x = ⊥} = {x | q x = ⊥} := by
    ext x
    constructor
    · intro hx
      have heq := hpq (show min (p x) (q x) < ((-C : ℝ) : EReal) by
        simpa only [show p x = ⊥ from hx, min_bot_left] using EReal.bot_lt_coe (-C))
      change q x = ⊥
      rw [← heq]
      exact hx
    · intro hx
      have heq := hpq (show min (p x) (q x) < ((-C : ℝ) : EReal) by
        simpa only [show q x = ⊥ from hx, min_bot_right] using EReal.bot_lt_coe (-C))
      change p x = ⊥
      rw [heq]
      exact hx
  have hnullp : binaryMixedMeasure theta ha hb hp sigma i0 {x | p x = ⊥} = 0 := by
    simpa only [binaryMixedMeasure, Function.update_self] using
      GlobalSlotComparison.globalMixedMeasure_pole_null
        (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hp sigma i0) i0
  have hnullq : binaryMixedMeasure theta ha hb hq sigma i0 {x | p x = ⊥} = 0 := by
    rw [hpoles]
    simpa only [binaryMixedMeasure, Function.update_self] using
      GlobalSlotComparison.globalMixedMeasure_pole_null
        (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hq sigma i0) i0
  have hleft := tendsto_setIntegral_canonicalDiff_canonicalTruncation ham hbm hpm
    ha.quasiPlurisubharmonic.ne_top hb.quasiPlurisubharmonic.ne_top
    hp.quasiPlurisubharmonic.ne_top habtype hnullp hT
  have hright := tendsto_setIntegral_canonicalDiff_canonicalTruncation ham hbm hpm
    ha.quasiPlurisubharmonic.ne_top hb.quasiPlurisubharmonic.ne_top
    hp.quasiPlurisubharmonic.ne_top habtype hnullq hT
  apply (hleft.sub hright).congr'
  filter_upwards [(tendsto_atTop.1 hT) (C + 1)] with k hk
  have hCk : C < T k := by linarith
  let : IsFiniteMeasure (binaryMixedCutoffMeasure theta htheta ha hb hp sigma i0 (T k)) :=
    globalMixedMeasure_isFiniteMeasure omega (fun i =>
      thetaPlurisubharmonic_canonicalTruncation htheta
        (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hp sigma i0 i) (T k))
  let : IsFiniteMeasure (binaryMixedCutoffMeasure theta htheta ha hb hq sigma i0 (T k)) :=
    globalMixedMeasure_isFiniteMeasure omega (fun i =>
      thetaPlurisubharmonic_canonicalTruncation htheta
        (thetaPlurisubharmonic_binaryUpdatedTuple theta ha hb hq sigma i0 i) (T k))
  exact (binaryMixedCutoffMeasure_integral_sub_eq theta htheta ha hb hp hq sigma i0 hCk hab hpq
    (integrable_canonicalDiff_canonicalTruncation ham hbm
      ha.quasiPlurisubharmonic.ne_top hb.quasiPlurisubharmonic.ne_top habtype (T k))
    (integrable_canonicalDiff_canonicalTruncation ham hbm
      ha.quasiPlurisubharmonic.ne_top hb.quasiPlurisubharmonic.ne_top habtype (T k))).symm

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarMixedCutoffs
