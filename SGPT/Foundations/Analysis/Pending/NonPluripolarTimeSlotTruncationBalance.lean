import SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlotPositiveBalance
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

set_option autoImplicit false

/-! # Actual smooth floor stabilization and canonical NP truncation balance -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotTruncationBalance

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  BedfordTaylor BedfordTaylorTimeSlot BedfordTaylorFibreSlicing MixedDensityRankOneSlot
  MixedMongeAmpere MixedNonPluripolar BedfordTaylorTimeSlotPositiveBalance

noncomputable section

variable {n : ℕ} {Ω Q : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- Replacing a last slot by an actual smooth PSH function produces an actual extended-real PSH tuple. -/
theorem plurisubharmonicOn_update_last (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {s : ComplexModel (n + 1) → ℝ} (hs : IsSmoothPsdOn Ω s) :
    ∀ i, PlurisubharmonicOn ((Function.update u (Fin.last n) fun q => (s q : EReal)) i) Ω := by
  classical
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simpa using hs.plurisubharmonicOn
  · simpa [Function.update_of_ne hi] using hu i

/-- The common integer floor is produced from actual compactness and smoothness of the two regularizer slots. -/
theorem exists_common_smooth_floor (hQ : RelativelyCompactIn Q Ω)
    {a b : ComplexModel (n + 1) → ℝ} (ha : IsSmoothPsdOn Ω a) (hb : IsSmoothPsdOn Ω b) :
    ∃ R : ℕ, ∀ k q, q ∈ closure (Q : Set (ComplexModel (n + 1))) →
      -((k + (R + 1) : ℕ) : ℝ) < a q ∧ -((k + (R + 1) : ℕ) : ℝ) < b q := by
  obtain ⟨A, hA⟩ := hQ.1.exists_bound_of_continuousOn (ha.1.continuousOn.mono hQ.2)
  obtain ⟨B, hB⟩ := hQ.1.exists_bound_of_continuousOn (hb.1.continuousOn.mono hQ.2)
  obtain ⟨R, hR⟩ := exists_nat_gt (max A B)
  refine ⟨R, fun k q hq => ?_⟩
  have haq : -A ≤ a q := neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hA q hq)
  have hbq : -B ≤ b q := neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hB q hq)
  have hRA : A < R := (le_max_left A B).trans_lt hR
  have hRB : B < R := (le_max_right A B).trans_lt hR
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  simp only [Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

/-- The actual max-before-real-representative truncation of the smooth updated slot agrees on an ordinary open set above its floor. -/
theorem mixedTruncationReal_update_last_eqOn {s : ComplexModel (n + 1) → ℝ} {k : ℕ}
    (hfloor : ∀ q ∈ Q, -(k : ℝ) < s q) (i : Fin (n + 1)) :
    EqOn (mixedTruncationReal (Function.update u (Fin.last n) fun q => (s q : EReal)) k i)
      ((Function.update (mixedTruncationReal u k) (Fin.last n) s) i) Q := by
  classical
  intro q hq
  by_cases hi : i = Fin.last n
  · subst i
    simp only [mixedTruncationReal, Function.update_self, truncationReal, truncation]
    rw [max_eq_left (EReal.coe_le_coe_iff.mpr (hfloor q hq).le), EReal.toReal_coe]
  · simp only [mixedTruncationReal, Function.update_of_ne hi]

/-- Above the actual smooth floors, the full common strict loci of two last-slot replacements coincide on Q. -/
theorem commonStrictLocus_update_last_inter_eq
    {a b : ComplexModel (n + 1) → ℝ} {k : ℕ}
    (ha : ∀ q ∈ Q, -(k : ℝ) < a q) (hb : ∀ q ∈ Q, -(k : ℝ) < b q) :
    commonStrictLocus Ω (Function.update u (Fin.last n) fun q => (a q : EReal)) k ∩ Q =
      commonStrictLocus Ω (Function.update u (Fin.last n) fun q => (b q : EReal)) k ∩ Q := by
  classical
  ext q
  constructor
  · intro h
    refine ⟨⟨h.1.1, fun i => ?_⟩, h.2⟩
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [Function.update_self] using EReal.coe_lt_coe_iff.mpr (hb q h.2)
    · simpa only [Function.update_of_ne hi] using h.1.2 i
  · intro h
    refine ⟨⟨h.1.1, fun i => ?_⟩, h.2⟩
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [Function.update_self] using EReal.coe_lt_coe_iff.mpr (ha q h.2)
    · simpa only [Function.update_of_ne hi] using h.1.2 i

/-- Actual canonical bounded measures commute on Q with an above-floor smooth last-slot replacement, by genuine ordinary-open BT locality. -/
theorem canonical_truncation_update_last_restrict
    (hQΩ : Q ≤ Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {s : ComplexModel (n + 1) → ℝ} (hs : IsSmoothPsdOn Ω s) {k : ℕ}
    (hfloor : ∀ q ∈ Q, -(k : ℝ) < s q) :
    (canonicalMixedBedfordTaylorMeasure Ω
      (mixedTruncationReal (Function.update u (Fin.last n) fun q => (s q : EReal)) k)
      (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_update_last hu hs) k)).restrict Q =
    (canonicalMixedBedfordTaylorMeasure Ω
      (Function.update (mixedTruncationReal u k) (Fin.last n) s)
      (isLocallyBoundedMixedPshOn_update_last (mixedTruncationReal_isLocallyBounded hu k)
        hs.isLocallyBoundedPshOn)).restrict Q :=
  localMixedBedfordTaylorMeasure_unique
    (MixedNonPluripolar.IsLocalMixedBedfordTaylorMeasure.congr
      (localMixedBedfordTaylorMeasure_restrict (canonicalMixedBedfordTaylorMeasure_spec Ω _ _) hQΩ)
      (mixedTruncationReal_update_last_eqOn hfloor))
    (localMixedBedfordTaylorMeasure_restrict (canonicalMixedBedfordTaylorMeasure_spec Ω _ _) hQΩ)

private theorem mixedTruncationMeasure_update_last_restrict
    (hQΩ : Q ≤ Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {s t : ComplexModel (n + 1) → ℝ} (hs : IsSmoothPsdOn Ω s) (ht : IsSmoothPsdOn Ω t)
    {k : ℕ} (hsfloor : ∀ q ∈ Q, -(k : ℝ) < s q) (htfloor : ∀ q ∈ Q, -(k : ℝ) < t q) :
    (mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (s q : EReal))
      (plurisubharmonicOn_update_last hu hs) k).restrict Q =
    ((canonicalMixedBedfordTaylorMeasure Ω (Function.update (mixedTruncationReal u k) (Fin.last n) s)
      (isLocallyBoundedMixedPshOn_update_last (mixedTruncationReal_isLocallyBounded hu k)
        hs.isLocallyBoundedPshOn)).restrict Q).restrict
      (commonStrictLocus Ω (Function.update u (Fin.last n) fun q => (t q : EReal)) k) := by
  unfold mixedTruncationMeasure
  rw [Measure.restrict_restrict Q.isOpen.measurableSet, inter_comm,
    commonStrictLocus_update_last_inter_eq hsfloor htfloor,
    ← Measure.restrict_restrict (measurableSet_commonStrictLocus (plurisubharmonicOn_update_last hu ht) k),
    canonical_truncation_update_last_restrict hQΩ hu hs hsfloor]

/-- The genuine canonical mixed truncation measures satisfy positive time-slot balance on Q; strict loci are restricted only after the actual BT measure identity. -/
theorem mixedTruncationMeasure_timeLift_positive_balance
    (hQΩ : Q ≤ Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {k : ℕ} (hk : 0 < k)
    (hpfloor : ∀ q ∈ Q, -(k : ℝ) < p q)
    (hafloor : ∀ q ∈ Q, -(k : ℝ) < timeLift n ψ q + p q) :
    (mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp) k).restrict Q +
    ((mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)) k).restrict Q).withDensity
      (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n)))) =
    (mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp) k).restrict Q +
    ((mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)) k).restrict Q).withDensity
      (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n)))) := by
  have hrfloor : ∀ q ∈ Q, -(k : ℝ) < lastNormSq n q := by
    intro q _
    exact (neg_neg_of_pos (Nat.cast_pos.mpr hk)).trans_le (sq_nonneg _)
  have hbt := canonical_restrict_add_withDensity_timeLift (mixedTruncationReal_isLocallyBounded hu k) hψ hp hψp
  have hbtQ := congrArg (fun μ : Measure (ComplexModel (n + 1)) => μ.restrict Q) hbt
  simp only [Measure.restrict_restrict_of_subset hQΩ, Measure.restrict_add,
    restrict_withDensity Q.isOpen.measurableSet] at hbtQ
  let D := commonStrictLocus Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal)) k
  have hD : MeasurableSet D :=
    measurableSet_commonStrictLocus (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)) k
  have hbtD := congrArg (fun μ : Measure (ComplexModel (n + 1)) => μ.restrict D) hbtQ
  simp only [Measure.restrict_add, restrict_withDensity hD] at hbtD
  rw [← mixedTruncationMeasure_update_last_restrict hQΩ hu hψp (isSmoothPsdOn_lastNormSq Ω) hafloor hrfloor,
    ← mixedTruncationMeasure_update_last_restrict hQΩ hu hp (isSmoothPsdOn_lastNormSq Ω) hpfloor hrfloor,
    ← mixedTruncationMeasure_update_last_restrict hQΩ hu (isSmoothPsdOn_lastNormSq Ω)
      (isSmoothPsdOn_lastNormSq Ω) hrfloor hrfloor] at hbtD
  exact hbtD

/-- The common shifted canonical truncation balances, including their integer shift, are produced from actual compactness and PSH data. -/
theorem exists_shifted_mixedTruncationMeasure_timeLift_positive_balance
    (hQ : RelativelyCompactIn Q Ω) (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q) :
    ∃ R : ℕ, ∀ k : ℕ,
    (mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => ((timeLift n ψ q + p q : ℝ) : EReal))
      (plurisubharmonicOn_update_last hu hψp) (k + (R + 1))).restrict Q +
    ((mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)) (k + (R + 1))).restrict Q).withDensity
      (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n)))) =
    (mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (p q : EReal))
      (plurisubharmonicOn_update_last hu hp) (k + (R + 1))).restrict Q +
    ((mixedTruncationMeasure Ω (Function.update u (Fin.last n) fun q => (lastNormSq n q : EReal))
      (plurisubharmonicOn_update_last hu (isSmoothPsdOn_lastNormSq Ω)) (k + (R + 1))).restrict Q).withDensity
      (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n)))) := by
  obtain ⟨R, hR⟩ := exists_common_smooth_floor hQ hψp hp
  refine ⟨R, fun k => ?_⟩
  exact mixedTruncationMeasure_timeLift_positive_balance (subset_closure.trans hQ.2) hu hψ hp hψp
    (by omega) (fun q hq => (hR k q (subset_closure hq)).2)
    (fun q hq => (hR k q (subset_closure hq)).1)

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarTimeSlotTruncationBalance
