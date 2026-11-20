import SGPT.Foundations.Analysis.Pending.ActualCapacityUpperBound
import SGPT.Foundations.Analysis.Pending.ActualLocalFiniteBoxWeightedContinuity
import SGPT.Foundations.Analysis.Pending.ActualChartTruncatedCapacityConvergence
import SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar

set_option autoImplicit false

/-! # Actual lower-truncated local weighted limits for singular families

Original independent-background potentials have no supplied bounds.
Actual capacity upper bounds give one tail before all lower levels and
classifiers. Genuine compact smooth corrections and lower truncations
then produce the finite local boxes, capacity limits and weighted
ordinary Bedford--Taylor limits. Non-pluripolar locality and the final
unbounded mass liminf remain separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualChartTruncatedWeightedContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  GlobalSlotStokes BedfordTaylor MixedMongeAmpere ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]


omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_real_upper {α : ClosedRealOneOneForm n M} {v : M → EReal}
    (hv : IsThetaPshPotential α.val v) : ∃ H : ℝ, ∀ x, v x ≤ (H : EReal) := by
  cases isEmpty_or_nonempty M with
  | inl hE =>
      let _ := hE
      exact ⟨0, fun x => isEmptyElim x⟩
  | inr hN =>
      let _ := hN
      exact hv.exists_global_upper_bound

/-- Actual original capacity limits internally choose one tail and produce
all fixed corrected lower-truncation weighted ordinary local BT limits. -/
theorem exists_tail_weighted_limits (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (J : SlotChart θ omega.form) {D : Opens (ComplexModel n)}
    (hcompact : IsCompact (closure (D : Set (ComplexModel n))))
    (hclosure : closure (D : Set (ComplexModel n)) ⊆ J.domain)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ, ∀ k : ℕ,
      ∃ hU : ∀ j, IsLocallyBoundedMixedPshOn D (mixedTruncationReal
          (fun i y => u (j + N) i (J.chart.val.symm y) + (J.potential i y : EReal)) k),
      ∃ hV : IsLocallyBoundedMixedPshOn D (mixedTruncationReal
          (fun i y => v i (J.chart.val.symm y) + (J.potential i y : EReal)) k),
      ∀ (Φ : (Fin n → ℝ) → ℝ) (L : NNReal), LipschitzWith L Φ →
      ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h → tsupport h ⊆ K →
        Tendsto (fun j => ∫ y, h y * Φ (fun i => mixedTruncationReal
          (fun i y => u (j + N) i (J.chart.val.symm y) + (J.potential i y : EReal)) k i y)
          ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal
            (fun i y => u (j + N) i (J.chart.val.symm y) + (J.potential i y : EReal)) k) (hU j))
        atTop (𝓝 (∫ y, h y * Φ (fun i => mixedTruncationReal
          (fun i y => v i (J.chart.val.symm y) + (J.potential i y : EReal)) k i y)
          ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal
            (fun i y => v i (J.chart.val.symm y) + (J.potential i y : EReal)) k) hV)) := by
  classical
  obtain ⟨H, hH⟩ := Classical.axiomOfChoice fun i : Fin n =>
    ActualCapacityUpperBound.exists_eventual_upper_bound omega (fun j => hu j i) (hv i) (hcap i)
  have hAll : ∀ᶠ j : ℕ in atTop, ∀ i : Fin n, ∀ x, u j i x ≤ (H i : EReal) :=
    eventually_all.mpr hH
  obtain ⟨N, hN⟩ := eventually_atTop.mp hAll
  choose V hVbound using fun i => exists_real_upper (hv i)
  choose R hR using fun i : Fin n => hcompact.exists_bound_of_continuousOn
    ((J.localPotential i).2.2.1.continuousOn.mono hclosure)
  let B : ℝ := ∑ i : Fin n, (|H i| + |V i| + |R i|)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ =>
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hsingle (i : Fin n) : |H i| + |V i| + |R i| ≤ B := by
    exact Finset.single_le_sum (f := fun i : Fin n => |H i| + |V i| + |R i|)
      (fun i _ => add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (abs_nonneg _)) (Finset.mem_univ i)
  have hDJ : D ≤ J.domain := fun y hy => hclosure (subset_closure hy)
  let corr (f : Fin n → M → EReal) : Fin n → ComplexModel n → EReal :=
    fun i y => f i (J.chart.val.symm y) + (J.potential i y : EReal)
  have hCorr (f : Fin n → M → EReal) (hf : ∀ i, IsThetaPshPotential (θ i).val (f i)) :
      ∀ i, PlurisubharmonicOn (corr f i) D := fun i =>
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
      (hf i).1 J.chart (J.localPotential i)).mono hDJ
  have hCorrBound (f : Fin n → M → EReal) (A : Fin n → ℝ)
      (hA : ∀ i x, f i x ≤ (A i : EReal))
      (hAb : ∀ i, |A i| ≤ |H i| + |V i|) :
      ∀ i y, y ∈ D → corr f i y ≤ (B : EReal) := by
    intro i y hy
    have hr : |J.potential i y| ≤ R i := by
      simpa only [Real.norm_eq_abs] using hR i y (subset_closure hy)
    have hrho : |J.potential i y| ≤ |R i| := hr.trans (le_abs_self _)
    have hreal : A i + J.potential i y ≤ B := by
      have hs := hsingle i
      have hh := hAb i
      have hp := le_abs_self (J.potential i y)
      have ha := le_abs_self (A i)
      linarith
    have hsum : corr f i y ≤ ((A i + J.potential i y : ℝ) : EReal) := by
      change f i (J.chart.val.symm y) + (J.potential i y : EReal) ≤ _
      rw [EReal.coe_add]
      exact add_le_add (hA i (J.chart.val.symm y)) le_rfl
    exact hsum.trans (EReal.coe_le_coe_iff.mpr hreal)
  have hUB (j : ℕ) : ∀ i y, y ∈ D → corr (u (j + N)) i y ≤ (B : EReal) :=
    hCorrBound (u (j + N)) H (hN (j + N) (Nat.le_add_left N j))
      (fun i => le_add_of_nonneg_right (abs_nonneg _))
  have hVB : ∀ i y, y ∈ D → corr v i y ≤ (B : EReal) :=
    hCorrBound v V hVbound (fun i => le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨N, fun k => ?_⟩
  let hTU (j : ℕ) : IsLocallyBoundedMixedPshOn D (mixedTruncationReal (corr (u (j + N))) k) :=
    mixedTruncationReal_isLocallyBounded (hCorr (u (j + N)) (hu (j + N))) k
  let hTV : IsLocallyBoundedMixedPshOn D (mixedTruncationReal (corr v) k) :=
    mixedTruncationReal_isLocallyBounded (hCorr v hv) k
  have hbox (f : Fin n → M → EReal)
      (hf : ∀ i, IsThetaPshPotential (θ i).val (f i))
      (hb : ∀ i y, y ∈ D → corr f i y ≤ (B : EReal)) :
      ∀ i y, y ∈ D → -(B + (k : ℝ)) ≤ mixedTruncationReal (corr f) k i y ∧
        mixedTruncationReal (corr f) k i y ≤ B + (k : ℝ) := by
    intro i y hy
    have hlo : -(k : ℝ) ≤ mixedTruncationReal (corr f) k i y := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_mixedTruncationReal (hCorr f hf) k i hy]
      exact truncation_lower_bound (corr f i) k y
    have hhi : mixedTruncationReal (corr f) k i y ≤ B := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_mixedTruncationReal (hCorr f hf) k i hy]
      exact max_le (hb i y hy) (EReal.coe_le_coe_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlocal : ∀ i (Q : Opens (ComplexModel n)), Q ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ Q → ∀ a : ℝ, 0 < a → Tendsto (fun j => relCapacity Q
        {y | y ∈ T ∧ a < |mixedTruncationReal (corr (u (j + N))) k i y -
          mixedTruncationReal (corr v) k i y|}) atTop (𝓝 0) := by
    intro i Q hQD T hT hTQ a ha
    have hQJ : Q ≤ J.domain := hQD.trans hDJ
    have hlocalLimit := ActualChartTruncatedCapacityConvergence.tendsto_relative_capacity_lower_truncation
      (n := n) (M := M) (D := Q) (α := θ i) (I := ℕ) (F := atTop)
      (u := fun j => u (j + N) i) (v := v i) omega J.chart
      (fun y hy => J.domain_le_target (hQJ hy))
      (J.kahlerLocal.mono Q.isOpen hQJ) hT hTQ (fun j => hu (j + N) i) (hv i)
      (fun a ha => (hcap i a ha).comp (tendsto_add_atTop_nat N)) (J.potential i) (-(k : ℝ)) ha
    simpa only [mixedTruncationReal, truncationReal, truncation, corr] using hlocalLimit
  refine ⟨hTU, hTV, fun Φ L hΦ h hc hk ht => ?_⟩
  exact ActualLocalFiniteBoxWeightedContinuity.tendsto_integral_classifier_of_relative_capacity
    omega J.chart (fun y hy => J.domain_le_target (hDJ hy))
    (J.kahlerLocal.mono D.isOpen hDJ) hK hKD hTU hTV
    (B := B + (k : ℝ)) (add_nonneg hB (Nat.cast_nonneg _))
    (fun j => hbox (u (j + N)) (hu (j + N)) (hUB j)) (hbox v hv hVB) hlocal
    (fun j i => hTU j i) (fun i => hTV i)
    (fun j => hbox (u (j + N)) (hu (j + N)) (hUB j)) (hbox v hv hVB) hlocal hΦ hc hk ht

end
end SGPT.Foundations.Analysis.Pending.ActualChartTruncatedWeightedContinuity
