import SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformComparison
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze
import SGPT.Foundations.Analysis.Pending.MetricIteratedComparisonLimit

set_option autoImplicit false

/-! # Actual QEA comparison identifies genuine restricted native limits -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularNativeRestrictionComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation RelativeEnergy ThetaPshL1Topology
  SingularGlobalPOrder SingularCanonicalSingularityDistance
  SingularCanonicalOrderSqueeze ThetaPshConvexCombination SingularMinimalCanonicalRay
  PluripolarCapacityDichotomy EndpointMixedMassConvexCombination

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V]
  [CompactSpace V] [ConnectedSpace V]

private theorem dist_le_of_sourcePOrder_chain (omegaV β : KahlerBackground k V)
    (a b c : ThetaPshL1 β.form.val)
    (hab : SourcePOrder (n := k) a.val b.val)
    (hbc : SourcePOrder (n := k) b.val c.val) :
    letI := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
    dist a b ≤ dist a c := by
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  obtain ⟨r, _, _, _, hr⟩ :=
    exists_tendsto_singularityDistance omegaV β.form (isBigClass_kahler β) a.property b.property
  obtain ⟨s, hs, _, _, hsc⟩ :=
    exists_tendsto_singularityDistance omegaV β.form (isBigClass_kahler β) b.property c.property
  obtain ⟨q, _, _, _, hq⟩ :=
    exists_tendsto_singularityDistance omegaV β.form (isBigClass_kahler β) a.property c.property
  have hadd := singularityDistance_eq_add_of_sourcePOrder omegaV β.form
    (isBigClass_kahler β) a.property b.property c.property hab hbc
  rw [hr, hsc, hq, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hadd
  rw [dist_eq_singularityDistance_toReal, dist_eq_singularityDistance_toReal,
    hr, hq, EReal.toReal_coe, EReal.toReal_coe]
  linarith

/-- Actual QEA comparison, genuine native interpolation and three actual
limits identify restricted native limits up to the defining zero distance. -/
theorem singularityDistance_eq_zero_of_native_limits
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {omega : KahlerBackground n M} (omegaV β : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε δ : ℕ → ℝ} {uSeq wSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hw : IsQuasiEquisingularApproximation omega θ u δ wSeq)
    (ι : V → M)
    (hU : ∀ j, IsThetaPshPotential β.form.val (fun y => uSeq j (ι y)))
    (hW : ∀ j, IsThetaPshPotential β.form.val (fun y => wSeq j (ι y)))
    (horder : ∀ j y, uSeq j (ι y) ≤ wSeq j (ι y))
    (A B : ThetaPshL1 β.form.val) :
    let U : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => uSeq j (ι y), hU j⟩
    let W : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => wSeq j (ι y), hW j⟩
    letI := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
    letI : TopologicalSpace (ThetaPshL1 β.form.val) :=
      (singularityPseudoMetricSpace omegaV β.form
        (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
    Tendsto U atTop (𝓝 A) → Tendsto W atTop (𝓝 B) →
      singularityDistance omegaV β.form (isBigClass_kahler β) A.val B.val = 0 := by
  let U : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => uSeq j (ι y), hU j⟩
  let W : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => wSeq j (ι y), hW j⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  change Tendsto U atTop (𝓝 A) → Tendsto W atTop (𝓝 B) →
    singularityDistance omegaV β.form (isBigClass_kahler β) A.val B.val = 0
  intro hUA hWB
  have hcoeff (m : ℕ) : 0 < 1 / ((m : ℝ) + 2) ∧ 1 / ((m : ℝ) + 2) < 1 := by
    have hm := Nat.cast_nonneg (α := ℝ) m
    have hden : 0 < (m : ℝ) + 2 := by linarith
    exact ⟨one_div_pos.mpr hden, (div_lt_one hden).mpr (by linarith)⟩
  let t : ℕ → Ioo (0 : ℝ) 1 := fun m => ⟨1 / ((m : ℝ) + 2), hcoeff m⟩
  have ht : Tendsto (fun m => (t m).val) atTop (𝓝 0) := by
    simpa only [t, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hVmin : IsThetaPshPotential β.form.val (thetaPshSupremum β.form.val) :=
    (isModelPotential_thetaPshSupremum omegaV β.form (isBigClass_kahler β)).plurisubharmonic
  have hVzero : thetaPshSupremum β.form.val = (fun _ => 0) :=
    le_antisymm (thetaPshSupremum_le_zero β.form.val)
      (le_thetaPshSupremum (isThetaPshPotential_zero β) le_rfl)
  let Q : ℕ → ThetaPshL1 β.form.val → ThetaPshL1 β.form.val := fun m v =>
    ⟨convexComb (1 - (t m).val) v.val (thetaPshSupremum β.form.val),
      isThetaPshPotential_convexComb_closed v.property hVmin
        (sub_nonneg.mpr (t m).property.2.le) (sub_le_self 1 (t m).property.1.le)⟩
  have hQ (m : ℕ) : Continuous (Q m) :=
    SingularCanonicalSingularityInterpolation.continuous_native_convexComb_minimal
      omegaV β.form (isBigClass_kahler β)
      (sub_nonneg.mpr (t m).property.2.le) (sub_le_self 1 (t m).property.1.le)
  have hQA : Tendsto (fun m => Q m A) atTop (𝓝 A) :=
    SingularCanonicalSingularityInterpolation.tendsto_native_convexComb_minimal_zero
      omegaV β.form (isBigClass_kahler β) A atTop t ht
  have hQval (m : ℕ) (v : ThetaPshL1 β.form.val) :
      (Q m v).val = fun y => ((1 - (t m).val : ℝ) : EReal) * v.val y := by
    funext y
    change ((1 - (t m).val : ℝ) : EReal) * v.val y +
      ((1 - (1 - (t m).val) : ℝ) : EReal) * thetaPshSupremum β.form.val y = _
    rw [hVzero]
    simp only [mul_zero, add_zero]
  have hbound (m j : ℕ) : ∀ᶠ l in atTop,
      dist (U l) (W l) ≤ dist (U l) (Q m (U j)) := by
    have hc := QuasiEquisingularUniformComparison.eventually_moreSingularOn_scaled_term
      hu hw (t m).property.1 (t m).property.2 j
    filter_upwards [hc] with l hl
    have hab : SourcePOrder (n := k) (U l).val (W l).val :=
      sourcePOrder_of_moreSingularOn omegaV β.form β.form (hU l) (hW l)
        (MoreSingularOn.of_le fun y _ => horder l y)
    have hmore : MoreSingularOn (W l).val (Q m (U j)).val univ := by
      rw [hQval]
      obtain ⟨C, hC⟩ := hl
      exact ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩
    have hbc : SourcePOrder (n := k) (W l).val (Q m (U j)).val :=
      sourcePOrder_of_moreSingularOn omegaV β.form β.form (hW l) (Q m (U j)).property hmore
    exact dist_le_of_sourcePOrder_chain omegaV β (U l) (W l) (Q m (U j)) hab hbc
  have hdist : dist A B = 0 :=
    MetricIteratedComparisonLimit.dist_eq_zero_of_iterated_comparison hUA hWB Q hQ hQA hbound
  obtain ⟨r, _, _, _, hr⟩ := exists_tendsto_singularityDistance omegaV β.form
    (isBigClass_kahler β) A.property B.property
  rw [dist_eq_singularityDistance_toReal omegaV β.form (isBigClass_kahler β),
    hr, EReal.toReal_coe] at hdist
  rw [hr, hdist, EReal.coe_zero]

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularNativeRestrictionComparison
