import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIdealOrderTailComparison
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularMaximum
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-! # Actual full QEA maximum for two different potentials -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularTwoPotentialMaximum

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation
  FirstPass.IEnvelope

noncomputable section

/-- A new genuine full approximation of the maximum target and natural ideal
orders internally produce every strict multiplier clause for two distinct limits. -/
theorem eventually_multiplierIdealIncluded_max_two_potentials
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ v δ vSeq)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ k in atTop, MultiplierIdealIncluded (n := n)
      (fun x => max (uSeq k x) (vSeq k x)) d (fun x => max (u x) (v x)) c := by
  have hw : IsThetaPshPotential θ.val (fun x => max (u x) (v x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu.target hv.target
  obtain ⟨η, wSeq, hwSeq⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hw
  have hUorder : IOrderOnManifold (n := n) u (fun x => max (u x) (v x)) :=
    iOrderOnManifold_of_le hw.1.quasiPlurisubharmonic (fun x => le_max_left _ _)
  have hVorder : IOrderOnManifold (n := n) v (fun x => max (u x) (v x)) :=
    iOrderOnManifold_of_le hw.1.quasiPlurisubharmonic (fun x => le_max_right _ _)
  have hd : 0 < d := hc.trans hcd
  let s : ℝ := (c + d) / (2 * d)
  have hs0 : 0 < s := div_pos (add_pos hc hd) (mul_pos (by norm_num) hd)
  have hs1 : s < 1 := (div_lt_one (mul_pos (by norm_num) hd)).mpr (by linarith)
  have hds : d * s = (c + d) / 2 := by
    dsimp only [s]
    field_simp
  have hcds : c < d * s := by rw [hds]; linarith
  let a : ℝ := 1 - s
  have ha0 : 0 < a := sub_pos.mpr hs1
  have ha1 : a < 1 := by dsimp only [a]; linarith
  have hsa : 1 - a = s := by dsimp only [a]; ring
  obtain ⟨j, hj⟩ := eventually_atTop.mp (hwSeq.eventually_multiplierIdealIncluded hc hcds)
  have hjJ := hj j le_rfl
  have hUcomp : ∀ᶠ k in atTop, MoreSingularOn (uSeq k)
      (fun x => (s : EReal) * wSeq j x) univ := by
    simpa only [hsa] using
      QuasiEquisingularIdealOrderTailComparison.eventually_moreSingularOn_scaled_term_of_iOrder
        hwSeq hu hUorder ha0 ha1 j
  have hVcomp : ∀ᶠ k in atTop, MoreSingularOn (vSeq k)
      (fun x => (s : EReal) * wSeq j x) univ := by
    simpa only [hsa] using
      QuasiEquisingularIdealOrderTailComparison.eventually_moreSingularOn_scaled_term_of_iOrder
        hwSeq hv hVorder ha0 ha1 j
  have hscaled : ManifoldQuasiPlurisubharmonic (n := n)
      (fun x => (s : EReal) * wSeq j x) :=
    (GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hs0 (hwSeq.term j).1).quasiPlurisubharmonic
  filter_upwards [hUcomp, hVcomp] with k hUk hVk
  obtain ⟨C, hC⟩ := hUk
  obtain ⟨D, hD⟩ := hVk
  have hbound (x : M) : max (uSeq k x) (vSeq k x) ≤
      (s : EReal) * wSeq j x + ((max C D : ℝ) : EReal) := by
    exact max_le
      ((hC x (mem_univ x)).trans (add_le_add le_rfl
        (EReal.coe_le_coe_iff.mpr (le_max_left C D))))
      ((hD x (mem_univ x)).trans (add_le_add le_rfl
        (EReal.coe_le_coe_iff.mpr (le_max_right C D))))
  have hI := iOrderOnManifold_of_le_add hscaled hbound
  intro e z hz f hf hi
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hiS : MultiplierIntegrableAt
      (fun w => (s : EReal) * chartFunction (wSeq j) e w) d f z volume :=
    hI d hd e z hz f hf hi
  have hiJ : MultiplierIntegrableAt (chartFunction (wSeq j) e) (d * s) f z volume :=
    (PositiveCurrentTraceMultiplier.multiplierIntegrableAt_coe_mul_iff hd hs0).mp hiS
  exact hjJ e z hz f hf hiJ

/-- The true maximum, with the maximum of the actual errors, satisfies the
complete genuine approximation predicate. -/
theorem isQuasiEquisingularApproximation_max_two_potentials
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ v δ vSeq) :
    IsQuasiEquisingularApproximation omega θ (fun x => max (u x) (v x))
      (fun k => max (ε k) (δ k))
      (fun k x => max (uSeq k x) (vSeq k x)) := by
  have herror : NonnegativeDecreasesToZero (fun k => max (ε k) (δ k)) := by
    refine ⟨fun k => le_max_of_le_left (hu.error_nonneg k),
      fun i j hij => max_le_max (hu.error_antitone hij) (hv.error_antitone hij), ?_⟩
    simpa only [max_self] using hu.error_tendsto.max hv.error_tendsto
  have hu' := QuasiEquisingularComparison.IsQuasiEquisingularApproximation.mono_error
    hu herror fun k => le_max_left _ _
  have hv' := QuasiEquisingularComparison.IsQuasiEquisingularApproximation.mono_error
    hv herror fun k => le_max_right _ _
  refine ⟨SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu.target hv.target, herror, fun k =>
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
      (hu'.term k) (hv'.term k), ?_, ?_, ?_⟩
  · intro k e z hz
    exact RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max
      (hu.term_hasAnalyticSingularityType k e z hz)
      (hv.term_hasAnalyticSingularityType k e z hz)
  · refine ⟨fun x i j hij => max_le_max (hu.term_antitone x hij) (hv.term_antitone x hij),
      fun x => ?_⟩
    exact (hu.term_tendsto x).max (hv.term_tendsto x)
  · intro c d hc hcd
    exact eventually_multiplierIdealIncluded_max_two_potentials hu hv hc hcd

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularTwoPotentialMaximum
