import SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformComparison

set_option autoImplicit false

/-! # Actual ideal-ordered limits supply scaled analytic full-QEA tail comparisons -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularIdealOrderTailComparison

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation
  FirstPass.HolomorphicIdealSheaves FirstPass.IEnvelope

noncomputable section

private theorem scaled_comparison_dim_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] [CompactSpace M]
    {θ ζ : SmoothRealForm 0 M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential ζ v) (a : ℝ) :
    MoreSingularOn v (fun x => (a : EReal) * u x) univ := by
  apply IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt
  intro x
  have hux : u x = ((u x).toReal : EReal) :=
    (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x)
      (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hu x)).symm
  have hvx : v x = ((v x).toReal : EReal) :=
    (EReal.coe_toReal (hv.1.quasiPlurisubharmonic.ne_top x)
      (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hv x)).symm
  refine ⟨(v x).toReal - a * (u x).toReal,
    eventually_of_mem ((FiniteGeodesicsFullMassAnyDim.isOpen_singleton_of_dim_zero x).mem_nhds
      (mem_singleton x)) ?_⟩
  intro y hy
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  dsimp only
  rw [hux, hvx, ← EReal.coe_mul, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  simp only [EReal.toReal_coe]
  ring_nf
  exact le_rfl

/-- A natural ideal order between the literal limits is inserted between
the actual full-QEA multiplier clause and the fixed analytic term's bounded ideal. -/
theorem eventually_moreSingularOn_scaled_term_of_iOrder
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {omega₀ omega₁ : KahlerBackground n M} {θ₀ θ₁ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {U V : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega₀ θ₀ u ε U)
    (hv : IsQuasiEquisingularApproximation omega₁ θ₁ v δ V)
    (horder : IOrderOnManifold (n := n) v u)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ∀ᶠ k in atTop, MoreSingularOn (V k)
      (fun x => ((1 - a : ℝ) : EReal) * U j x) univ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Eventually.of_forall fun k =>
      scaled_comparison_dim_zero (hu.term j) (hv.term k) (1 - a)
  · obtain ⟨R, hR, hgap⟩ :=
      CompactAnalyticBoundedMultiplierInclusion.exists_pos_uniform_bounded_multiplier_gap
        (hu.term_hasAnalyticSingularityType j)
    obtain ⟨m, hmgt⟩ := exists_nat_gt (2 * R / a)
    have hmR : (0 : ℝ) < m := (div_pos (mul_pos (by norm_num) hR) ha0).trans hmgt
    have hm : 0 < m := by exact_mod_cast hmR
    have hscale : 2 * R < (m : ℝ) * a := (div_lt_iff₀ ha0).mp hmgt
    let p : ℝ := (1 - a) * m
    let q : ℝ := (1 - a / 2) * m
    have hp : 0 < p := mul_pos (sub_pos.mpr ha1) hmR
    have hq : 0 < q := mul_pos (by linarith) hmR
    have hqm : q < m := by dsimp only [q]; nlinarith
    have hqgap : p + R ≤ q := by dsimp only [p, q]; nlinarith
    have hle : u ≤ U j := fun x =>
      (hu.term_antitone x).le_of_tendsto (hu.term_tendsto x) j
    have hI : (multiplierIdeal (n := n) q u).Le (multiplierIdeal (n := n) q (U j)) :=
      PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
        (iOrderOnManifold_of_le (hu.term j).1.quasiPlurisubharmonic hle) hq
    have hVu : (multiplierIdeal (n := n) q v).Le (multiplierIdeal (n := n) q u) :=
      PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold horder hq
    have hB := hgap p hp q hqgap
    have hpm : p / (m : ℝ) = 1 - a := by
      dsimp only [p]
      exact mul_div_cancel_right₀ (1 - a) hmR.ne'
    filter_upwards [hv.eventually_multiplierIdealIncluded hq hqm] with k hk
    have hK := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded hk
    have hKB : (multiplierIdeal (n := n) (m : ℝ) (V k)).Le
        (AnalyticBoundedMultiplierIdeal.boundedMultiplierIdeal (n := n)
          (fun x => (p : EReal) * U j x)) :=
      fun x f hf => hB x f (hI x f (hVu x f (hK x f hf)))
    have hcomp :=
      BoundedMultiplierPotentialComparison.moreSingularOn_of_multiplierIdeal_le_boundedMultiplierIdeal
        hn (hv.term k) hm hKB
    simpa only [hpm] using hcomp

/-- Genuine antitonicity gives one actual constant on the whole produced tail. -/
theorem exists_uniform_tail_comparison_of_iOrder
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {omega₀ omega₁ : KahlerBackground n M} {θ₀ θ₁ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {U V : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega₀ θ₀ u ε U)
    (hv : IsQuasiEquisingularApproximation omega₁ θ₁ v δ V)
    (horder : IOrderOnManifold (n := n) v u)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    ∃ k₀ : ℕ, ∃ C : ℝ, ∀ k ≥ k₀, ∀ x : M,
      V k x ≤ ((1 - a : ℝ) : EReal) * U j x + (C : EReal) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    (eventually_moreSingularOn_scaled_term_of_iOrder hu hv horder ha0 ha1 j)
  obtain ⟨C, hC⟩ := hk₀ k₀ le_rfl
  exact ⟨k₀, C, fun k hk x => (hv.term_antitone x hk).trans (hC x (mem_univ x))⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularIdealOrderTailComparison
