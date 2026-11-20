import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities

set_option autoImplicit false

/-!
# Analytic singularities are two-sided bounded off their poles

Xia's Lemma 2.4.1 (`xia-sgpt:page-0074`) reads: for a big class `{theta}`, the
canonical reference `V_theta` is *locally bounded* on `X \ nK({theta})`.  Its
mechanism is Boucksom's theorem — `nK({theta})` is the polar set of a Kähler
current with analytic singularities — plus the elementary fact proved here: a
potential with a logarithmic presentation

  `u = c log (|f_1|^2 + ... + |f_N|^2) + b`,   `c > 0`, `b` bounded,

is bounded *both ways* on a neighbourhood of every point that is not a common
zero of the generators.  Above, because the generators are continuous; below,
because at a non-zero the sum of squares stays away from `0`.

`Pending.PatchBoundedNeighborhood.diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_reference_offPoles`
asks for exactly the conclusion in the form
`∀ x, psi x ≠ ⊥ → ∃ N ∈ 𝓝 x, IsBoundedPotentialOn psi N`, so this module is the
second of the two inputs that reduce Xia's Corollary 2.4.4 to Boucksom.

Nothing here is about `theta`: the statements are properties of a presentation,
so they hold for any potential with chartwise analytic singularity type.

The *lower* half of the model statement is the computation inlined at
`Pending.NoIsolatedPoints`:182-203; what is new here is that the same
neighbourhood also bounds the germ from ABOVE, and that the result is available
as a reusable lemma in manifold form.
-/

open Set Filter
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound

open FirstPass
open FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

noncomputable section

/-! ### The local statement, in the model space -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The sum of squared moduli of a finite holomorphic family is continuous at
each point of the family's common domain of definition. -/
theorem continuousAt_generatorNormSq {N : ℕ} {f : Fin N → E → ℂ} {x : E}
    (hf : HolomorphicGeneratorsAt f x) : ContinuousAt (generatorNormSq f) x := by
  obtain ⟨U, hUo, hxU, hdiff⟩ := hf
  have hcont : ∀ j, ContinuousAt (f j) x := fun j =>
    ((hdiff j).continuousOn.continuousWithinAt hxU).continuousAt (hUo.mem_nhds hxU)
  have hsum : ContinuousAt (fun y => ∑ j, ‖f j y‖ ^ 2) x :=
    tendsto_finsetSum _ (fun j _ => ((hcont j).norm.pow 2))
  exact hsum

/-- **A logarithmic presentation is two-sided bounded near any non-pole.**  At a
point where the generators do not all vanish, `∑ |f_j|²` is continuous and
positive, so its logarithm is bounded above and below on a neighbourhood; the
remainder is bounded by hypothesis. -/
theorem LogarithmicTypeAt.eventually_bounded {u : E → EReal} {c : ℝ} {N : ℕ}
    {f : Fin N → E → ℂ} {x : E} (hu : LogarithmicTypeAt u c f x) (hx : u x ≠ ⊥) :
    ∃ a b : ℝ, ∀ᶠ y in 𝓝 x, (a : EReal) ≤ u y ∧ u y ≤ (b : EReal) := by
  obtain ⟨hc, hgen, r, ⟨C, hC0, hCr⟩, heq⟩ := id hu
  -- the generators do not all vanish at `x`
  have hxf : ¬ ∀ j, f j x = 0 := fun h => hx (LogarithmicTypeAt.eq_bot_iff hu |>.mpr h)
  have hpos : 0 < generatorNormSq f x := by
    obtain ⟨j, hj⟩ := not_forall.mp hxf
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun k => ‖f k x‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j))
    positivity
  set g : E → ℝ := generatorNormSq f with hg
  have hgc : ContinuousAt g x := continuousAt_generatorNormSq hgen
  have hlow : ∀ᶠ y in 𝓝 x, g x / 2 < g y :=
    continuousAt_const.eventually_lt hgc (by linarith)
  have hhigh : ∀ᶠ y in 𝓝 x, g y < g x + 1 :=
    hgc.eventually_lt continuousAt_const (by linarith)
  refine ⟨c * Real.log (g x / 2) - C, c * Real.log (g x + 1) + C, ?_⟩
  filter_upwards [heq, hCr, hlow, hhigh] with y hy hyC hylow hyhigh
  -- at `y` the generators do not all vanish either
  have hgy : 0 < g y := lt_trans (by linarith) hylow
  have hne : ∃ j, f j y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact absurd (by simp [hg, generatorNormSq, hcon] : g y = 0) (ne_of_gt hgy)
  have hlog : generatorLog f y = ((Real.log (g y) : ℝ) : EReal) :=
    generatorLog_of_nonzero hne
  have hval : u y = ((c * Real.log (g y) + r y : ℝ) : EReal) := by
    rw [hy, hlog, ← EReal.coe_mul, ← EReal.coe_add]
  obtain ⟨hr1, hr2⟩ := abs_le.mp hyC
  have hmono1 : Real.log (g x / 2) ≤ Real.log (g y) :=
    Real.log_le_log (by linarith) hylow.le
  have hmono2 : Real.log (g y) ≤ Real.log (g x + 1) :=
    Real.log_le_log hgy hyhigh.le
  rw [hval]
  constructor
  · exact EReal.coe_le_coe_iff.mpr (by nlinarith [mul_le_mul_of_nonneg_left hmono1 hc.le])
  · exact EReal.coe_le_coe_iff.mpr (by nlinarith [mul_le_mul_of_nonneg_left hmono2 hc.le])

/-- The same conclusion from the rational-coefficient convention. -/
theorem HasAnalyticSingularityTypeAt.eventually_bounded {u : E → EReal} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (hx : u x ≠ ⊥) :
    ∃ a b : ℝ, ∀ᶠ y in 𝓝 x, (a : EReal) ≤ u y ∧ u y ≤ (b : EReal) := by
  obtain ⟨c, N, f, hpres⟩ := hu
  exact LogarithmicTypeAt.eventually_bounded hpres hx

end Model

/-! ### The manifold statement -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A potential with global analytic singularities is locally two-sided bounded
away from its poles.  This is the same elementary logarithmic estimate as the
chartwise version below, stated directly in the coherent-ideal convention. -/
theorem exists_isBoundedPotentialOn_of_hasAnalyticSingularities {u : M → EReal}
    (hu : HasAnalyticSingularities (n := n) u) {x : M} (hx : u x ≠ ⊥) :
    ∃ N ∈ 𝓝 x, IsBoundedPotentialOn u N := by
  obtain ⟨c, 𝔞, hc, -, hloc⟩ := hu
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  obtain ⟨U, hUo, hxU, N, g, hgdiff, -, R, C, hRC, hrep⟩ := hloc x
  have hxg : ¬ ∀ j, g j x = 0 := fun h => hx (by
    rw [hrep x hxU]
    exact (scaled_generatorLog_add_eq_bot_iff g x hcR (R x)).mpr h)
  have hpos : 0 < generatorNormSq g x := by
    obtain ⟨j, hj⟩ := not_forall.mp hxg
    refine lt_of_lt_of_le (by positivity) (Finset.single_le_sum
      (f := fun i => ‖g i x‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hcont : ContinuousAt (generatorNormSq g) x := by
    unfold generatorNormSq
    exact tendsto_finsetSum _ fun j _ =>
      (((hgdiff j).continuousOn.continuousAt (hUo.mem_nhds hxU)).norm).pow 2
  have hlow : ∀ᶠ y in 𝓝 x, generatorNormSq g x / 2 < generatorNormSq g y :=
    hcont.eventually (lt_mem_nhds (half_lt_self hpos))
  have hhigh : ∀ᶠ y in 𝓝 x, generatorNormSq g y < generatorNormSq g x + 1 :=
    hcont.eventually_lt continuousAt_const (by linarith)
  refine ⟨U ∩ {y | generatorNormSq g x / 2 < generatorNormSq g y} ∩
      {y | generatorNormSq g y < generatorNormSq g x + 1},
    Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds hxU) hlow) hhigh,
    (c : ℝ) * Real.log (generatorNormSq g x / 2) - C,
    (c : ℝ) * Real.log (generatorNormSq g x + 1) + C, ?_⟩
  intro y hy
  have hypos : 0 < generatorNormSq g y := (half_pos hpos).trans hy.1.2
  have hyg : ∃ j, g j y ≠ 0 := by
    by_contra! h
    simp [generatorNormSq, h] at hypos
  have hval : u y = ((c : ℝ) : EReal) * generatorLog g y + (R y : EReal) :=
    hrep y hy.1.1
  have hlog : generatorLog g y = ((Real.log (generatorNormSq g y) : ℝ) : EReal) :=
    generatorLog_of_nonzero hyg
  obtain ⟨hRlow, hRhigh⟩ := abs_le.mp (hRC y hy.1.1)
  rw [hval, hlog, ← EReal.coe_mul, ← EReal.coe_add]
  constructor
  · apply EReal.coe_le_coe_iff.mpr
    have hloglow : Real.log (generatorNormSq g x / 2) ≤ Real.log (generatorNormSq g y) :=
      Real.log_le_log (half_pos hpos) hy.1.2.le
    nlinarith [mul_le_mul_of_nonneg_left hloglow hcR.le]
  · apply EReal.coe_le_coe_iff.mpr
    have hloghigh : Real.log (generatorNormSq g y) ≤ Real.log (generatorNormSq g x + 1) :=
      Real.log_le_log hypos hy.2.le
    nlinarith [mul_le_mul_of_nonneg_left hloghigh hcR.le]

omit [IsComplexManifold n M] in
/-- **A potential with chartwise analytic singularity type is locally bounded
off its poles.**  This is the analytic content of Xia's Lemma 2.4.1 once
Boucksom's theorem has supplied the presentation. -/
theorem exists_isBoundedPotentialOn_of_analyticSingularityType {u : M → EReal}
    (hu : FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType
      (n := n) u)
    {x : M} (hx : u x ≠ ⊥) :
    ∃ N ∈ 𝓝 x, IsBoundedPotentialOn u N := by
  classical
  set e := complexChartAt (n := n) x with he
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxsrc
  have hchart : chartFunction u e (e.val x) = u x := by
    simp only [chartFunction, e.val.left_inv hxsrc]
  have hne : chartFunction u e (e.val x) ≠ ⊥ := by rw [hchart]; exact hx
  obtain ⟨a, b, hab⟩ :=
    HasAnalyticSingularityTypeAt.eventually_bounded (hu e (e.val x) hz) hne
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hab
  refine ⟨e.val.source ∩ e.val ⁻¹' V, ?_, a, b, ?_⟩
  · exact Filter.inter_mem (e.val.open_source.mem_nhds hxsrc)
      (e.val.continuousAt hxsrc (hVopen.mem_nhds hVmem))
  · intro y hy
    have hyval : chartFunction u e (e.val y) = u y := by
      simp only [chartFunction, e.val.left_inv hy.1]
    have hmem := hVsub hy.2
    simp only [Set.mem_ofPred_eq] at hmem
    rwa [hyval] at hmem

end Manifold

end

end SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound
