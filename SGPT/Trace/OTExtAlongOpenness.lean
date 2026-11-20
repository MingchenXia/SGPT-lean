import SGPT.Trace.TwistedL2OTExtStatement
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra
import SGPT.Foundations.Analysis.Pending.StrongOpennessSliceInduction
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction

/-!
# Uniform strong openness for sections along a compact submanifold

Blueprint `claude-ot2.tex`, nodes `claude-ot2:germ-calculus`, `claude-ot2:uniform-openness`.

The proof of `thm:OT_ext_global` (`chapter_trace.tex` 527--558) begins with: *"By
`thm:strongopen`, there exists `ε ∈ (0, ε₀)` such that
`s ∈ H⁰(Y, T|_Y ⊗ L|_Y^k ⊗ 𝓘(k(1+ε) Tr^θ_Y(φ)))`."*  Strong openness is a statement about one
germ at one point; the book's `ε` has to work at every point of `Y` at once.  This file proves
that uniform version on a compact complex manifold, for the coefficients of a section of a
holomorphic line bundle along a submanifold (`IsAlongMultiplierSection`), whose preferred frame
changes from point to point.

## Results

* `mem_multiplierIdeal_congr`, `mem_multiplierIdeal_mul`, `mem_multiplierIdeal_of_exponent_le`:
  germ calculus of `𝓘(c u)` (eventual equality, multiplication by a holomorphic germ, monotonicity
  in the exponent for quasi-psh `u`);
* `eventually_mem_multiplierIdeal`: the set of points at which a fixed holomorphic function lies
  in `𝓘(c u)` is open (`u` `θ`-psh);
* `exists_gt_forall_mem_of_frames`: uniform strong openness on a compact manifold for a family of
  germs related by holomorphic frame changes;
* `alongCoefficient_eventuallyEq_mul`: the coefficients of a section along `W` in two holomorphic
  frames differ by a holomorphic factor;
* `IsAlongMultiplierSection.exists_gt`: the book's `ε` (uniform strong openness along `W`);
* `IsAlongMultiplierSection.of_le`: sections along `W` with values in a smaller multiplier ideal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Trace.TwistedL2

/-! ### Germ calculus of multiplier ideals -/

section Germ

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- Membership in `𝓘(c u)` depends only on the germ. -/
theorem mem_multiplierIdeal_congr {c : ℝ} {u : Z → EReal} {p : Z} {g g' : Z → ℂ}
    (hg : (multiplierIdeal (n := k) c u).mem p g) (h : g =ᶠ[𝓝 p] g') :
    (multiplierIdeal (n := k) c u).mem p g' := by
  obtain ⟨hhol, hint⟩ := hg
  refine ⟨hhol.congr h, hint.congr (EventuallyEq.refl _ _) ?_⟩
  set e := complexChartAt (n := k) p
  have hT : Tendsto e.val.symm (𝓝 (e.val p)) (𝓝 p) := by
    have := e.val.continuousAt_symm (e.val.map_source (mem_complexChartAt_source p))
    rwa [ContinuousAt, e.val.left_inv (mem_complexChartAt_source p)] at this
  exact hT.eventually h

/-- `𝓘(c u)` is an ideal: it is stable under multiplication by holomorphic germs. -/
theorem mem_multiplierIdeal_mul {c : ℝ} {u : Z → EReal} {p : Z} {g h : Z → ℂ}
    (hg : (multiplierIdeal (n := k) c u).mem p g) (hh : HolomorphicAt k h p) :
    (multiplierIdeal (n := k) c u).mem p (fun q => h q * g q) := by
  obtain ⟨hghol, hint⟩ := hg
  refine ⟨hh.mul hghol, ?_⟩
  have hd := CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel k) p) hh
  exact multiplierIntegrableAt_differentiable_mul hint hd

/-- For quasi-psh `u`, `𝓘(d u) ⊆ 𝓘(c u)` when `0 < c ≤ d`. -/
theorem mem_multiplierIdeal_of_exponent_le {c d : ℝ} {u : Z → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u) (hc : 0 < c) (hcd : c ≤ d) {p : Z}
    {g : Z → ℂ} (hg : (multiplierIdeal (n := k) d u).mem p g) :
    (multiplierIdeal (n := k) c u).mem p g := by
  set e := complexChartAt (n := k) p
  have hz : e.val p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source p)
  exact ⟨hg.1, multiplierIntegrableAt_of_exponent_le (hu e (e.val p) hz) hc hcd hg.2⟩

/-- **Openness.**  For a `θ`-psh `u`, the set of points at which a fixed function lies in
`𝓘(c u)` is open. -/
theorem eventually_mem_multiplierIdeal {θ : SmoothRealForm k Z 2} {u : Z → EReal}
    (hu : ThetaPlurisubharmonic θ u) {c : ℝ} (hc : 0 < c) {p : Z} {g : Z → ℂ}
    (hg : (multiplierIdeal (n := k) c u).mem p g) :
    ∀ᶠ q in 𝓝 p, (multiplierIdeal (n := k) c u).mem q g := by
  obtain ⟨_, hint⟩ := hg
  set e := complexChartAt (n := k) p
  obtain ⟨-, U, hU, hpU, hdiff, hL2⟩ := hint
  have hsrc : e.val.source ∈ 𝓝 p := e.val.open_source.mem_nhds (mem_complexChartAt_source p)
  have hpre : ∀ᶠ q in 𝓝 p, e.val q ∈ U :=
    (e.val.continuousAt (mem_complexChartAt_source p)).eventually (hU.mem_nhds hpU)
  filter_upwards [hsrc, hpre] with q hq hqU
  have hG0 : MultiplierIntegrableAt (chartFunction u e) c (fun z => g (e.val.symm z)) (e.val q)
      volume := ⟨hc, U, hU, hqU, hdiff, hL2⟩
  have hG : MultiplierIntegrableAt (fun w => chartFunction u e w + (((fun _ => (0 : ℝ)) w : ℝ) :
      EReal)) c (fun z => g (e.val.symm z)) (e.val q) volume := by
    simpa only [EReal.coe_zero, add_zero] using hG0
  have hmem := DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hu hc e
    e.val.open_target continuousOn_const hq (e.val.map_source hq) hG
  refine mem_multiplierIdeal_congr hmem ?_
  filter_upwards [e.val.open_source.mem_nhds hq] with r hr
  simp only [e.val.left_inv hr]

/-- **Uniform strong openness on a compact manifold.**  Let `G p` be a germ at `p` of `𝓘(c u)`
for every `p`, such that near every `p` the germs `G q` are holomorphic multiples of `G p`
(frame changes).  Then one exponent `c' > c` works at every point. -/
theorem exists_gt_forall_mem_of_frames [CompactSpace Z] {θ : SmoothRealForm k Z 2}
    {u : Z → EReal} (hu : ThetaPlurisubharmonic θ u) {c : ℝ} (hc : 0 < c) (G : Z → Z → ℂ)
    (hG : ∀ p, (multiplierIdeal (n := k) c u).mem p (G p))
    (hframe : ∀ p, ∀ᶠ q in 𝓝 p, ∃ h : Z → ℂ, HolomorphicAt k h q ∧
      G q =ᶠ[𝓝 q] fun r => h r * G p r) :
    ∃ c' : ℝ, c < c' ∧ ∀ p, (multiplierIdeal (n := k) c' u).mem p (G p) := by
  have hq := hu.quasiPlurisubharmonic
  choose cp hcp hmemp using fun p => PositiveCurrentTraceMultiplier.exists_gt_mem_multiplierIdeal
    hq (hG p)
  -- near `p`, every `G q` lies in `𝓘(c_p u)`
  have hnbhd : ∀ p, ∀ᶠ q in 𝓝 p, (multiplierIdeal (n := k) (cp p) u).mem q (G q) := by
    intro p
    filter_upwards [eventually_mem_multiplierIdeal hu (hc.trans (hcp p)) (hmemp p), hframe p]
      with q hqmem hqframe
    obtain ⟨h, hh, heq⟩ := hqframe
    exact mem_multiplierIdeal_congr (mem_multiplierIdeal_mul hqmem hh) heq.symm
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover' (fun p _ => {q | (multiplierIdeal (n := k)
    (cp p) u).mem q (G q)}) (fun p _ => hnbhd p)
  by_cases hne : t.Nonempty
  · obtain ⟨p₀, hp₀t, hmin⟩ := t.exists_min_image (fun p => cp p.val) hne
    refine ⟨cp p₀.val, hcp p₀.val, fun q => ?_⟩
    have hqmem := ht (mem_univ q)
    simp only [mem_iUnion] at hqmem
    obtain ⟨p, hpt, hqp⟩ := hqmem
    exact mem_multiplierIdeal_of_exponent_le hq (hc.trans (hcp p₀.val)) (hmin p hpt) hqp
  · refine ⟨c + 1, by linarith, fun q => ?_⟩
    have hqmem := ht (mem_univ q)
    simp only [mem_iUnion] at hqmem
    obtain ⟨p, hpt, -⟩ := hqmem
    exact absurd ⟨p, hpt⟩ hne

end Germ

/-! ### Frames along a submanifold -/

section Along

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]
  {W : Set X} [ChartedSpace (ComplexModel m) W] [IsComplexManifold m W]

/-- **Frame change along `W`.**  If the inclusion `W → X` is holomorphic, then near every point
`y` of `W` the coefficient of a section of `V|_W` in the preferred frame at `y` is a holomorphic
multiple of its coefficient in the preferred frame at a nearby base point `y₀`. -/
theorem alongCoefficient_eventuallyEq_mul
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    (s : (y : W) → V y) (y₀ : W) :
    ∀ᶠ y in 𝓝 y₀, ∃ h : W → ℂ, HolomorphicAt m h y ∧
      alongCoefficient V (trivializationAt ℂ V y.val) s =ᶠ[𝓝 y]
        fun w => h w * alongCoefficient V (trivializationAt ℂ V y₀.val) s w := by
  set e := trivializationAt ℂ V y₀.val with he
  have hbase : ∀ᶠ y in 𝓝 y₀, y.val ∈ e.baseSet :=
    hι.continuous.continuousAt.eventually
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ V y₀.val))
  filter_upwards [hbase] with y hy
  set e' := trivializationAt ℂ V y.val with he'
  set O : Set W := Subtype.val ⁻¹' (e.baseSet ∩ e'.baseSet) with hO
  have hOopen : IsOpen O :=
    (e.open_baseSet.inter e'.open_baseSet).preimage hι.continuous
  have hyO : y ∈ O := ⟨hy, mem_baseSet_trivializationAt ℂ V y.val⟩
  set h : W → ℂ := fun w => (e.coordChangeL ℂ e' w.val) 1 with hh
  refine ⟨h, ?_, ?_⟩
  · -- holomorphy of the transition function
    have hcc : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
        (fun b : X => (e.coordChangeL ℂ e' b : ℂ →L[ℂ] ℂ)) (e.baseSet ∩ e'.baseSet) :=
      ContMDiffVectorBundle.contMDiffOn_coordChangeL e e'
    have hcc1 : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
        (fun b : X => (e.coordChangeL ℂ e' b : ℂ →L[ℂ] ℂ) 1) (e.baseSet ∩ e'.baseSet) :=
      hcc.clm_apply contMDiffOn_const
    have hW : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) ∞ h O :=
      hcc1.comp hι.contMDiffOn (fun w hw => hw)
    filter_upwards [hOopen.mem_nhds hyO] with w hw
    exact (hW.contMDiffAt (hOopen.mem_nhds hw)).mdifferentiableAt (by simp)
  · filter_upwards [hOopen.mem_nhds hyO] with w hw
    have hlin : ∀ z : ℂ, e.coordChangeL ℂ e' w.val z = e.coordChangeL ℂ e' w.val 1 * z := by
      intro z
      have := (e.coordChangeL ℂ e' w.val).map_smul z 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      rw [this, mul_comm]
    simp only [alongCoefficient, hh]
    rw [← hlin, e.coordChangeL_apply e' hw, e.symm_apply_apply_mk hw.1]

/-- **Uniform strong openness along a compact submanifold** (the `ε` of the book's proof of
`thm:OT_ext_global`): if `s ∈ H⁰(W, V|_W ⊗ 𝓘(c u))` with `u` `θ`-psh on the compact `W` and
`c > 0`, then `s ∈ H⁰(W, V|_W ⊗ 𝓘(c' u))` for some `c' > c`. -/
theorem IsAlongMultiplierSection.exists_gt [CompactSpace W]
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    {θ : SmoothRealForm m W 2} {u : W → EReal} (hu : ThetaPlurisubharmonic θ u) {c : ℝ}
    (hc : 0 < c) {s : (y : W) → V y} (hs : IsAlongMultiplierSection V (m := m) c u s) :
    ∃ c' : ℝ, c < c' ∧ IsAlongMultiplierSection V (m := m) c' u s := by
  have hscale : ∀ {a : ℝ}, 0 < a → ∀ (y : W) (g : W → ℂ),
      (multiplierIdeal (n := m) 1 (fun w => (a : EReal) * u w)).mem y g ↔
        (multiplierIdeal (n := m) a u).mem y g := by
    intro a ha y g
    exact and_congr_right fun _ =>
      (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff _ ha _ _ _)
  obtain ⟨c', hcc', hall⟩ := exists_gt_forall_mem_of_frames hu hc
    (fun y => alongCoefficient V (trivializationAt ℂ V y.val) s)
    (fun y => (hscale hc y _).mp (hs y))
    (fun y₀ => alongCoefficient_eventuallyEq_mul V hι s y₀)
  exact ⟨c', hcc', fun y => (hscale (hc.trans hcc') y _).mpr (hall y)⟩

/-- Sections along `W` with values in `𝓘(c u)` have values in every larger ideal sheaf
`𝓘(c' u')`. -/
theorem IsAlongMultiplierSection.of_le {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    {u u' : W → EReal}
    (hle : (multiplierIdeal (n := m) c u).Le (multiplierIdeal (n := m) c' u'))
    {s : (y : W) → V y} (hs : IsAlongMultiplierSection V (m := m) c u s) :
    IsAlongMultiplierSection V (m := m) c' u' s := by
  intro y
  have h1 := (and_congr_right fun _ =>
    (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff _ hc _ _ _)).mp
    (hs y)
  exact (and_congr_right fun _ =>
    (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff _ hc' _ _ _)).mpr
    (hle y _ h1)

end Along

end SGPT.Trace.OTExt
