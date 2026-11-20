import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.AnalyticGluingProof
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false

/-!
# The non-Kähler locus has no isolated points

Source: Copy-4, `lem:no-isolated-points` (`transcendental-nakamaye-copy4-20260911`),
extracted from the proof of CT15, Lemma 3.1; blueprint `ana:no-isolated-points`.

The non-Kähler locus of a big class on a connected compact Kähler manifold has no
isolated points: every point of `E_nK(α)` is an accumulation point of `E_nK(α)`
(`AccPt x (𝓟 E_nK(α))`).

The hypothesis `0 < n` is essential in this encoding: in dimension zero Lelong
numbers are `⊤`, so `E_nK(α)` is the whole one-point manifold, whose point is
isolated.

## Proof

Suppose `x` is isolated in `E_nK(α)`.  Boucksom's theorem
(`LocusProperties.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`) gives a Kähler
current `T = θ + ddᶜφ_G ≥ ω₀` with analytic singularities whose polar set is
exactly `E_nK(α)`; in particular `φ_G(x) = -∞`.

*The local branch.*  In the chart at `x`, `θ - ω₀` has a smooth local potential
`ρ` (part of the theta-PSH data of `T`).  Cut it off to a chart-smooth function
`ψ` on the manifold (`ChartPartition.chartExtend`) which equals `ρ` near `x`.  The
global form `ddᶜψ` (`SmoothDDCForm.ddcForm`) agrees with `θ - ω₀` near `x` in the
chart at `x`, hence, by the transformation law of both forms, in EVERY chart
(`coeff_eq_of_coeff_eq_chartTransition`).  So `ψ` itself is a smooth local
potential of `θ - ω₀` in every chart near `x`, and `φ_U := -ψ` satisfies
`φ_U + ψ = 0`, which is plurisubharmonic: `θ + ddᶜφ_U = ω₀` near `x`.  No
quadratic term `A|z|²` is needed.

*The collar.*  Choose open `U₁ ⋐ U₂` around `x` inside the neighbourhood where
`φ_U` is defined and `x` is the only point of `E_nK(α)`.  On the compact collar
`closure U₂ \ U₁` the potential `φ_G` has no poles, so, having analytic
singularities, it is bounded below (`exists_lowerBound_of_hasAnalyticSingularities`),
while `φ_U` is bounded.

The gluing proposition (`AnalyticGluingProof.exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses`,
proved sorry-free) now gives `x ∉ E_nK(α)`, a contradiction.

The proof is sorry-free; its only open input is Boucksom's theorem
(`LocusProperties.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`).
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NoIsolatedPoints

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.AnalyticGluingData FirstPass.GlobalAnalyticSingularities
  FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Two smooth two-forms which agree at the image point in one chart agree at the
source point in every other chart: the transformation law. -/
theorem coeff_eq_of_coeff_eq_chartTransition {a b : SmoothRealForm n Y 2}
    (e e' : ComplexChart n Y) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e' e).source)
    (h : a.coeff e (chartTransition e' e z) = b.coeff e (chartTransition e' e z)) :
    a.coeff e' z = b.coeff e' z := by
  ext v
  rw [a.compatible e' e z hz v, b.compatible e' e z hz v, h]

/-- **A chart-smooth global potential near a point.**  A smooth local potential
of a smooth two-form in the chart at `x` can be cut off to a bounded chart-smooth
function `ψ` on the manifold whose `ddᶜ` equals the form, in every chart, over an
open neighbourhood of `x`. -/
theorem exists_chartSmooth_potential_near (η : SmoothRealForm n Y 2) (x : Y)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hxW : (complexChartAt (n := n) x).val x ∈ W)
    (hρ : IsSmoothLocalPotential η (complexChartAt (n := n) x) W ρ) :
    ∃ ψ : Y → ℝ, ChartSmooth (n := n) ψ ∧ (∃ B : ℝ, ∀ y, |ψ y| ≤ B) ∧
      ∃ Ω : Set Y, IsOpen Ω ∧ x ∈ Ω ∧
        ∀ (e' : ComplexChart n Y) (w : ComplexModel n), w ∈ e'.val.target →
          e'.val.symm w ∈ Ω → smoothDDC (fun z => ψ (e'.val.symm z)) w = η.coeff e' w := by
  classical
  set e := complexChartAt (n := n) x with he
  obtain ⟨g, hg, hρg⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hρ.1 hρ.2.2.1 hxW
  let Ω₀ : TopologicalSpace.Opens (ComplexModel n) := ⟨W, hρ.1⟩
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := Ω₀) (K := ({e.val x} : Set (ComplexModel n))) isCompact_singleton
    (singleton_subset_iff.2 hxW)
  rw [nhdsSet_singleton] at hχ1
  obtain ⟨V₂, hV₂P, hV₂o, hxV₂⟩ := eventually_nhds_iff.mp
    (hρg.and (hχ1.and (hρ.1.mem_nhds hxW)))
  let bfun : ComplexModel n → ℝ := fun q => χ q * g q
  have hbfun : ContDiff ℝ ∞ bfun := χ.contDiff.mul hg
  have hbsupp : tsupport bfun ⊆ tsupport (χ : ComplexModel n → ℝ) :=
    tsupport_mul_subset_left
  have hχt : tsupport (χ : ComplexModel n → ℝ) ⊆ W := χ.tsupport_subset
  have hbc : HasCompactSupport bfun := χ.hasCompactSupport.mul_right
  let ψ : Y → ℝ := ChartPartition.chartExtend e bfun
  have hψ : ChartSmooth (n := n) ψ :=
    ChartPartition.chartSmooth_chartExtend e hbfun hbc
      (hbsupp.trans (hχt.trans hρ.2.1))
  refine ⟨ψ, hψ, ?_, e.val.source ∩ e.val ⁻¹' V₂,
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source hV₂o,
    ⟨mem_complexChartAt_source (n := n) x, hxV₂⟩, ?_⟩
  · obtain ⟨B, hB⟩ := hbfun.continuous.bounded_above_of_compact_support hbc
    refine ⟨B, fun y => ?_⟩
    by_cases hy : y ∈ e.val.source
    · rw [show ψ y = bfun (e.val y) from ChartPartition.chartExtend_of_mem hy]
      simpa [Real.norm_eq_abs] using hB (e.val y)
    · rw [show ψ y = 0 from ChartPartition.chartExtend_of_notMem hy, abs_zero]
      exact (norm_nonneg _).trans (hB 0)
  · intro e' w hw hwΩ
    have hsrc : w ∈ (chartTransition e' e).source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
      exact ⟨hw, hwΩ.1⟩
    have hform := coeff_eq_of_coeff_eq_chartTransition
      (a := SmoothDDCForm.ddcForm ψ hψ) (b := η) e e' hsrc ?_
    · simpa only [SmoothDDCForm.ddcForm_coeff] using hform
    set p := chartTransition e' e w with hp
    have hpV : p ∈ V₂ := hwΩ.2
    have hpW : p ∈ W := (hV₂P p hpV).2.2
    rw [SmoothDDCForm.ddcForm_coeff, ← hρ.2.2.2 hpW]
    apply smoothDDC_congr
    filter_upwards [hV₂o.mem_nhds hpV] with q hq
    obtain ⟨hρq, hχq, hqW⟩ := hV₂P q hq
    have hqt : q ∈ e.val.target := hρ.2.1 hqW
    change ChartPartition.chartExtend e bfun (e.val.symm q) = ρ q
    rw [ChartPartition.chartExtend_of_mem (e.val.map_target hqt), e.val.right_inv hqt]
    simp only [bfun, hχq, one_mul, hρq]

/-- **The local branch.**  If `ddᶜψ = η` in every chart over the open set `Ω`,
then `-ψ` is an `η`-PSH potential on `Ω`: in each chart `ψ` itself is a smooth
local potential of `η`, and `-ψ + ψ = 0` is plurisubharmonic. -/
theorem isThetaPshPotentialOn_neg (η : SmoothRealForm n Y 2) {ψ : Y → ℝ}
    (hψ : ChartSmooth (n := n) ψ) {Ω : Set Y} (hΩ : IsOpen Ω)
    (hddc : ∀ (e' : ComplexChart n Y) (w : ComplexModel n), w ∈ e'.val.target →
      e'.val.symm w ∈ Ω → smoothDDC (fun z => ψ (e'.val.symm z)) w = η.coeff e' w) :
    IsThetaPshPotentialOn η (fun y => ((-ψ y : ℝ) : EReal)) Ω := by
  refine ⟨fun e' z hz hzΩ => ?_, fun y _ U _ hyU => ⟨y, hyU, EReal.coe_ne_bot _⟩⟩
  have hWo : IsOpen (e'.val.target ∩ e'.val.symm ⁻¹' Ω) :=
    e'.val.isOpen_inter_preimage_symm hΩ
  refine ⟨e'.val.target ∩ e'.val.symm ⁻¹' Ω, fun w => ψ (e'.val.symm w), ⟨hz, hzΩ⟩,
    ⟨hWo, inter_subset_left, (hψ e').mono inter_subset_left,
      fun w hw => hddc e' w hw.1 hw.2⟩, ?_⟩
  have hzero := plurisubharmonicOn_coe_of_smoothDDC_eq_zero (h := fun _ => (0 : ℝ))
    hWo contDiffOn_const (fun w _ => GlobalPotentialTransforms.smoothDDC_const 0 w)
  convert hzero using 2 with w
  simp only [chartFunction]
  rw [← EReal.coe_add, neg_add_cancel]

omit [IsComplexManifold n Y] in
/-- **Potentials with analytic singularities are bounded below on compact sets
avoiding their poles.** -/
theorem exists_lowerBound_of_hasAnalyticSingularities {φ : Y → EReal}
    (hφ : HasAnalyticSingularities (n := n) φ) {L : Set Y} (hL : IsCompact L)
    (hLP : ∀ y ∈ L, φ y ≠ ⊥) : ∃ m : ℝ, ∀ y ∈ L, (m : EReal) ≤ φ y := by
  obtain ⟨c, 𝔞, hc, -, hloc⟩ := hφ
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  refine hL.induction_on (p := fun s => ∃ m : ℝ, ∀ y ∈ s, (m : EReal) ≤ φ y)
    ⟨0, fun y hy => hy.elim⟩
    (fun s t hst ⟨m, hm⟩ => ⟨m, fun y hy => hm y (hst hy)⟩)
    (fun s t ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩ => ⟨min m₁ m₂, fun y hy => hy.elim
      (fun h => (EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans (hm₁ y h))
      (fun h => (EReal.coe_le_coe_iff.mpr (min_le_right _ _)).trans (hm₂ y h))⟩) ?_
  intro y hy
  obtain ⟨U, hUo, hyU, N, g, hgdiff, -, R, C, hRC, hrep⟩ := hloc y
  have hgy : ∃ j, g j y ≠ 0 := by
    by_contra! h
    exact hLP y hy (by
      rw [hrep y hyU]
      exact (scaled_generatorLog_add_eq_bot_iff g y hcR (R y)).mpr h)
  have hpos : 0 < generatorNormSq g y := by
    obtain ⟨j, hj⟩ := hgy
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
      (f := fun i => ‖g i y‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hcont : ContinuousAt (generatorNormSq g) y := by
    unfold generatorNormSq
    exact tendsto_finsetSum _ fun j _ =>
      (((hgdiff j).continuousOn.continuousAt (hUo.mem_nhds hyU)).norm).pow 2
  have hev : ∀ᶠ z in 𝓝 y, generatorNormSq g y / 2 < generatorNormSq g z :=
    hcont.eventually (lt_mem_nhds (half_lt_self hpos))
  refine ⟨U ∩ {z | generatorNormSq g y / 2 < generatorNormSq g z},
    mem_nhdsWithin_of_mem_nhds (inter_mem (hUo.mem_nhds hyU) hev),
    (c : ℝ) * Real.log (generatorNormSq g y / 2) - C, fun z hz => ?_⟩
  have hz2 : 0 < generatorNormSq g z := (half_pos hpos).trans hz.2
  have hgz : ∃ j, g j z ≠ 0 := by
    by_contra! h
    simp [generatorNormSq, h] at hz2
  rw [hrep z hz.1, generatorLog_of_nonzero hgz, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  have hlog : Real.log (generatorNormSq g y / 2) ≤ Real.log (generatorNormSq g z) :=
    Real.log_le_log (half_pos hpos) hz.2.le
  have hR : -C ≤ R z := neg_le_of_abs_le (hRC z hz.1)
  nlinarith [mul_le_mul_of_nonneg_left hlog hcR.le]

/-- **The non-Kähler locus has no isolated points** (Copy-4,
`lem:no-isolated-points`). -/
theorem accPt_nonKahlerLocus [CompactSpace Y] [ConnectedSpace Y] (hn : 0 < n)
    (hKahler : Nonempty (KahlerBackground n Y)) (alpha : RealBottChern n Y)
    (hbig : IsBigClass alpha) :
    ∀ x ∈ nonKahlerLocus alpha, AccPt x (𝓟 (nonKahlerLocus alpha)) := by
  intro x hx
  by_contra hacc
  rw [accPt_iff_frequently, not_frequently] at hacc
  obtain ⟨N, hNx, hNo, hxN⟩ : ∃ N : Set Y, (∀ y ∈ N, y ≠ x → y ∉ nonKahlerLocus alpha) ∧
      IsOpen N ∧ x ∈ N := by
    obtain ⟨N, hN, hNo, hxN⟩ := eventually_nhds_iff.mp hacc
    exact ⟨N, fun y hy hyx => by simpa [hyx] using hN y hy, hNo, hxN⟩
  -- Boucksom: a Kähler current with analytic singularities and polar set `E_nK(α)`.
  obtain ⟨T, hsing, -, hpole⟩ :=
    LocusProperties.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn hKahler alpha hbig
  set θ := T.representative with hθ
  set η : ClosedRealOneOneForm n Y := θ - T.lowerBound.form with hη
  have hTpsh : IsThetaPshPotential η.val T.potential := T.strictlyPsh
  -- The local branch.
  obtain ⟨W, ρ, hxW, hρ, -⟩ := hTpsh.1 (complexChartAt (n := n) x)
    ((complexChartAt (n := n) x).val x)
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source (n := n) x))
  obtain ⟨ψ, hψ, ⟨B, hB⟩, Ω, hΩo, hxΩ, hddc⟩ :=
    exists_chartSmooth_potential_near η.val x hxW hρ
  set φU : Y → EReal := fun y => ((-ψ y : ℝ) : EReal) with hφU
  have hdom : DominatesKahlerFormOn θ φU Ω :=
    ⟨T.lowerBound, isThetaPshPotentialOn_neg η.val hψ hΩo hddc⟩
  have hsmooth : IsSmoothNear (n := n) φU x :=
    ⟨univ, isOpen_univ, mem_univ x, fun y => -ψ y,
      fun e => (hψ e).neg.mono inter_subset_left, fun _ _ => rfl⟩
  -- The collar.
  obtain ⟨U₂, hU₂o, hxU₂, hU₂sub, -⟩ := exists_open_between_and_isCompact_closure
    isCompact_singleton (hΩo.inter hNo) (singleton_subset_iff.2 ⟨hxΩ, hxN⟩)
  obtain ⟨U₁, hU₁o, hxU₁, hU₁sub, -⟩ := exists_open_between_and_isCompact_closure
    isCompact_singleton hU₂o hxU₂
  have hxU₁' : x ∈ U₁ := singleton_subset_iff.1 hxU₁
  have hLc : IsCompact (closure U₂ \ U₁) :=
    (isClosed_closure.sdiff hU₁o).isCompact
  have hLP : ∀ y ∈ closure U₂ \ U₁, T.potential y ≠ ⊥ := by
    intro y hy hbot
    have hyE : y ∈ nonKahlerLocus alpha := hpole ▸ hbot
    exact hNx y (hU₂sub hy.1).2 (fun hyx => hy.2 (hyx ▸ hxU₁')) hyE
  obtain ⟨m, hm⟩ := exists_lowerBound_of_hasAnalyticSingularities hsing hLc hLP
  have hcollar : ∃ C : ℝ, ∀ y ∈ closure U₂ \ U₁, φU y ≤ T.potential y + (C : EReal) := by
    refine ⟨B - m, fun y hy => ?_⟩
    have h1 : φU y ≤ (B : EReal) :=
      EReal.coe_le_coe_iff.mpr (by have := abs_le.mp (hB y); linarith)
    have h2 : (B : EReal) = (m : EReal) + ((B - m : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    exact h1.trans (h2 ▸ add_le_add (hm y hy) le_rfl)
  have hxpole : T.potential x = ⊥ := by
    have : x ∈ poleSet T.potential := hpole ▸ hx
    exact this
  have hglue : GluingHypotheses θ U₁ U₂ x T.potential φU :=
    ⟨⟨⟨T.lowerBound, hTpsh⟩, hxpole⟩,
      ⟨⟨Ω, hΩo, hU₂sub.trans inter_subset_left, hdom⟩, hsmooth⟩, hcollar⟩
  have hrel : RelCompactSubset U₁ U₂ := ⟨isClosed_closure.isCompact, hU₁sub⟩
  have hnot := (AnalyticGluingProof.exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses
    hKahler θ U₁ U₂ hU₁o hU₂o hrel x hxU₁' T.potential φU hglue).2
  rw [hθ, T.represents] at hnot
  exact hnot hx

end

end SGPT.Foundations.Analysis.Pending.NoIsolatedPoints
