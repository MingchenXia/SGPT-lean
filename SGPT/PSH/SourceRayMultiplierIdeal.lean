import SGPT.PSH.SourceRayMultiplierWeight
import SGPT.PSH.SourceRayLegendreTestCurve
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.Convex.RelativeInterior
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior

/-!
# Multiplier ideals of a test curve through its geodesic ray

Source `prop:mis_RWN` (He--Testorf--Wang), chapter `chapter_testcurve`: for a
geodesic ray `ℓ ∈ 𝓡(X,θ;φ)`, every `τ < ℓ^*_max` and every `x ∈ X`,

  `𝓘(ℓ^*_τ)_x = { f ∈ 𝓞_{X,x} : |f|² ∫_0^∞ exp(-ℓ_t + tτ) dt is integrable near x }`.

The multiplier ideal is the existing `multiplierIdeal 1` (germs holomorphic near
`x` with `|f|² e^{-ℓ^*_τ}` Lebesgue integrable near `x` in the preferred chart at
`x`); the right-hand side `SourceRayMultiplierGerm` uses the same chart, measure
and integrability convention (measurability and finiteness of the integral).

Main ingredients: the one-variable estimates of `SourceRayMultiplierWeight`, the
right continuity of test curves outside a pluripolar set
(`SourceTestCurvePredata.le_uscRegularization_later`, the second half of
`eq:Gammataucont`), and the strong openness theorem for increasing sequences
(`increasingStrongOpenness_ofRegularRoute`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.RayMultiplier

section RightContinuity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

private lemma negativeTrace_nonneg' (Γ : SourceTestCurvePredata θ) (x : M) (t : ℝ) :
    0 ≤ sourceTestCurveNegativeTrace Γ.max Γ.potential x t := by
  by_cases ht : t < Γ.max
  · simpa [sourceTestCurveNegativeTrace, ht] using
      EReal.neg_le_neg_iff.mpr (Γ.le_zero ⟨t, ht⟩ x)
  · simp [sourceTestCurveNegativeTrace, ht]

private lemma negativeTrace_finite_before' (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥)
    {t : ℝ} (ht : t < b.1) :
    sourceTestCurveNegativeTrace Γ.max Γ.potential x t ≠ ⊤ := by
  have htm : t < Γ.max := ht.trans b.2
  have hbot : Γ.potential ⟨t, htm⟩ x ≠ ⊥ :=
    ne_bot_of_le_ne_bot hb (Γ.antitone x (show (⟨t, htm⟩ : Iio Γ.max) ≤ b from ht.le))
  simpa [sourceTestCurveNegativeTrace, htm] using hbot

/-- A finite concave function is continuous: the test curve is continuous in `τ`
at every point where a later slice is finite. -/
private lemma negativeTrace_continuousAt' (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥)
    {t : ℝ} (ht : t < b.1) :
    ContinuousAt (sourceTestCurveNegativeTrace Γ.max Γ.potential x) t := by
  let f := sourceTestCurveNegativeTrace Γ.max Γ.potential x
  have hnb (s : ℝ) : f s ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥) (negativeTrace_nonneg' Γ x s)
  have hp : SGPT.Convex.IsProper f := ⟨Γ.concave x,
    ⟨t, lt_top_iff_ne_top.mpr (negativeTrace_finite_before' Γ x b hb ht)⟩, hnb⟩
  have hsub : Iio b.1 ⊆ SGPT.Convex.effectiveDomain f := by
    intro s hs
    exact lt_top_iff_ne_top.mpr (negativeTrace_finite_before' Γ x b hb hs)
  have hint : t ∈ interior (SGPT.Convex.effectiveDomain f) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Iio_mem_nhds ht) hsub)
  have hc : ContinuousAt (fun s ↦ (f s).toReal) t :=
    ((SGPT.Convex.convexOn_toReal_effectiveDomain hp).continuousOn_interior t hint).continuousAt
      (isOpen_interior.mem_nhds hint)
  apply (continuous_coe_real_ereal.continuousAt.comp hc).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact (EReal.coe_toReal (negativeTrace_finite_before' Γ x b hb hs) (hnb s)).symm

/-- The parameters `τ + (Γ_max - τ)/(j+2)`, decreasing to `τ` from above. -/
def laterParameter (m τ : ℝ) (j : ℕ) : ℝ := τ + (m - τ) / ((j : ℝ) + 2)

theorem laterParameter_lt {m τ : ℝ} (hτ : τ < m) (j : ℕ) : laterParameter m τ j < m := by
  unfold laterParameter
  have hj : (2 : ℝ) ≤ (j : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hpos : 0 < m - τ := by linarith
  have : (m - τ) / ((j : ℝ) + 2) ≤ (m - τ) / 2 := div_le_div_of_nonneg_left hpos.le (by norm_num) hj
  linarith

theorem lt_laterParameter {m τ : ℝ} (hτ : τ < m) (j : ℕ) : τ < laterParameter m τ j := by
  unfold laterParameter
  have : 0 < (m - τ) / ((j : ℝ) + 2) := div_pos (by linarith) (by positivity)
  linarith

theorem laterParameter_le_zero {m τ : ℝ} (hτ : τ < m) (j : ℕ) :
    laterParameter m τ j ≤ laterParameter m τ 0 := by
  unfold laterParameter
  have hj : (0 : ℝ) + 2 ≤ (j : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have : (m - τ) / ((j : ℝ) + 2) ≤ (m - τ) / ((0 : ℕ) + 2) := by
    rw [Nat.cast_zero]
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hj
  linarith

theorem laterParameter_antitone (m τ : ℝ) (hτ : τ < m) : Antitone (laterParameter m τ) := by
  intro i j hij
  unfold laterParameter
  have hij' : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
    have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    linarith
  have : (m - τ) / ((j : ℝ) + 2) ≤ (m - τ) / ((i : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hij'
  linarith

theorem tendsto_laterParameter (m τ : ℝ) :
    Tendsto (laterParameter m τ) atTop (𝓝 τ) := by
  have h : Tendsto (fun j : ℕ => (m - τ) / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := h1.inv_tendsto_atTop.const_mul (m - τ)
    simpa [div_eq_mul_inv] using h2
  show Tendsto (fun j : ℕ => τ + (m - τ) / ((j : ℝ) + 2)) atTop (𝓝 τ)
  simpa using h.const_add τ

/-- The later slices `Γ_{τ_j}`, `τ_j ↘ τ`, an increasing sequence. -/
def SourceTestCurvePredata.laterSlices (Γ : SourceTestCurvePredata θ) {τ : ℝ}
    (hτ : τ < Γ.max) (j : ℕ) : M → EReal :=
  Γ.potential ⟨laterParameter Γ.max τ j, laterParameter_lt hτ j⟩

theorem SourceTestCurvePredata.laterSlices_mono (Γ : SourceTestCurvePredata θ) {τ : ℝ}
    (hτ : τ < Γ.max) : Monotone (Γ.laterSlices hτ) := by
  intro i j hij x
  exact Γ.antitone x (show (⟨laterParameter Γ.max τ j, laterParameter_lt hτ j⟩ : Iio Γ.max) ≤
    ⟨laterParameter Γ.max τ i, laterParameter_lt hτ i⟩ from
      laterParameter_antitone Γ.max τ hτ hij)

/-- Second half of source `eq:Gammataucont`: `Γ_τ ≤ usc-sup_{j} Γ_{τ_j}`
(the reverse inequality is trivial). The pointwise inequality holds outside the
pluripolar set `{Γ_{τ_0} = -∞}`, by continuity of finite concave functions, and
hence everywhere. -/
theorem SourceTestCurvePredata.le_uscRegularization_later (Γ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ < Γ.max) :
    Γ.potential ⟨τ, hτ⟩ ≤ uscRegularization (⨆ j, Γ.laterSlices hτ j) := by
  have hSn : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (uscRegularization (fun x => ⨆ j, Γ.laterSlices hτ j x)) :=
    SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun j => Γ.native_thetaPSH _) (C := 0)
      (fun j x => by rw [EReal.coe_zero]; exact Γ.le_zero _ x)
  have hfun : (⨆ j, Γ.laterSlices hτ j) = fun x => ⨆ j, Γ.laterSlices hτ j x := by
    funext x; exact iSup_apply
  rw [hfun]
  have hS : (ofFixedModel n M).IsThetaPSH θ
      (uscRegularization (fun x => ⨆ j, Γ.laterSlices hτ j x)) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hSn
  apply (sourceQuasiEverywhere_le_iff (Γ.thetaPSH ⟨τ, hτ⟩) hS).mp
  apply (sourceQuasiEverywhere_iff_native _).mpr
  let b : Iio Γ.max := ⟨laterParameter Γ.max τ 0, laterParameter_lt hτ 0⟩
  apply (quasiPsh_finite_quasiEverywhere (Γ.native_thetaPSH b).quasiPshPotential).mono
  intro x hx
  have hb : τ < b.1 := lt_laterParameter hτ 0
  have hc := negativeTrace_continuousAt' Γ x b hx.1 hb
  have ht : Tendsto (fun j => sourceTestCurveNegativeTrace Γ.max Γ.potential x
      (laterParameter Γ.max τ j)) atTop
      (𝓝 (sourceTestCurveNegativeTrace Γ.max Γ.potential x τ)) :=
    hc.tendsto.comp (tendsto_laterParameter Γ.max τ)
  have ht' : Tendsto (fun j => Γ.laterSlices hτ j x) atTop (𝓝 (Γ.potential ⟨τ, hτ⟩ x)) := by
    have hneg := ((continuous_neg : Continuous fun a : EReal => -a).tendsto _).comp ht
    simpa [Function.comp_def, sourceTestCurveNegativeTrace, hτ, laterParameter_lt hτ,
      SourceTestCurvePredata.laterSlices] using hneg
  exact (le_of_tendsto' ht' fun j => le_iSup (fun j => Γ.laterSlices hτ j x) j).trans
    (le_uscRegularization (fun y => ⨆ j, Γ.laterSlices hτ j y) x)

end RightContinuity

section StrongOpenness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Strong openness for an increasing sequence of `θ`-PSH functions, in one
chart: a multiplier germ of the regularized limit is a multiplier germ of some
member of the sequence. -/
theorem exists_multiplierIntegrableAt_of_uscRegularization_iSup
    {θ : SmoothRealForm n M 2} (hlocal : HasSmoothLocalPotentials θ)
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential θ (u j))
    (hu0 : ∀ j, u j ≤ 0) (hmono : Monotone u)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    {c : ℝ} (hc : 0 < c) {f : ComplexModel n → ℂ} (hf : AnalyticAt ℂ f z)
    (hmem0 : MultiplierIntegrableAt (chartFunction (uscRegularization (⨆ j, u j)) e) c f z
      volume) :
    ∃ j, MultiplierIntegrableAt (chartFunction (u j) e) c f z volume := by
  have hmem := (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp hmem0
  have hconv := fun j => QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    (chartFunction (u j) e) c f z
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  set P := uscRegularization (⨆ j, u j) with hP
  have hPpot : IsThetaPshPotential θ P := by
    refine ⟨thetaPlurisubharmonic_uscRegularization_sSup hlocal (range_nonempty u)
      (by rintro _ ⟨j, rfl⟩; exact hu j) (by rintro _ ⟨j, rfl⟩; exact hu0 j), ?_⟩
    exact (hu 0).2.mono ((le_iSup u 0).trans (le_uscRegularization _))
  obtain ⟨W, ρ, hzW, hρ⟩ := hlocal e z hz
  let v : ℕ → ComplexModel n → EReal := fun j y => chartFunction (u j) e y + (ρ y : EReal)
  have hvpsh : ∀ j, PlurisubharmonicOn (v j) W := fun j =>
    chartCorrectedFamily_plurisubharmonicOn (F := {u j})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hu j) e hρ _
      ⟨u j, mem_singleton _, rfl⟩
  have hvmono : ∀ y ∈ W, Monotone fun j => v j y := fun y _ i j hij =>
    add_le_add (hmono hij _) le_rfl
  have hvbound : FirstPass.LocallyUniformlyBoundedAbove (range v) W := by
    refine (chartCorrectedFamily_locallyUniformlyBoundedAbove (F := range u)
      (by rintro _ ⟨j, rfl⟩; exact hu0 j) e hρ.1 hρ.2.2.1).mono_family ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨u j, ⟨j, rfl⟩, rfl⟩
  have hρc : ∀ y ∈ W, ContinuousAt ρ y := fun y hy =>
    ((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).continuousAt
  have hsup : (⨆ j, v j) = fun y => chartFunction (⨆ j, u j) e y + (ρ y : EReal) := by
    funext y
    simp only [iSup_apply, chartFunction, v]
    exact FirstPass.iSup_add_coe (fun j => u j (e.val.symm y)) (ρ y)
  have hVeq : ∀ y ∈ W, uscRegularization (⨆ j, v j) y =
      chartFunction P e y + (ρ y : EReal) := by
    intro y hy
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hρc y hy),
      uscRegularization_chartFunction_apply _ e (hρ.2.1 hy)]
  have hPpsh : PlurisubharmonicOn
      (fun y => chartFunction P e y + (ρ y : EReal)) W :=
    chartCorrectedFamily_plurisubharmonicOn (F := {P})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hPpot) e hρ _
      ⟨_, mem_singleton _, rfl⟩
  have hVqpsh : QuasiPlurisubharmonicAt (uscRegularization (⨆ j, v j)) z :=
    (hPpsh z hzW).quasiPlurisubharmonicAt.congr
      (eventually_of_mem (hρ.1.mem_nhds hzW) fun y hy => (hVeq y hy).symm)
  have hlow : ∀ᶠ y in 𝓝 z, ρ z - 1 < ρ y := hρc z hzW (Ioi_mem_nhds (by linarith))
  have hhigh : ∀ᶠ y in 𝓝 z, ρ y < ρ z + 1 := hρc z hzW (Iio_mem_nhds (by linarith))
  have h2 : MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c f z volume := by
    refine multiplierIntegrableAt_of_moreSingularAt hVqpsh ⟨1 - ρ z, ?_⟩ hmem
    filter_upwards [hlow, hρ.1.mem_nhds hzW] with y hy hyW
    rw [hVeq y hyW, add_assoc, ← EReal.coe_add]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by linarith))
  obtain ⟨j, hj⟩ := increasingStrongOpenness_ofRegularRoute n W v hρ.1 hvpsh hvmono hvbound
    z hzW c hc f hf h2
  have h4 : MultiplierIntegrableAt (chartFunction (u j) e) c f z volume := by
    refine multiplierIntegrableAt_of_moreSingularAt
      ((hu j).1.quasiPlurisubharmonic e z hz) ⟨ρ z + 1, ?_⟩ hj
    filter_upwards [hhigh] with y hy
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hy.le)
  exact ⟨j, (hconv j).mpr h4⟩

end StrongOpenness

section HeTestorfWang

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}

/-- The density `|g|² ∫_0^∞ exp(-ℓ_t + tτ) dt` of the right-hand side of
`eq:mis_RWN`. -/
def sourceRayMultiplierDensity (ℓ : SourceRayFamily M) (τ : ℝ) (g : M → ℂ) (y : M) : ℝ≥0∞ :=
  ENNReal.ofReal (‖g y‖ ^ 2) * rayWeight (fun t => sourceRayExtension ℓ t y) τ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
variable (n) in
/-- The right-hand side of `eq:mis_RWN`: `g` is holomorphic near `x` and
`|g|² ∫_0^∞ exp(-ℓ_t + tτ) dt` is (measurable and) Lebesgue integrable on a
neighborhood of `x` in the preferred chart at `x`. -/
def SourceRayMultiplierGerm (ℓ : SourceRayFamily M) (τ : ℝ) (x : M) (g : M → ℂ) : Prop :=
  HolomorphicAt n g x ∧
    ∃ U : Set (ComplexModel n), IsOpen U ∧ (complexChartAt (n := n) x).val x ∈ U ∧
      DifferentiableOn ℂ (fun z => g ((complexChartAt (n := n) x).val.symm z)) U ∧
      AEMeasurable (fun z => sourceRayMultiplierDensity ℓ τ g
        ((complexChartAt (n := n) x).val.symm z)) (volume.restrict U) ∧
      ∫⁻ z in U, sourceRayMultiplierDensity ℓ τ g ((complexChartAt (n := n) x).val.symm z) < ⊤

omit [BorelSpace M] [ConnectedSpace M] in
private theorem ray_slice_thetaPSH (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (t : ℝ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceRayExtension ℓ t) := by
  obtain ⟨hu, -, -⟩ := h.1.1 ⟨max t 0, le_max_right t 0⟩
  exact hu

private theorem ray_antitone (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (y : M) :
    AntitoneOn (fun t : ℝ => sourceRayExtension ℓ t y -
      ((t * sourceRayLegendreCutoff omega h : ℝ) : EReal)) (Ici 0) :=
  (source_ray_inverse_cutoff_linear_whole omega h).2 y

private theorem measurable_rayWeight_ray (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (τ : ℝ) :
    Measurable fun y => rayWeight (fun t => sourceRayExtension ℓ t y) τ := by
  apply measurable_rayWeight (m := sourceRayLegendreCutoff omega h)
  · exact fun y => (ray_antitone omega h y).mono Ioi_subset_Ici_self
  · intro t
    exact ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (ray_slice_thetaPSH omega h t)).1.quasiPlurisubharmonic.upperSemicontinuous.measurable

omit [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M] in
private theorem aemeasurable_symm_target (x : M) {U : Set (ComplexModel n)} (hU : IsOpen U) :
    AEMeasurable (complexChartAt (n := n) x).val.symm
      (volume.restrict (U ∩ (complexChartAt (n := n) x).val.target)) :=
  ((complexChartAt (n := n) x).val.continuousOn_symm.mono inter_subset_right).aemeasurable
    (hU.inter (complexChartAt (n := n) x).val.open_target).measurableSet

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] in
private theorem aemeasurable_normSq {g : M → ℂ} (x : M) {U : Set (ComplexModel n)}
    (hU : IsOpen U)
    (hd : DifferentiableOn ℂ (fun z => g ((complexChartAt (n := n) x).val.symm z)) U) :
    AEMeasurable (fun z => ENNReal.ofReal (‖g ((complexChartAt (n := n) x).val.symm z)‖ ^ 2))
      (volume.restrict (U ∩ (complexChartAt (n := n) x).val.target)) := by
  have hc := (hd.mono (inter_subset_left (t := (complexChartAt (n := n) x).val.target))).continuousOn
  exact ((hc.aemeasurable (hU.inter (complexChartAt (n := n) x).val.open_target).measurableSet
    ).norm.pow_const 2).ennreal_ofReal

/-- Source `prop:mis_RWN` (He--Testorf--Wang). For a geodesic ray
`ℓ ∈ 𝓡(X,θ;φ)`, every `τ < ℓ^*_max` and every point `x`, a germ `g` lies in the
multiplier ideal `𝓘(ℓ^*_τ)_x` iff `|g|² ∫_0^∞ exp(-ℓ_t + tτ) dt` is integrable near
`x`. Here `ℓ^*` is the Legendre transform test curve (`thm:Legenbij`), with
`ℓ^*_τ = inf_{t>0} (ℓ_t - tτ)` and `ℓ^*_max = sourceRayLegendreCutoff`. -/
theorem source_ray_multiplierIdeal_mem_iff (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ}
    (hτ : τ < (sourceRayLegendreTestCurve omega h).max) (x : M) (g : M → ℂ) :
    (multiplierIdeal (n := n) 1
        ((sourceRayLegendreTestCurve omega h).potential ⟨τ, hτ⟩)).mem x g ↔
      SourceRayMultiplierGerm n ℓ τ x g := by
  set e := complexChartAt (n := n) x with he
  set Γ := sourceRayLegendreTestCurve omega h with hΓ
  set m := sourceRayLegendreCutoff omega h with hm
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hΓpot : ∀ (s : ℝ) (hs : s < Γ.max) (y : M),
      Γ.potential ⟨s, hs⟩ y = rayInverse (fun t => sourceRayExtension ℓ t y) s :=
    fun _ _ _ => rfl
  constructor
  · rintro ⟨hg, hmem⟩
    -- strong openness: pass to a later slice
    have hle := Γ.toSourceTestCurvePredata.le_uscRegularization_later hτ
    have hSn : IsThetaPshPotential (atlasClosedFormToNative θ).val
        (uscRegularization (⨆ j, Γ.toSourceTestCurvePredata.laterSlices hτ j)) := by
      have hfun : (⨆ j, Γ.toSourceTestCurvePredata.laterSlices hτ j) =
          fun y => ⨆ j, Γ.toSourceTestCurvePredata.laterSlices hτ j y := by
        funext y; exact iSup_apply
      rw [hfun]
      exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
        (fun j => Γ.toSourceTestCurvePredata.native_thetaPSH _) (C := 0)
        (fun j y => by rw [EReal.coe_zero]; exact Γ.toSourceTestCurvePredata.le_zero _ y)
    obtain ⟨-, U₀, hU₀, hzU₀, hd₀, -⟩ := id hmem
    have hf : AnalyticAt ℂ (fun z => g (e.val.symm z)) (e.val x) :=
      HolomorphicAnalytic.analyticAt_of_differentiableOn hU₀ hd₀ hzU₀
    have hmemS : MultiplierIntegrableAt
        (chartFunction (uscRegularization (⨆ j, Γ.toSourceTestCurvePredata.laterSlices hτ j)) e)
        1 (fun z => g (e.val.symm z)) (e.val x) volume := by
      refine multiplierIntegrableAt_of_moreSingularAt
        (hSn.1.quasiPlurisubharmonic e (e.val x) hz) ⟨0, ?_⟩ hmem
      exact Eventually.of_forall fun y => by
        simpa only [chartFunction, EReal.coe_zero, add_zero] using hle (e.val.symm y)
    obtain ⟨j, hj⟩ := exists_multiplierIntegrableAt_of_uscRegularization_iSup
      (Γ.toSourceTestCurvePredata.native_thetaPSH ⟨τ, hτ⟩).1.hasSmoothLocalPotentials
      (fun j => Γ.toSourceTestCurvePredata.native_thetaPSH _)
      (fun j => Γ.toSourceTestCurvePredata.le_zero _)
      (Γ.toSourceTestCurvePredata.laterSlices_mono hτ) e hz one_pos hf hmemS
    obtain ⟨-, U, hU, hzU, hd, -, hint⟩ := hj
    set τ' := laterParameter Γ.max τ j with hτ'
    have hττ' : τ < τ' := lt_laterParameter hτ j
    refine ⟨hg, U ∩ e.val.target, hU.inter e.val.open_target, ⟨hzU, hz⟩,
      hd.mono inter_subset_left, ?_, ?_⟩
    · exact (aemeasurable_normSq x hU hd).mul
        ((measurable_rayWeight_ray omega h τ).comp_aemeasurable (aemeasurable_symm_target x hU))
    · have hpt : ∀ z, sourceRayMultiplierDensity ℓ τ g (e.val.symm z) ≤
          ENNReal.ofReal (1 / (τ' - τ)) *
            multiplierDensity (chartFunction (Γ.toSourceTestCurvePredata.laterSlices hτ j) e) 1
              (fun z => g (e.val.symm z)) z := by
        intro z
        unfold sourceRayMultiplierDensity multiplierDensity
        rw [mul_left_comm]
        gcongr
        exact rayWeight_le_multiplierWeight_iInf _ hττ'
      calc ∫⁻ z in U ∩ e.val.target, sourceRayMultiplierDensity ℓ τ g (e.val.symm z)
          ≤ ∫⁻ z in U ∩ e.val.target, ENNReal.ofReal (1 / (τ' - τ)) *
              multiplierDensity (chartFunction (Γ.toSourceTestCurvePredata.laterSlices hτ j) e) 1
                (fun z => g (e.val.symm z)) z := lintegral_mono hpt
        _ = ENNReal.ofReal (1 / (τ' - τ)) * ∫⁻ z in U ∩ e.val.target,
              multiplierDensity (chartFunction (Γ.toSourceTestCurvePredata.laterSlices hτ j) e) 1
                (fun z => g (e.val.symm z)) z := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (1 / (τ' - τ)) * ∫⁻ z in U,
              multiplierDensity (chartFunction (Γ.toSourceTestCurvePredata.laterSlices hτ j) e) 1
                (fun z => g (e.val.symm z)) z := by
            gcongr
            exact inter_subset_left
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  · rintro ⟨hg, U, hU, hzU, hd, -, hint⟩
    refine ⟨hg, one_pos, U ∩ e.val.target, hU.inter e.val.open_target, ⟨hzU, hz⟩,
      hd.mono inter_subset_left, ?_, ?_⟩
    · have hΓm : Measurable (Γ.potential ⟨τ, hτ⟩) :=
        (Γ.toSourceTestCurvePredata.native_thetaPSH ⟨τ, hτ⟩).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      have hw : Measurable (multiplierWeight 1) := by
        have : multiplierWeight 1 = fun a : EReal => EReal.exp (-a) :=
          funext multiplierWeight_one
        rw [this]
        exact EReal.measurable_exp.comp measurable_neg
      exact (aemeasurable_normSq x hU hd).mul
        (hw.comp_aemeasurable (hΓm.comp_aemeasurable (aemeasurable_symm_target x hU)))
    · have hpt : ∀ z, multiplierDensity (chartFunction (Γ.potential ⟨τ, hτ⟩) e) 1
          (fun z => g (e.val.symm z)) z ≤
            ENNReal.ofReal (Real.exp (1 + (m - τ))) *
              sourceRayMultiplierDensity ℓ τ g (e.val.symm z) := by
        intro z
        unfold sourceRayMultiplierDensity multiplierDensity
        rw [mul_left_comm]
        gcongr
        change multiplierWeight 1 (Γ.potential ⟨τ, hτ⟩ (e.val.symm z)) ≤ _
        rw [hΓpot]
        exact multiplierWeight_iInf_le_rayWeight hτ (ray_antitone omega h _)
      calc ∫⁻ z in U ∩ e.val.target, multiplierDensity (chartFunction (Γ.potential ⟨τ, hτ⟩) e) 1
            (fun z => g (e.val.symm z)) z
          ≤ ∫⁻ z in U ∩ e.val.target, ENNReal.ofReal (Real.exp (1 + (m - τ))) *
              sourceRayMultiplierDensity ℓ τ g (e.val.symm z) := lintegral_mono hpt
        _ = ENNReal.ofReal (Real.exp (1 + (m - τ))) * ∫⁻ z in U ∩ e.val.target,
              sourceRayMultiplierDensity ℓ τ g (e.val.symm z) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Real.exp (1 + (m - τ))) * ∫⁻ z in U,
              sourceRayMultiplierDensity ℓ τ g (e.val.symm z) := by
            gcongr
            exact inter_subset_left
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

end HeTestorfWang

end SGPT.PSH.VariableComplexAtlas
