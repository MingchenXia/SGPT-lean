import SGPT.Okounkov.TranscendentalCoreSiuLocal
import SGPT.Okounkov.FlattenedDivisorMetric
import SGPT.Okounkov.LocalThetaReader
import SGPT.Okounkov.GlobalDivisorResidual
import SGPT.Foundations.Analysis.Pending.ActualFiniteFamilyPrimeMultiplicity
import SGPT.Foundations.Analysis.Pending.FlattenedGlobalGenericLelongComparison
import SGPT.Foundations.Analysis.Pending.LelongNumberComparison
import SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds

/-!
# Subtracting a smooth hypersurface from a potential with analytic singularities

Source: blueprint node `tok:siu-analytic` (DRWNXZ Lemma 2.3), for a smooth connected hypersurface
`Y`. Let `u` be `θ`-psh with analytic singularities, `c = ν(u, Y)` its generic Lelong number along
`Y`, and `v` the residual `u - c log |s_Y|²` (with a smooth metric of `𝒪(Y)`), extended across
`Y`. Then `c ∈ ℚ_{≥ 0}` and `v` has analytic singularities.

Near a point of `Y`, in flat coordinates with `Y = {z_n = 0}`, `u = c' log ∑ |F_i|² + O(1)` and
`F_i = z_n^a H_i` with some `H_i` not vanishing identically on `Y`; the generic Lelong number of `u`
along `Y` near the point is `c' a`, so `c ≤ c' a`, and by compactness `c` is the minimum of finitely
many such rationals. Off `Y`, `v = c' log ∑|H_i|² + (c' a - c) log |z_n|² + O(1)`; the same
two-sided bound holds on `Y` because `v` (corrected by a smooth local potential) and
`c' log ∑|H_i|² + (c' a - c) log |z_n|² ± B` are plurisubharmonic and `Y` is Lebesgue-null.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

omit [IsComplexManifold (m + 1) M] in
/-- **Flat presentation.** In coordinates `Φ` centred at `x`, a potential with analytic
singularities is `c' log ∑ |F_i|² + b` near `0`, with holomorphic `F_i` not all identically zero
(if `u` is locally nondegenerate). -/
theorem exists_flat_presentation {u : M → EReal}
    (hA : HasManifoldAnalyticSingularityType (n := m + 1) u) (hne : LocallyNondegenerate u)
    (x : M) (χ : ComplexChart (m + 1) M) (hxχ : x ∈ χ.val.source)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) (χ.val x)) (hΦ0 : Φ.toFun (χ.val x) = 0) :
    ∃ (c' : ℚ) (K : ℕ) (F : Fin K → ComplexModel (m + 1) → ℂ) (b : ComplexModel (m + 1) → ℝ),
      0 < c' ∧ (∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (F i) z) ∧
      (∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), F i z = 0) ∧
      BoundedRealGermAt b 0 ∧
      ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        u (χ.val.symm (Φ.invFun z)) =
          ((c' : ℝ) : EReal) * generatorLog F z + (b z : EReal) := by
  have hχx : χ.val x ∈ χ.val.target := χ.val.map_source hxχ
  obtain ⟨c', K, f, hc', ⟨Df, hDf, hxDf, hf⟩, b, hb, heq⟩ := hA χ (χ.val x) hχx
  have hc'Q : (0 : ℚ) < c' := by exact_mod_cast hc'
  have h0T : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← hΦ0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = χ.val x := by
    rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have hInvD : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ Φ.invFun z := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0T] with z hz
    exact Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
  have hInvT : Tendsto Φ.invFun (𝓝 0) (𝓝 (χ.val x)) := by
    have := hInvD.self_of_nhds.continuousAt.tendsto
    rwa [hinv0] at this
  have hF : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => f i (Φ.invFun z)) z := by
    intro i
    filter_upwards [hInvD, hInvT.eventually (hDf.mem_nhds hxDf)] with z hz hzD
    exact ((hf i).differentiableAt (hDf.mem_nhds hzD)).comp z hz
  have hb' : BoundedRealGermAt (fun z => b (Φ.invFun z)) 0 := by
    have := hb
    rw [← hinv0] at this
    exact this.comp_continuousAt hInvD.self_of_nhds.continuousAt
  have hrep : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      u (χ.val.symm (Φ.invFun z)) =
        ((c' : ℝ) : EReal) * generatorLog (fun i z => f i (Φ.invFun z)) z +
          (b (Φ.invFun z) : EReal) :=
    heq.comp_tendsto hInvT
  refine ⟨c', K, fun i z => f i (Φ.invFun z), fun z => b (Φ.invFun z), hc'Q, hF, ?_, hb', hrep⟩
  -- not all generators vanish identically near `0`
  by_contra hall
  push Not at hall
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ∀ i, f i (Φ.invFun z) = 0 :=
    eventually_all.mpr hall
  have hbot : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), u (χ.val.symm (Φ.invFun z)) = ⊥ := by
    filter_upwards [hzero, hrep] with z hz hz'
    rw [hz', scaled_generatorLog_add_eq_bot_iff _ _ (by exact_mod_cast hc') _]
    exact hz
  -- pull back to a neighbourhood of `x`
  have hcont : ContinuousAt (fun y => Φ.toFun (χ.val y)) x := by
    have h1 : ContinuousAt χ.val x := χ.val.continuousAt hxχ
    have h2 : ContinuousAt Φ.toFun (χ.val x) :=
      Φ.toFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
    exact h2.comp h1
  have hcont' : Tendsto (fun y => Φ.toFun (χ.val y)) (𝓝 x) (𝓝 0) := by
    have := hcont.tendsto
    rwa [hΦ0] at this
  have hnear : ∀ᶠ y in 𝓝 x, u y = ⊥ := by
    filter_upwards [hcont'.eventually hbot, χ.val.open_source.mem_nhds hxχ,
      χ.val.continuousAt hxχ |>.eventually
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with y hy hys hyΦ
    rwa [Φ.left_inv _ hyΦ, χ.val.left_inv hys] at hy
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hnear
  obtain ⟨y, hyU, hy⟩ := hne x U hU hxU
  exact hy (hUsub hyU)

/-- Lelong numbers read in coordinates `χ.symm ∘ Φ.invFun`. -/
theorem lelongNumber_comp_flat_point (χ : ComplexChart (m + 1) M) {x : M}
    (Φ : LocalHolomorphicEquivAt (n := m + 1) (χ.val x)) (hΦe : Φ.source ⊆ χ.val.target)
    (v : M → EReal) {z : ComplexModel (m + 1)} (hz : z ∈ Φ.target) :
    lelongNumber (n := m + 1) (fun w => v (χ.val.symm (Φ.invFun w))) z =
      lelongNumber (n := m + 1) v (χ.val.symm (Φ.invFun z)) := by
  have hcov := LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq
    Φ (Φ.mapsTo_invFun hz) (u := chartFunction v χ)
  rw [Φ.right_inv z hz] at hcov
  have hiT : Φ.invFun z ∈ χ.val.target := hΦe (Φ.mapsTo_invFun hz)
  have hchart := LelongChartReaderInvariance.lelongNumber_chartFunction_eq χ
    (χ.val.map_target hiT) (u := v)
  rw [χ.val.right_inv hiT] at hchart
  exact hcov.trans hchart

/-- **The local analysis of the residual** at a point `x` of the smooth hypersurface `W`, in
flat coordinates `Φ` (with `W = {z_last = 0}`) where the metric weight of `W` is
`log |z_last|² + ℓ`: the local generic Lelong number `q = c' a` satisfies `c ≤ q` and bounds the
Lelong numbers along `W` near `x` from below; and if `c` is rational, the residual has analytic
singularities near `x`. -/
theorem exists_local_residual_data_of_flattening {θ : ClosedRealOneOneForm (m + 1) M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hA : HasManifoldAnalyticSingularityType (n := m + 1) u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEW : E.support = W) {c : ℝ≥0}
    (hc : (c : ℝ≥0∞) = SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
      (n := m + 1) (Subtype.val : W → M) u)
    (hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)))
    {x : M} (χ : ComplexChart (m + 1) M) (hxχ : x ∈ χ.val.source)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) (χ.val x)) (hΦe : Φ.source ⊆ χ.val.target)
    (hΦ0 : Φ.toFun (χ.val x) = 0)
    (hflat : ∀ y ∈ χ.val.source, χ.val y ∈ Φ.source →
      (y ∈ W ↔ (Φ.toFun (χ.val y)) (Fin.last m) = 0))
    {V₁ : Set M} (hV₁ : IsOpen V₁) (hxV₁ : x ∈ V₁) {ell : M → ℝ} (hell : ContinuousAt ell x)
    (hweight : ∀ y ∈ V₁, E.weight y =
      ENNReal.log (ENNReal.ofReal (‖(Φ.toFun (χ.val y)) (Fin.last m)‖ ^ 2)) + (ell y : EReal)) :
    ∃ q : ℚ, 0 ≤ q ∧ (c : ℝ) ≤ q ∧
      (∃ N ∈ 𝓝 x, ∀ y ∈ W ∩ N, ENNReal.ofReal q ≤
        SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u y) ∧
      ∀ c₀ : ℚ, (c : ℝ) = c₀ → ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ChartTypeOver (n := m + 1)
          (ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)) U := by
  classical
  -- the flat presentation of `u` and its common power of `z_last`
  obtain ⟨c', K, F, b, hc', hF, hne, hb, hrep⟩ := exists_flat_presentation hA hu.2 x χ hxχ Φ hΦ0
  obtain ⟨a, H, hH, hfact, -, hreader⟩ :=
    ActualFiniteFamilyPrimeMultiplicity.exists_generic_prime_reader F hF hne
  have hc'R : (0 : ℝ) < (c' : ℝ) := by exact_mod_cast hc'
  obtain ⟨R₀, O, hR₀, -, -, -, hlower, -, hinf, -⟩ := hreader (c' : ℝ) hc'R b hb
  -- the plurisubharmonic reader of the residual
  obtain ⟨Dv, ρ, hDv, h0Dv, -, hρ, hP, -⟩ :=
    SGPT.Okounkov.exists_flattened_theta_psh_reader hv χ x hxχ Φ
  rw [hΦ0] at h0Dv
  have h0T : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← hΦ0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = χ.val x := by
    rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have hInvC : ContinuousAt Φ.invFun 0 :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0T)).continuousAt
  have hpoint0 : χ.val.symm (Φ.invFun 0) = x := by rw [hinv0, χ.val.left_inv hxχ]
  have hpointC : ContinuousAt (fun z => χ.val.symm (Φ.invFun z)) 0 := by
    have h1 : ContinuousAt χ.val.symm (Φ.invFun 0) := by
      rw [hinv0]
      exact χ.val.continuousAt_symm (χ.val.map_source hxχ)
    exact h1.comp hInvC
  -- uniform bounds near `0`
  obtain ⟨Bb, hBb0, hBb⟩ := hb
  have hellC : ContinuousAt (fun z => ell (χ.val.symm (Φ.invFun z))) 0 := by
    have : ContinuousAt ell (χ.val.symm (Φ.invFun 0)) := by rw [hpoint0]; exact hell
    exact ContinuousAt.comp (f := fun z => χ.val.symm (Φ.invFun z)) this hpointC
  obtain ⟨Bℓ, hBℓ0, hBℓ⟩ := boundedRealGermAt_of_continuousAt hellC
  obtain ⟨Bρ, hBρ0, hBρ⟩ := boundedRealGermAt_of_continuousAt
    ((hρ 0 h0Dv).continuousAt.comp hInvC)
  have hV₁0 : V₁ ∈ 𝓝 (χ.val.symm (Φ.invFun 0)) := by
    rw [hpoint0]
    exact hV₁.mem_nhds hxV₁
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      z ∈ Dv ∧ z ∈ Φ.target ∧
      u (χ.val.symm (Φ.invFun z)) = ((c' : ℝ) : EReal) * generatorLog F z + (b z : EReal) ∧
      (∀ i, F i z = z (Fin.last m) ^ a * H i z) ∧ (∀ i, DifferentiableAt ℂ (H i) z) ∧
      |b z| ≤ Bb ∧ |ell (χ.val.symm (Φ.invFun z))| ≤ Bℓ ∧ |ρ (Φ.invFun z)| ≤ Bρ ∧
      χ.val.symm (Φ.invFun z) ∈ V₁ := by
    filter_upwards [hDv.mem_nhds h0Dv, Φ.isOpen_target.mem_nhds h0T, hrep,
      eventually_all.mpr (fun i => (hfact i).eventually_nhds), eventually_all.mpr hH, hBb, hBℓ,
      hBρ, hpointC.eventually hV₁0] with z h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, fun i => (h4 i).self_of_nhds, h5, h6, h7, h8, h9⟩
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set r := min r₁ R₀ with hrdef
  have hr : 0 < r := lt_min hr₁ hR₀
  have hball : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, _ := fun z hz =>
    hball₁ z (ball_subset_ball (min_le_left _ _) hz)
  -- membership in `W` in flat coordinates
  have hmemW : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
      (χ.val.symm (Φ.invFun z) ∈ W ↔ z (Fin.last m) = 0) := by
    intro z hz
    have hzT : z ∈ Φ.target := (hball z hz).2.1
    have hiS : Φ.invFun z ∈ Φ.source := Φ.mapsTo_invFun hzT
    have hiT : Φ.invFun z ∈ χ.val.target := hΦe hiS
    have h := hflat _ (χ.val.map_target hiT) (by rwa [χ.val.right_inv hiT])
    rwa [χ.val.right_inv hiT, Φ.right_inv z hzT] at h
  -- Lelong numbers in flat coordinates
  set w : ComplexModel (m + 1) → EReal :=
    fun z => ((c' : ℝ) : EReal) * generatorLog F z + (b z : EReal) with hwdef
  have hlel : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
      lelongNumber (n := m + 1) w z = 2 *
        SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u
          (χ.val.symm (Φ.invFun z)) := by
    intro z hz
    have heqz : w =ᶠ[𝓝 z] (fun z => u (χ.val.symm (Φ.invFun z))) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'
      exact ((hball z' hz').2.2.1).symm
    rw [LelongNumberComparison.lelongNumber_congr heqz,
      lelongNumber_comp_flat_point χ Φ hΦe u (hball z hz).2.1,
      SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  have hsq : ∀ y ∈ W, (c : ℝ≥0∞) ≤
      SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u y := by
    intro y hy
    rw [hc]
    exact iInf_le (fun y : W =>
      SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u y.val) ⟨y, hy⟩
  -- `c ≤ c' a`
  have hcq : (c : ℝ) ≤ (c' : ℝ) * a := by
    have hinfr := hinf r hr (min_le_right _ _)
    have h2 : 2 * (c : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (c' : ℝ) * a) := by
      rw [← hinfr]
      refine le_iInf₂ fun z hz => ?_
      rw [hlel z hz.1]
      gcongr
      exact hsq _ ((hmemW z hz.1).mpr hz.2)
    have h3 : ENNReal.ofReal (2 * (c : ℝ)) ≤ ENNReal.ofReal (2 * (c' : ℝ) * a) := by
      rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
    linarith
  -- the flat neighbourhood
  have hΦcont : ContinuousOn Φ.toFun Φ.source := Φ.toFun_holomorphic.continuousOn
  have hUopen : IsOpen (χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)) :=
    χ.val.continuousOn.isOpen_inter_preimage χ.val.open_source
      (hΦcont.isOpen_inter_preimage Φ.isOpen_source isOpen_ball)
  have hx0 : Φ.toFun (χ.val x) ∈ ball (0 : ComplexModel (m + 1)) r := by
    rw [hΦ0]
    exact mem_ball_self hr
  have hxU : x ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) :=
    ⟨hxχ, Φ.center_mem_source, hx0⟩
  have hback : ∀ y ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r),
      χ.val.symm (Φ.invFun (Φ.toFun (χ.val y))) = y := fun y hy => by
    rw [Φ.left_inv _ hy.2.1, χ.val.left_inv hy.1]
  refine ⟨c' * a, by positivity, by push_cast; exact hcq,
    ⟨_, hUopen.mem_nhds hxU, fun y hy => ?_⟩, fun c₀ hc₀ => ?_⟩
  · -- the lower bound for the Lelong numbers along `W` near `x`
    obtain ⟨hyW, hyU⟩ := hy
    have hz : Φ.toFun (χ.val y) ∈ ball (0 : ComplexModel (m + 1)) r := hyU.2.2
    have hz0 : (Φ.toFun (χ.val y)) (Fin.last m) = 0 := (hflat y hyU.1 hyU.2.1).mp hyW
    have h1 := hlower _ (ball_subset_ball (min_le_right _ _) hz) hz0
    rw [hlel _ hz, hback y hyU] at h1
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((c' : ℝ) * a) ≤
        2 * SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u y := by
      rwa [show (2 : ℝ) * c' * a = 2 * (c' * a) by ring, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat] at h1
    have h3 := (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
    push_cast
    exact h3
  · -- the residual has analytic singularities near `x`
    have hcc : (c : ℝ) = c₀ := hc₀
    set δ : ℚ := c' * a - c₀ with hδdef
    have hδR : ((δ : ℚ) : ℝ) = (c' : ℝ) * a - c := by
      rw [hδdef, hcc]
      push_cast
      ring
    have hδ0 : 0 ≤ δ := by
      have h' : (0 : ℝ) ≤ ((δ : ℚ) : ℝ) := by rw [hδR]; linarith
      exact_mod_cast h'
    set L1 : ComplexModel (m + 1) → EReal :=
      fun z => generatorLog (fun _ : Fin 1 => fun z : ComplexModel (m + 1) => z (Fin.last m)) z
      with hL1def
    set A : ComplexModel (m + 1) → EReal :=
      fun z => ((c' : ℝ) : EReal) * generatorLog H z + ((δ : ℝ) : EReal) * L1 z with hAdef
    set v := ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)
      with hvdef
    have hoff : ThetaPshCodimTwoExtension.ThetaPshOff (θ - (c : ℝ) • E.curvature).val W
        (smoothDivisorOffResidual E c u) := by
      simpa only [hEW] using SGPT.Okounkov.thetaPshOff_smoothDivisorOffResidual hu E c
    -- the residual off `W` in flat coordinates
    have hformula : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z (Fin.last m) ≠ 0 →
        v (χ.val.symm (Φ.invFun z)) =
          A z + ((b z - c * ell (χ.val.symm (Φ.invFun z)) : ℝ) : EReal) := by
      intro z hz hz0
      obtain ⟨-, hzT, hu_z, hF_z, -, -, -, -, hV_z⟩ := hball z hz
      have hnotW : χ.val.symm (Φ.invFun z) ∉ W := fun h => hz0 ((hmemW z hz).mp h)
      rw [hvdef, ThetaPshCodimTwoExtension.extensionAcross_eq_of_notMem hW.1 hoff hnotW]
      have hnotS : χ.val.symm (Φ.invFun z) ∉ E.support := hEW ▸ hnotW
      simp only [smoothDivisorOffResidual, if_neg hnotS]
      have hiT : Φ.invFun z ∈ χ.val.target := hΦe (Φ.mapsTo_invFun hzT)
      have hcoordz : Φ.toFun (χ.val (χ.val.symm (Φ.invFun z))) = z := by
        rw [χ.val.right_inv hiT, Φ.right_inv z hzT]
      rw [hu_z, hweight _ hV_z, hcoordz]
      have hgen : generatorLog F z = generatorLog (fun i z => z (Fin.last m) ^ a * H i z) z := by
        simp only [generatorLog_eq_log_sum, hF_z]
      rw [hgen, generatorLog_pow_mul (fun z : ComplexModel (m + 1) => z (Fin.last m))]
      have hpos : 0 < ‖z (Fin.last m)‖ ^ 2 := by
        have : 0 < ‖z (Fin.last m)‖ := norm_pos_iff.mpr hz0
        positivity
      rw [ENNReal.log_ofReal_of_pos hpos]
      have hL1 : L1 z = ((Real.log (‖z (Fin.last m)‖ ^ 2) : ℝ) : EReal) := by
        rw [hL1def]
        dsimp only
        rw [generatorLog_single, ENNReal.log_ofReal_of_pos hpos]
      rw [hAdef]
      dsimp only
      rw [hL1, hδR, ereal_residual_identity hc'R]
    -- a uniform bound for the real remainder, including the local potential `ρ`
    set B₁ : ℝ := Bb + c * Bℓ + Bρ with hB₁def
    have hB₁ : 0 ≤ B₁ := by positivity
    have hβ : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
        |b z - c * ell (χ.val.symm (Φ.invFun z)) + ρ (Φ.invFun z)| ≤ B₁ := by
      intro z hz
      obtain ⟨-, -, -, -, -, h6, h7, h8, -⟩ := hball z hz
      have hc0 : (0 : ℝ) ≤ c := NNReal.coe_nonneg c
      calc |b z - c * ell (χ.val.symm (Φ.invFun z)) + ρ (Φ.invFun z)|
          ≤ |b z - c * ell (χ.val.symm (Φ.invFun z))| + |ρ (Φ.invFun z)| := abs_add_le _ _
        _ ≤ (|b z| + |c * ell (χ.val.symm (Φ.invFun z))|) + |ρ (Φ.invFun z)| := by
            gcongr
            exact abs_sub _ _
        _ = |b z| + c * |ell (χ.val.symm (Φ.invFun z))| + |ρ (Φ.invFun z)| := by
            rw [abs_mul, abs_of_nonneg hc0]
        _ ≤ Bb + c * Bℓ + Bρ := by gcongr
    have hPoff : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z (Fin.last m) ≠ 0 →
        chartFunction v χ (Φ.invFun z) + (ρ (Φ.invFun z) : EReal) =
          A z + ((b z - c * ell (χ.val.symm (Φ.invFun z)) + ρ (Φ.invFun z) : ℝ) : EReal) := by
      intro z hz hz0
      change v (χ.val.symm (Φ.invFun z)) + _ = _
      rw [hformula z hz hz0, add_assoc, ← EReal.coe_add]
    -- plurisubharmonicity of the model `A`
    have hApsh : PlurisubharmonicOn A (ball (0 : ComplexModel (m + 1)) r) := by
      have h1 : PlurisubharmonicOn (fun z => ((c' : ℝ) : EReal) * generatorLog H z)
          (ball (0 : ComplexModel (m + 1)) r) := fun z hz =>
        Pending.plurisubharmonicAt_scaled_generatorLog
          ⟨ball 0 r, isOpen_ball, hz,
            fun i z' hz' => ((hball z' hz').2.2.2.2.1 i).differentiableWithinAt⟩ hc'R
      have h2 : PlurisubharmonicOn (fun z => ((δ : ℝ) : EReal) * L1 z)
          (ball (0 : ComplexModel (m + 1)) r) :=
        MeteredDivisorPositivity.plurisubharmonicOn_qsmul_generatorLog isOpen_ball hδ0
          (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiable.differentiableOn
      exact h1.add h2
    have hPpsh : PlurisubharmonicOn
        (fun z => chartFunction v χ (Φ.invFun z) + (ρ (Φ.invFun z) : EReal))
        (ball (0 : ComplexModel (m + 1)) r) :=
      hP.mono (fun z hz => (hball z hz).1)
    have hae : ∀ᵐ z ∂(volume : Measure (ComplexModel (m + 1))).restrict (ball 0 r),
        z ∈ ball (0 : ComplexModel (m + 1)) r ∧ z (Fin.last m) ≠ 0 := by
      have hnull := volume_last_coordinate_hyperplane m
      have h1 : ∀ᵐ z ∂(volume : Measure (ComplexModel (m + 1))), z (Fin.last m) ≠ 0 := by
        rw [ae_iff]
        simpa using hnull
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet, ae_restrict_of_ae h1]
        with z h1 h2
      exact ⟨h1, h2⟩
    have hup : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
        chartFunction v χ (Φ.invFun z) + (ρ (Φ.invFun z) : EReal) ≤ A z + (B₁ : EReal) := by
      refine PlurisubharmonicOn.le_of_ae_le hPpsh isOpen_ball
        (hApsh.add_const B₁).upperSemicontinuousOn volume ?_
      filter_upwards [hae] with z hz
      rw [hPoff z hz.1 hz.2]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_of_abs_le (hβ z hz.1)))
    have hlow : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
        A z + ((-B₁ : ℝ) : EReal) ≤ chartFunction v χ (Φ.invFun z) + (ρ (Φ.invFun z) : EReal) := by
      refine PlurisubharmonicOn.le_of_ae_le (hApsh.add_const (-B₁)) isOpen_ball
        hPpsh.upperSemicontinuousOn volume ?_
      filter_upwards [hae] with z hz
      rw [hPoff z hz.1 hz.2]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hβ z hz.1)))
    -- the two-sided bound on the manifold
    have hAtop : ∀ z, A z ≠ ⊤ := by
      intro z
      have h1 := ereal_coe_mul_ne_top hc'R.le (generatorLog_ne_top H z)
      have h2 := ereal_coe_mul_ne_top (show (0 : ℝ) ≤ (δ : ℝ) by exact_mod_cast hδ0)
        (generatorLog_ne_top (fun _ : Fin 1 => fun z : ComplexModel (m + 1) => z (Fin.last m)) z)
      exact (EReal.add_lt_top h1 h2).ne
    have hrem : ∀ y, y ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) →
        ∃ rr : ℝ, |rr| ≤ B₁ + Bρ ∧ v y = A (Φ.toFun (χ.val y)) + (rr : EReal) := by
      intro y hy
      have hz : Φ.toFun (χ.val y) ∈ ball (0 : ComplexModel (m + 1)) r := hy.2.2
      have hρz := (hball _ hz).2.2.2.2.2.2.2.1
      have hup' := ereal_le_add_sub_of_add_le (hup _ hz)
      have hlow' := ereal_add_sub_le_of_le_add (hlow _ hz)
      change v (χ.val.symm (Φ.invFun (Φ.toFun (χ.val y)))) ≤ _ at hup'
      change _ ≤ v (χ.val.symm (Φ.invFun (Φ.toFun (χ.val y)))) at hlow'
      rw [hback y hy] at hup' hlow'
      refine exists_remainder_of_bounds (by positivity) (hAtop _) ?_ ?_
      · refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)) hlow'
        linarith [le_abs_self (ρ (Φ.invFun (Φ.toFun (χ.val y))))]
      · refine le_trans hup' (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
        linarith [neg_abs_le (ρ (Φ.invFun (Φ.toFun (χ.val y))))]
    choose! Rr hRr using hrem
    -- chartwise analytic types
    have hΨ : ∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)), z ∈ e.val.target →
        e.val.symm z ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) →
        ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => Φ.toFun (χ.val (e.val.symm w))) w := by
      intro e z hz hzU
      have hsrc : z ∈ (chartTransition e χ).source := by
        simp only [chartTransition, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
        exact ⟨hz, hzU.1⟩
      have hcont := (chartTransition e χ).continuousAt hsrc
      have hΦmem : Φ.source ∈ 𝓝 (chartTransition e χ z) := Φ.isOpen_source.mem_nhds hzU.2.1
      filter_upwards [(chartTransition e χ).open_source.mem_nhds hsrc,
        hcont.eventually hΦmem] with w hw hwΦ
      exact (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hwΦ)).comp w
        ((chartTransition_contDiffAt e χ hw).differentiableAt (by simp))
    have hAtype : ∀ y ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r),
        HasAnalyticSingularityTypeAt A (Φ.toFun (χ.val y)) := by
      intro y hy
      have hz : Φ.toFun (χ.val y) ∈ ball (0 : ComplexModel (m + 1)) r := hy.2.2
      have hHz : ∀ i, ∀ᶠ w in 𝓝 (Φ.toFun (χ.val y)), DifferentiableAt ℂ (H i) w := by
        intro i
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        exact (hball w hw).2.2.2.2.1 i
      have h1 := hasAnalyticSingularityTypeAt_generatorLog hHz hc'
      have h2 : HasAnalyticSingularityTypeAt (fun w => ((δ : ℝ) : EReal) * L1 w)
          (Φ.toFun (χ.val y)) := by
        rcases hδ0.lt_or_eq with hδ | hδ
        · exact hasAnalyticSingularityTypeAt_generatorLog
            (H := fun _ : Fin 1 => fun w : ComplexModel (m + 1) => w (Fin.last m))
            (fun _ => Eventually.of_forall fun w =>
              (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiableAt) hδ
        · have hfun : (fun w => ((δ : ℝ) : EReal) * L1 w) = fun _ => 0 := by
            funext w
            rw [← hδ]
            simp
          rw [hfun]
          exact hasAnalyticSingularityTypeAt_zero _
      exact Pending.RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add h1 h2
    have hct := chartTypeOver_of_comp_coordinates (φ := fun y => A (Φ.toFun (χ.val y))) hUopen
      hΨ hAtype (fun _ _ => rfl)
    exact ⟨_, hUopen, hxU, hct.of_eqOn_add_bounded hUopen (fun y hy => (hRr y hy).1)
      (fun y hy => (hRr y hy).2)⟩


variable [CompactSpace M]

/-- **Blueprint `tok:siu-analytic`, smooth hypersurfaces.** Let `u` be `θ`-psh with analytic
singularities, `W` a smooth connected hypersurface, `c = ν(u, W)` the generic Lelong number of `u`
along `W` and `v = u - c log |s_W|²` (for a smooth metric of `𝒪(W)`), extended across `W`. Then
`c` is rational and `v` has analytic singularities. -/
theorem residual_rational_and_hasManifoldAnalyticSingularityType
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hA : HasManifoldAnalyticSingularityType (n := m + 1) u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) (D : EffectiveDivisor (m + 1) M)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) W) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEW : E.support = W) (hmetric : DivisorMetric.IsDivisorMetric D E) :
    let c : ℝ≥0 := (SourceTraceRepresentativeDefinition.sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : W → M) u).toNNReal
    (∃ c₀ : ℚ, 0 ≤ c₀ ∧ (c : ℝ) = c₀) ∧
      HasManifoldAnalyticSingularityType (n := m + 1)
        (ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)) := by
  intro c
  have hc : (c : ℝ≥0∞) = SourceTraceRepresentativeDefinition.sourceGenericLelongNumber
      (n := m + 1) (Subtype.val : W → M) u :=
    ENNReal.coe_toNNReal (SGPT.Okounkov.sourceGeneric_subtype_ne_top hW hu.quasiPshPotential)
  have hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)) :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D hDI E hEW
      hmetric
  -- the local data at every point of `W`
  have hloc : ∀ x ∈ W, ∃ (q : ℚ) (N : Set M), 0 ≤ q ∧ (c : ℝ) ≤ q ∧ N ∈ 𝓝 x ∧
      (∀ y ∈ W ∩ N, ENNReal.ofReal q ≤
        SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u y) ∧
      ∀ c₀ : ℚ, (c : ℝ) = c₀ → ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ChartTypeOver (n := m + 1)
          (ThetaPshCodimTwoExtension.extensionAcross W (smoothDivisorOffResidual E c u)) U := by
    intro x hx
    obtain ⟨-, -, Φ, hΦe, hΦ0, hflat⟩ := hW.2.2 x hx
    obtain ⟨V₁, ell, hV₁, hxV₁, -, hell, hweight⟩ :=
      SGPT.Okounkov.exists_divisor_metric_flat_normal_form Φ hΦe hflat hW D hDI E hmetric
    have hflat' : ∀ y ∈ (complexChartAt (n := m + 1) x).val.source,
        (complexChartAt (n := m + 1) x).val y ∈ Φ.source →
        (y ∈ W ↔ (Φ.toFun ((complexChartAt (n := m + 1) x).val y)) (Fin.last m) = 0) :=
      fun y hy hyΦ => (hflat hy hyΦ).trans (SGPT.Okounkov.mem_codimension_one_plane_iff _)
    have hxs : x ∈ (complexChartAt (n := m + 1) x).val.source := mem_complexChartAt_source x
    have hellC : ContinuousAt ell x := by
      have hO : IsOpen ((complexChartAt (n := m + 1) x).val.target ∩
          (complexChartAt (n := m + 1) x).val.symm ⁻¹' V₁) :=
        (complexChartAt (n := m + 1) x).val.isOpen_inter_preimage_symm hV₁
      have hmem : (complexChartAt (n := m + 1) x).val x ∈
          (complexChartAt (n := m + 1) x).val.target ∩
            (complexChartAt (n := m + 1) x).val.symm ⁻¹' V₁ := by
        refine ⟨(complexChartAt (n := m + 1) x).val.map_source hxs, ?_⟩
        simp only [mem_preimage, (complexChartAt (n := m + 1) x).val.left_inv hxs]
        exact hxV₁
      have h1 := ((hell (complexChartAt (n := m + 1) x)).continuousOn.continuousAt
        (hO.mem_nhds hmem))
      have h2 := ContinuousAt.comp (f := (complexChartAt (n := m + 1) x).val)
        (h1.congr (by rfl)) ((complexChartAt (n := m + 1) x).val.continuousAt hxs)
      refine h2.congr ?_
      filter_upwards [(complexChartAt (n := m + 1) x).val.open_source.mem_nhds hxs] with y hy
      exact congrArg ell ((complexChartAt (n := m + 1) x).val.left_inv hy)
    obtain ⟨q, hq0, hcq, ⟨N, hN, hNb⟩, hct⟩ := exists_local_residual_data_of_flattening hu hA hW
      E hEW hc hv (complexChartAt (n := m + 1) x) hxs Φ hΦe hΦ0 hflat' hV₁ hxV₁ hellC
      (fun y hy => hweight y hy)
    exact ⟨q, N, hq0, hcq, hN, hNb, hct⟩
  choose q N hq0 hcq hNx hNbound hct using hloc
  -- rationality of `c`, by compactness of `W`
  have hWne : W.Nonempty := hW.2.1.nonempty
  obtain ⟨t, ht⟩ := hW.1.isCompact.elim_nhds_subcover' (fun x hx => N x hx)
    (fun x hx => hNx x hx)
  have htne : t.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hWne
    obtain ⟨x, hxt, -⟩ := mem_iUnion₂.mp (ht hx₀)
    exact ⟨x, hxt⟩
  set q₀ : ℚ := t.inf' htne (fun x => q x.1 x.2) with hq₀def
  have hcq₀ : (c : ℝ) = q₀ := by
    apply le_antisymm
    · obtain ⟨x, hxt, hx⟩ := Finset.exists_mem_eq_inf' htne (fun x => q x.1 x.2)
      rw [hq₀def, hx]
      exact hcq x.1 x.2
    · have hle : ENNReal.ofReal (q₀ : ℝ) ≤ (c : ℝ≥0∞) := by
        rw [hc]
        refine le_iInf fun y => ?_
        obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht y.2)
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hNbound x.1 x.2 y ⟨y.2, hyx⟩)
        exact_mod_cast Finset.inf'_le (fun x => q x.1 x.2) hxt
      rw [← ENNReal.ofReal_coe_nnreal] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg c)).mp hle
  have hq₀0 : 0 ≤ q₀ := by
    have : (0 : ℝ) ≤ (q₀ : ℝ) := hcq₀ ▸ NNReal.coe_nonneg c
    exact_mod_cast this
  refine ⟨⟨q₀, hq₀0, hcq₀⟩, ?_⟩
  -- the analytic type, point by point
  apply hasManifoldAnalyticSingularityType_of_chartTypeOver
  intro x
  by_cases hx : x ∈ W
  · obtain ⟨U, -, hxU, hU⟩ := hct x hx q₀ hcq₀
    exact ⟨U, hxU, hU⟩
  · have hxS : x ∉ E.support := by rw [hEW]; exact hx
    obtain ⟨Fw, hFc, hFeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hxS
    obtain ⟨C, hC0, hC⟩ := boundedRealGermAt_of_continuousAt hFc
    have h1 : ∀ᶠ y in 𝓝 x, y ∉ W := hW.1.isOpen_compl.mem_nhds hx
    have hev : ∀ᶠ y in 𝓝 x, y ∉ W ∧ E.weight y = (Fw y : EReal) ∧ |Fw y| ≤ C :=
      h1.and (hFeq.and hC)
    obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hev
    refine ⟨U, hxU, ?_⟩
    have hoff : ThetaPshCodimTwoExtension.ThetaPshOff (θ - (c : ℝ) • E.curvature).val W
        (smoothDivisorOffResidual E c u) := by
      simpa only [hEW] using SGPT.Okounkov.thetaPshOff_smoothDivisorOffResidual hu E c
    refine ChartTypeOver.of_eqOn_add_bounded (φ := u) (fun e z hz _ => hA e z hz) hU
      (R := fun y => -((c : ℝ) * Fw y)) (C := (c : ℝ) * C) ?_ ?_
    · intro y hy
      rw [abs_neg, abs_mul, abs_of_nonneg (NNReal.coe_nonneg c)]
      exact mul_le_mul_of_nonneg_left (hUsub hy).2.2 (NNReal.coe_nonneg c)
    · intro y hy
      obtain ⟨hyW, hyF, -⟩ := hUsub hy
      rw [ThetaPshCodimTwoExtension.extensionAcross_eq_of_notMem hW.1 hoff hyW]
      have hyS : y ∉ E.support := by rw [hEW]; exact hyW
      simp only [smoothDivisorOffResidual, if_neg hyS, hyF, ← EReal.coe_mul]
      rw [sub_eq_add_neg, EReal.coe_neg]

end SGPT.Okounkov.TranscendentalCore
