import SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshChartBounds
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

/-!
# Genuine original theta-PSH realization of actual weak chart distributions

The original corrected PSH regular distributions supply positivity.
The same finite local potential and original native restrictions are used
before applying the actual global singular representative gluing theorem.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshWeakLimitRealization

open FirstPass ThetaPshChartLimitGluing NaturalNormalizedThetaPshChartBounds

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Actual weak chart distributions of a genuine theta-PSH family retain local corrected Levi positivity. -/
theorem isLocallyThetaPshDistribution_of_genuine_chart_limit
    (hθ : HasSmoothLocalPotentials θ) {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} (hu : ∀ i, IsThetaPshPotential θ (u i))
    (T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ))
    (hT : ∀ e, IsChartLimit volume l (fun i x => (u i x).toReal) e (T e)) :
    ∀ e, IsLocallyThetaPshDistribution volume θ e (T e) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := hθ e z hz
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhds_iff.mp (hρ.1.mem_nhds hzW)
  let Ω : Opens (ComplexModel n) := ⟨ball z ε, isOpen_ball⟩
  have hΩW : (Ω : Set (ComplexModel n)) ⊆ W := hlocal
  have hΩt : Ω ≤ chartTarget e := hΩW.trans hρ.2.1
  have hpot : IsSmoothLocalPotential θ e Ω ρ := hρ.mono Ω.isOpen hΩW
  have hρi : LocallyIntegrableOn ρ Ω volume :=
    hpot.2.2.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  let corrected (i : ι) : ComplexModel n → EReal :=
    fun y => chartFunction (u i) e y + (ρ y : EReal)
  have hcpsh (i : ι) : PlurisubharmonicOn (corrected i) Ω :=
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      (hu i).1 e hpot
  have hne (i : ι) : ∃ y ∈ Ω, corrected i y ≠ ⊥ := by
    obtain ⟨y, hyΩ, hy⟩ :=
      (hu i).2.exists_chart_ne_bot e Ω.isOpen hΩt (mem_ball_self hε)
    exact ⟨y, hyΩ, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot (ρ y)⟩⟩
  have hpre : IsPreconnected (Ω : Set (ComplexModel n)) := (convex_ball z ε).isPreconnected
  have hraw (i : ι) : LocallyIntegrableOn
      (fun y => (chartFunction (u i) e y).toReal) Ω volume :=
    ((hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e).mono_set hΩt
  let S (i : ι) : 𝓓'(Ω, ℝ) := pshRegularDistribution (hcpsh i) volume hpre (hne i)
  have hS (i : ι) : S i =
      regularDistribution volume (fun y => (chartFunction (u i) e y).toReal) (hraw i) +
        regularDistribution volume ρ hρi := by
    rw [← regularDistribution_add (hraw i) hρi]
    change regularDistribution volume (fun y => (corrected i y).toReal) _ = _
    apply regularDistribution_congr_ae_on
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩt
      ((hu i).quasiPshPotential.ae_finite_chart e)] with y hy
    simp only [corrected, EReal.toReal_add hy.1 hy.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hweak : ∀ φ : 𝓓(Ω, ℝ), Tendsto (fun i => S i φ) l
      (𝓝 ((restrictDistribution (T e) hΩt + regularDistribution volume ρ hρi) φ)) := by
    intro φ
    let ψ : 𝓓(chartTarget e, ℝ) := TestFunction.monoCLM ℝ φ
    have hψ : (ψ : ComplexModel n → ℝ) = φ := by
      simp only [ψ, TestFunction.monoCLM_apply, le_refl, hΩt, and_self, ite_true]
    have h := (hT e ψ).add
      (tendsto_const_nhds (x := ∫ y, φ y * ρ y ∂volume))
    simpa only [hS, _root_.add_apply, regularDistribution_apply,
      restrictDistribution_apply, hψ, chartFunction, ψ] using h
  refine ⟨Ω, hΩt, ρ, hρi, mem_ball_self hε, hpot, ?_⟩
  exact PshUltrafilterLimit.HasNonnegativeDistributionalLevi.of_tendsto hweak
    (Eventually.of_forall (fun i =>
      (PshUltrafilterLimit.isPshRepresentative_pshRegularDistribution volume hpre
        (hcpsh i) (hne i)).hasNonnegativeDistributionalLevi))

/-- All actual weak chart distributions are represented by one genuine original theta-PSH potential. -/
theorem exists_genuine_of_chart_limit
    (hθ : HasSmoothLocalPotentials θ) {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} (hu : ∀ i, IsThetaPshPotential θ (u i))
    (T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ))
    (hT : ∀ e, IsChartLimit volume l (fun i x => (u i x).toReal) e (T e)) :
    ∃ v : M → EReal, IsThetaPshPotential θ v ∧
      ∀ (e : ComplexChart n M) (φ : 𝓓(chartTarget e, ℝ)),
        Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
          (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)) := by
  obtain ⟨v, hv, hrep⟩ := exists_isThetaPshPotential_of_isChartLimit
    (fun i x => (u i x).toReal) T hT
      (isLocallyThetaPshDistribution_of_genuine_chart_limit hθ hu T hT)
  refine ⟨v, hv, fun e φ => ?_⟩
  obtain ⟨hvloc, heq⟩ := (hrep e).2
  have h := hT e φ
  rw [heq, regularDistribution_apply] at h
  exact h

/-- Normalized original singular families internally produce a genuine weak theta-PSH limit. -/
theorem exists_genuine_weak_limit_of_normalized [CompactSpace M] [ConnectedSpace M]
    (hθ : HasSmoothLocalPotentials θ) {ι : Type*} (U : Ultrafilter ι)
    (u : ι → M → EReal) (hu : ∀ i, IsThetaPshPotential θ (u i))
    (hle : ∀ i x, u i x ≤ 0) (hnorm : ∀ i, ∃ x₀, 0 ≤ u i x₀) :
    ∃ v : M → EReal, IsThetaPshPotential θ v ∧
      ∀ (e : ComplexChart n M) (φ : 𝓓(chartTarget e, ℝ)),
        Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume)
          (U : Filter ι) (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)) := by
  obtain ⟨T, hT⟩ := exists_isChartLimit_of_normalized hθ U u hu hle hnorm
  exact exists_genuine_of_chart_limit hθ hu T hT

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshWeakLimitRealization
