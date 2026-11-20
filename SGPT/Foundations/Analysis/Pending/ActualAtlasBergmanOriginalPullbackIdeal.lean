import SGPT.Foundations.Analysis.Pending.ActualBergmanEvaluationMultiplierPullbackIdeal
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType

set_option autoImplicit false

/-! # Every actual atlas Hilbert kernel has the original multiplier pullback ideal

All evaluation forms, rather than selected sections, generate the same
original manifold multiplier ideal after every local holomorphic pullback.
The corrected weight and both actual chart transfers are produced from the
original theta-PSH potential and its smooth local theta-potential.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualAtlasBergmanOriginalPullbackIdeal

open FirstPass FirstPass.HolomorphicIdealSheaves BergmanKernelSmooth
  ActualBergmanEvaluationMultiplierPullbackIdeal QuantitativeRegularizationChartBranch

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem holomorphic_comp_atlas_symm (e : ComplexChart n X) {x : X}
    (hx : x ∈ e.val.source) {a : X → ℂ} (ha : HolomorphicAt n a x) :
    ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (fun z => a (e.val.symm z)) z := by
  have ht : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
    have h := e.val.continuousAt_symm (e.val.map_source hx)
    rw [ContinuousAt, e.val.left_inv hx] at h
    exact h
  filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hx), ht.eventually ha]
    with z hz haz
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact haz.comp z (mdifferentiableAt_atlas_symm
    (I := 𝓘(ℂ, ComplexModel n)) e.property hz)

private theorem holomorphic_comp_map {d : ℕ}
    {Φ : ComplexModel d → ComplexModel n}
    (hΦ : ∀ᶠ t in 𝓝 0, DifferentiableAt ℂ Φ t)
    {b : ComplexModel n → ℂ}
    (hb : ∀ᶠ z in 𝓝 (Φ 0), DifferentiableAt ℂ b z) :
    ∀ᶠ t in 𝓝 0, DifferentiableAt ℂ (fun t => b (Φ t)) t := by
  have ht := hΦ.self_of_nhds.continuousAt.tendsto
  filter_upwards [hΦ, ht.eventually hb] with t ht hbt
  exact hbt.comp t ht

/-- The actual original multiplier representative pulled back through the
specified atlas chart and the same holomorphic map. -/
def originalChartPullbackGerm {d : ℕ} {u : X → EReal} {c : ℝ}
    (e : ComplexChart n X) (Φ : ComplexModel d → ComplexModel n)
    (hΦ : ∀ᶠ t in 𝓝 0, DifferentiableAt ℂ Φ t) (hyT : Φ 0 ∈ e.val.target)
    (a : {a : X → ℂ // (multiplierIdeal (n := n) c u).mem (e.val.symm (Φ 0)) a}) :
    HolGerm (ComplexModel d) :=
  HolGerm.mk (fun t => a.val (e.val.symm (Φ t)))
    (holomorphic_comp_map hΦ (by
      simpa only [e.val.right_inv hyT] using
        holomorphic_comp_atlas_symm e (e.val.map_target hyT) a.property.1))

/-- Every atlas chart's full weighted evaluation ideal is precisely the
pullback of the same original manifold multiplier ideal. -/
theorem exists_full_evaluation_original_pullback_span {m : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    {θ : SmoothRealForm (m + 1) X 2} {u : X → EReal}
    (hu : ThetaPlurisubharmonic θ u) (e : ComplexChart (m + 1) X)
    {Ω : Set (ComplexModel (m + 1))} {ρ : ComplexModel (m + 1) → ℝ}
    (hρ : IsSmoothLocalPotential θ e Ω ρ)
    {c : ℝ} (hc : 0 < c) {L : Set (ComplexModel (m + 1))}
    (hLo : IsOpen L) (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L)
    (hLΩ : closure L ⊆ Ω) {K : Set (ComplexModel (m + 1))}
    (hKo : IsOpen K) (hKL : closure K ⊆ L) :
    ∃ hBw : BergmanWeight K (fun z => multiplierWeight c (correctedWeight e ρ u z)),
      DifferentiableOn ℂ (evalCLM hBw) K ∧
      ∀ (d : ℕ) (Φ : ComplexModel d → ComplexModel (m + 1))
        (hΦ : ∀ᶠ t in 𝓝 0, DifferentiableAt ℂ Φ t) (hyK : Φ 0 ∈ K),
        Ideal.span (range (evaluationGerm hBw Φ hΦ hyK)) =
          Ideal.span (range (originalChartPullbackGerm (u := u) (c := c) e Φ hΦ
            (hρ.2.1 ((subset_closure.trans
              (hKL.trans (subset_closure.trans hLΩ))) hyK)))) := by
  classical
  have hKΩ : K ⊆ Ω := subset_closure.trans (hKL.trans (subset_closure.trans hLΩ))
  have hKT : K ⊆ e.val.target := hKΩ.trans hρ.2.1
  have hpsh := plurisubharmonicOn_correctedWeight hu hρ
  let Ωo : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨Ω, hρ.1⟩
  obtain ⟨hBw, hA, hspan⟩ := exists_bergmanWeight_and_pullback_germ_span
    (Ω := Ωo) hpsh hc hLo hLc hLb hLΩ hKo hKL
  refine ⟨hBw, hA, ?_⟩
  intro d Φ hΦ hyK
  rw [hspan d Φ hΦ hyK]
  have hyT := hKT hyK
  let x : X := e.val.symm (Φ 0)
  have hx : x ∈ e.val.source := e.val.map_target hyT
  have hex : e.val x = Φ 0 := e.val.right_inv hyT
  have hxΩ : e.val x ∈ Ω := by rw [hex]; exact hKΩ hyK
  have ht : Tendsto Φ (𝓝 0) (𝓝 (Φ 0)) := hΦ.self_of_nhds.continuousAt.tendsto
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    have hb : MultiplierIntegrableAt (correctedWeight e ρ u) c b.val (e.val x) volume := by
      rw [hex]; exact b.property
    have ha := DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hu hc e
      hρ.1 hρ.2.2.1.continuousOn hx hxΩ hb
    let a : {a : X → ℂ // (multiplierIdeal (n := m + 1) c u).mem x a} :=
      ⟨fun p => b.val (e.val p), ha⟩
    have hEq : weightedPullbackGerm (Ψ := correctedWeight e ρ u) (c := c) Φ hΦ b =
        originalChartPullbackGerm (u := u) (c := c) e Φ hΦ hyT a := by
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [ht.eventually (e.val.open_target.mem_nhds hyT)] with t hty
      exact (congrArg b.val (e.val.right_inv hty)).symm
    rw [hEq]
    exact Ideal.subset_span ⟨a, rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    have hb : MultiplierIntegrableAt (correctedWeight e ρ u) c
        (fun z => a.val (e.val.symm z)) (e.val x) volume :=
      QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_corrected_of_mem_multiplierIdeal
        hu e hρ.1 hρ.2.2.1.continuousOn hpsh hc hx hxΩ a.property
    let b : {b : ComplexModel (m + 1) → ℂ //
        MultiplierIntegrableAt (correctedWeight e ρ u) c b (Φ 0) volume} :=
      ⟨fun z => a.val (e.val.symm z), by simpa only [hex] using hb⟩
    have hEq : originalChartPullbackGerm (u := u) (c := c) e Φ hΦ hyT a =
        weightedPullbackGerm (Ψ := correctedWeight e ρ u) (c := c) Φ hΦ b :=
      HolGerm.mk_eq_mk_iff.mpr (EventuallyEq.refl _ _)
    rw [hEq]
    exact Ideal.subset_span ⟨b, rfl⟩

end SGPT.Foundations.Analysis.Pending.ActualAtlasBergmanOriginalPullbackIdeal
