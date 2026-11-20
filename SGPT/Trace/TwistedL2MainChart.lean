import SGPT.Trace.TwistedL2MainUnitFrame

/-!
# Chart computations for the twisted `L²` estimate

Basic facts on the local pieces of `TwistedL2MainStatement.lean`: chart integrals, the local
weight `p = -log |e|² + φ - log ρ` and `e^{-p} = |e|² e^{-φ} ρ`, the operator `ϑ = chartTheta`,
and the realization of `H₁ = L²(U, L; e^{-φ}/(a+b) dμ)` as `L²(μ|_U)` through the coordinate
`H1coord s = (e^{-φ}/(a+b))^{1/2} ⟪ε, s⟫` (`ε` the measurable unit frame).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1 SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Charts -/

theorem isOpen_chartFrameDomain (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (e : AtlasFrame L) : IsOpen (chartFrameDomain L c e) :=
  c.val.isOpen_inter_preimage_symm e.val.open_baseSet

theorem isOpen_chartFrameDomain_inter (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (e : AtlasFrame L) {U : Set X} (hU : IsOpen U) :
    IsOpen (chartFrameDomain L c e ∩ c.val.symm ⁻¹' U) := by
  have h := c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter hU)
  simpa [chartFrameDomain, preimage_inter, inter_assoc] using h

/-- A function smooth on `U` in all charts is continuous on `U`. -/
theorem mainContinuousOn_of_chartSmoothOn {f : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hf : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) f U) : ContinuousOn f U := by
  intro x hx
  set c := complexChartAt (n := n) x
  have hxs : x ∈ c.val.source := mem_complexChartAt_source x
  have hcz : c.val x ∈ c.val.target ∩ c.val.symm ⁻¹' U := by
    refine ⟨c.val.map_source hxs, ?_⟩
    simp [c.val.left_inv hxs, hx]
  have hopen : IsOpen (c.val.target ∩ c.val.symm ⁻¹' U) := c.val.isOpen_inter_preimage_symm hU
  have h1 : ContinuousAt (fun z => f (c.val.symm z)) (c.val x) :=
    ((hf c).continuousOn.continuousAt (hopen.mem_nhds hcz))
  have h2 : ContinuousAt c.val x := c.val.continuousAt hxs
  have h3 : ContinuousAt (fun y => f (c.val.symm (c.val y))) x := h1.comp h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [c.val.open_source.mem_nhds hxs] with y hy
  simp [c.val.left_inv hy]

variable [MeasurableSpace X] [BorelSpace X]

/-- **A set integral in a chart.**  If `μ = ρ dz` in the chart `c`, then for a measurable `f` and a
compact `K` inside the chart target, `∫_{c⁻¹(K)} f dμ = ∫_K ρ(z) f(c⁻¹ z) dz`. -/
theorem setIntegral_source_inter_preimage {μ : Measure X} (c : ComplexChart n X)
    {ρ : ComplexModel n → ℝ} (hρc : ContinuousOn ρ c.val.target)
    (hρpos : ∀ z ∈ c.val.target, 0 < ρ z)
    (hmap : Measure.map c.val (μ.restrict c.val.source) =
      (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ c.val.target)
    {f : X → ℂ} (hf : Measurable f) :
    ∫ x in c.val.source ∩ c.val ⁻¹' K, f x ∂μ = ∫ z in K, (ρ z : ℂ) * f (c.val.symm z) := by
  set ν := μ.restrict c.val.source with hν
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have he : AEMeasurable c.val ν :=
    c.val.continuousOn.aemeasurable c.val.open_source.measurableSet
  have hmapK : Measure.map c.val (ν.restrict (c.val ⁻¹' K)) =
      (volume.restrict K).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [← Measure.restrict_map_of_aemeasurable he hKm, hmap, restrict_withDensity hKm,
      Measure.restrict_restrict hKm, inter_eq_left.mpr hKt]
  have hF : AEStronglyMeasurable (fun z => f (c.val.symm z)) (volume.restrict K) :=
    (hf.comp_aemeasurable ((c.val.continuousOn_symm.mono hKt).aemeasurable hKm)).aestronglyMeasurable
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict K) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρc.mono hKt)).aemeasurable hKm
  have hS := measurableSet_source_inter_preimage c.val hK.isClosed
  calc ∫ x in c.val.source ∩ c.val ⁻¹' K, f x ∂μ
      = ∫ x in c.val.source ∩ c.val ⁻¹' K, f (c.val.symm (c.val x)) ∂μ :=
        setIntegral_congr_fun hS fun x hx => by rw [c.val.left_inv hx.1]
    _ = ∫ x, f (c.val.symm (c.val x)) ∂(ν.restrict (c.val ⁻¹' K)) := by
        rw [hν, Measure.restrict_restrict' c.val.open_source.measurableSet, inter_comm]
    _ = ∫ z, f (c.val.symm z) ∂(Measure.map c.val (ν.restrict (c.val ⁻¹' K))) := by
        refine (integral_map (f := fun z => f (c.val.symm z)) he.restrict ?_).symm
        rw [hmapK]
        exact hF.mono_ac (withDensity_absolutelyContinuous _ _)
    _ = ∫ z in K, (ENNReal.ofReal (ρ z)).toReal • f (c.val.symm z) := by
        rw [hmapK, integral_withDensity_eq_integral_toReal_smul₀ hρ
          (Eventually.of_forall fun z => ENNReal.ofReal_lt_top) (fun z => f (c.val.symm z))]
    _ = ∫ z in K, (ρ z : ℂ) * f (c.val.symm z) := by
        refine setIntegral_congr_fun hKm fun z hz => ?_
        rw [ENNReal.toReal_ofReal (hρpos z (hKt hz)).le, Complex.real_smul]

/-- Compact subsets of a chart have finite measure. -/
theorem measure_source_inter_preimage_lt_top {μ : Measure X} (c : ComplexChart n X)
    {ρ : ComplexModel n → ℝ} (hρc : ContinuousOn ρ c.val.target)
    (hmap : Measure.map c.val (μ.restrict c.val.source) =
      (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ c.val.target) :
    μ (c.val.source ∩ c.val ⁻¹' K) < ⊤ := by
  have h := setLIntegral_source_inter_preimage c hρc hmap hK hKt (f := fun _ => (1 : ℝ≥0∞))
    measurable_const
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
    mul_one] at h
  rw [h]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hρc.mono hKt)
  calc ∫⁻ z in K, ENNReal.ofReal (ρ z) ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC z hz)
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- `λ`-a.e. on a chart target gives `μ`-a.e. on the chart source. -/
theorem ae_source_of_ae_target {μ : Measure X} (c : ComplexChart n X) {ρ : ComplexModel n → ℝ}
    (hmap : Measure.map c.val (μ.restrict c.val.source) =
      (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {P : ComplexModel n → Prop} (h : ∀ᵐ z ∂(volume.restrict c.val.target), P z) :
    ∀ᵐ x ∂(μ.restrict c.val.source), P (c.val x) := by
  have he : AEMeasurable c.val (μ.restrict c.val.source) :=
    c.val.continuousOn.aemeasurable c.val.open_source.measurableSet
  refine ae_of_ae_map he ?_
  rw [hmap]
  exact (withDensity_absolutelyContinuous _ _).ae_le h

end SGPT.Trace.TwistedL2
