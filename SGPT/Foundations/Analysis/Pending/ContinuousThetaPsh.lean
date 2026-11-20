import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing

set_option autoImplicit false

/-!
# A continuous function that is locally `θ`-psh as a distribution is `θ`-psh

Let `v : M → ℝ` be continuous on a complex manifold.  Suppose that in every chart `e` the chart
distribution `[v ∘ e⁻¹]` is locally `θ`-psh in the sense of distributions
(`ThetaPshChartLimitGluing.IsLocallyThetaPshDistribution`: near every point there is a smooth
local potential `ρ` of `θ` such that `[v ∘ e⁻¹] + ρ` has nonnegative distributional Levi form).
Then `v` itself, as an extended-real function, is `θ`-psh
(`thetaPlurisubharmonic_of_continuous_of_isLocallyThetaPshDistribution`).

Proof (Demailly, *Complex Analytic and Differential Geometry*, Ch. I, Thm. 5.8 and the
uniqueness of psh representatives): on the domain `W` of a local representative there is a psh
function `u` with `u = v ∘ e⁻¹ + ρ` almost everywhere (`ThetaPshChartLimitGluing.LocalRep`).
Since `v ∘ e⁻¹ + ρ` is continuous, the two functions agree everywhere on `W`:
`u ≤ v ∘ e⁻¹ + ρ` because a psh function below an upper semicontinuous one almost everywhere is
below it everywhere (`PlurisubharmonicOn.le_of_ae_le`), and `v ∘ e⁻¹ + ρ ≤ u` because a lower
semicontinuous function below an upper semicontinuous one almost everywhere is below it
everywhere (`le_of_ae_le_of_semicontinuousOn`: the set where the inequality fails would contain a
nonempty open set).  Hence `v ∘ e⁻¹ + ρ` is psh on `W`, which is the definition of `θ`-psh.

Statement handed over by TN-CLASSICAL (I-0831 C-0025, piece (b1) of the B6 nef-core glue,
Boucksom 4.8 / Demailly--Păun 2.12): it upgrades the `ε`-level Levi identity of the fibre
potentials (`ProductStokesLevi`, `PositivityLeviLink`) to `θ`-plurisubharmonicity, to which
`ThetaPshUniformL1Bound` applies.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.ContinuousThetaPsh

open FirstPass ThetaPshChartLimitGluing

section Semicontinuity

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [μ.IsOpenPosMeasure]

/-- If `w` is lower semicontinuous and `u` upper semicontinuous on an open set `W`, and `w ≤ u`
almost everywhere on `W`, then `w ≤ u` everywhere on `W`: otherwise `u < q < w` on a nonempty
open subset of `W` for some `q`. -/
theorem le_of_ae_le_of_semicontinuousOn {u w : E → EReal} {W : Set E} (hW : IsOpen W)
    (hu : UpperSemicontinuousOn u W) (hw : LowerSemicontinuousOn w W)
    (hae : ∀ᵐ y ∂μ.restrict W, w y ≤ u y) : ∀ x ∈ W, w x ≤ u x := by
  intro x hx
  by_contra hnot
  have hlt : u x < w x := lt_of_not_ge hnot
  obtain ⟨q, huq, hqw⟩ := exists_between hlt
  have h1 : ∀ᶠ y in 𝓝 x, u y < q := by
    have := hu x hx q huq
    rwa [nhdsWithin_eq_nhds.2 (hW.mem_nhds hx)] at this
  have h2 : ∀ᶠ y in 𝓝 x, q < w y := by
    have := hw x hx q hqw
    rwa [nhdsWithin_eq_nhds.2 (hW.mem_nhds hx)] at this
  obtain ⟨V, hVsub, hVo, hxV⟩ := _root_.mem_nhds_iff.1 ((h1.and h2).and (hW.mem_nhds hx))
  have hae' : ∀ᵐ y ∂μ, y ∈ W → w y ≤ u y := (ae_restrict_iff' hW.measurableSet).1 hae
  have hV0 : μ V = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae'] with y hy hyV
    obtain ⟨⟨hyu, hyw⟩, hyW⟩ := hVsub hyV
    exact absurd (hy hyW) (not_le.2 (hyu.trans hyw))
  exact hVo.measure_ne_zero μ ⟨x, hxV⟩ hV0

end Semicontinuity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A continuous function which is locally `θ`-psh as a distribution in every chart is
`θ`-psh** (I-0831 C-0025, (b1)). -/
theorem thetaPlurisubharmonic_of_continuous_of_isLocallyThetaPshDistribution
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] {θ : SmoothRealForm n M 2}
    {v : M → ℝ} (hv : Continuous v)
    (hloc : ∀ e : ComplexChart n M,
      LocallyIntegrableOn (fun z => v (e.val.symm z)) (chartTarget e) μ)
    (h : ∀ e : ComplexChart n M, ThetaPshChartLimitGluing.IsLocallyThetaPshDistribution μ θ e
      (regularDistribution μ (fun z => v (e.val.symm z)) (hloc e))) :
    ThetaPlurisubharmonic θ (fun x => (v x : EReal)) := by
  intro e z hz
  obtain ⟨R, hzR⟩ := (h e).exists_localRep hz
  refine ⟨R.W, R.ρ, hzR, R.pot, ?_⟩
  have hWt : (R.W : Set (ComplexModel n)) ⊆ e.val.target := R.hW
  -- the continuous function `w = v ∘ e⁻¹ + ρ` on `W`
  set w : ComplexModel n → EReal := fun y => ((v (e.val.symm y) + R.ρ y : ℝ) : EReal) with hwdef
  have hwc : ContinuousOn w R.W :=
    continuous_coe_real_ereal.comp_continuousOn
      ((hv.comp_continuousOn (e.val.continuousOn_symm.mono hWt)).add
        R.pot.2.2.1.continuousOn)
  -- the psh representative `u` equals `w` almost everywhere on `W`
  obtain ⟨huP, huF, huL, huT⟩ := R.rep
  have hdist : regularDistribution μ (fun y => v (e.val.symm y) + R.ρ y)
      (((hloc e).mono_set R.hW).add R.hρi) =
        regularDistribution μ (fun y => (R.u y).toReal) huL := by
    rw [regularDistribution_add ((hloc e).mono_set R.hW) R.hρi,
      ← restrictDistribution_regularDistribution μ (hloc e) R.hW]
    exact huT
  have hae := ae_eq_of_regularDistribution_eq μ _ huL hdist
  have hae' : ∀ᵐ y ∂μ.restrict R.W, R.u y = w y := by
    filter_upwards [hae, huF] with y hy hyF
    rw [← EReal.coe_toReal hyF.1 hyF.2, hwdef]
    exact congrArg _ hy.symm
  -- hence `u = w` everywhere on `W`
  have hle1 := huP.le_of_ae_le R.W.isOpen hwc.upperSemicontinuousOn μ
    (hae'.mono fun _ hy => hy.le)
  have hle2 := le_of_ae_le_of_semicontinuousOn R.W.isOpen huP.upperSemicontinuousOn
    hwc.lowerSemicontinuousOn (hae'.mono fun _ hy => hy.ge)
  intro y hy
  refine (huP y hy).congr ?_
  filter_upwards [R.W.isOpen.mem_nhds hy] with x hx
  rw [le_antisymm (hle1 x hx) (hle2 x hx), hwdef]
  simp only [chartFunction, EReal.coe_add]

end SGPT.Foundations.Analysis.Pending.ContinuousThetaPsh
