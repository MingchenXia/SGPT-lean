import SGPT.Envelopes.LapClass3Density
import SGPT.Envelopes.DNTC11Density

/-!
# The Monge–Ampère measure `θ_fⁿ` of `f ∈ C^{1,1̄}(X)`

Lane CZ-LP (`claude-cz-lp`, node `czlp:measure`).  The book (remark after `lma:DNTroof`) defines,
for `f ∈ C^{1,1̄}(X)`, `θ_fⁿ` as the absolutely continuous measure whose density is the top power of
`θ + ddᶜf`, the complex Hessian of `f` being a function.  We define it by its chart densities:

* `IsLapTopMeasure θ f μ`: in every chart `e`, for every smooth local potential `ψ` of `θ` on
  `W ⊆ e.target`, every locally integrable Hessian density `h` of `f ∘ e⁻¹ + ψ` on `W`
  (`CZLp.IsHessianDensityOn`) and every measurable `K ⊆ W`,
  `μ(e⁻¹ K) = ∫_K max((n!/πⁿ) Re det h, 0) dV`.
  (As for `DNTC11.c11TopMeasure`, the positive part of the signed density is taken; on contact sets
  the density is nonnegative, `ae_hessDensity_nonneg_on_contact`.)
* `lapTopMeasure θ f`: the measure with this property (`0` if there is none).

Main results (`n = m + 1`; `X` compact with a Kähler form `ω`, `f` continuous with bounded
`ω`-Laplacian):

* `exists_isLapTopMeasure`: such a measure exists — `kahlerVolume.withDensity ρ`, with `ρ` the almost
  everywhere limit of the densities `(θ + ddᶜv_k)ⁿ/ωⁿ` of the strong approximations `v_k`
  (`LapClass3Density`); in particular it does not depend on choices.
* `eq_of_isLapTopMeasure`, `isLapTopMeasure_lapTopMeasure`, `lapTopMeasure_image_eq`: uniqueness and
  the chart formula for `lapTopMeasure θ f` (it does not depend on `ω`).
* `lapTopMeasure_eq_c11TopMeasure`: for `f` with bounded complex Hessian it is the measure
  `DNTC11.c11TopMeasure` of the earlier clauses.
* `ae_kahlerVolume_of_chart`, `ae_chart_of_ae_kahlerVolume`: null sets of `ωⁿ` are the sets that are
  Lebesgue null in every chart.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix ComplexOrder ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ClosedTopCurrents SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### Definition -/

/-- **The chart formula for `θ_fⁿ`**: in every chart, for every smooth local potential `ψ` of `θ` on
`W`, every locally integrable Hessian density `h` of `f ∘ e⁻¹ + ψ` on `W` and every measurable
`K ⊆ W`, `μ(e⁻¹ K) = ∫_K max((n!/πⁿ) Re det h, 0) dV`. -/
def IsLapTopMeasure (θ : ClosedRealOneOneForm n M) (f : M → ℝ) (μ : Measure M) : Prop :=
  ∀ (e : ComplexChart n M) (W : Set (ComplexModel n)) (ψ : ComplexModel n → ℝ)
    (h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ), IsSmoothLocalPotential θ.val e W ψ →
    IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W →
    ∀ K, MeasurableSet K → K ⊆ W →
      μ (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (hessDensity h z)

/-- `f` has a locally integrable Hessian density in every chart. -/
def HasHessianDensities (f : M → ℝ) : Prop :=
  ∀ e : ComplexChart n M, ∃ h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ,
    IsHessianDensityOn (fun z => f (e.val.symm z)) h e.val.target

/-- **`θ_fⁿ` for `f ∈ C^{1,1̄}(X)`**: the measure with the chart formula `IsLapTopMeasure` (it exists
and is unique for `f` with bounded `ω`-Laplacian, `isLapTopMeasure_lapTopMeasure`,
`eq_of_isLapTopMeasure`); `0` if there is none. -/
def lapTopMeasure (θ : ClosedRealOneOneForm n M) (f : M → ℝ) : Measure M := by
  classical
  exact if h : ∃ μ, IsLapTopMeasure θ f μ then Classical.choose h else 0

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Local Hessian densities of `f ∘ e⁻¹ + ψ`. -/
theorem HasHessianDensities.exists_add {f : M → ℝ} (hf : HasHessianDensities (n := n) f)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} (hW : IsOpen W) (hWt : W ⊆ e.val.target)
    {ψ : ComplexModel n → ℝ} (hψ : ContDiffOn ℝ ∞ ψ W) :
    ∃ h, IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W := by
  obtain ⟨h, hh⟩ := hf e
  exact ⟨_, (hh.mono hW hWt).add_contDiffOn hψ⟩

omit [IsComplexManifold n M] [CompactSpace M] in
/-- A chart piece of a measurable set. -/
theorem measurableSet_chart_piece (e : ComplexChart n M) {W : Set (ComplexModel n)}
    (hW : IsOpen W) {S : Set M} (hS : MeasurableSet S) :
    MeasurableSet (e.val '' (S ∩ (e.val.source ∩ e.val ⁻¹' W))) := by
  have hSN : S ∩ (e.val.source ∩ e.val ⁻¹' W) ⊆ e.val.source := fun y hy => hy.2.1
  rw [e.val.image_eq_target_inter_inv_preimage hSN]
  exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
    e.val.continuousOn_symm (hS.inter (e.val.isOpen_inter_preimage hW).measurableSet)

omit [CompactSpace M] in
/-- **Uniqueness of `θ_fⁿ`**: two measures with the chart formula agree. -/
theorem eq_of_isLapTopMeasure {θ : ClosedRealOneOneForm n M} {f : M → ℝ}
    (hf : HasHessianDensities (n := n) f) {μ ν : Measure M} (hμ : IsLapTopMeasure θ f μ)
    (hν : IsLapTopMeasure θ f ν) : μ = ν := by
  classical
  have hpatch : ∀ x : M, ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ μ.restrict N = ν.restrict N := by
    intro x
    set e := complexChartAt (n := n) x with he
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ψ, hz₀W, hψ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x) hz₀
    obtain ⟨h, hh⟩ := hf.exists_add e hψ.1 hψ.2.1 hψ.2.2.1
    set N := e.val.source ∩ e.val ⁻¹' W with hN
    refine ⟨N, e.val.isOpen_inter_preimage hψ.1, ⟨hxe, hz₀W⟩, ?_⟩
    ext S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
    have hSN : S ∩ N ⊆ e.val.source := fun y hy => hy.2.1
    set K := e.val '' (S ∩ N) with hK
    have hKm : MeasurableSet K := measurableSet_chart_piece e hψ.1 hS
    have hKW : K ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2.2
    have hSK : S ∩ N = e.val.symm '' K := (e.val.symm_image_image_of_subset_source hSN).symm
    rw [hSK, hμ e W ψ h hψ hh K hKm hKW, hν e W ψ h hψ hh K hKm hKW]
  choose N hNo hxN hN using hpatch
  exact GlobalSlotStokes.measure_eq_of_restrict_eq_of_openCover (fun x => N x) hNo
    (fun x => ⟨x, hxN x⟩) hN

omit [BorelSpace M] [CompactSpace M] in
theorem isLapTopMeasure_lapTopMeasure {θ : ClosedRealOneOneForm n M} {f : M → ℝ}
    (h : ∃ μ, IsLapTopMeasure θ f μ) : IsLapTopMeasure θ f (lapTopMeasure θ f) := by
  classical
  unfold lapTopMeasure
  rw [dif_pos h]
  exact Classical.choose_spec h

omit [CompactSpace M] in
theorem eq_lapTopMeasure {θ : ClosedRealOneOneForm n M} {f : M → ℝ} (hf : HasHessianDensities (n := n) f)
    {μ : Measure M} (hμ : IsLapTopMeasure θ f μ) : μ = lapTopMeasure θ f :=
  eq_of_isLapTopMeasure hf hμ (isLapTopMeasure_lapTopMeasure ⟨μ, hμ⟩)

/-! ### Consistency with the bounded-Hessian measure -/

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Functions with bounded complex Hessian have Hessian densities. -/
theorem hasHessianDensities_of_hasBoundedComplexHessian {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) : HasHessianDensities (n := n) f := fun e => by
  obtain ⟨h, hh⟩ := hf.2 e
  exact ⟨h, isHessianDensityOn_of_bounded hh⟩

/-- **For `f` with bounded complex Hessian, `θ_fⁿ` is `DNTC11.c11TopMeasure`.** -/
theorem lapTopMeasure_eq_c11TopMeasure (hn : 0 < n) (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f) :
    lapTopMeasure θ f = c11TopMeasure w θ f := by
  have hc : IsLapTopMeasure θ f (c11TopMeasure w θ f) := by
    intro e W ψ h hψ hh K hK hKW
    obtain ⟨h', hh'⟩ := hf.exists_density_add e hψ.1 hψ.2.1 hψ.2.2.1
    rw [c11TopMeasure_image_eq hn w θ hf hψ hh' hK hKW]
    have hae := hh.ae_eq (isHessianDensityOn_of_bounded hh')
    refine setLIntegral_congr_fun_ae hK ?_
    filter_upwards [hae] with z hz hzK
    rw [hessDensity, hessDensity, hz (hKW hzK)]
  exact (eq_lapTopMeasure (hasHessianDensities_of_hasBoundedComplexHessian hf) hc).symm

/-! ### Null sets in charts -/

section Null

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- The Kähler volume in a chart. -/
theorem lintegral_kahlerVolume_image (w : KahlerBackground (m + 1) Y) (e : ComplexChart (m + 1) Y)
    {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K) (hKt : K ⊆ e.val.target)
    {g : Y → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in e.val.symm '' K, g x ∂(kahlerVolume w) =
      ∫⁻ z in K, ENNReal.ofReal (volDensity w e z) * g (e.val.symm z) := by
  have hω : ∀ _ : Fin (m + 1), ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin (m + 1) => w.form) (fun _ _ => 0) hω :=
    rfl
  rw [hvol, SmoothMixedMeasureDensity.setLIntegral_image_eq hω e hK hKt hg]
  refine setLIntegral_congr_fun hK fun z _ => ?_
  simp only [SmoothMixedMeasureDensity.chartDensity, volDensity]
  rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]

theorem kahlerVolume_image (w : KahlerBackground (m + 1) Y) (e : ComplexChart (m + 1) Y)
    {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K) (hKt : K ⊆ e.val.target) :
    kahlerVolume w (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (volDensity w e z) := by
  have h := lintegral_kahlerVolume_image w e hK hKt (g := fun _ => 1) measurable_const
  simp only [mul_one, lintegral_const, one_mul] at h
  rw [Measure.restrict_apply_univ] at h
  exact h

/-- **Chart-null sets are `ωⁿ`-null.** -/
theorem ae_kahlerVolume_of_chart (w : KahlerBackground (m + 1) Y) {P : Y → Prop}
    (h : ∀ x₀ : Y, ∃ (e : ComplexChart (m + 1) Y) (W : Set (ComplexModel (m + 1))),
      IsOpen W ∧ W ⊆ e.val.target ∧ e.val x₀ ∈ W ∧ x₀ ∈ e.val.source ∧
        ∀ᵐ z, z ∈ W → P (e.val.symm z)) :
    ∀ᵐ x ∂(kahlerVolume w), P x := by
  have hloc : ∀ x₀ : Y, ∃ N : Set Y, IsOpen N ∧ x₀ ∈ N ∧ ∀ᵐ x ∂(kahlerVolume w), x ∈ N → P x := by
    intro x₀
    obtain ⟨e, W, hW, hWt, hzW, hx₀, hP⟩ := h x₀
    refine ⟨e.val.source ∩ e.val ⁻¹' W, e.val.isOpen_inter_preimage hW, ⟨hx₀, hzW⟩, ?_⟩
    set B : Set (ComplexModel (m + 1)) := {z | ¬(z ∈ W → P (e.val.symm z))} with hB
    have hB0 : volume B = 0 := hP
    set Z := toMeasurable volume B ∩ W with hZ
    have hZm : MeasurableSet Z := (measurableSet_toMeasurable _ _).inter hW.measurableSet
    have hZt : Z ⊆ e.val.target := fun z hz => hWt hz.2
    have hZ0 : volume Z = 0 :=
      measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact hB0)
    have himg : kahlerVolume w (e.val.symm '' Z) = 0 := by
      rw [kahlerVolume_image w e hZm hZt]
      exact setLIntegral_measure_zero _ _ hZ0
    refine measure_mono_null (fun x hx => ?_) himg
    have hx' : ¬(x ∈ e.val.source ∩ e.val ⁻¹' W → P x) := hx
    obtain ⟨⟨hxs, hxW⟩, hPx⟩ := Classical.not_imp.mp hx'
    refine ⟨e.val x, ⟨subset_toMeasurable _ _ ?_, hxW⟩, e.val.left_inv hxs⟩
    show ¬(e.val x ∈ W → P (e.val.symm (e.val x)))
    rw [e.val.left_inv hxs]
    exact fun h' => hPx (h' hxW)
  choose N hNo hxN hN using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable N hNo
  have : Countable T := hTc.to_subtype
  have hall : ∀ᵐ x ∂(kahlerVolume w), ∀ i : T, x ∈ N i → P x := ae_all_iff.mpr fun i => hN i
  filter_upwards [hall] with x hx
  have hxU : x ∈ ⋃ i ∈ T, N i := by rw [hTU]; exact mem_iUnion.mpr ⟨x, hxN x⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
  exact hx ⟨i, hi⟩ hxi

/-- **`ωⁿ`-null sets are null in every chart.** -/
theorem ae_chart_of_ae_kahlerVolume (w : KahlerBackground (m + 1) Y) {P : Y → Prop}
    (h : ∀ᵐ x ∂(kahlerVolume w), P x) (e : ComplexChart (m + 1) Y) :
    ∀ᵐ z, z ∈ e.val.target → P (e.val.symm z) := by
  set S := toMeasurable (kahlerVolume w) {x | ¬P x} with hS
  have hS0 : kahlerVolume w S = 0 := by rw [hS, measure_toMeasurable]; exact h
  set Z := e.val.target ∩ e.val.symm ⁻¹' S with hZ
  have hZm : MeasurableSet Z := SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
    e.val.open_target.measurableSet e.val.continuousOn_symm (measurableSet_toMeasurable _ _)
  have hZt : Z ⊆ e.val.target := inter_subset_left
  have himg : kahlerVolume w (e.val.symm '' Z) = 0 :=
    measure_mono_null (by rintro _ ⟨z, hz, rfl⟩; exact hz.2) hS0
  rw [kahlerVolume_image w e hZm hZt] at himg
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (volDensity w e z)) (volume.restrict Z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuousOn_volDensity w e).mono hZt).aemeasurable hZm)
  have h0 := (lintegral_eq_zero_iff' hmeas).mp himg
  have hnot : ∀ᵐ z, z ∉ Z := by
    have h1 : ∀ᵐ z, z ∈ Z → ENNReal.ofReal (volDensity w e z) = 0 :=
      (ae_restrict_iff' hZm).mp h0
    filter_upwards [h1] with z hz hzZ
    have := hz hzZ
    rw [ENNReal.ofReal_eq_zero] at this
    exact absurd (volDensity_pos w e (hZt hzZ)) (not_lt.mpr this)
  filter_upwards [hnot] with z hz hzt
  by_contra hP
  exact hz ⟨hzt, subset_toMeasurable _ _ hP⟩

end Null

/-! ### Existence -/

section Exists

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **`C^{1,1̄}(X) ⊆ W^{2,2}_loc`** (complex Hessians): functions with bounded `ω`-Laplacian have
locally integrable Hessian densities in every chart. -/
theorem hasHessianDensities_of_hasBoundedMetricLaplacian (w : KahlerBackground (m + 1) Y)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) : HasHessianDensities (n := m + 1) f :=
  fun e => by
    obtain ⟨A⟩ := nonempty_lapApprox w hf
    obtain ⟨h, hh, -⟩ := A.exists_density hf.1 e
    exact ⟨h, hh⟩

/-- **Existence of `θ_fⁿ`** for `f ∈ C^{1,1̄}(X)`: the measure `max(ρ, 0) ωⁿ`, where `ρ` is the
almost everywhere limit of the densities `(θ + ddᶜv_k)ⁿ/ωⁿ` of the strong approximations. -/
theorem exists_isLapTopMeasure (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    ∃ μ : Measure Y, IsLapTopMeasure θ f μ := by
  classical
  obtain ⟨A⟩ := nonempty_lapApprox w hf
  choose H hH hHt using fun e : ComplexChart (m + 1) Y => A.exists_density hf.1 e
  set ρk : ℕ → Y → ℝ := fun k x => topRatio w.form.val
    (formPow (θ + ddcClosedForm (A.v k) (A.smooth k)).val (m + 1)) x with hρk
  have hρc : ∀ k, Continuous (ρk k) := fun k => continuous_topRatio w.isKahler.1 _
  -- convergence in a chart
  have hchart : ∀ (e : ComplexChart (m + 1) Y) (W : Set (ComplexModel (m + 1)))
      (ψ : ComplexModel (m + 1) → ℝ), IsSmoothLocalPotential θ.val e W ψ →
      ∀ᵐ z, z ∈ W → Tendsto (fun k => ρk k (e.val.symm z)) atTop
        (𝓝 (hessDensity (fun z => H e z + smoothHess W ψ z) z / volDensity w e z)) := by
    intro e W ψ hψ
    filter_upwards [hHt e] with z hz hzW
    have hzt : z ∈ e.val.target := hψ.2.1 hzW
    have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hψ2 : ContDiffAt ℝ 2 ψ z := ((hψ.2.2.1 z hzW).contDiffAt (hψ.1.mem_nhds hzW)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hρeq : ∀ k, ρk k (e.val.symm z) =
        hessDensity (fun z => complexHessian (fun y => A.v k (e.val.symm y)) z +
          smoothHess W ψ z) z / volDensity w e z := fun k => by
      have hv2 : ContDiffAt ℝ 2 (fun y => A.v k (e.val.symm y)) z :=
        ((A.smooth k e z hzt).contDiffAt (e.val.open_target.mem_nhds hzt)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hS := SGPT.Okounkov.TranscendentalWN.smoothDensity_eq_topDensity_formPow θ
        (A.smooth k) hψ hzW
      simp only [hρk]
      rw [topRatio_eq_chartRatio w.isKahler.1 _ hx, chartRatio, e.val.right_inv hzt, ← hS,
        smoothDensity_eq_hessDensity]
      congr 1
      · simp only [hessDensity]
        rw [AubinYauLocalStep.complexHessian_fun_add hv2 hψ2]
        simp [smoothHess, hzW]
    simp_rw [hρeq]
    refine Tendsto.div_const ?_ _
    exact tendsto_hessDensity ((hz hzt).add tendsto_const_nhds)
  -- almost everywhere convergence on `Y`
  have hae : ∀ᵐ x ∂(kahlerVolume w), ∃ l, Tendsto (fun k => ρk k x) atTop (𝓝 l) := by
    refine ae_kahlerVolume_of_chart w fun x₀ => ?_
    set e := complexChartAt (n := m + 1) x₀
    have hxe : x₀ ∈ e.val.source := mem_complexChartAt_source x₀
    have hz₀ : e.val x₀ ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ψ, hz₀W, hψ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x₀) hz₀
    refine ⟨e, W, hψ.1, hψ.2.1, hz₀W, hxe, ?_⟩
    filter_upwards [hchart e W ψ hψ] with z hz hzW
    exact ⟨_, hz hzW⟩
  obtain ⟨ρ, hρm, hρt⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun k => (hρc k).aemeasurable) hae
  refine ⟨(kahlerVolume w).withDensity fun x => ENNReal.ofReal (ρ x), ?_⟩
  intro e W ψ h hψ hh K hK hKW
  have hKt : K ⊆ e.val.target := hKW.trans hψ.2.1
  rw [withDensity_apply _ (SmoothMixedMeasureDensity.measurableSet_chartSymm_image e hK hKt),
    lintegral_kahlerVolume_image w e hK hKt (g := fun x => ENNReal.ofReal (ρ x))
      (ENNReal.measurable_ofReal.comp hρm)]
  refine setLIntegral_congr_fun_ae hK ?_
  have hdens : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z)
      (fun z => H e z + smoothHess W ψ z) W :=
    ((hH e).mono hψ.1 hψ.2.1).add_contDiffOn hψ.2.2.1
  filter_upwards [ae_chart_of_ae_kahlerVolume w hρt e, hchart e W ψ hψ, hh.ae_eq hdens]
    with z h1 h2 h3 hzK
  have hzW := hKW hzK
  have hzt := hKt hzK
  have hlim := tendsto_nhds_unique (h1 hzt) (h2 hzW)
  have hv : 0 < volDensity w e z := volDensity_pos w e hzt
  rw [← ENNReal.ofReal_mul hv.le, hlim, mul_div_cancel₀ _ hv.ne']
  congr 1
  simp only [hessDensity, h3 hzW]

/-- **`θ_fⁿ` satisfies the chart formula** for `f ∈ C^{1,1̄}(X)`. -/
theorem isLapTopMeasure_lapTopMeasure_of_hasBoundedMetricLaplacian (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    IsLapTopMeasure θ f (lapTopMeasure θ f) :=
  isLapTopMeasure_lapTopMeasure (exists_isLapTopMeasure w θ hf)

/-- **The chart formula for `θ_fⁿ`**, `f ∈ C^{1,1̄}(X)`. -/
theorem lapTopMeasure_image_eq (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f)
    {e : ComplexChart (m + 1) Y} {W : Set (ComplexModel (m + 1))} {ψ : ComplexModel (m + 1) → ℝ}
    (hψ : IsSmoothLocalPotential θ.val e W ψ)
    {h : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W) {K : Set (ComplexModel (m + 1))}
    (hK : MeasurableSet K) (hKW : K ⊆ W) :
    lapTopMeasure θ f (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (hessDensity h z) :=
  isLapTopMeasure_lapTopMeasure_of_hasBoundedMetricLaplacian w θ hf e W ψ h hψ hh K hK hKW

end Exists

end SGPT.Envelopes.LapClass3
