import SGPT.NPP.DN5Smoothing
import SGPT.NPP.DN5ChangeVar
import SGPT.Envelopes.TosC11cMetric
import SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence

/-!
# Regularity of the smoothing: the fields `contDiffOn`, `mono`, `add_const`

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 216–224: the smoothing is
"obtained by integrating `u` against a positive kernel of total mass one", "smooth … linear in
`u`", and "smooth for `w ≠ 0` even when `u` has poles").

* `exists_localKernelRep` — near every chart point the numerator of `Ψ` is
  `∫ g(e⁻¹ y) K((z, t), y) dy` with `K ≥ 0` smooth and supported in a compact part of the chart
  (`SGPT.NPP.DN5.exists_transportKernel` applied to `Φ = e ∘ F`, `k = χ(|ξ|²_ω)`).
* `exists_uniform_radius` — by compactness one radius `r₀` works at every point.
* `smoothing_contDiffOn`, `smoothing_mono`, `smoothing_add_const` — the fields `contDiffOn`,
  `mono`, `add_const` of `SGPT.NPP.DN2.IsJointSmoothing` for `Ψ = SGPT.NPP.DN5.smoothing wY A`
  and radii `t ∈ (0, r₀)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending IntegrationCurrent

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### The weight -/

section Weight

variable (wY : KahlerBackground N Y) (e : ComplexChart N Y)

theorem contDiffOn_fibreWeight :
    ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => fibreWeight wY e q.1 q.2)
      (e.val.target ×ˢ univ) := by
  have hα : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N =>
      SGPT.Envelopes.TosC11c.twoFormMetric (wY.form.val.coeff e q.1)) (e.val.target ×ˢ univ) :=
    (SGPT.Envelopes.TosC11c.isBoundedLinearMap_twoFormMetric (n := N)).contDiff.comp_contDiffOn
      ((wY.form.val.smooth e).comp contDiffOn_fst (fun q hq => hq.1))
  have hξ : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => q.2)
      (e.val.target ×ˢ univ) := contDiffOn_snd
  exact (DN3.contDiff_chi N).comp_contDiffOn
    (contDiffOn_const.mul ((hα.clm_apply hξ).clm_apply hξ))

/-- The support of the weight is bounded uniformly near every chart point. -/
theorem exists_fibreWeight_support_bound {z₀ : ComplexModel N} (hz₀ : z₀ ∈ e.val.target) :
    ∃ U : Set (ComplexModel N), IsOpen U ∧ z₀ ∈ U ∧ U ⊆ e.val.target ∧ ∃ R : ℝ,
      ∀ z ∈ U, ∀ ξ, fibreWeight wY e z ξ ≠ 0 → ‖ξ‖ ≤ R := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  have hK : closedBall z₀ (r / 2) ⊆ e.val.target :=
    (closedBall_subset_ball (by linarith)).trans hrsub
  obtain ⟨m, hm, hmK⟩ := SGPT.Analysis.KahlerNormal.exists_pos_le_apply_I_smul
    (wY.form.val.smooth e).continuousOn (fun z hz => (wY.isKahler.1 e z hz).2)
    (isCompact_closedBall z₀ (r / 2)) hK
  refine ⟨ball z₀ (r / 2), isOpen_ball, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hK, 1 + (Real.pi * m)⁻¹, ?_⟩
  intro z hz ξ hξ
  have hlt : fibreNormSq wY e z ξ < 1 := by
    by_contra h
    exact hξ (DN3.chi_eq_zero_of_le N (not_lt.mp h))
  have hle := hmK z (ball_subset_closedBall hz) ξ
  have hpm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have h2 : Real.pi * m * ‖ξ‖ ^ 2 < 1 := by
    unfold fibreNormSq DN2.chartNormSq at hlt
    nlinarith [Real.pi_pos]
  have h3 : ‖ξ‖ ^ 2 ≤ (Real.pi * m)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpm]
    linarith
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

end Weight

/-! ### Integrability in charts -/

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- An `ωⁿ`-integrable function is integrable, in a chart, on every compact part of the chart. -/
theorem integrableOn_chart_of_integrable (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {g : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) {C : Set (ComplexModel N)}
    (hC : IsCompact C) (hCt : C ⊆ e.val.target) :
    IntegrableOn (fun z => g (e.val.symm z)) C := by
  obtain ⟨ρ, hρ, hpos, hmap⟩ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY e
  let ν := (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))
  have hac : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hinv : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hac
  have hforward : AEMeasurable e.val ((kahlerVolume wY).restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hinvmap : AEMeasurable e.val.symm
      (Measure.map e.val ((kahlerVolume wY).restrict e.val.source)) := by
    rw [hmap]
    exact hinv
  have hleft : (e.val.symm ∘ e.val) =ᵐ[(kahlerVolume wY).restrict e.val.source] id :=
    (ae_restrict_mem e.val.open_source.measurableSet).mono fun x hx => e.val.left_inv hx
  have hν : (kahlerVolume wY).restrict e.val.source = Measure.map e.val.symm ν := by
    calc
      _ = Measure.map id ((kahlerVolume wY).restrict e.val.source) := Measure.map_id.symm
      _ = Measure.map (e.val.symm ∘ e.val) ((kahlerVolume wY).restrict e.val.source) :=
        (Measure.map_congr hleft).symm
      _ = Measure.map e.val.symm (Measure.map e.val ((kahlerVolume wY).restrict e.val.source)) :=
        (hinvmap.map_map_of_aemeasurable hforward).symm
      _ = _ := by rw [hmap]
  have hg1 : Integrable g (Measure.map e.val.symm ν) := by
    rw [← hν]
    exact hg.restrict
  have hg2 : Integrable (g ∘ e.val.symm) ν :=
    (integrable_map_measure hg1.aestronglyMeasurable hinv).mp hg1
  have hd : AEMeasurable (fun z => (ρ z).toNNReal) (volume.restrict e.val.target) :=
    (continuous_real_toNNReal.comp_continuousOn hρ.continuousOn).aemeasurable
      e.val.open_target.measurableSet
  have hg3 : Integrable (fun z => (ρ z).toNNReal • g (e.val.symm z))
      (volume.restrict e.val.target) :=
    (integrable_withDensity_iff_integrable_smul₀ hd).mp hg2
  have hg4 : IntegrableOn (fun z => ρ z * g (e.val.symm z)) C := by
    have h : IntegrableOn (fun z => (ρ z).toNNReal • g (e.val.symm z)) C :=
      hg3.mono_measure (Measure.restrict_mono hCt le_rfl)
    refine h.congr_fun (fun z hz => ?_) hC.measurableSet
    change ((ρ z).toNNReal : ℝ) * g (e.val.symm z) = ρ z * g (e.val.symm z)
    rw [Real.coe_toNNReal _ (hpos z (hCt hz)).le]
  have hinvρ : ContinuousOn (fun z => (ρ z)⁻¹) C :=
    (hρ.continuousOn.mono hCt).inv₀ (fun z hz => (hpos z (hCt hz)).ne')
  refine (hg4.continuousOn_mul hinvρ hC).congr_fun (fun z hz => ?_) hC.measurableSet
  change (ρ z)⁻¹ * (ρ z * g (e.val.symm z)) = g (e.val.symm z)
  rw [← mul_assoc, inv_mul_cancel₀ (hpos z (hCt hz)).ne', one_mul]

/-! ### Local kernel representations -/

/-- A local kernel representation of the numerator of the smoothing near `z₀` in the chart `e`. -/
structure LocalKernelRep (wY : KahlerBackground N Y) (A : FibreAtlas N Y) (e : ComplexChart N Y)
    (z₀ : ComplexModel N) (ε δ : ℝ) (C : Set (ComplexModel N))
    (K : ComplexModel N × ℝ → ComplexModel N → ℝ) : Prop where
  ε_pos : 0 < ε
  δ_pos : 0 < δ
  ball_subset : ball z₀ ε ⊆ e.val.target
  isCompact : IsCompact C
  subset_target : C ⊆ e.val.target
  smooth : ContDiffOn ℝ ∞ (fun q : (ComplexModel N × ℝ) × ComplexModel N => K q.1 q.2)
    ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ)
  supp : ∀ p y, y ∉ C → K p y = 0
  nonneg : ∀ p y, 0 ≤ K p y
  rep : ∀ z ∈ ball z₀ ε, ∀ t ∈ Ioo 0 δ, ∀ g : Y → ℝ,
    (∫ ξ, g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ) =
      ∫ y, g (e.val.symm y) * K (z, t) y

/-- **Local kernel representation** of the smoothing at every chart point. -/
theorem exists_localKernelRep (wY : KahlerBackground N Y) (A : FibreAtlas N Y)
    {e : ComplexChart N Y} {z₀ : ComplexModel N} (hz₀ : z₀ ∈ e.val.target) :
    ∃ ε δ C K, LocalKernelRep wY A e z₀ ε δ C K := by
  obtain ⟨U, hU, hz₀U, hUt, R, hR⟩ := exists_fibreWeight_support_bound wY e hz₀
  have hk := (contDiffOn_fibreWeight wY e).mono
    (prod_mono hUt (subset_refl (univ : Set (ComplexModel N))))
  obtain ⟨ε, δ, hε, hδ, C, hC, hCt, K, hK, hKC, hK0, hεU, hsrc, hrep⟩ :=
    exists_transportKernel (isLocalFibreMap_goodSet A e) hU hk hR hz₀U
      (mem_goodSet_of_mem_target A hz₀) (e.val.open_target.mem_nhds hz₀)
  refine ⟨ε, δ, C, K, ⟨hε, hδ, hεU.trans hUt, hC, hCt, hK, hKC,
    hK0 (fun z ξ => fibreWeight_nonneg wY e z ξ), fun z hz t ht g => ?_⟩⟩
  rw [← hrep z hz t ht (fun y => g (e.val.symm y))]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  change g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ =
    g (e.val.symm (e.val (fibreMap A e z (t • ξ)))) * fibreWeight wY e z ξ
  by_cases hw : fibreWeight wY e z ξ = 0
  · rw [hw, mul_zero, mul_zero]
  · rw [e.val.left_inv (goodSet_target A (hsrc z hz t ht ξ hw)).2]

section Rep

variable {wY : KahlerBackground N Y} {A : FibreAtlas N Y} {e : ComplexChart N Y}
  {z₀ : ComplexModel N} {ε δ : ℝ} {C : Set (ComplexModel N)}
  {K : ComplexModel N × ℝ → ComplexModel N → ℝ}

theorem LocalKernelRep.continuous_slice (h : LocalKernelRep wY A e z₀ ε δ C K)
    {z : ComplexModel N} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    Continuous (K (z, t)) := by
  have hc : Continuous fun y : ComplexModel N => ((z, t), y) :=
    continuous_const.prodMk continuous_id
  have H : ContinuousOn (fun q : (ComplexModel N × ℝ) × ComplexModel N => K q.1 q.2)
      ((ball z₀ ε ×ˢ Ioo 0 δ) ×ˢ univ) := h.smooth.continuousOn
  have H' := H.comp_continuous hc (fun y => ⟨⟨hz, ht⟩, mem_univ y⟩)
  exact H'

theorem LocalKernelRep.integrable_mul (h : LocalKernelRep wY A e z₀ ε δ C K)
    {g : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) {z : ComplexModel N} (hz : z ∈ ball z₀ ε)
    {t : ℝ} (ht : t ∈ Ioo 0 δ) : Integrable (fun y => g (e.val.symm y) * K (z, t) y) := by
  have hon : IntegrableOn (fun y => K (z, t) y * g (e.val.symm y)) C :=
    (integrableOn_chart_of_integrable wY e hg h.isCompact h.subset_target).continuousOn_mul
      (h.continuous_slice hz ht).continuousOn h.isCompact
  have hsupp : Function.support (fun y => g (e.val.symm y) * K (z, t) y) ⊆ C := by
    intro y hy
    by_contra hyC
    exact hy (by simp only [h.supp _ y hyC, mul_zero])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact hon.congr_fun (fun y _ => mul_comm _ _) h.isCompact.measurableSet

theorem LocalKernelRep.integrable_kernel (h : LocalKernelRep wY A e z₀ ε δ C K)
    {z : ComplexModel N} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    Integrable (K (z, t)) := by
  have hsupp : Function.support (K (z, t)) ⊆ C := by
    intro y hy
    by_contra hyC
    exact hy (h.supp _ y hyC)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact (h.continuous_slice hz ht).continuousOn.integrableOn_compact h.isCompact

/-- The denominator of the smoothing is the total mass of the kernel. -/
theorem LocalKernelRep.integral_fibreWeight (h : LocalKernelRep wY A e z₀ ε δ C K)
    {z : ComplexModel N} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    (∫ ξ, fibreWeight wY e z ξ) = ∫ y, K (z, t) y := by
  have H := h.rep z hz t ht (fun _ => 1)
  simp only [one_mul] at H
  exact H

/-- **The smoothing as a kernel quotient.** -/
theorem LocalKernelRep.chartSmoothing_eq (h : LocalKernelRep wY A e z₀ ε δ C K)
    {z : ComplexModel N} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) (g : Y → ℝ) :
    chartSmoothing wY A g e z t = (∫ y, g (e.val.symm y) * K (z, t) y) / ∫ y, K (z, t) y := by
  rw [chartSmoothing, h.rep z hz t ht g, h.integral_fibreWeight hz ht]

theorem LocalKernelRep.integral_kernel_pos (h : LocalKernelRep wY A e z₀ ε δ C K)
    {z : ComplexModel N} (hz : z ∈ ball z₀ ε) {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    0 < ∫ y, K (z, t) y := by
  rw [← h.integral_fibreWeight hz ht]
  exact integral_fibreWeight_pos wY (h.ball_subset hz)

/-- **`add_const`** in a local kernel representation. -/
theorem LocalKernelRep.chartSmoothing_add_const (h : LocalKernelRep wY A e z₀ ε δ C K)
    {g : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) {z : ComplexModel N} (hz : z ∈ ball z₀ ε)
    {t : ℝ} (ht : t ∈ Ioo 0 δ) (c : ℝ) :
    chartSmoothing wY A (fun y => g y + c) e z t = chartSmoothing wY A g e z t + c := by
  rw [h.chartSmoothing_eq hz ht, h.chartSmoothing_eq hz ht]
  have hpos := h.integral_kernel_pos hz ht
  simp_rw [add_mul]
  rw [integral_add (h.integrable_mul hg hz ht) ((h.integrable_kernel hz ht).const_mul c),
    integral_const_mul, add_div, mul_div_cancel_right₀ _ hpos.ne']

/-- **`mono`** in a local kernel representation. -/
theorem LocalKernelRep.chartSmoothing_mono (h : LocalKernelRep wY A e z₀ ε δ C K)
    {g g' : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) (hg' : Integrable g' (kahlerVolume wY))
    (hle : g ≤ᵐ[kahlerVolume wY] g') {z : ComplexModel N} (hz : z ∈ ball z₀ ε)
    {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    chartSmoothing wY A g e z t ≤ chartSmoothing wY A g' e z t := by
  rw [h.chartSmoothing_eq hz ht, h.chartSmoothing_eq hz ht]
  refine div_le_div_of_nonneg_right ?_ (h.integral_kernel_pos hz ht).le
  refine integral_mono_ae (h.integrable_mul hg hz ht) (h.integrable_mul hg' hz ht) ?_
  have hchart := KahlerVolumeChartAEEquivalence.ae_chartTarget_of_ae_kahlerVolume wY e hle
  have hchart' : ∀ᵐ y, y ∈ e.val.target → g (e.val.symm y) ≤ g' (e.val.symm y) :=
    (ae_restrict_iff' e.val.open_target.measurableSet).mp hchart
  filter_upwards [hchart'] with y hy
  by_cases hyC : y ∈ C
  · exact mul_le_mul_of_nonneg_right (hy (h.subset_target hyC)) (h.nonneg _ y)
  · simp only [h.supp _ y hyC, mul_zero, le_refl]

/-- **Smoothness** of the chart smoothing in a local kernel representation. -/
theorem LocalKernelRep.contDiffOn (h : LocalKernelRep wY A e z₀ ε δ C K)
    {g : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => chartSmoothing wY A g e p.1 p.2)
      (ball z₀ ε ×ˢ Ioo 0 δ) := by
  have hS : IsOpen (ball z₀ ε ×ˢ Ioo (0 : ℝ) δ) := isOpen_ball.prod isOpen_Ioo
  have hnum := contDiffOn_integral_mul_kernel hS h.smooth h.isCompact h.supp
    (integrableOn_chart_of_integrable wY e hg h.isCompact h.subset_target)
  have hden := contDiffOn_integral_mul_kernel hS h.smooth h.isCompact h.supp
    (f := fun _ => (1 : ℝ)) (continuousOn_const.integrableOn_compact h.isCompact)
  simp only [one_mul] at hden
  refine (hnum.div hden fun p hp => (h.integral_kernel_pos hp.1 hp.2).ne').congr ?_
  intro p hp
  exact h.chartSmoothing_eq hp.1 hp.2 g

end Rep

/-! ### A uniform radius -/

/-- **A uniform radius**: every point of `Y` lies in the domain of a local kernel representation
valid for all radii `t < r₀`. -/
theorem exists_uniform_radius (wY : KahlerBackground N Y) (A : FibreAtlas N Y) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x : Y, ∃ (e : ComplexChart N Y) (z₀ : ComplexModel N) (ε δ : ℝ)
      (C : Set (ComplexModel N)) (K : ComplexModel N × ℝ → ComplexModel N → ℝ),
      LocalKernelRep wY A e z₀ ε δ C K ∧ x ∈ e.val.source ∧ e.val x ∈ ball z₀ ε ∧ r₀ ≤ δ := by
  classical
  have hloc (x : Y) := exists_localKernelRep wY A
    ((complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x))
  choose ε δ C K hrep using hloc
  let V : Y → Set Y := fun x =>
    (complexChartAt (n := N) x).val.source ∩
      (complexChartAt (n := N) x).val ⁻¹' ball ((complexChartAt (n := N) x).val x) (ε x)
  have hVo (x : Y) : IsOpen (V x) :=
    (complexChartAt (n := N) x).val.isOpen_inter_preimage isOpen_ball
  have hxV (x : Y) : x ∈ V x := ⟨mem_complexChartAt_source x, mem_ball_self (hrep x).ε_pos⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  by_cases hsne : s.Nonempty
  · let r₀ := s.inf' hsne δ
    have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff hsne).mpr fun x _ => (hrep x).δ_pos
    refine ⟨r₀, hr₀, fun y => ?_⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨hxs, hy⟩ := mem_iUnion.mp hx
    exact ⟨_, _, _, _, _, _, hrep x, hy.1, hy.2, Finset.inf'_le δ hxs⟩
  · refine ⟨1, one_pos, fun y => ?_⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨hxs, _⟩ := mem_iUnion.mp hx
    exact absurd ⟨x, hxs⟩ hsne

/-! ### The fields `contDiffOn`, `mono`, `add_const` -/

section Fields

variable {wY : KahlerBackground N Y} {A : FibreAtlas N Y} {r₀ : ℝ}

/-- Abbreviation for the conclusion of `exists_uniform_radius`. -/
def IsUniformRadius (wY : KahlerBackground N Y) (A : FibreAtlas N Y) (r₀ : ℝ) : Prop :=
  0 < r₀ ∧ ∀ x : Y, ∃ (e : ComplexChart N Y) (z₀ : ComplexModel N) (ε δ : ℝ)
    (C : Set (ComplexModel N)) (K : ComplexModel N × ℝ → ComplexModel N → ℝ),
    LocalKernelRep wY A e z₀ ε δ C K ∧ x ∈ e.val.source ∧ e.val x ∈ ball z₀ ε ∧ r₀ ≤ δ

theorem exists_isUniformRadius (wY : KahlerBackground N Y) (A : FibreAtlas N Y) :
    ∃ r₀, IsUniformRadius wY A r₀ := by
  obtain ⟨r₀, h0, h⟩ := exists_uniform_radius wY A
  exact ⟨r₀, h0, h⟩

/-- **The field `add_const`.** -/
theorem smoothing_add_const (hr : IsUniformRadius wY A r₀) {g : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (c : ℝ) (x : Y) {t : ℝ} (ht : 0 < t) (htr : t < r₀) :
    smoothing wY A (fun y => g y + c) x t = smoothing wY A g x t + c := by
  obtain ⟨e, z₀, ε, δ, C, K, h, hxe, hxb, hδ⟩ := hr.2 x
  rw [smoothing_eq_chartSmoothing A hxe, smoothing_eq_chartSmoothing A hxe]
  exact h.chartSmoothing_add_const hg hxb ⟨ht, htr.trans_le hδ⟩ c

/-- **The field `mono`.** -/
theorem smoothing_mono (hr : IsUniformRadius wY A r₀) {g g' : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (hg' : Integrable g' (kahlerVolume wY))
    (hle : g ≤ᵐ[kahlerVolume wY] g') (x : Y) {t : ℝ} (ht : 0 < t) (htr : t < r₀) :
    smoothing wY A g x t ≤ smoothing wY A g' x t := by
  obtain ⟨e, z₀, ε, δ, C, K, h, hxe, hxb, hδ⟩ := hr.2 x
  rw [smoothing_eq_chartSmoothing A hxe, smoothing_eq_chartSmoothing A hxe]
  exact h.chartSmoothing_mono hg hg' hle hxb ⟨ht, htr.trans_le hδ⟩

/-- **The field `contDiffOn`**: in every chart, `(z, t) ↦ Ψ_g(e⁻¹ z, t)` is smooth on
`target × (0, r₀)`. -/
theorem smoothing_contDiffOn (hr : IsUniformRadius wY A r₀) {g : Y → ℝ}
    (hg : Integrable g (kahlerVolume wY)) (e' : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => smoothing wY A g (e'.val.symm p.1) p.2)
      (e'.val.target ×ˢ Ioo 0 r₀) := by
  intro p hp
  set x := e'.val.symm p.1
  obtain ⟨e, z₀, ε, δ, C, K, h, hxe, hxb, hδ⟩ := hr.2 x
  set τ := chartTransition e' e
  have hpτ : p.1 ∈ τ.source := mem_transition_source_iff.mpr ⟨hp.1, hxe⟩
  have hτp : τ p.1 = e.val x := rfl
  -- the open set where the representation applies
  have hτc : ContinuousOn τ τ.source := τ.continuousOn
  set S : Set (ComplexModel N × ℝ) := (τ.source ∩ τ ⁻¹' ball z₀ ε) ×ˢ Ioo 0 δ
  have hSo : IsOpen S :=
    (hτc.isOpen_inter_preimage τ.open_source isOpen_ball).prod isOpen_Ioo
  have hpb : τ p.1 ∈ ball z₀ ε := hxb
  have hpS : p ∈ S := ⟨⟨hpτ, hpb⟩, hp.2.1, hp.2.2.trans_le hδ⟩
  -- smoothness of the composite
  have hsm : ContDiffAt ℝ ∞
      (fun q : ComplexModel N × ℝ => chartSmoothing wY A g e (τ q.1) q.2) p := by
    have h1 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℝ => (τ q.1, q.2)) p :=
      ((transition_contDiffAt hpτ).comp p contDiffAt_fst).prodMk contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℝ => chartSmoothing wY A g e q.1 q.2)
        (τ p.1, p.2) :=
      (h.contDiffOn hg).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        ⟨hpb, hp.2.1, hp.2.2.trans_le hδ⟩)
    exact h2.comp p h1
  have heq : (fun q : ComplexModel N × ℝ => smoothing wY A g (e'.val.symm q.1) q.2) =ᶠ[𝓝 p]
      fun q => chartSmoothing wY A g e (τ q.1) q.2 := by
    filter_upwards [hSo.mem_nhds hpS] with q hq
    have hq1 : q.1 ∈ τ.source := hq.1.1
    have hqe : e'.val.symm q.1 ∈ e.val.source := (mem_transition_source_iff.mp hq1).2
    rw [smoothing_eq_chartSmoothing A hqe]
    rfl
  exact (hsm.congr_of_eventuallyEq heq).contDiffWithinAt

end Fields

end SGPT.NPP.DN5
