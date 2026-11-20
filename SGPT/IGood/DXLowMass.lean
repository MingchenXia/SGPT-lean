import SGPT.IGood.DXLowFatou
import SGPT.Okounkov.TranscendentalWNConvFLChart
import SGPT.Okounkov.TranscendentalWNEnvelopeLocal
import SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

/-!
# The non-pluripolar mass is the integral of the pointwise Bergman limit

Blueprint `claude-dx-low`, node `claude-dx-low:mass`. For `φ ∈ PSH(X, θ)` smooth off its pole set,
`θ = c₁(L, h_L)`, `θ_φ` a Kähler current, and the pieces `E_a` and densities `G_a` of
`SGPT.IGood.DXLowFatou`:

`∫_X θ_φⁿ = θ_φⁿ(X \ P) = ∑_a θ_φⁿ(E_a) ≤ ∑_a ∫_{E_a} G_a dμ`
(`diagonalPotentialMass_le_sum_lintegral`).

Ingredients: the non-pluripolar measure does not charge the pole set
(`globalMixedMeasure_pole_null_of_nondegenerate`); in a chart, on a ball where `φ` is smooth, the
non-pluripolar measure is the Bedford–Taylor measure of `Φ = φ ∘ z⁻¹ - log |e_L|²`
(`lintegral_diagonalPotentialMeasure_eq_canonical`), which is at most `(ddᶜΦ)ⁿ = smoothDensity Φ dλ`
(`canonicalBedfordTaylorMeasure_contact_le` with equal potentials); a countable cover of the
smooth locus (Lindelöf) globalizes the local bound; and `G_a ρ_a = smoothDensity Φ_a` in the chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory Bundle TopologicalSpace
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
  SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SGPT.IGood.DXLow

/-- `smoothDensity u` is Borel measurable for every `u`. -/
theorem measurable_smoothDensity (u : ComplexModel n → ℝ) : Measurable (smoothDensity u) := by
  have h2 : Measurable (fderiv ℝ (fderiv ℝ u)) := measurable_fderiv ℝ _
  have hent : ∀ v w : ComplexModel n, Measurable (fun z => realHessian u z v w) := by
    intro v w
    simp_rw [realHessian_eq_fderiv]
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (ContinuousLinearMap.apply ℝ (ComplexModel n →L[ℝ] ℝ) v).continuous).measurable.comp h2
  have hH : Measurable (fun z => (fun j k => complexHessian u z j k : Fin n → Fin n → ℂ)) := by
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
    simp only [complexHessian]
    exact ((Complex.measurable_ofReal.comp ((hent _ _).add (hent _ _))).div_const 4).add
      (((Complex.measurable_ofReal.comp ((hent _ _).sub (hent _ _))).const_mul Complex.I).div_const 4)
  have hdc : Continuous (fun M : Fin n → Fin n → ℂ => (Matrix.det (M : Matrix (Fin n) (Fin n) ℂ)).re) :=
    Complex.continuous_re.comp (continuous_id.matrix_det)
  have hdet : Measurable (fun z => (complexHessian u z).det.re) := hdc.measurable.comp hH
  exact hdet.const_mul _

/-- Preimages of measurable sets under a chart (on its source) are measurable. -/
theorem measurableSet_chart_preimage (e : ComplexChart n X) {T : Set (ComplexModel n)}
    (hT : MeasurableSet T) : MeasurableSet (e.val.source ∩ e.val ⁻¹' T) := by
  classical
  have hm : Measurable (e.val.source.piecewise e.val (fun _ => (0 : ComplexModel n))) :=
    e.val.continuousOn.measurable_piecewise continuousOn_const e.val.open_source.measurableSet
  have : e.val.source ∩ e.val ⁻¹' T =
      e.val.source ∩ (e.val.source.piecewise e.val (fun _ => (0 : ComplexModel n))) ⁻¹' T := by
    ext x
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hx, ?_⟩
      simp only [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx]
      exact hxT
    · rintro ⟨hx, hxT⟩; exact ⟨hx, by simpa [Set.piecewise_eq_of_mem _ _ _ hx] using hxT⟩
  rw [this]
  exact e.val.open_source.measurableSet.inter (hm hT)

/-- Images of measurable subsets of a chart source are measurable. -/
theorem measurableSet_chart_image (e : ComplexChart n X) {S : Set X} (hS : MeasurableSet S)
    (hSs : S ⊆ e.val.source) : MeasurableSet (e.val '' S) := by
  classical
  have hm : Measurable (e.val.target.piecewise e.val.symm (fun _ => e.val.symm 0)) :=
    e.val.continuousOn_symm.measurable_piecewise continuousOn_const
      e.val.open_target.measurableSet
  rw [e.val.image_eq_target_inter_inv_preimage hSs]
  have : e.val.target ∩ e.val.symm ⁻¹' S =
      e.val.target ∩ (e.val.target.piecewise e.val.symm (fun _ => e.val.symm 0)) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨hz, hzS⟩
      refine ⟨hz, ?_⟩
      simp only [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hz]
      exact hzS
    · rintro ⟨hz, hzS⟩; exact ⟨hz, by simpa [Set.piecewise_eq_of_mem _ _ _ hz] using hzS⟩
  rw [this]
  exact e.val.open_target.measurableSet.inter (hm hS)

/-- **Reading a set integral in a chart**, measurable version of `setLIntegral_chart_ball`. -/
theorem setLIntegral_chart_measurable {μ : Measure X} (e : ComplexChart n X)
    {ρ : ComplexModel n → ℝ} (hρc : ContinuousOn ρ e.val.target)
    (hmap : Measure.map e.val (μ.restrict e.val.source) =
      (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {B : Set (ComplexModel n)} (hBm : MeasurableSet B) (hBt : B ⊆ e.val.target)
    {f : X → ℝ≥0∞} (hf : AEMeasurable (fun z => f (e.val.symm z)) (volume.restrict B)) :
    ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f x ∂μ =
      ∫⁻ z in B, f (e.val.symm z) * ENNReal.ofReal (ρ z) := by
  set ν := μ.restrict e.val.source with hν
  have he : AEMeasurable e.val ν :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hmapB : Measure.map e.val (ν.restrict (e.val ⁻¹' B)) =
      (volume.restrict B).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [← Measure.restrict_map_of_aemeasurable he hBm, hmap, restrict_withDensity hBm,
      Measure.restrict_restrict hBm, inter_eq_left.mpr hBt]
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict B) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρc.mono hBt)).aemeasurable hBm
  have hS : MeasurableSet (e.val.source ∩ e.val ⁻¹' B) := measurableSet_chart_preimage e hBm
  calc ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f x ∂μ
      = ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f (e.val.symm (e.val x)) ∂μ :=
        setLIntegral_congr_fun hS fun x hx => by rw [e.val.left_inv hx.1]
    _ = ∫⁻ x, f (e.val.symm (e.val x)) ∂(ν.restrict (e.val ⁻¹' B)) := by
        rw [hν, Measure.restrict_restrict' e.val.open_source.measurableSet, inter_comm]
    _ = ∫⁻ z, f (e.val.symm z) ∂(Measure.map e.val (ν.restrict (e.val ⁻¹' B))) := by
        refine (lintegral_map' (f := fun z => f (e.val.symm z)) ?_ he.restrict).symm
        rw [hmapB]
        exact hf.mono_ac (withDensity_absolutelyContinuous _ _)
    _ = ∫⁻ z in B, f (e.val.symm z) * ENNReal.ofReal (ρ z) := by
        rw [hmapB, lintegral_withDensity_eq_lintegral_mul₀ hρ hf]
        refine lintegral_congr fun z => ?_
        simp only [Pi.mul_apply]
        ring

/-- **Local-to-global comparison of measures** on a second-countable space: if `ν₁ ≤ ν₂` on
subsets of a neighbourhood of every point of an open `U`, then `ν₁ ≤ ν₂` on measurable subsets
of `U`. -/
theorem measure_le_of_local {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν₁ ν₂ : Measure Y} {U : Set Y}
    (h : ∀ y ∈ U, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      ∀ S, MeasurableSet S → S ⊆ V → S ⊆ U → ν₁ S ≤ ν₂ S)
    {S : Set Y} (hS : MeasurableSet S) (hSU : S ⊆ U) : ν₁ S ≤ ν₂ S := by
  classical
  choose! V hVo hyV hV using h
  obtain ⟨C, hCU, hCc, hCeq⟩ := TopologicalSpace.isOpen_biUnion_countable U V
    fun y hy => hVo y hy
  have hSC : S ⊆ ⋃ i ∈ C, V i := by
    intro y hy
    rw [hCeq]
    exact mem_biUnion (hSU hy) (hyV y (hSU hy))
  rcases C.eq_empty_or_nonempty with hC | hC
  · have : S = ∅ := by
      apply eq_empty_of_subset_empty
      simpa [hC] using hSC
    simp [this]
  obtain ⟨g, hg⟩ := hCc.exists_eq_range hC
  have hgC : ∀ j, g j ∈ C := fun j => by rw [hg]; exact mem_range_self j
  set W : ℕ → Set Y := fun j => V (g j) with hW
  have hWm : ∀ j, MeasurableSet (W j) := fun j => (hVo _ (hCU (hgC j))).measurableSet
  have hcov : S ⊆ ⋃ j, W j := by
    intro y hy
    obtain ⟨i, hiC, hyi⟩ := mem_iUnion₂.mp (hSC hy)
    rw [hg] at hiC
    obtain ⟨j, rfl⟩ := hiC
    exact mem_iUnion.mpr ⟨j, hyi⟩
  set D : ℕ → Set Y := fun j => S ∩ disjointed W j with hD
  have hDm : ∀ j, MeasurableSet (D j) := fun j => hS.inter (MeasurableSet.disjointed hWm j)
  have hDd : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
    ((disjoint_disjointed W) hij).mono inter_subset_right inter_subset_right
  have hDU : ⋃ j, D j = S := by
    simp only [hD, ← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.mpr hcov
  rw [← hDU, measure_iUnion hDd hDm, measure_iUnion hDd hDm]
  refine ENNReal.tsum_le_tsum fun j => hV (g j) (hCU (hgC j)) (D j) (hDm j) ?_ ?_
  · exact inter_subset_right.trans ((disjointed_subset W j))
  · exact inter_subset_left.trans hSU

end SGPT.IGood.DXLow

namespace SGPT.PSH.GlobalL2.CoverData

open SGPT.IGood.DXLow SGPT.Okounkov.TranscendentalWN

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- **The local bound** `θ_φⁿ ≤ (ddᶜΦ)ⁿ` on small balls of chart `a` where `φ` is smooth. -/
theorem diagonal_le_lintegral_local [CompactSpace X] (hn : 0 < n)
    (hL : IsSourceSmoothHermitianMetric L) (hθ : IsOwnFirstChernForm L θ)
    {φ : X → EReal} (hφθ : IsThetaPshPotential θ.val φ) (a : Fin D.m)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ ball (ctr (n := n) (D.pt a)) (D.R a))
    {g : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U) (hz₀U : z₀ ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (hgφ : ∀ z ∈ U, φ ((D.chartA a).val.symm z) = (g z : EReal)) :
    ∃ r : ℝ, 0 < r ∧ ∀ S : Set (ComplexModel n), MeasurableSet S → S ⊆ ball z₀ r →
      diagonalPotentialMeasure θ φ hφθ ((D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' S) ≤
        ∫⁻ z in S, ENNReal.ofReal (smoothDensity (D.canonicalWeight a φ) z) := by
  classical
  set c := D.chartA a with hc
  set fw := frameWeight (prefFrame L (D.pt a)) c with hfw
  set U' := U ∩ ball (ctr (n := n) (D.pt a)) (D.R a) with hU'
  have hU'o : IsOpen U' := hU.inter isOpen_ball
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU'o z₀ ⟨hz₀U, hz₀⟩
  set r : ℝ := ε / 8 with hr
  have hr0 : 0 < r := by positivity
  have hcl : closedBall z₀ (4 * r) ⊆ U' :=
    (closedBall_subset_ball (by rw [hr]; linarith)).trans hεU
  set A : Opens (ComplexModel n) := ⟨ball z₀ (4 * r), isOpen_ball⟩ with hA
  have hAU : (A : Set (ComplexModel n)) ⊆ U' := ball_subset_closedBall.trans hcl
  have hAR : (A : Set (ComplexModel n)) ⊆ ball (ctr (n := n) (D.pt a)) (2 * D.R a) :=
    fun z hz => D.ball_subset_two a (hAU hz).2
  have hAt : (A : Set (ComplexModel n)) ⊆ c.val.target := fun z hz =>
    D.ball_subset_target a (hAU hz).2
  have hfws : ContDiffOn ℝ ∞ fw A := (D.contDiffOn_frameWeight_L hL a).mono hAR
  have hρ : IsSmoothLocalPotential θ.val c A fw := by
    refine ⟨isOpen_ball, hAt, hfws, fun z hz => ?_⟩
    have hb := (D.symm_mem_baseSets a (hAR hz)).1
    exact (hθ c (prefFrame L (D.pt a)) z (hAt hz) hb).symm
  set f := D.peakWeight a g with hfdef
  have hfs : ContDiffOn ℝ ∞ f A := (hg.mono fun z hz => (hAU hz).1).add hfws
  have hpsh : PlurisubharmonicOn (fun z => (f z : EReal)) A := by
    intro z hz
    refine (plurisubharmonicOn_add_localPotential hφθ c hρ z hz).congr
      (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun w hw => ?_)
    show (fw w : EReal) + φ (c.val.symm w) = ((g w + fw w : ℝ) : EReal)
    rw [hgφ w (hAU hw).1, EReal.coe_add, add_comm]
  have hlevi : ∀ z ∈ (A : Set (ComplexModel n)), ∀ v, 0 ≤ leviForm f z v := fun z hz v =>
    leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := A) hfs hpsh hz v
  have hfcont : ContinuousOn f (closedBall z₀ (4 * r)) := by
    have hfV : ContDiffOn ℝ ∞ f U' :=
      (hg.mono fun z hz => hz.1).add ((D.contDiffOn_frameWeight_L hL a).mono
        fun z hz => D.ball_subset_two a hz.2)
    exact hfV.continuousOn.mono hcl
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ (4 * r)).exists_bound_of_continuousOn hfcont
  have hfb : IsLocallyBoundedPshOn A f := ⟨hpsh, fun z hz => ⟨A, hz, le_rfl, C,
    fun w hw => by simpa [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)⟩⟩
  have hq : IsSmoothPshOn A f := ⟨hfs, hpsh, fun z hz =>
    SmoothDDCHessianPositivity.complexHessian_posSemidef_of_leviForm_nonneg
      ((hfs z hz).contDiffAt (isOpen_ball.mem_nhds hz) |>.of_le (by norm_cast)) (hlevi z hz)⟩
  have hfeq : ∀ y ∈ (A : Set (ComplexModel n)), chartFunction φ c y + (fw y : EReal) =
      (f y : EReal) := by
    intro y hy
    show φ (c.val.symm y) + (fw y : EReal) = ((g y + fw y : ℝ) : EReal)
    rw [hgφ y (hAU hy).1, EReal.coe_add]
  refine ⟨r, hr0, fun S hSm hSr => ?_⟩
  have hSA : S ⊆ (A : Set (ComplexModel n)) :=
    hSr.trans (ball_subset_ball (by linarith))
  set G : X → ℝ≥0∞ := (c.val.source ∩ c.val ⁻¹' S).indicator 1 with hG
  have hGm : MeasurableSet (c.val.source ∩ c.val ⁻¹' S) := measurableSet_chart_preimage c hSm
  have hGsupp : ∀ x, G x ≠ 0 → x ∈ c.val.source ∧ c.val x ∈ A := by
    intro x hx
    by_cases hxS : x ∈ c.val.source ∩ c.val ⁻¹' S
    · exact ⟨hxS.1, hSA hxS.2⟩
    · exact absurd (indicator_of_notMem hxS _) hx
  have h1 := lintegral_diagonalPotentialMeasure_eq_canonical θ hφθ c A hρ hfb hfeq G hGsupp
  rw [lintegral_indicator_one hGm] at h1
  rw [h1]
  have hcompl := MongeAmpere.canonicalBedfordTaylorMeasure_compl A f hfb
  calc ∫⁻ y, G (c.val.symm y) ∂(MongeAmpere.canonicalBedfordTaylorMeasure A f hfb)
      ≤ ∫⁻ y, S.indicator 1 y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A f hfb) := by
        refine lintegral_mono_ae ?_
        have : ∀ᵐ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A f hfb),
            y ∈ (A : Set (ComplexModel n)) := by
          rw [ae_iff]
          exact hcompl
        filter_upwards [this] with y hy
        by_cases hGy : c.val.symm y ∈ c.val.source ∩ c.val ⁻¹' S
        · have hyS : y ∈ S := by
            have := hGy.2
            rwa [mem_preimage, c.val.right_inv (hAt hy)] at this
          simp [hG, indicator_of_mem hGy, indicator_of_mem hyS]
        · simp [hG, indicator_of_notMem hGy]
    _ = MongeAmpere.canonicalBedfordTaylorMeasure A f hfb S := lintegral_indicator_one hSm
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (smoothDensity f z) :=
        EnvelopeLocal.canonicalBedfordTaylorMeasure_contact_le hn hfb hq (fun z _ => le_rfl) hr0
          ((closedBall_subset_ball (by linarith)).trans le_rfl)
          (fun z hz => ⟨⟨hSA hz, rfl⟩, hSr hz⟩)
    _ = ∫⁻ z in S, ENNReal.ofReal (smoothDensity (D.canonicalWeight a φ) z) := by
        refine setLIntegral_congr_fun hSm fun z hz => ?_
        congr 1
        refine smoothDensity_congr ?_
        filter_upwards [isOpen_ball.mem_nhds (hSA hz)] with w hw
        simp only [hfdef, CoverData.peakWeight, CoverData.canonicalWeight]
        rw [hgφ w (hAU hw).1, EReal.toReal_coe]

/-- Off its pole set, a potential smooth off its poles is finite on an open set. -/
theorem isOpen_compl_poleSet {φ : X → EReal} (hsm : SmoothOffPoleSet (n := n) φ) :
    IsOpen (poleSet φ)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hzt : e.val x ∈ e.val.target := e.val.map_source hxs
  have hnp : e.val.symm (e.val x) ∉ poleSet φ := by rw [e.val.left_inv hxs]; exact hx
  obtain ⟨g, -, hgφ⟩ := hsm e (e.val x) hzt hnp
  have h1 : ∀ᶠ y in 𝓝 x, chartFunction φ e (e.val y) = (g (e.val y) : EReal) :=
    (e.val.continuousAt hxs).eventually hgφ
  filter_upwards [h1, e.val.open_source.mem_nhds hxs] with y hy hys
  simp only [chartFunction, e.val.left_inv hys] at hy
  show φ y ≠ ⊥
  rw [hy]
  exact EReal.coe_ne_bot _

/-- **The non-pluripolar mass is at most `∑_a ∫_{E_a} G_a dμ`** (blueprint `claude-dx-low:mass`). -/
theorem diagonalPotentialMass_le_sum_lintegral [CompactSpace X] (hn : 0 < n)
    (hL : IsSourceSmoothHermitianMetric L) (hθ : IsOwnFirstChernForm L θ)
    {φ : X → EReal} (hφθ : IsThetaPshPotential θ.val φ) (hsm : SmoothOffPoleSet (n := n) φ) :
    diagonalPotentialMass θ φ hφθ ≤ ∑ a, ∫⁻ x in D.piece φ a, D.limitDensity a φ x ∂μ := by
  classical
  have hφm : Measurable φ := hφθ.quasiPshPotential.1.upperSemicontinuous.measurable
  set ν := diagonalPotentialMeasure θ φ hφθ with hν
  have hP : ν (poleSet φ) = 0 := by
    change globalMixedMeasure (fun _ : Fin n => θ) (fun _ => φ) (fun _ => hφθ.1) {x | φ x = ⊥} = 0
    exact globalMixedMeasure_pole_null_of_nondegenerate (fun _ => hφθ.1) hφθ
  have hcover : (univ : Set X) ⊆ poleSet φ ∪ ⋃ a, D.piece φ a := by
    intro x _
    by_cases hx : x ∈ poleSet φ
    · exact Or.inl hx
    · obtain ⟨a, ha⟩ := D.exists_mem_piece φ hx
      exact Or.inr (mem_iUnion.mpr ⟨a, ha⟩)
  have hPo := isOpen_compl_poleSet hsm
  -- the bound on each piece
  have hpiece : ∀ a, ν (D.piece φ a) ≤ ∫⁻ x in D.piece φ a, D.limitDensity a φ x ∂μ := by
    intro a
    set c := D.chartA a with hc
    set E := D.piece φ a with hE
    have hEm : MeasurableSet E := D.measurableSet_piece hφm a
    have hEs : E ⊆ c.val.source := fun x hx => hx.1.1.1
    set Tset := c.val '' E with hTset
    have hTm : MeasurableSet Tset := measurableSet_chart_image c hEm hEs
    have hTt : Tset ⊆ c.val.target := by
      rintro _ ⟨x, hx, rfl⟩; exact c.val.map_source (hEs hx)
    have hpre : c.val.source ∩ c.val ⁻¹' Tset = E := by
      ext x
      constructor
      · rintro ⟨hxs, y, hy, hyx⟩
        rwa [← c.val.injOn (hEs hy) hxs hyx]
      · intro hx; exact ⟨hEs hx, x, hx, rfl⟩
    -- comparison in the chart
    set Uc := c.val.target ∩ c.val.symm ⁻¹' (D.smallRegion a ∩ (poleSet φ)ᶜ) with hUc
    have hTU : Tset ⊆ Uc := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨c.val.map_source (hEs hx), ?_⟩
      rw [mem_preimage, c.val.left_inv (hEs hx)]
      exact ⟨hx.1.1, hx.2⟩
    have he : AEMeasurable c.val (ν.restrict c.val.source) :=
      c.val.continuousOn.aemeasurable c.val.open_source.measurableSet
    set ν₁ := Measure.map c.val (ν.restrict c.val.source) with hν₁
    set ν₂ := volume.withDensity
      (fun z => ENNReal.ofReal (smoothDensity (D.canonicalWeight a φ) z)) with hν₂
    have hν₁S : ∀ S, MeasurableSet S → ν₁ S = ν (c.val.source ∩ c.val ⁻¹' S) := by
      intro S hS
      rw [hν₁, Measure.map_apply_of_aemeasurable he hS,
        Measure.restrict_apply' c.val.open_source.measurableSet, inter_comm]
    have hloc : ∀ z ∈ Uc, ∃ V : Set (ComplexModel n), IsOpen V ∧ z ∈ V ∧
        ∀ S, MeasurableSet S → S ⊆ V → S ⊆ Uc → ν₁ S ≤ ν₂ S := by
      intro z hz
      have hzS : c.val.symm z ∈ D.smallRegion a := hz.2.1
      have hzr : c.val (c.val.symm z) ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hzS.2
      rw [c.val.right_inv hz.1] at hzr
      have hzR : z ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
        ball_subset_ball (by linarith [D.R_pos a]) hzr
      obtain ⟨g, hgs, hgφ⟩ := hsm c z hz.1 hz.2.2
      obtain ⟨U, hUo, hzU, hU⟩ : ∃ U : Set (ComplexModel n), IsOpen U ∧ z ∈ U ∧
          ∀ w ∈ U, ContDiffAt ℝ ∞ g w ∧ chartFunction φ c w = (g w : EReal) := by
        obtain ⟨U, hU, hUo, hzU⟩ := _root_.mem_nhds_iff.mp (hgs.and hgφ)
        exact ⟨U, hUo, hzU, fun w hw => hU hw⟩
      obtain ⟨r, hr, hrb⟩ := D.diagonal_le_lintegral_local hn hL hθ hφθ a hzR hUo hzU
        (fun w hw => (hU w hw).1.contDiffWithinAt) (fun w hw => (hU w hw).2)
      refine ⟨ball z r, isOpen_ball, mem_ball_self hr, fun S hS hSV _ => ?_⟩
      rw [hν₁S S hS, hν₂, withDensity_apply _ hS]
      exact hrb S hS hSV
    have hcmp := measure_le_of_local hloc hTm hTU
    rw [hν₁S Tset hTm, hpre, hν₂, withDensity_apply _ hTm] at hcmp
    refine hcmp.trans (le_of_eq ?_)
    -- reading `∫_{E} G_a dμ` in the chart
    have hρc := D.dens_cont a
    have hmeas : AEMeasurable (fun z => D.limitDensity a φ (c.val.symm z))
        (volume.restrict Tset) := by
      have hdm : AEMeasurable (D.dens a) (volume.restrict Tset) :=
        (hρc.mono hTt).aemeasurable hTm
      have hm : AEMeasurable (fun z => ENNReal.ofReal
          (smoothDensity (D.canonicalWeight a φ) z / D.dens a z)) (volume.restrict Tset) :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((measurable_smoothDensity _).aemeasurable.div hdm)
      refine hm.congr ?_
      refine (ae_restrict_iff' hTm).mpr (Eventually.of_forall fun z hz => ?_)
      have hz' : (D.chartA a).val (c.val.symm z) = z := c.val.right_inv (hTt hz)
      simp only [CoverData.limitDensity]
      rw [hz']
    have h2 := setLIntegral_chart_measurable c hρc (D.dens_map a) hTm hTt hmeas
    rw [hpre] at h2
    rw [h2]
    refine setLIntegral_congr_fun hTm fun z hz => ?_
    have hz' : (D.chartA a).val (c.val.symm z) = z := c.val.right_inv (hTt hz)
    simp only [CoverData.limitDensity]
    rw [hz']
    have hzR : z ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := by
      obtain ⟨x, hx, rfl⟩ := hz
      exact ball_subset_ball (by linarith [D.R_pos a]) hx.1.1.2
    have hρz : 0 < D.dens a z := by
      have h1 := D.one_le a z hzR
      by_contra hneg
      have hneg' : D.dens a z ≤ 0 := not_lt.mp hneg
      have := mul_nonpos_of_nonneg_of_nonpos D.Aμ_pos.le hneg'
      linarith
    rw [← ENNReal.ofReal_mul' hρz.le, div_mul_cancel₀ _ hρz.ne']
  calc diagonalPotentialMass θ φ hφθ = ν univ := rfl
    _ ≤ ν (poleSet φ ∪ ⋃ a, D.piece φ a) := measure_mono hcover
    _ ≤ ν (poleSet φ) + ν (⋃ a, D.piece φ a) := measure_union_le _ _
    _ ≤ 0 + ∑ a, ν (D.piece φ a) := by rw [hP]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ a, ∫⁻ x in D.piece φ a, D.limitDensity a φ x ∂μ := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hpiece a

end SGPT.PSH.GlobalL2.CoverData
