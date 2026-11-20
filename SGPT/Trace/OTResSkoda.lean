import SGPT.Trace.OTResShell
import SGPT.Trace.OTExt2Statement
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.LelongNumberFiniteness
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

/-!
# Gentle weights: the exponential `ψ = e^{Φ/c}`, chart comparisons and Skoda on the submanifold

Blueprint `claude-ot-residue.tex`, nodes `claude-ot-residue:weight`, `claude-ot-residue:skoda`.

* `gentlePsi c Φ = (e^{Φ/c})` as a real function; for `Φ` with gentle analytic singularities of
  type `(c, 𝔞)` (TN's `HasGentleAnalyticSingularitiesOfType`) it is smooth in every chart, and
  `e^{-αΦ} = ψ^{-αc}` (`multiplierWeight_eq_gentlePsi_rpow`).
* `exists_lintegral_chart_le`, `exists_setLIntegral_le_chart`: on a manifold with a smooth positive
  volume, integrals over a compact subset of a chart target and integrals against the volume are
  comparable.
* `exists_lintegral_gentlePsi_rpow_neg_ne_top` (**Skoda on `W`**): if `Φ` is `θ`-psh on `X`,
  gentle, and `Φ|_W ≢ -∞` on the closed connected submanifold `W` (`dim W > 0`), then
  `∫_W ψ^{-β} dV_W < ∞` for some `β > 0`.  Proof: `Φ|_W` is `θ|_W`-psh
  (`thetaPlurisubharmonic_comp`), nondegenerate (identity principle), with finite Lelong numbers;
  Skoda's theorem (TN `one_mem_multiplierIdeal_of_lelongNumber_lt`) gives local integrability of
  `e^{-c_y Φ|_W}` near every point, and compactness of `W` gives one exponent.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTRes

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences

/-! ### The exponential of a gentle weight -/

/-- `ψ = e^{Φ/c}` as a real function (`0` where `Φ = -∞`). -/
def gentlePsi {X : Type*} (c : ℚ) (Φ : X → EReal) (x : X) : ℝ :=
  (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * Φ x)).toReal

theorem gentlePsi_nonneg {X : Type*} (c : ℚ) (Φ : X → EReal) (x : X) : 0 ≤ gentlePsi c Φ x :=
  ENNReal.toReal_nonneg

/-- `e^{-α a} = (e^{a/c})^{-αc}` in `[0, ∞]`, when `e^{a/c} < ∞`. -/
theorem multiplierWeight_eq_rpow {c : ℝ} (hc : 0 < c) {a : EReal}
    (htop : EReal.exp (((c⁻¹ : ℝ) : EReal) * a) ≠ ⊤) (α : ℝ) :
    multiplierWeight α a =
      ENNReal.ofReal ((EReal.exp (((c⁻¹ : ℝ) : EReal) * a)).toReal) ^ (-(α * c)) := by
  rw [ENNReal.ofReal_toReal htop, ← EReal.exp_mul, multiplierWeight]
  congr 1
  have h1 : ((c⁻¹ : ℝ) : EReal) * a * ((-(α * c) : ℝ) : EReal) =
      ((c⁻¹ * -(α * c) : ℝ) : EReal) * a := by
    rw [EReal.coe_mul, mul_comm (((c⁻¹ : ℝ) : EReal)) a, mul_assoc, mul_comm a]
  have h2 : c⁻¹ * -(α * c) = -α := by field_simp
  rw [h1, h2, EReal.coe_neg, EReal.neg_mul]

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem multiplierWeight_eq_gentlePsi_rpow {Φ : X → EReal} {c : ℚ} {𝔞 : GermIdeal n X}
    (hΦ : HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) (α : ℝ) (x : X) :
    multiplierWeight α (Φ x) = ENNReal.ofReal (gentlePsi c Φ x) ^ (-(α * c)) :=
  multiplierWeight_eq_rpow (by exact_mod_cast hΦ.2.1.1) (hΦ.2.2.1 x) α

theorem chartSmooth_gentlePsi {Φ : X → EReal} {c : ℚ} {𝔞 : GermIdeal n X}
    (hΦ : HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) :
    ChartSmooth (n := n) (gentlePsi c Φ) :=
  hΦ.2.2.2.1

theorem continuous_gentlePsi {Φ : X → EReal} {c : ℚ} {𝔞 : GermIdeal n X}
    (hΦ : HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) :
    Continuous (gentlePsi c Φ) :=
  continuous_iff_continuousAt.mpr fun _ =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (n := n) (h := gentlePsi c Φ)
      isOpen_univ (fun e => by simpa using chartSmooth_gentlePsi hΦ e) (mem_univ _)

/-! ### Chart comparisons for a smooth positive volume -/

section Chart

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Lower comparison**: `∫_K f ∘ e⁻¹ dz ≤ C ∫_M f dμ` for a compact `K` in a chart target. -/
theorem exists_lintegral_chart_le {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := k) μ)
    (e : ComplexChart k M) {K : Set (ComplexModel k)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : M → ℝ≥0∞, Measurable f →
      ∫⁻ z in K, f (e.val.symm z) ≤ ENNReal.ofReal C * ∫⁻ y, f y ∂μ := by
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, le_rfl, fun f _ => by simp [hKe]⟩
  obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hKne (hρs.continuousOn.mono hKt)
  have hc : 0 < ρ z₀ := hρpos z₀ (hKt hz₀K)
  refine ⟨(ρ z₀)⁻¹, by positivity, fun f hf => ?_⟩
  have heq := setLIntegral_source_inter_preimage e hρs.continuousOn hmap hK hKt hf
  calc ∫⁻ z in K, f (e.val.symm z)
      = ∫⁻ z in K, ENNReal.ofReal (ρ z₀)⁻¹ * (ENNReal.ofReal (ρ z₀) * f (e.val.symm z)) := by
        refine lintegral_congr fun z => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ∫⁻ z in K, ENNReal.ofReal (ρ z₀)⁻¹ * (ENNReal.ofReal (ρ z) * f (e.val.symm z)) := by
        refine setLIntegral_mono' hK.isClosed.measurableSet fun z hz => ?_
        gcongr
        exact hmin hz
    _ = ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ y in e.val.source ∩ e.val ⁻¹' K, f y ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, heq]
    _ ≤ ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ y, f y ∂μ :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- **Upper comparison**: `∫_{e⁻¹ K} f dμ ≤ C ∫_K f ∘ e⁻¹ dz` for a compact `K` in a chart target. -/
theorem exists_setLIntegral_le_chart {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := k) μ)
    (e : ComplexChart k M) {K : Set (ComplexModel k)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : M → ℝ≥0∞, Measurable f →
      ∫⁻ y in e.val.source ∩ e.val ⁻¹' K, f y ∂μ ≤ ENNReal.ofReal C * ∫⁻ z in K, f (e.val.symm z) := by
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hρs.continuousOn.mono hKt)
  refine ⟨max C 0, le_max_right _ _, fun f hf => ?_⟩
  rw [setLIntegral_source_inter_preimage e hρs.continuousOn hmap hK hKt hf,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hK.isClosed.measurableSet fun z hz => ?_
  gcongr
  have := hC z hz
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

end Chart

/-- `∫_{⋃_{y ∈ t} O_y} f ≤ ∑_{y ∈ t} ∫_{O_y} f`. -/
theorem setLIntegral_biUnion_finset_le {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    (t : Finset β) (O : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in ⋃ y ∈ t, O y, f x ∂μ ≤ ∑ y ∈ t, ∫⁻ x in O y, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

/-- `x^{-β} ≤ M^{β' - β} x^{-β'}` for `0 ≤ x ≤ M`, `M ≥ 1`... in `[0, ∞]`, `0 < β ≤ β'`. -/
theorem ofReal_rpow_neg_le {x M β β' : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) (hM : 0 < M) (hβ : 0 < β)
    (hββ' : β ≤ β') :
    ENNReal.ofReal x ^ (-β) ≤ ENNReal.ofReal (M ^ (β' - β)) * ENNReal.ofReal x ^ (-β') := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hM _)).ne']
  · rw [ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_rpow_of_pos hpos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hM.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h : x ^ (-β) = x ^ (β' - β) * x ^ (-β') := by
      rw [← Real.rpow_add hpos]; ring_nf
    rw [h]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le hxM (by linarith))
      (Real.rpow_nonneg hpos.le _)

/-! ### Skoda on the submanifold -/

section Skoda

variable [CompactSpace X]

/-- **Skoda on `W`**: for `Φ` `θ`-psh on `X` with gentle analytic singularities of type `(c, 𝔞)`
and `Φ|_W ≢ -∞` on the closed connected submanifold `W` of positive dimension, there is `β > 0`
with `∫_W ψ^{-β} dV_W < ∞`, `ψ = e^{Φ/c}`. -/
theorem exists_lintegral_gentlePsi_rpow_neg_ne_top (ωb : KahlerBackground n X) {W : Set X}
    {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) (hm : 0 < m) {θ : SmoothRealForm n X 2}
    {Φ : X → EReal} (hΦθ : ThetaPlurisubharmonic θ Φ) (hne : ∃ y ∈ W, Φ y ≠ ⊥) {c : ℚ}
    {𝔞 : GermIdeal n X} (hΦ : HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) :
    let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    ∃ β : ℝ, 0 < β ∧ ∫⁻ y : W, ENNReal.ofReal (gentlePsi c Φ y) ^ (-β)
      ∂(IntegrationCurrent.kahlerVolume
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)) ≠ ⊤ := by
  intro hk
  let _ : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have _ : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have _ : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let _ : MeasurableSpace W := borel W
  have _ : BorelSpace W := ⟨rfl⟩
  have _ : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) with hμW
  have hμ : IsSmoothPositiveVolume (n := m) μW :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume _
  set φ : W → EReal := fun y => Φ y with hφdef
  have hφ : ThetaPlurisubharmonic (SmoothRealForm.pullback (contMDiff_val hk hW.2.2) θ) φ :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp (contMDiff_val hk hW.2.2) hΦθ
  obtain ⟨y₀, hy₀, hy₀ne⟩ := hne
  have hnd : LocallyNondegenerate φ :=
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hφ ⟨⟨y₀, hy₀⟩, hy₀ne⟩
  have hq : ManifoldQuasiPlurisubharmonic (n := m) φ := hφ.quasiPlurisubharmonic
  have hν : ∀ y : W, NonKahlerLocus.lelongNumber (n := m) φ y ≠ ⊤ :=
    LelongNumberFiniteness.lelongNumber_ne_top_of_quasiPsh hm hq hnd
  have hcg : (0 : ℝ) < c := by exact_mod_cast hΦ.2.1.1
  -- the exponents of Skoda's theorem
  set cy : W → ℝ := fun y => 1 / ((NonKahlerLocus.lelongNumber (n := m) φ y).toReal + 1)
    with hcydef
  have hcy0 : ∀ y, 0 < cy y := fun y => by positivity
  have hsk : ∀ y : W, (multiplierIdeal (n := m) (cy y) φ).mem y (fun _ => 1) := by
    intro y
    refine SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hφ (hcy0 y) ?_
    rw [← ENNReal.ofReal_toReal (hν y)]
    refine ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨?_, by positivity⟩
    have h0 := ENNReal.toReal_nonneg (a := NonKahlerLocus.lelongNumber (n := m) φ y)
    simp only [hcydef]
    rw [div_div_eq_mul_div, div_one]
    nlinarith
  -- local integrability on a closed ball in the preferred chart
  have hloc : ∀ y : W, ∃ r : ℝ, 0 < r ∧
      closedBall ((complexChartAt (n := m) y).val y) r ⊆ (complexChartAt (n := m) y).val.target ∧
      ∫⁻ z in closedBall ((complexChartAt (n := m) y).val y) r,
        ENNReal.ofReal (gentlePsi c Φ ((complexChartAt (n := m) y).val.symm z)) ^ (-(cy y * c))
          ≠ ⊤ := by
    intro y
    obtain ⟨-, -, U, hU, hyU, -, -, hint⟩ := hsk y
    set e := complexChartAt (n := m) y with he
    have hyt : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp (hU.inter e.val.open_target) _ ⟨hyU, hyt⟩
    refine ⟨r / 2, by positivity, fun z hz => (hrU (closedBall_subset_ball (by linarith) hz)).2,
      ne_top_of_le_ne_top hint.ne ?_⟩
    refine (lintegral_mono_set fun z hz => (hrU (closedBall_subset_ball (by linarith) hz)).1).trans
      (le_of_eq (lintegral_congr fun z => ?_))
    simp only [multiplierDensity, chartFunction, norm_one, one_pow, ENNReal.ofReal_one, one_mul,
      hφdef]
    rw [multiplierWeight_eq_gentlePsi_rpow hΦ]
  choose r hr0 hrt hrint using hloc
  -- a finite cover
  set e : W → ComplexChart m W := fun y => complexChartAt (n := m) y with hedef
  set O : W → Set W := fun y => (e y).val.source ∩ (e y).val ⁻¹' ball ((e y).val y) (r y)
    with hOdef
  have hOo : ∀ y, IsOpen (O y) := fun y => (e y).val.isOpen_inter_preimage isOpen_ball
  have hOy : ∀ y, y ∈ O y := fun y => ⟨mem_complexChartAt_source y, mem_ball_self (hr0 y)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOo
    (fun y _ => mem_iUnion.mpr ⟨y, hOy y⟩)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨y₀, hy₀⟩ : W)))
    exact ⟨i, hi⟩
  set β : ℝ := t.inf' htne (fun y => cy y * c) with hβdef
  have hβ0 : 0 < β := (Finset.lt_inf'_iff htne).mpr fun y _ => mul_pos (hcy0 y) hcg
  have hβle : ∀ y ∈ t, β ≤ cy y * c := fun y hy => Finset.inf'_le _ hy
  -- a bound for `ψ`
  obtain ⟨Mψ, hMψ⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_gentlePsi hΦ).continuousOn
  set M1 : ℝ := max Mψ 1 with hM1
  have hψM : ∀ x, gentlePsi c Φ x ≤ M1 := fun x => by
    have := hMψ x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hM10 : 0 < M1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfm : Measurable (fun y : W => ENNReal.ofReal (gentlePsi c Φ y) ^ (-β)) :=
    (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp
      ((continuous_gentlePsi hΦ).comp continuous_subtype_val))).measurable
  have hpiece : ∀ y ∈ t, ∫⁻ x in O y, ENNReal.ofReal (gentlePsi c Φ x) ^ (-β) ∂μW ≠ ⊤ := by
    intro y hy
    obtain ⟨C, -, hC⟩ := exists_setLIntegral_le_chart hμ (e y) (isCompact_closedBall _ _) (hrt y)
    have hsub : O y ⊆ (e y).val.source ∩ (e y).val ⁻¹' closedBall ((e y).val y) (r y) :=
      fun x hx => ⟨hx.1, ball_subset_closedBall hx.2⟩
    have hle := (lintegral_mono_set (μ := μW) hsub).trans (hC _ hfm)
    refine ne_top_of_le_ne_top ?_ hle
    have hb : ∫⁻ z in closedBall ((e y).val y) (r y),
        ENNReal.ofReal (gentlePsi c Φ ((e y).val.symm z)) ^ (-β) ≤
        ENNReal.ofReal (M1 ^ (cy y * c - β)) * ∫⁻ z in closedBall ((e y).val y) (r y),
          ENNReal.ofReal (gentlePsi c Φ ((e y).val.symm z)) ^ (-(cy y * c)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_closedBall fun z _ =>
        ofReal_rpow_neg_le (gentlePsi_nonneg _ _ _) (hψM _) hM10 hβ0 (hβle y hy)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hrint y)) hb)
  refine ⟨β, hβ0, ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hpiece) ?_⟩
  calc ∫⁻ x, ENNReal.ofReal (gentlePsi c Φ x) ^ (-β) ∂μW
      = ∫⁻ x in univ, ENNReal.ofReal (gentlePsi c Φ x) ^ (-β) ∂μW := setLIntegral_univ _ |>.symm
    _ ≤ ∫⁻ x in ⋃ y ∈ t, O y, ENNReal.ofReal (gentlePsi c Φ x) ^ (-β) ∂μW := lintegral_mono_set ht
    _ ≤ _ := setLIntegral_biUnion_finset_le t O _

end Skoda

end SGPT.Trace.OTRes
