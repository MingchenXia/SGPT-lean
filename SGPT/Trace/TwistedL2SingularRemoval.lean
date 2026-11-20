import SGPT.Trace.TwistedL2Statement
import SGPT.Okounkov.TranscendentalL2Extension
import SGPT.PSH.GlobalL2Correction

/-!
# `L²` removable singularities across locally analytic null sets

Blueprint node `claude-twisted-l2:l2-removable` in `claude-twisted-l2.tex`;
Xia, *Foundations of pluripotential
theory* (FPT), q07, `lem:l2-holomorphic-analytic-removal`.

## Main results

* `interior_eq_empty_of_isLocallyAnalyticNull`, `measure_eq_zero_of_isLocallyAnalyticNull`: a set
  locally contained in the zero set of a holomorphic function vanishing identically on no open
  set has empty interior and is null for every smooth positive volume.
* `isLocallyFiniteMeasure_of_isSmoothPositiveVolume`: smooth positive volumes are locally finite.
* `norm_eq_coord_mul`: `‖v‖ = |e(v)| ‖e⁻¹(1)‖` in an atlas frame.
* `exists_local_extension` (`claude-twisted-l2-c:local-removal`): near a point of `A`, the frame
  coefficient of an `L²` section holomorphic off `A` agrees off `A` with a holomorphic function
  (the Euclidean `L²` Riemann extension theorem
  `SGPT.Okounkov.TranscendentalL2.exists_extension_of_locally_sq_integrable`).
* `l2RemovableSingularityStatement` (`claude-twisted-l2:l2-removable`): **the proof of
  `L2RemovableSingularityStatement`**; the local extensions glue because two continuous
  functions which agree off the nowhere dense closed set `A` agree everywhere.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Locally analytic null sets -/

omit [IsComplexManifold n X] in
/-- A locally analytic null set has empty interior. -/
theorem interior_eq_empty_of_isLocallyAnalyticNull {A : Set X}
    (hA : IsLocallyAnalyticNull (n := n) A) : interior A = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨c, W, g, hxc, hWo, hxW, hWt, -, hgne, hgA⟩ := hA x
  set W' : Set (ComplexModel n) := W ∩ (c.val.target ∩ c.val.symm ⁻¹' interior A) with hW'
  have hW'o : IsOpen W' := hWo.inter (c.val.isOpen_inter_preimage_symm isOpen_interior)
  have hxW' : c.val x ∈ W' := ⟨hxW, c.val.map_source hxc, by rwa [mem_preimage,
    c.val.left_inv hxc]⟩
  obtain ⟨z, hz, hgz⟩ := hgne W' inter_subset_left hW'o ⟨_, hxW'⟩
  exact hgz (hgA z hz.1 (interior_subset hz.2.2))

omit [IsComplexManifold n X] in
/-- The complement of a locally analytic null set is dense. -/
theorem dense_compl_of_isLocallyAnalyticNull {A : Set X}
    (hA : IsLocallyAnalyticNull (n := n) A) : Dense Aᶜ :=
  interior_eq_empty_iff_dense_compl.mp (interior_eq_empty_of_isLocallyAnalyticNull hA)

variable [MeasurableSpace X] [BorelSpace X]

/-- **Locally analytic null sets are null** for a smooth positive volume. -/
theorem measure_eq_zero_of_isLocallyAnalyticNull {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {A : Set X}
    (hA : IsLocallyAnalyticNull (n := n) A) : μ A = 0 := by
  refine measure_null_of_locally_null A fun x _ => ?_
  obtain ⟨c, W, g, hxc, hWo, hxW, hWt, hg, hgne, hgA⟩ := hA x
  obtain ⟨ρ, -, -, hmap⟩ := hμ c
  set N : Set X := c.val.source ∩ c.val ⁻¹' W with hN
  have hNo : IsOpen N := c.val.isOpen_inter_preimage hWo
  refine ⟨A ∩ N, inter_mem_nhdsWithin _ (hNo.mem_nhds ⟨hxc, hxW⟩), ?_⟩
  set Z : Set (ComplexModel n) := W ∩ g ⁻¹' {0} with hZ
  have hZm : MeasurableSet Z := by
    have ho : IsOpen (W ∩ g ⁻¹' {0}ᶜ) :=
      hg.continuousOn.isOpen_inter_preimage hWo isOpen_compl_singleton
    have : Z = W \ (W ∩ g ⁻¹' {0}ᶜ) := by ext y; simp [hZ]
    rw [this]
    exact hWo.measurableSet.diff ho.measurableSet
  have hZ0 : volume Z = 0 := by
    have hae := Pending.LelongPoincareDivisor.ae_ne_zero hWo hg fun y hy =>
      fun hev => by
        obtain ⟨V, hVsub, hVo, hyV⟩ := _root_.mem_nhds_iff.mp hev
        obtain ⟨w, hw, hgw⟩ := hgne (V ∩ W) inter_subset_right (hVo.inter hWo) ⟨y, hyV, hy⟩
        exact hVsub hw.1 hgw
    rw [ae_restrict_iff' hWo.measurableSet] at hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyZ
    exact hy hyZ.1 hyZ.2
  have hsub : A ∩ N ⊆ c.val.source ∩ c.val ⁻¹' Z := fun y hy =>
    ⟨hy.2.1, hy.2.2, hgA _ hy.2.2 (by rw [c.val.left_inv hy.2.1]; exact hy.1)⟩
  refine measure_mono_null hsub ?_
  have hce : AEMeasurable c.val (μ.restrict c.val.source) :=
    c.val.continuousOn.aemeasurable c.val.open_source.measurableSet
  have h1 : μ (c.val.source ∩ c.val ⁻¹' Z) = Measure.map c.val (μ.restrict c.val.source) Z := by
    rw [Measure.map_apply_of_aemeasurable hce hZm,
      Measure.restrict_apply' c.val.open_source.measurableSet, inter_comm]
  rw [h1, hmap, withDensity_apply _ hZm]
  refine setLIntegral_measure_zero _ _ ?_
  rw [Measure.restrict_apply hZm]
  exact measure_mono_null inter_subset_left hZ0

omit [IsComplexManifold n X] in
/-- Smooth positive volumes are locally finite. -/
theorem isLocallyFiniteMeasure_of_isSmoothPositiveVolume {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x => ?_⟩
  set c := complexChartAt (n := n) x
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  have hzt : c.val x ∈ c.val.target := c.val.map_source hxc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.val.open_target _ hzt
  set K : Set (ComplexModel n) := closedBall (c.val x) (r / 2) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ c.val.target := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨ρ, hρs, -, hmap⟩ := hμ c
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hρs.continuousOn.mono hKt)
  refine ⟨c.val.source ∩ c.val ⁻¹' K, ?_, ?_⟩
  · refine inter_mem (c.val.open_source.mem_nhds hxc)
      (c.val.continuousAt hxc (closedBall_mem_nhds _ (by linarith)))
  · have h := setLIntegral_source_inter_preimage c hρs.continuousOn hmap hKc hKt
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const
    simp only [setLIntegral_one, mul_one] at h
    rw [h]
    calc ∫⁻ z in K, ENNReal.ofReal (ρ z) ≤ ∫⁻ _ in K, ENNReal.ofReal B := by
          refine setLIntegral_mono' hKc.isClosed.measurableSet fun z hz => ?_
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hB z hz))
      _ = ENNReal.ofReal B * volume K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top


/-! ### Frames -/

section Frames

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

omit [MeasurableSpace X] [BorelSpace X] in
/-- `‖v‖ = |e(v)| ‖e⁻¹(1)‖` for `v` in a fiber over the base set of an atlas frame. -/
theorem norm_eq_coord_mul (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X))
    [MemTrivializationAtlas e] {y : X} (hy : y ∈ e.baseSet) (v : L.Fiber y) :
    ‖v‖ = ‖(e ⟨y, v⟩).2‖ * ‖e.symm y 1‖ := by
  have h1 : e.symm y ((e ⟨y, v⟩).2) = v := e.symm_apply_apply_mk hy v
  have h2 : ∀ t : ℂ, e.symm y t = t • e.symm y 1 := by
    intro t
    rw [← e.symmL_apply (R := ℂ) hy t, ← e.symmL_apply (R := ℂ) hy 1, ← map_smul, smul_eq_mul,
      mul_one]
  calc ‖v‖ = ‖e.symm y ((e ⟨y, v⟩).2)‖ := by rw [h1]
    _ = _ := by rw [h2, norm_smul]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The frame vector of an atlas frame does not vanish. -/
theorem frameNorm_pos (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X))
    [MemTrivializationAtlas e] {y : X} (hy : y ∈ e.baseSet) : 0 < ‖e.symm y 1‖ := by
  refine norm_pos_iff.mpr fun h0 => ?_
  have h1 : (e ⟨y, e.symm y 1⟩).2 = 1 := by rw [e.apply_mk_symm hy]
  have h2 : (e ⟨y, (0 : L.Fiber y)⟩).2 = 0 := (e.continuousLinearEquivAt ℂ y hy).map_zero
  rw [h0, h2] at h1
  exact zero_ne_one h1

end Frames

/-! ### The local extension -/

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- **Local `L²` removability** (`claude-twisted-l2-c:local-removal`; FPT
`lem:l2-holomorphic-analytic-removal`, local step).  Near a point `y ∈ U`, in a chart `c` and the
frame at `y`, the coefficient of a section which is holomorphic on `U \ A` and `L²` on `K \ A`
for compact `K ⊆ U` agrees off `A` with a function holomorphic on an open `O ∋ c y`. -/
theorem exists_local_extension {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {U A : Set X} (hU : IsOpen U) (hA : IsClosed A) (hAn : IsLocallyAnalyticNull (n := n) A)
    {S : (x : X) → L.Fiber x}
    (hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S (U \ A))
    (hL2 : ∀ K : Set X, IsCompact K → K ⊆ U → ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ < ⊤)
    {y : X} (hyU : y ∈ U) :
    ∃ (c : ComplexChart n X) (O : Set (ComplexModel n)) (G : ComplexModel n → ℂ),
      IsOpen O ∧ O ⊆ c.val.target ∧ c.val y ∈ O ∧ y ∈ c.val.source ∧
      (∀ z ∈ O, c.val.symm z ∈ U ∩ (trivializationAt ℂ L.Fiber y).baseSet) ∧
      DifferentiableOn ℂ G O ∧
      ∀ z ∈ O, c.val.symm z ∉ A →
        G z = ((trivializationAt ℂ L.Fiber y) ⟨c.val.symm z, S (c.val.symm z)⟩).2 := by
  classical
  obtain ⟨c, W, g, hyc, hWo, hyW, hWt, hg, hgne, hgA⟩ := hAn y
  set e := trivializationAt ℂ L.Fiber y with he
  set O : Set (ComplexModel n) := W ∩ (c.val.target ∩ c.val.symm ⁻¹' (U ∩ e.baseSet)) with hO
  have hOo : IsOpen O :=
    hWo.inter (c.val.isOpen_inter_preimage_symm (hU.inter e.open_baseSet))
  have hyO : c.val y ∈ O := ⟨hyW, c.val.map_source hyc, by
    rw [mem_preimage, c.val.left_inv hyc]; exact ⟨hyU, mem_baseSet_trivializationAt ℂ L.Fiber y⟩⟩
  have hOW : O ⊆ W := inter_subset_left
  have hOt : O ⊆ c.val.target := fun z hz => hz.2.1
  set f : ComplexModel n → ℂ := fun z => (e ⟨c.val.symm z, S (c.val.symm z)⟩).2 with hf
  set O' : Set (ComplexModel n) := O ∩ (c.val.target ∩ c.val.symm ⁻¹' Aᶜ) with hO'
  have hO'o : IsOpen O' := hOo.inter (c.val.isOpen_inter_preimage_symm hA.isOpen_compl)
  have hfd : DifferentiableOn ℂ f O' := by
    have h := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn e c
      (hU.sdiff hA) hS
    refine (h.mono fun z hz => ⟨hz.1.2.1, ⟨hz.1.2.2.1, hz.2.2⟩, hz.1.2.2.2⟩).congr fun z hz => ?_
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hz.1.2.2.2 _).symm
  have hgA' : ∀ z ∈ O, g z ≠ 0 → c.val.symm z ∉ A := fun z hz hgz hzA => hgz (hgA z hz.1 hzA)
  set F : ComplexModel n → ℂ := fun z => if g z = 0 then 0 else f z with hF
  have hOg : IsOpen (O ∩ {z | g z ≠ 0}) :=
    (hg.continuousOn.mono hOW).isOpen_inter_preimage hOo isOpen_compl_singleton
  have hFd : DifferentiableOn ℂ F (O ∩ {z | g z ≠ 0}) :=
    (hfd.mono fun z hz => ⟨hz.1, hz.1.2.1, hgA' z hz.1 hz.2⟩).congr fun z hz => if_neg hz.2
  have hkne : ∀ x ∈ O, ¬ ∀ᶠ w in 𝓝 x, g w = 0 := fun x hx hev => by
    obtain ⟨V, hVsub, hVo, hxV⟩ := _root_.mem_nhds_iff.mp hev
    obtain ⟨w, hw, hgw⟩ := hgne (V ∩ O) (inter_subset_right.trans hOW) (hVo.inter hOo)
      ⟨x, hxV, hx⟩
    exact hgw (hVsub hw.1)
  -- the continuity of `‖S‖` off `A`
  have hcontS : ContinuousOn (fun x => ‖S x‖) (U \ A) :=
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous.comp_continuousOn
      hS.continuousOn
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ c
  have hL2F : ∀ x ∈ O, ∃ r > 0, ball x r ⊆ O ∧
      ∫⁻ w in ball x r, ENNReal.ofReal (‖F w‖ ^ 2) ≠ ⊤ := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOo x hx
    set K : Set (ComplexModel n) := closedBall x (ε / 2) with hK
    have hKO : K ⊆ O := (closedBall_subset_ball (by linarith)).trans hball
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hKt : K ⊆ c.val.target := hKO.trans hOt
    have hKne : K.Nonempty := ⟨x, mem_closedBall_self (by positivity)⟩
    refine ⟨ε / 2, by positivity, ball_subset_closedBall.trans hKO, ?_⟩
    obtain ⟨z₁, hz₁K, hρmin⟩ := hKc.exists_isMinOn hKne (hρs.continuousOn.mono hKt)
    have hρm : 0 < ρ z₁ := hρpos z₁ (hKt hz₁K)
    have hφc : ContinuousOn (fun z => ‖e.symm (c.val.symm z) 1‖) O :=
      (SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn L.Fiber e).comp
        (c.val.continuousOn_symm.mono hOt) fun z hz => hz.2.2.2
    obtain ⟨z₂, hz₂K, hφmin⟩ := hKc.exists_isMinOn hKne (hφc.mono hKO)
    have hm : 0 < ‖e.symm (c.val.symm z₂) 1‖ := frameNorm_pos L e (hKO hz₂K).2.2.2
    set m := ‖e.symm (c.val.symm z₂) 1‖ with hmdef
    set Y : Set X := c.val.source ∩ c.val ⁻¹' (O ∩ {z | g z ≠ 0}) with hY
    have hYo : IsOpen Y := c.val.isOpen_inter_preimage hOg
    have hYUA : Y ⊆ U \ A := fun x' hx' => by
      have h1 : c.val.symm (c.val x') ∈ U ∩ e.baseSet := hx'.2.1.2.2
      rw [c.val.left_inv hx'.1] at h1
      have h2 := hgA' _ hx'.2.1 hx'.2.2
      rw [c.val.left_inv hx'.1] at h2
      exact ⟨h1.1, h2⟩
    set h : X → ℝ≥0∞ := Y.indicator fun x' => ENNReal.ofReal (‖S x'‖ ^ 2) with hh
    have hhm : Measurable h := by
      rw [hh, ← Set.piecewise_eq_indicator]
      refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hYo.measurableSet
      exact (ENNReal.continuous_ofReal.comp_continuousOn
        ((hcontS.mono hYUA).pow 2))
    set K' : Set X := c.val.symm '' K with hK'
    have hK'c : IsCompact K' := hKc.image_of_continuousOn (c.val.continuousOn_symm.mono hKt)
    have hK'U : K' ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact ((hKO hz).2.2).1
    have hK'A : MeasurableSet (K' \ A) := hK'c.isClosed.measurableSet.diff hA.measurableSet
    have hT : MeasurableSet (c.val.source ∩ c.val ⁻¹' K) :=
      measurableSet_source_inter_preimage c.val hKc.isClosed
    set C₀ : ℝ := 1 / (m ^ 2 * ρ z₁) with hC₀
    have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; exact (div_pos one_pos (mul_pos (pow_pos hm 2) hρm)).le
    have hpt : ∀ w ∈ K, ENNReal.ofReal (‖F w‖ ^ 2) ≤
        ENNReal.ofReal C₀ * (ENNReal.ofReal (ρ w) * h (c.val.symm w)) := by
      intro w hw
      by_cases hgw : g w = 0
      · simp [hF, hgw]
      have hwY : c.val.symm w ∈ Y := by
        refine ⟨c.val.map_target (hKt hw), ?_⟩
        show c.val (c.val.symm w) ∈ O ∩ {z | g z ≠ 0}
        rw [c.val.right_inv (hKt hw)]
        exact ⟨hKO hw, hgw⟩
      have hnorm := norm_eq_coord_mul L e (hKO hw).2.2.2 (S (c.val.symm w))
      rw [hh, indicator_of_mem hwY]
      simp only [hF, if_neg hgw]
      rw [hnorm, ← ENNReal.ofReal_mul (hρpos w (hKt hw)).le, ← ENNReal.ofReal_mul hC₀0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hρw : ρ z₁ ≤ ρ w := hρmin hw
      have hφw : m ≤ ‖e.symm (c.val.symm w) 1‖ := hφmin hw
      change ‖f w‖ ^ 2 ≤ C₀ * (ρ w * (‖f w‖ * ‖e.symm (c.val.symm w) 1‖) ^ 2)
      have hprod : m ^ 2 * ρ z₁ ≤ ρ w * ‖e.symm (c.val.symm w) 1‖ ^ 2 := by
        have : m ^ 2 ≤ ‖e.symm (c.val.symm w) 1‖ ^ 2 := by nlinarith
        nlinarith
      rw [hC₀, mul_pow]
      have hpos : 0 < m ^ 2 * ρ z₁ := by positivity
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
      nlinarith [sq_nonneg ‖f w‖]
    have hfin : ∫⁻ x' in K' \ A, ENNReal.ofReal (‖S x'‖ ^ 2) ∂μ < ⊤ := hL2 K' hK'c hK'U
    have hle : ∫⁻ x' in c.val.source ∩ c.val ⁻¹' K, h x' ∂μ ≤
        ∫⁻ x' in K' \ A, ENNReal.ofReal (‖S x'‖ ^ 2) ∂μ := by
      rw [← lintegral_indicator hK'A]
      refine (setLIntegral_mono' hT fun x' hx' => ?_).trans (setLIntegral_le_lintegral _ _)
      by_cases hx'Y : x' ∈ Y
      · have hx'K : x' ∈ K' := ⟨c.val x', hx'.2, c.val.left_inv hx'.1⟩
        rw [hh, indicator_of_mem hx'Y, indicator_of_mem (show x' ∈ K' \ A from ⟨hx'K, (hYUA hx'Y).2⟩)]
      · rw [hh, indicator_of_notMem hx'Y]
        exact zero_le
    refine (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top
      (ENNReal.ofReal_lt_top : ENNReal.ofReal C₀ < ⊤) (hle.trans_lt hfin))).ne
    calc ∫⁻ w in ball x (ε / 2), ENNReal.ofReal (‖F w‖ ^ 2)
        ≤ ∫⁻ w in K, ENNReal.ofReal (‖F w‖ ^ 2) := lintegral_mono_set ball_subset_closedBall
      _ ≤ ∫⁻ w in K, ENNReal.ofReal C₀ * (ENNReal.ofReal (ρ w) * h (c.val.symm w)) :=
          setLIntegral_mono' hKc.isClosed.measurableSet hpt
      _ = ENNReal.ofReal C₀ * ∫⁻ w in K, ENNReal.ofReal (ρ w) * h (c.val.symm w) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C₀ * ∫⁻ x' in c.val.source ∩ c.val ⁻¹' K, h x' ∂μ := by
          rw [setLIntegral_source_inter_preimage c hρs.continuousOn hmap hKc hKt hhm]
  obtain ⟨G, hGd, hGF⟩ := SGPT.Okounkov.TranscendentalL2.exists_extension_of_locally_sq_integrable
    hOo (hg.mono hOW) hkne hFd hL2F
  refine ⟨c, O, G, hOo, hOt, hyO, hyc, fun z hz => hz.2.2, hGd, fun z hz hzA => ?_⟩
  have hEq : EqOn G f O' := by
    refine Set.EqOn.of_subset_closure (s := O' ∩ {z | g z ≠ 0}) (fun w hw => ?_)
      (hGd.continuousOn.mono inter_subset_left) hfd.continuousOn inter_subset_left
      (fun w hw => ?_)
    · rw [hGF ⟨hw.1.1, hw.2⟩]
      exact if_neg hw.2
    · rw [_root_.mem_closure_iff]
      intro o ho hwo
      obtain ⟨v, hv, hgv⟩ := hgne (o ∩ O') ((inter_subset_right.trans inter_subset_left).trans hOW)
        (ho.inter hO'o) ⟨w, hwo, hw⟩
      exact ⟨v, hv.1, hv.2, hgv⟩
  exact hEq ⟨hz, hOt hz, hzA⟩


/-! ### Gluing the local extensions -/

variable (n X) in
/-- **`L2RemovableSingularityStatement` holds** (`claude-twisted-l2:l2-removable`; FPT
`lem:l2-holomorphic-analytic-removal`).  At each `y ∈ U` put `S' y = e_y⁻¹(G_y(c_y y))` with the
local extension of `exists_local_extension`.  In the frame `e_y` the coefficient of `S'` is
`G_y ∘ c_y` near `y`: off `A` both are the coefficient of `S`, and at a point `w ∈ A` the two
continuous functions `e_y(e_w⁻¹(G_w ∘ c_w))` and `G_y ∘ c_y` agree on the dense set off `A`. -/
theorem l2RemovableSingularityStatement : L2RemovableSingularityStatement n X := by
  intro μ hμ L U A hU hA hAn S hS hL2
  classical
  rcases U.eq_empty_or_nonempty with rfl | ⟨y₀, -⟩
  · exact ⟨S, fun y hy => hy.elim, fun x _ => rfl⟩
  have : Nonempty (ComplexChart n X) := ⟨complexChartAt y₀⟩
  choose! c O G hOo hOt hyO hysrc hOU hGd hGS using
    fun y (hy : y ∈ U) => exists_local_extension L hμ hU hA hAn hS hL2 hy
  set E : X → Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → X) :=
    fun y => trivializationAt ℂ L.Fiber y with hE
  set S' : (x : X) → L.Fiber x :=
    fun x => if x ∈ U then (E x).symm x (G x ((c x).val x)) else S x with hS'
  have hS'S : ∀ x ∈ U \ A, S' x = S x := by
    intro x hx
    simp only [hS', if_pos hx.1]
    have h := hGS x hx.1 _ (hyO x hx.1) (by rw [(c x).val.left_inv (hysrc x hx.1)]; exact hx.2)
    rw [(c x).val.left_inv (hysrc x hx.1)] at h
    rw [h]
    exact (E x).symm_apply_apply_mk (mem_baseSet_trivializationAt ℂ L.Fiber x) (S x)
  refine ⟨S', fun y hy => ?_, hS'S⟩
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  set e := E y with he
  have hye : y ∈ e.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber y
  rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e S' hye]
  -- the neighbourhood `N_w` of the local data at `w`
  have hN : ∀ w ∈ U, IsOpen ((c w).val.source ∩ (c w).val ⁻¹' O w) := fun w hw =>
    (c w).val.isOpen_inter_preimage (hOo w hw)
  have hNsub : ∀ w ∈ U, ∀ v ∈ (c w).val.source ∩ (c w).val ⁻¹' O w, v ∈ U ∩ (E w).baseSet :=
    fun w hw v hv => by
      have h := hOU w hw _ hv.2
      rwa [(c w).val.left_inv hv.1] at h
  have hcoef : ∀ w ∈ U, ∀ v ∈ (c w).val.source ∩ (c w).val ⁻¹' O w, v ∉ A →
      (E w).symm v (G w ((c w).val v)) = S v := fun w hw v hv hvA => by
    have h := hGS w hw _ hv.2 (by rw [(c w).val.left_inv hv.1]; exact hvA)
    rw [(c w).val.left_inv hv.1] at h
    rw [h]
    exact (E w).symm_apply_apply_mk (hNsub w hw v hv).2 (S v)
  have hGc : ∀ w ∈ U, ContinuousOn (fun v => G w ((c w).val v))
      ((c w).val.source ∩ (c w).val ⁻¹' O w) := fun w hw =>
    (hGd w hw).continuousOn.comp ((c w).val.continuousOn.mono inter_subset_left)
      fun v hv => hv.2
  set N := (c y).val.source ∩ (c y).val ⁻¹' O y with hNdef
  have hyN : y ∈ N := ⟨hysrc y hy, hyO y hy⟩
  have hkey : ∀ w ∈ N, (e ⟨w, S' w⟩).2 = G y ((c y).val w) := by
    intro w hw
    have hwU : w ∈ U := (hNsub y hy w hw).1
    set Nw := (c w).val.source ∩ (c w).val ⁻¹' O w with hNw
    have hwNw : w ∈ Nw := ⟨hysrc w hwU, hyO w hwU⟩
    set T := N ∩ Nw with hT
    have hTo : IsOpen T := (hN y hy).inter (hN w hwU)
    have hTbase : T ⊆ (E w).baseSet ∩ e.baseSet := fun v hv =>
      ⟨(hNsub w hwU v hv.2).2, (hNsub y hy v hv.1).2⟩
    have hφ1 : ContinuousOn (fun v => (e ⟨v, (E w).symm v (G w ((c w).val v))⟩).2) T := by
      have hcc := (continuousOn_coordChange ℂ (E w) e).mono hTbase
      refine (hcc.clm_apply ((hGc w hwU).mono inter_subset_right)).congr fun v hv => ?_
      exact (Trivialization.coordChangeL_apply (R := ℂ) (E w) e (hTbase hv) _).symm
    have hφ2 : ContinuousOn (fun v => G y ((c y).val v)) T := (hGc y hy).mono inter_subset_left
    have heq : EqOn (fun v => (e ⟨v, (E w).symm v (G w ((c w).val v))⟩).2)
        (fun v => G y ((c y).val v)) (T \ A) := by
      intro v hv
      simp only
      rw [hcoef w hwU v hv.1.2 hv.2]
      have h := hGS y hy _ hv.1.1.2 (by rw [(c y).val.left_inv hv.1.1.1]; exact hv.2)
      rw [(c y).val.left_inv hv.1.1.1] at h
      exact h.symm
    have hcl : T ⊆ closure (T \ A) :=
      (dense_compl_of_isLocallyAnalyticNull hAn).open_subset_closure_inter hTo
    have := Set.EqOn.of_subset_closure heq hφ1 hφ2 sdiff_subset hcl ⟨hw, hwNw⟩
    simp only [hS', if_pos hwU]
    exact this
  refine MDifferentiableAt.congr_of_eventuallyEq ?_
    (eventually_of_mem ((hN y hy).mem_nhds hyN) hkey)
  exact ((hGd y hy).differentiableAt ((hOo y hy).mem_nhds (hyO y hy))).comp_mdifferentiableAt
    (mdifferentiableAt_atlas (c y).property (hysrc y hy))

end SGPT.Trace.TwistedL2
