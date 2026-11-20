import SGPT.Trace.TwistedL2YReps

/-!
# Representatives of the localized projected field on a manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:level`).  For a chart-smooth
function `ζ` supported in the chart-frame domain of `(c, e)` and the projected field `v ∈ H₂`:

* `repX_wsys`: the piece `ζ W_{ce}(v)` is represented by `ζ v`;
* `ArX_f0`: the `T*`-representative of `f_ϑ = ζ ϑ τ - ∑_l ∂_l ζ W_l` is
  `√(a+b) (e^{-φ/2} ζ ϑ_ε τ - ⟨B*⁻¹∂̄ζ, v⟩)`, independent of the chart;
* `SrX_fS`: the `S`-representative of `f_S = ∂̄ζ ∧ σ^♭ W` is `B*⁻¹∂̄ζ ∧ v`.

Also the uniform `L²` bounds `exists_eLpNorm_ArX_le`, `exists_eLpNorm_SrX_le` for pieces supported
in a compact subset of a chart-frame domain, and measurability.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Metric
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder InnerProductSpace ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ}

theorem measurable_of_continuousOn_of_eq_zero {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] [Zero β] {S : Set α} (hS : IsOpen S) {f : α → β} (hf : ContinuousOn f S)
    (h0 : ∀ z ∉ S, f z = 0) : Measurable f := by
  have h := measurable_indicator_of_continuousOn_ref hS hf
  convert h using 1
  funext z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, h0 z hz]

theorem mul_mul_apply (A B C : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (A * B * C) a b = ∑ p, ∑ q, A a p * B p q * C q b := by
  simp only [mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem wedgeM_smul_right (x y : ComplexModel n) (c : ℂ) :
    wedgeM x (c • y) = c • wedgeM x y := by
  ext j k; simp [wedgeM]; ring

theorem wedgeM_zero_left' (y : ComplexModel n) : wedgeM 0 y = 0 := by
  ext j k; simp [wedgeM]

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable {T : TwistedDatum n X}

/-! ### Measurability of the representatives -/

theorem measurable_ArX (c : ComplexChart n X) (e : AtlasFrame T.L) {g : ComplexModel n → ℂ}
    (hg : Measurable g) : Measurable (T.ArX c e g) := by
  have h1 : Measurable ((T.cfd c e).indicator fun x => ((T.cwX x : ℝ) : ℂ)) :=
    measurable_indicator_of_continuousOn_ref (T.isOpen_cfd c e)
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_cwX.mono fun x hx => hx.2))
  have h2 := h1.mul (((measurable_ucX (T := T) e).inv).mul (measurable_indicator_comp_chart c hg))
  convert h2 using 1
  funext x
  by_cases hx : x ∈ T.cfd c e
  · simp [ArX, indicator_of_mem hx, indicator_of_mem hx.1.1]
  · simp [ArX, indicator_of_notMem hx]

theorem measurable_SrX (c : ComplexChart n X) (e : AtlasFrame T.L)
    {β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} (hβ : ∀ a b, Measurable fun z => β z a b) :
    Measurable (T.SrX c e β) := by
  have hS := T.isOpen_cfd c e
  have hBi : ∀ c' : ComplexChart n X, ContinuousOn (fun x => BiX T.omega T.r c' (c'.val x))
      (T.cfd c e ∩ c'.val.source) := fun c' =>
    (continuousOn_BiX T.isOpen_U T.kahler c').comp (c'.val.continuousOn.mono inter_subset_right)
      fun x hx => ⟨c'.val.map_source hx.2, by rw [mem_preimage, c'.val.left_inv hx.2]; exact hx.1.2⟩
  have hJ : ∀ c' : ComplexChart n X, ContinuousOn (fun x => Jm c' c (c'.val x))
      (T.cfd c e ∩ c'.val.source) := fun c' =>
    (continuousOn_Jm c' c).comp (c'.val.continuousOn.mono inter_subset_right)
      fun x hx => chart_mem_ovl hx.2 hx.1.1.1
  have hhw : ContinuousOn (fun x => ((T.hw x : ℝ) : ℂ)) (T.cfd c e) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_hw.mono fun x hx => hx.2)
  have hL : ∀ a p, Measurable fun x => (T.cfd c e).indicator (fun x =>
      (((T.hw x : ℝ) : ℂ) • (T.BiR x * (JiR c x)ᴴ)) a p) x := fun a p =>
    measurable_ref_indicator (F := fun c' x => (((T.hw x : ℝ) : ℂ) •
      (BiX T.omega T.r c' (c'.val x) * (Jm c' c (c'.val x))ᴴ)) a p) hS fun c' => by
        simp only [Matrix.smul_apply, smul_eq_mul, mul_apply, conjTranspose_apply, RCLike.star_def]
        exact (hhw.mono inter_subset_left).mul (continuousOn_finsetSum _ fun k _ =>
          (continuousOn_entry' (hBi c') a k).mul (Complex.continuous_conj.comp_continuousOn
            (continuousOn_entry' (hJ c') p k)))
  have hR : ∀ q b, Measurable fun x => (T.cfd c e).indicator (fun x =>
      ((JiR c x).map conj * (T.BiR x)ᵀ) q b) x := fun q b =>
    measurable_ref_indicator (F := fun c' x =>
      ((Jm c' c (c'.val x)).map conj * (BiX T.omega T.r c' (c'.val x))ᵀ) q b) hS fun c' => by
        simp only [mul_apply, map_apply, transpose_apply]
        exact continuousOn_finsetSum _ fun k _ => (Complex.continuous_conj.comp_continuousOn
          (continuousOn_entry' (hJ c') q k)).mul (continuousOn_entry' (hBi c') b k)
  have hB : ∀ p q, Measurable fun x => c.val.source.indicator (fun x => β (c.val x) p q) x :=
    fun p q => measurable_indicator_comp_chart c (hβ p q)
  have hM : Measurable fun x => (T.ucX e x)⁻¹ • flat2 (Matrix.of fun a b => ∑ p, ∑ q,
      (T.cfd c e).indicator (fun x => (((T.hw x : ℝ) : ℂ) • (T.BiR x * (JiR c x)ᴴ)) a p) x *
      c.val.source.indicator (fun x => β (c.val x) p q) x *
      (T.cfd c e).indicator (fun x => ((JiR c x).map conj * (T.BiR x)ᵀ) q b) x) :=
    ((measurable_ucX (T := T) e).inv).smul (measurable_flat2' fun a b => by
      simp only [of_apply]
      exact Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
        ((hL a p).mul (hB p q)).mul (hR q b))
  convert hM using 1
  funext x
  by_cases hx : x ∈ T.cfd c e
  · rw [SrX, indicator_of_mem hx, mul_comm, mul_smul]
    congr 1
    rw [← flat2_smul]
    congr 1
    ext a b
    simp only [of_apply, indicator_of_mem hx, indicator_of_mem hx.1.1, Matrix.smul_apply,
      smul_eq_mul]
    rw [show T.BiR x * ((JiR c x)ᴴ * β (c.val x) * (JiR c x).map conj) * (T.BiR x)ᵀ =
      (T.BiR x * (JiR c x)ᴴ) * β (c.val x) * ((JiR c x).map conj * (T.BiR x)ᵀ) by
        simp only [Matrix.mul_assoc], mul_mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  · have h0 : (Matrix.of fun (_ _ : Fin n) => (0 : ℂ)) = 0 := by ext; simp
    simp [SrX, indicator_of_notMem hx, h0, flat2_zero]

/-! ### Uniform `L²` bounds -/

theorem exists_eLpNorm_ArX_le (c : ComplexChart n X) (e : AtlasFrame T.L)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e) :
    ∃ C : ℝ, ∀ g : ComplexModel n → ℂ, Measurable g → (∀ z ∉ K, g z = 0) →
      eLpNorm (T.ArX c e g) 2 T.μ ≤ ENNReal.ofReal C * eLpNorm g 2 volume := by
  have hκ : ContinuousOn (fun z => Real.sqrt (T.aC c z + T.bC c z) * Real.sqrt (T.wX c e z))
      (T.pieceDomain c e) :=
    (((contDiffOn_aC (e := e) c).continuousOn.add
      (contDiffOn_bC (e := e) c).continuousOn).sqrt).mul (continuousOn_wX c e).sqrt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hκ.mono hKd)
  have hKt : K ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  obtain ⟨Cρ, -, hρ⟩ := exists_eLpNorm_le_chart c (T.isChartDensity_ρX c) hK hKt
  refine ⟨max C 0 * Cρ, fun g hg h0 => ?_⟩
  refine hρ (T.ArX c e g) g (max C 0) (le_max_right _ _) (measurable_ArX c e hg)
    (fun x hx => ?_) fun x hx => ?_
  · by_cases hxd : x ∈ T.cfd c e
    · have hw := wX_chart_eq (T := T) hxd.1
      have hu := ucX_ne_zero (T := T) hxd.1.2
      have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
      have hs : Real.sqrt (T.wX c e (c.val x)) = T.hw x / ‖T.ucX e x‖ := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (hw_pos x) hpos)]
        field_simp
        nlinarith [hw]
      have ha : T.aC c (c.val x) = T.a x := by simp only [aC, c.val.left_inv hxd.1.1]
      have hb : T.bC c (c.val x) = T.b x := by simp only [bC, c.val.left_inv hxd.1.1]
      have hCx := (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC _ hx.2).trans (le_max_left C 0))
      rw [ha, hb, hs] at hCx
      rw [ArX, indicator_of_mem hxd, norm_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (cwX_nonneg x), cwX]
      calc Real.sqrt (T.a x + T.b x) * T.hw x * (‖T.ucX e x‖⁻¹ * ‖g (c.val x)‖)
          = (Real.sqrt (T.a x + T.b x) * (T.hw x / ‖T.ucX e x‖)) * ‖g (c.val x)‖ := by
            field_simp
        _ ≤ max C 0 * ‖g (c.val x)‖ := mul_le_mul_of_nonneg_right hCx (norm_nonneg _)
    · rw [ArX, indicator_of_notMem hxd, norm_zero]; positivity
  · by_cases hxd : x ∈ T.cfd c e
    · rw [ArX, indicator_of_mem hxd, h0 _ fun h' => hx ⟨hxd.1.1, h'⟩, mul_zero, mul_zero]
    · exact indicator_of_notMem hxd _

theorem exists_eLpNorm_SrX_le (c : ComplexChart n X) (e : AtlasFrame T.L)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e) :
    ∃ C : ℝ, ∀ β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ,
      (∀ a b, Measurable fun z => β z a b) → (∀ z ∉ K, β z = 0) →
      eLpNorm (T.SrX c e β) 2 T.μ ≤ ENNReal.ofReal C * eLpNorm (fun z => flat2 (β z)) 2 volume := by
  have hκ : ContinuousOn (fun z => Real.sqrt (T.wX c e z) *
      ((n * n : ℝ) * (mnorm (BiX T.omega T.r c z) ^ 2 * (n * n : ℝ)))) (T.pieceDomain c e) :=
    (continuousOn_wX c e).sqrt.mul (continuousOn_const.mul (((continuous_mnorm.comp_continuousOn
      ((continuousOn_BiX T.isOpen_U T.kahler c).mono
        (T.pieceDomain_subset_chartSmooth c e))).pow 2).mul continuousOn_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hκ.mono hKd)
  have hKt : K ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  obtain ⟨Cρ, -, hρ⟩ := exists_eLpNorm_le_chart c (T.isChartDensity_ρX c) hK hKt
  refine ⟨max C 0 * Cρ, fun β hβ h0 => ?_⟩
  refine hρ (T.SrX c e β) (fun z => flat2 (β z)) (max C 0) (le_max_right _ _)
    (measurable_SrX c e hβ) (fun x hx => ?_) fun x hx => ?_
  · by_cases hxd : x ∈ T.cfd c e
    · rw [norm_SrX_pt β hxd]
      have hb := norm_flat2_mul_le (BiX T.omega T.r c (c.val x)) (β (c.val x))
      have hs := sum_norm_le_flat2 (β (c.val x))
      have hCx := (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC _ hx.2).trans (le_max_left C 0))
      have hm := mnorm_nonneg (BiX T.omega T.r c (c.val x))
      have hnn : (0 : ℝ) ≤ n * n := by positivity
      calc Real.sqrt (T.wX c e (c.val x)) * ‖flat2 (BiX T.omega T.r c (c.val x) * β (c.val x) *
            (BiX T.omega T.r c (c.val x))ᵀ)‖
          ≤ Real.sqrt (T.wX c e (c.val x)) * ((n * n : ℝ) *
            (mnorm (BiX T.omega T.r c (c.val x)) ^ 2 * ((n * n : ℝ) * ‖flat2 (β (c.val x))‖))) :=
            mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs (by positivity)) hnn)) (Real.sqrt_nonneg _)
        _ = (Real.sqrt (T.wX c e (c.val x)) * ((n * n : ℝ) *
            (mnorm (BiX T.omega T.r c (c.val x)) ^ 2 * (n * n : ℝ)))) * ‖flat2 (β (c.val x))‖ := by
            ring
        _ ≤ max C 0 * ‖flat2 (β (c.val x))‖ := mul_le_mul_of_nonneg_right hCx (norm_nonneg _)
    · rw [SrX, indicator_of_notMem hxd, norm_zero]; positivity
  · by_cases hxd : x ∈ T.cfd c e
    · rw [SrX, indicator_of_mem hxd, h0 _ fun h' => hx ⟨hxd.1.1, h'⟩, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul, flat2_zero, smul_zero]
    · exact indicator_of_notMem hxd _

/-! ### The limit representatives -/

variable (T) in
/-- The `T*`-representative of the cut-off `χ v` of the projected field. -/
def AlimX (F : T.XFam) (χ : X → ℝ) (v : X → ComplexModel n) (x : X) : ℂ :=
  T.U.indicator (fun x => ((T.cwX x : ℝ) : ℂ) * (χ x : ℂ) * T.TepsX F x -
    ((Real.sqrt (T.a x + T.b x) : ℝ) : ℂ) * ⟪T.dRX χ x, v x⟫_ℂ) x

variable (T) in
/-- The `S`-representative `B*⁻¹∂̄χ ∧ v` of the cut-off of the projected field. -/
def SlimX (χ : X → ℝ) (v : X → ComplexModel n) (x : X) : EuclideanSpace ℂ (Fin n × Fin n) :=
  flat2 (wedgeM (T.dRX χ x) (v x))

theorem dRX_eq_zero {χ : X → ℝ} {x : X} (hx : x ∉ tsupport χ) : T.dRX χ x = 0 := by
  by_cases hxU : x ∈ T.U
  · rw [dRX, indicator_of_mem hxU]
    set c := cR n x
    have hz : c.val x ∈ c.val.target := c.val.map_source (mem_cR_source x)
    have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (tsupport χ)ᶜ) :=
      c.val.continuousOn_symm.isOpen_inter_preimage c.val.open_target
        (isClosed_tsupport χ).isOpen_compl
    have hmem : c.val x ∈ c.val.target ∩ c.val.symm ⁻¹' (tsupport χ)ᶜ := by
      refine ⟨hz, ?_⟩
      rw [mem_preimage, c.val.left_inv (mem_cR_source x)]
      exact hx
    have hev : (fun y => ((χ (c.val.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 (c.val x)] fun _ => 0 := by
      filter_upwards [hO.mem_nhds hmem] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy.2]
    have h0 : dbarV (fun y => ((χ (c.val.symm y) : ℝ) : ℂ)) (c.val x) = 0 := by
      ext l
      simp [dbarV, dbarDir_eq_zero_of_eventuallyEq_zero hev]
    rw [h0, mv_zero]
  · rw [dRX, indicator_of_notMem hxU]

theorem chartFn_chart {c : ComplexChart n X} (ζ : X → ℝ) {x : X} (hx : x ∈ c.val.source) :
    chartFn c ζ (c.val x) = ζ x := by
  rw [chartFn, indicator_of_mem (c.val.map_source hx), c.val.left_inv hx]

/-- **The data limit of a localized piece**: `ζ W_{ce}(v)` is represented by `ζ v`. -/
theorem repX_wsys {c : ComplexChart n X} {e : AtlasFrame T.L} {ζ : X → ℝ}
    (hζd : tsupport ζ ⊆ T.cfd c e) (v : X → ComplexModel n) (x : X) :
    T.repX c e (ofComps (wsysG (chartFn c ζ) (T.WeX c e v))) x = (ζ x : ℂ) • v x := by
  by_cases hx : x ∈ T.cfd c e
  · have hu := ucX_ne_zero (T := T) hx.1.2
    have hw : ofComps (wsysG (chartFn c ζ) (T.WeX c e v)) (c.val x) =
        ((ζ x : ℂ) * T.ucX e x) • mv (JiR c x) (T.WepsX v x) := by
      ext i
      simp only [ofComps, wsysG, chartFn_chart ζ hx.1.1, WeX_chart v hx, PiLp.smul_apply,
        smul_eq_mul]
      ring
    rw [repX_of_mem hx, hw, mv_smul, smul_smul, mv_smul_mat, ← mv_mul, Matrix.mul_assoc,
      JR_mul_JiR hx.1.1, Matrix.mul_one, ← mv_smul_mat, mv_BR_WepsX hx.2]
    congr 1
    field_simp
  · have hζ : ζ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hζd h)
    rw [repX_of_notMem hx, hζ]
    simp

/-- **The `T*`-limit of a localized piece.** -/
theorem ArX_f0 (F : T.XFam) {c : ComplexChart n X} {e : AtlasFrame T.L} {ζ : X → ℝ}
    (hζ : ChartSmooth (n := n) ζ) (hζd : tsupport ζ ⊆ T.cfd c e) (v : X → ComplexModel n) (x : X) :
    T.ArX c e (f0G (chartFn c ζ) (T.WeX c e v) (chartTheta (T.pX c e) (F.tot c e))) x =
      T.U.indicator (fun x => ((T.cwX x : ℝ) : ℂ) * (ζ x : ℂ) * T.TepsX F x -
        ((Real.sqrt (T.a x + T.b x) : ℝ) : ℂ) * ⟪T.dRX ζ x, v x⟫_ℂ) x := by
  by_cases hx : x ∈ T.cfd c e
  · rw [ArX, indicator_of_mem hx, indicator_of_mem hx.2]
    have hu := ucX_ne_zero (T := T) hx.1.2
    set cs := cR n x
    have hzo : c.val x ∈ ovl c cs := chart_mem_ovl_cR hx.1.1
    have hψz : chg c cs (c.val x) = cs.val x := chg_chart hx.1.1
    have hzs : cs.val x ∈ cs.val.target := cs.val.map_source (mem_cR_source x)
    -- `ζ` in the chart `c` through the reference chart
    have hev : (fun y => ((chartFn c ζ y : ℝ) : ℂ)) =ᶠ[𝓝 (c.val x)]
        fun y => ((fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs y)) := by
      filter_upwards [(isOpen_ovl c cs).mem_nhds hzo] with y hy
      simp only [chartFn, indicator_of_mem hy.1, symm_chg hy]
    have hfd : DifferentiableAt ℝ (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs (c.val x)) := by
      rw [hψz]
      exact ((contDiffOn_ofReal' (hζ cs)).contDiffAt (cs.val.open_target.mem_nhds hzs)).differentiableAt
        (by simp)
    have hsum : ∑ l, dDir (coordVec l) (fun y => ((chartFn c ζ y : ℝ) : ℂ)) (c.val x) *
        T.WeX c e v (c.val x) l = T.ucX e x * ⟪dbarV (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ))
          (cs.val x), T.WepsX v x⟫_ℂ := by
      have h1 : ∀ l, dDir (coordVec l) (fun y => ((chartFn c ζ y : ℝ) : ℂ)) (c.val x) =
          dDir (coordVec l) (fun y => ((fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs y)))
            (c.val x) := fun l => by
        simp only [dDir]; rw [hev.fderiv_eq]
      simp only [h1]
      rw [WeX_chart v hx]
      simp only [PiLp.smul_apply, smul_eq_mul]
      have h2 : ∑ l, dDir (coordVec l) (fun y => ((fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ))
          (chg c cs y))) (c.val x) * (T.ucX e x * mv (JiR c x) (T.WepsX v x) l) =
          T.ucX e x * dDir (mv (JiR c x) (T.WepsX v x)) (fun y => ((fun w =>
            ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs y))) (c.val x) := by
        rw [dDir_vec_eq_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [h2, dDir_comp_holo (differentiableAt_chg hzo) hfd, ← mv_Jm, hψz]
      change _ * dDir (mv (JR c x) (mv (JiR c x) (T.WepsX v x))) _ _ = _
      rw [← mv_mul, JR_mul_JiR hx.1.1, mv_one, dDir_vec_eq_sum, inner_eq_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have hd : DifferentiableAt ℝ (fun w => ζ (cs.val.symm w)) (cs.val x) :=
        ((hζ cs).contDiffAt (cs.val.open_target.mem_nhds hzs)).differentiableAt (by simp)
      rw [dDir_ofReal_eq_conj hd]
      simp only [dbarV, PiLp.toLp_apply]
      ring
    have hθ := theta_tot_eq F hx
    have hf0 : f0G (chartFn c ζ) (T.WeX c e v) (chartTheta (T.pX c e) (F.tot c e)) (c.val x) =
        (ζ x : ℂ) * chartTheta (T.pX c e) (F.tot c e) (c.val x) - T.ucX e x *
          ⟪dbarV (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (cs.val x), T.WepsX v x⟫_ℂ := by
      rw [f0G, chartFn_chart ζ hx.1.1, hsum]
    have hθ' : chartTheta (T.pX c e) (F.tot c e) (c.val x) = T.ucX e x * T.TepsX F x := by
      rw [← hθ, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    have hd : ⟪T.dRX ζ x, v x⟫_ℂ = ((T.hw x : ℝ) : ℂ) *
        ⟪dbarV (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (cs.val x), T.WepsX v x⟫_ℂ := by
      rw [dRX, indicator_of_mem hx.2, inner_mv_left, BiR_conjTranspose, WepsX_of_mem hx.2,
        mv_smul_mat, inner_smul_right, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (hw_pos x).ne', Complex.ofReal_one, one_mul]
    rw [hf0, hθ', hd, cwX]
    push_cast
    field_simp
  · have hζ0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hζd h)
    have hd0 : T.dRX ζ x = 0 := dRX_eq_zero fun h => hx (hζd h)
    rw [ArX, indicator_of_notMem hx]
    by_cases hxU : x ∈ T.U
    · rw [indicator_of_mem hxU, hζ0, hd0, inner_zero_left]; simp
    · rw [indicator_of_notMem hxU]

/-- **The `S`-limit of a localized piece.** -/
theorem SrX_fS {c : ComplexChart n X} {e : AtlasFrame T.L} {ζ : X → ℝ}
    (hζ : ChartSmooth (n := n) ζ) (hζd : tsupport ζ ⊆ T.cfd c e) (v : X → ComplexModel n) (x : X) :
    T.SrX c e (fun z => Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r c) (chartFn c ζ) (T.WeX c e v) j k z) x =
      T.SlimX ζ v x := by
  by_cases hx : x ∈ T.cfd c e
  · rw [SrX, indicator_of_mem hx, SlimX]
    have hu := ucX_ne_zero (T := T) hx.1.2
    set cs := cR n x
    have hzo : c.val x ∈ ovl c cs := chart_mem_ovl_cR hx.1.1
    have hψz : chg c cs (c.val x) = cs.val x := chg_chart hx.1.1
    have hzs : cs.val x ∈ cs.val.target := cs.val.map_source (mem_cR_source x)
    have hev : (fun y => ((chartFn c ζ y : ℝ) : ℂ)) =ᶠ[𝓝 (c.val x)]
        fun y => ((fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs y)) := by
      filter_upwards [(isOpen_ovl c cs).mem_nhds hzo] with y hy
      simp only [chartFn, indicator_of_mem hy.1, symm_chg hy]
    have hfd : DifferentiableAt ℝ (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs (c.val x)) := by
      rw [hψz]
      exact ((contDiffOn_ofReal' (hζ cs)).contDiffAt (cs.val.open_target.mem_nhds hzs)).differentiableAt
        (by simp)
    set a := dbarV (fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (cs.val x)
    have ha : dbarV (fun y => ((chartFn c ζ y : ℝ) : ℂ)) (c.val x) = mv (JR c x)ᴴ a := by
      have h1 : dbarV (fun y => ((chartFn c ζ y : ℝ) : ℂ)) (c.val x) =
          dbarV (fun y => ((fun w => ((ζ (cs.val.symm w) : ℝ) : ℂ)) (chg c cs y))) (c.val x) := by
        ext l; simp only [dbarV, PiLp.toLp_apply]; exact dbarDir_congr_of_eventuallyEq hev
      rw [h1, dbarV_comp_holo (differentiableAt_chg hzo) hfd, hψz]
      rfl
    have hb : mv (gX T.omega T.r c (c.val x)) (T.WeX c e v (c.val x)) =
        T.ucX e x • mv (JR c x)ᴴ (mv (T.gR x) (T.WepsX v x)) := by
      rw [gX_ref hx.1.1 hx.2, WeX_chart v hx, mv_smul, ← mv_mul, ← mv_mul]
      congr 1
      simp only [Matrix.mul_assoc, JR_mul_JiR hx.1.1, Matrix.mul_one]
    have hfS : (Matrix.of fun j k => fSG (sigmaMatX T.omega T.r c) (chartFn c ζ) (T.WeX c e v) j k
        (c.val x)) = wedgeM (dbarV (fun y => ((chartFn c ζ y : ℝ) : ℂ)) (c.val x))
          (mv (gX T.omega T.r c (c.val x)) (T.WeX c e v (c.val x))) := by
      ext j k
      simp only [of_apply, fSG, wedgeM, lowS_sigmaMatX, dbarV, PiLp.toLp_apply]
      ring
    have hJJ : ∀ y : ComplexModel n, mv (JiR c x)ᴴ (mv (JR c x)ᴴ y) = y := fun y => by
      rw [← mv_mul, ← conjTranspose_mul, JR_mul_JiR hx.1.1, conjTranspose_one, mv_one]
    rw [hfS, ha, hb, show (JiR c x).map conj = ((JiR c x)ᴴ)ᵀ from
      (transpose_conjTranspose' _).symm, mul_wedgeM_mul_transpose, hJJ, mv_smul, hJJ,
      mul_wedgeM_mul_transpose, mv_smul, wedgeM_smul_right, flat2_smul, smul_smul]
    have hv : mv (T.BiR x) (mv (T.gR x) (T.WepsX v x)) =
        (((T.hw x)⁻¹ : ℝ) : ℂ) • v x := by
      have h1 := mv_BR_WepsX (T := T) (v := v) hx.2
      rw [mv_smul_mat] at h1
      rw [← BR_mul_BR hx.2, ← mv_mul, ← Matrix.mul_assoc, BiR_mul_BR hx.2, Matrix.one_mul, ← h1,
        smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (hw_pos x).ne', Complex.ofReal_one,
        one_smul]
    rw [hv, wedgeM_smul_right, flat2_smul, smul_smul]
    have hc : ((T.hw x : ℝ) : ℂ) * (T.ucX e x)⁻¹ * T.ucX e x * (((T.hw x)⁻¹ : ℝ) : ℂ) = 1 := by
      have hh := (hw_pos (T := T) x).ne'
      push_cast
      field_simp
    rw [hc, one_smul, dRX, indicator_of_mem hx.2]
  · have hd0 : T.dRX ζ x = 0 := dRX_eq_zero fun h => hx (hζd h)
    rw [SrX, indicator_of_notMem hx, SlimX, hd0, wedgeM_zero_left', flat2_zero]

end TwistedDatum

end SGPT.Trace.TwistedL2
