import SGPT.Trace.TwistedL2YLocal

/-!
# Reference charts, `σ`-orthonormal coordinates and chart integrals on a manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:reference`).  To realize the
Hilbert space `H₂` of `L`-valued `(1,0)`-vector fields on a manifold `X` as an ordinary `L²` space of
`ℂⁿ`-valued functions, every fibre is identified with `ℂⁿ` through a *reference chart* `cR x`,
chosen measurably among countably many atlas charts covering `X` (`cR`, `measurable_cR_comp`), and
the `σ`-orthonormal coordinates `B = √(σᵀ)` of that chart (`BX`, `BiX`).

* `BX c z = √(g_c z)` with `g_c = σ_cᵀ`; `BX² = g_c`, `σ_c(v) = ‖BX v‖²` (`sigmaQX_eq_norm_sq`) and the
  dual bound `norm_mv_BiX_sq_le`.
* `Jm c c' z = D(c' ∘ c⁻¹)(z)` (as a matrix) and `g_c = Jmᴴ g_{c'} Jm` (`gX_chg'`).
* Chart integrals: `integral_eq_chart`, `lintegral_eq_chart`, and the `L²` comparison
  `eLpNorm_le_chart` between functions on `X` supported in a chart and functions on the chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder InnerProductSpace ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

variable {n : ℕ}

/-! ### Generalities on measurability -/

theorem measurable_indicator_of_continuousOn_ref {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {S : Set α} (hS : IsOpen S) {f : α → β} (hf : ContinuousOn f S) :
    Measurable (S.indicator f) := by
  classical
  have := hf.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const hS.measurableSet
  convert this using 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx, Set.piecewise]

theorem measurable_mv' {α : Type*} [MeasurableSpace α] {M : α → Matrix (Fin n) (Fin n) ℂ}
    {y : α → ComplexModel n} (hM : ∀ i j, Measurable fun x => M x i j) (hy : Measurable y) :
    Measurable fun x => mv (M x) (y x) := by
  have hfun : (fun x => mv (M x) (y x)) = fun x => ∑ i, ∑ j,
      (M x i j * y x j) • (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) := by
    funext x
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hyj : Measurable fun x => y x j :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.measurable).comp hy
  exact ((hM i j).mul hyj).smul_const _

theorem measurable_matrix_mul {α : Type*} [MeasurableSpace α] {M N : α → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, Measurable fun x => M x i j) (hN : ∀ i j, Measurable fun x => N x i j) (i j : Fin n) :
    Measurable fun x => (M x * N x) i j := by
  simp only [mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hM i k).mul (hN k j)

theorem mv_linMat (A : ComplexModel n →L[ℂ] ComplexModel n) (u : ComplexModel n) :
    mv (linMat A) u = A u := by
  ext j
  rw [mv_apply, linMat_apply_eq]

theorem continuous_linMat :
    Continuous (linMat (n := n) : (ComplexModel n →L[ℂ] ComplexModel n) → _) := by
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [linMat, of_apply]
  exact ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous).comp
    ((ContinuousLinearMap.apply ℂ (ComplexModel n) (coordVec k)).continuous)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The reference chart -/

theorem exists_chartSeqX (hX : Nonempty X) :
    ∃ f : ℕ → X, ∀ x : X, ∃ k, x ∈ (complexChartAt (n := n) (f k)).val.source := by
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : X => (complexChartAt (n := n) y).val.source)
    (fun y => (complexChartAt (n := n) y).val.open_source)
  have hcov : ∀ x : X, ∃ y ∈ T, x ∈ (complexChartAt (n := n) y).val.source := by
    intro x
    have hx : x ∈ ⋃ y, (complexChartAt (n := n) y).val.source :=
      mem_iUnion.2 ⟨x, mem_complexChartAt_source x⟩
    rw [← hT] at hx
    obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 hx
    exact ⟨y, hyT, hy⟩
  obtain ⟨x₀⟩ := hX
  have hTne : T.Nonempty := by
    obtain ⟨y, hy, -⟩ := hcov x₀
    exact ⟨y, hy⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  refine ⟨f, fun x => ?_⟩
  obtain ⟨y, hyT, hy⟩ := hcov x
  rw [hf] at hyT
  obtain ⟨k, rfl⟩ := hyT
  exact ⟨k, hy⟩

variable (n) in
/-- A sequence of points whose preferred charts cover `X`. -/
def chartSeqX (hX : Nonempty X) : ℕ → X := Classical.choose (exists_chartSeqX (n := n) hX)

theorem chartSeqX_spec (hX : Nonempty X) (x : X) :
    ∃ k, x ∈ (complexChartAt (n := n) (chartSeqX n hX k)).val.source :=
  Classical.choose_spec (exists_chartSeqX (n := n) hX) x

open Classical in
variable (n) in
/-- The index of the reference chart at `x`: the first chart of the sequence containing `x`. -/
def refIdx (x : X) : ℕ := Nat.find (chartSeqX_spec (n := n) ⟨x⟩ x)

variable (n) in
/-- **The reference chart** at `x`. -/
def cR (x : X) : ComplexChart n X := complexChartAt (n := n) (chartSeqX n ⟨x⟩ (refIdx n x))

theorem mem_cR_source (x : X) : x ∈ (cR n x).val.source := by
  classical
  exact Nat.find_spec (chartSeqX_spec (n := n) ⟨x⟩ x)

/-- **Measurability of quantities read in the reference chart.** -/
theorem measurable_cR_comp [MeasurableSpace X] [BorelSpace X] {β : Type*} [MeasurableSpace β]
    {f : ComplexChart n X → X → β} (hf : ∀ c, Measurable (f c)) :
    Measurable fun x => f (cR n x) x := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Subsingleton.measurable
  have hm := Measurable.find (f := fun k => f (complexChartAt (n := n) (chartSeqX n hX k)))
    (p := fun k x => x ∈ (complexChartAt (n := n) (chartSeqX n hX k)).val.source)
    (fun k => hf _) (fun k => (complexChartAt (n := n) (chartSeqX n hX k)).val.open_source.measurableSet)
    (chartSeqX_spec hX)
  convert hm using 1
  funext x
  rfl

/-- Indicator form of `measurable_cR_comp` for quantities continuous on chart domains. -/
theorem measurable_ref_indicator [MeasurableSpace X] [BorelSpace X] {S : Set X} (hS : IsOpen S)
    {F : ComplexChart n X → X → ℂ} (hF : ∀ c, ContinuousOn (F c) (S ∩ c.val.source)) :
    Measurable fun x => S.indicator (fun x => F (cR n x) x) x := by
  have h := measurable_cR_comp (n := n) (f := fun c x => (S ∩ c.val.source).indicator (F c) x)
    fun c => measurable_indicator_of_continuousOn_ref (hS.inter c.val.open_source) (hF c)
  convert h using 1
  funext x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ S ∩ (cR n x).val.source from
      ⟨hx, mem_cR_source x⟩)]
  · rw [indicator_of_notMem hx, indicator_of_notMem fun h => hx h.1]

/-! ### `σ`-orthonormal coordinates in a chart -/

section Sqrt

variable (omega : KahlerBackground n X) (r : X → ℝ)

/-- `BX c z = √(g_c z)`, `g_c = σ_cᵀ`. -/
def BX (c : ComplexChart n X) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  msqrt (gX omega r c z)

/-- `BiX c z = (BX c z)⁻¹`. -/
def BiX (c : ComplexChart n X) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  (BX omega r c z)⁻¹

variable {omega r}

theorem BX_conjTranspose (c : ComplexChart n X) (z : ComplexModel n) :
    (BX omega r c z)ᴴ = BX omega r c z := msqrt_conjTranspose _

theorem BiX_conjTranspose (c : ComplexChart n X) (z : ComplexModel n) :
    (BiX omega r c z)ᴴ = BiX omega r c z := by
  rw [BiX, conjTranspose_nonsing_inv, BX_conjTranspose]

variable {U : Set X} (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
include hU hr

theorem BX_mul_BX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : BX omega r c z * BX omega r c z = gX omega r c z :=
  msqrt_mul_self (posDef_gX hU hr hz hzU).posSemidef

theorem isUnit_det_BX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : IsUnit (BX omega r c z).det := by
  have h := (posDef_gX hU hr hz hzU).det_pos.ne'
  rw [← BX_mul_BX hU hr hz hzU, det_mul] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => h (by rw [h0, zero_mul])

theorem BiX_mul_BX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : BiX omega r c z * BX omega r c z = 1 :=
  nonsing_inv_mul _ (isUnit_det_BX hU hr hz hzU)

theorem BX_mul_BiX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : BX omega r c z * BiX omega r c z = 1 :=
  mul_nonsing_inv _ (isUnit_det_BX hU hr hz hzU)

theorem gX_inv_eq {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : (gX omega r c z)⁻¹ = BiX omega r c z * BiX omega r c z := by
  rw [← BX_mul_BX hU hr hz hzU, BiX, Matrix.mul_inv_rev]

theorem mv_BX_BiX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) (x : ComplexModel n) :
    mv (BX omega r c z) (mv (BiX omega r c z) x) = x := by
  rw [← mv_mul, BX_mul_BiX hU hr hz hzU, mv_one]

theorem mv_BiX_BX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) (x : ComplexModel n) :
    mv (BiX omega r c z) (mv (BX omega r c z) x) = x := by
  rw [← mv_mul, BiX_mul_BX hU hr hz hzU, mv_one]

theorem mv_BX_BX {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) (x : ComplexModel n) :
    mv (BX omega r c z) (mv (BX omega r c z) x) = mv (gX omega r c z) x := by
  rw [← mv_mul, BX_mul_BX hU hr hz hzU]

theorem gX_conjTranspose {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : (gX omega r c z)ᴴ = gX omega r c z :=
  (posDef_gX hU hr hz hzU).isHermitian

theorem continuousOn_BX (c : ComplexChart n X) :
    ContinuousOn (BX omega r c) (c.val.target ∩ c.val.symm ⁻¹' U) :=
  continuousOn_msqrt (continuousOn_gX hU hr c) fun _ hz => (posDef_gX hU hr hz.1 hz.2).posSemidef

theorem continuousOn_BiX (c : ComplexChart n X) :
    ContinuousOn (BiX omega r c) (c.val.target ∩ c.val.symm ⁻¹' U) := by
  intro z hz
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' U) := c.val.isOpen_inter_preimage_symm hU
  have hinv : ContinuousAt Ring.inverse (BX omega r c z).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_det_BX hU hr hz.1 hz.2).ne_zero
  exact (ContinuousAt.comp (f := BX omega r c) (continuousAt_matrix_inv _ hinv)
    ((continuousOn_BX hU hr c).continuousAt (hO.mem_nhds hz))).continuousWithinAt

/-- `σ_c(v) = ⟪v, g_c v⟫`. -/
theorem sigmaQX_eq_inner {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) (v : ComplexModel n) :
    (sigmaQX omega r c z v : ℂ) = ⟪v, mv (gX omega r c z) v⟫_ℂ := by
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potentialX hU hr c hz hzU
  have hRz : ContDiffAt ℝ 2 R z :=
    (hR.contDiffAt (hV.mem_nhds hzV)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hσ z hzV, ← leviS_self hRz, ← sum_sigmaMatX_mul hV hR hσ hzV]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, mv, dotProduct,
    mulVec, gX, transpose_apply, Pi.star_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sigmaQX_eq_norm_sq {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) (v : ComplexModel n) :
    sigmaQX omega r c z v = ‖mv (BX omega r c z) v‖ ^ 2 := by
  have h := sigmaQX_eq_inner hU hr hz hzU v
  rw [← mv_BX_BX hU hr hz hzU, inner_mv_right, BX_conjTranspose,
    inner_self_eq_norm_sq_to_K] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [this]
  first
  | (rw [← RCLike.ofReal_pow, RCLike.ofReal_re])
  | norm_cast

/-- **The dual-norm bound** in a chart: `|⟪v, a⟫|² ≤ c σ(v)` for all `v` gives `‖Bi a‖² ≤ c`. -/
theorem norm_mv_BiX_sq_le {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) {a : ComplexModel n} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, ‖⟪v, a⟫_ℂ‖ ^ 2 ≤ C * sigmaQX omega r c z v) :
    ‖mv (BiX omega r c z) a‖ ^ 2 ≤ C := by
  set y := mv (BiX omega r c z) a with hy
  have hv := h (mv (BiX omega r c z) y)
  rw [inner_mv_left, BiX_conjTranspose, ← hy, inner_self_eq_norm_sq_to_K,
    sigmaQX_eq_norm_sq hU hr hz hzU, mv_BX_BiX hU hr hz hzU] at hv
  have hv' : (‖y‖ ^ 2) ^ 2 ≤ C * ‖y‖ ^ 2 := by simpa [norm_pow] using hv
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0]
    simpa using hC
  · have hp : 0 < ‖y‖ ^ 2 := by positivity
    nlinarith

end Sqrt

/-! ### Jacobian matrices of coordinate changes -/

/-- The matrix of `D(c' ∘ c⁻¹)(z)`. -/
def Jm (c c' : ComplexChart n X) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  linMat (fderiv ℂ (chg c c') z)

theorem mv_Jm (c c' : ComplexChart n X) (z u : ComplexModel n) :
    mv (Jm c c' z) u = fderiv ℂ (chg c c') z u := mv_linMat _ u

theorem Jm_inv_mul {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    Jm c' c (chg c c' z) * Jm c c' z = 1 := by
  have h := fderiv_chg_comp (c'' := c) hz (c.val.map_target hz.1)
  rw [fderiv_chg_self hz.1] at h
  have h1 := congrArg linMat h
  rw [linMat_id, linMat_comp] at h1
  exact h1.symm

theorem Jm_mul_inv {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    Jm c c' z * Jm c' c (chg c c' z) = 1 :=
  mul_eq_one_comm.mp (Jm_inv_mul hz)

theorem continuousOn_Jm (c c' : ComplexChart n X) : ContinuousOn (Jm c c') (ovl c c') := by
  have h : ContDiffOn ℂ ∞ (chg c c') (ovl c c') :=
    contDiffOn_of_differentiableOn_complex (differentiableOn_chg c c') (isOpen_ovl c c')
  exact continuous_linMat.comp_continuousOn
    (h.continuousOn_fderiv_of_isOpen (isOpen_ovl c c') (by simp))

theorem gX_chg' {omega : KahlerBackground n X} {r : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hr : IsKahlerModificationOn omega r U) {c c' : ComplexChart n X} {z : ComplexModel n}
    (hz : z ∈ ovl c c') (hzU : c.val.symm z ∈ U) :
    gX omega r c z = (Jm c c' z)ᴴ * gX omega r c' (chg c c' z) * Jm c c' z :=
  gX_chg hU hr hz hzU

/-! ### Chart integrals -/

variable [MeasurableSpace X] [BorelSpace X]

theorem lintegral_eq_chart {μ : Measure X} (c : ComplexChart n X) {ρ : ComplexModel n → ℝ}
    (hρ : IsChartDensity μ c ρ) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKt : K ⊆ c.val.target) {f : X → ℝ≥0∞} (hf : Measurable f)
    (h0 : ∀ x, x ∉ c.val.source ∩ c.val ⁻¹' K → f x = 0) :
    ∫⁻ x, f x ∂μ = ∫⁻ z in K, ENNReal.ofReal (ρ z) * f (c.val.symm z) := by
  rw [← setLIntegral_source_inter_preimage c hρ.1.continuousOn hρ.2.2 hK hKt hf,
    ← lintegral_indicator (measurableSet_source_inter_preimage c.val hK.isClosed)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ c.val.source ∩ c.val ⁻¹' K
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, h0 x hx]

theorem integral_eq_chart {μ : Measure X} (c : ComplexChart n X) {ρ : ComplexModel n → ℝ}
    (hρ : IsChartDensity μ c ρ) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKt : K ⊆ c.val.target) {f : X → ℂ} (hf : Measurable f)
    (h0 : ∀ x, x ∉ c.val.source ∩ c.val ⁻¹' K → f x = 0) :
    ∫ x, f x ∂μ = ∫ z in K, (ρ z : ℂ) * f (c.val.symm z) := by
  rw [← setIntegral_source_inter_preimage c hρ.1.continuousOn hρ.2.1 hρ.2.2 hK hKt hf]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => h0 x hx).symm

/-- **`L²` norms of functions supported in a chart.** -/
theorem exists_eLpNorm_le_chart {μ : Measure X} (c : ComplexChart n X) {ρ : ComplexModel n → ℝ}
    (hρ : IsChartDensity μ c ρ) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKt : K ⊆ c.val.target) : ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ {E E' : Type} [NormedAddCommGroup E]
      [NormedAddCommGroup E'] [MeasurableSpace E] [BorelSpace E] (F : X → E)
      (g : ComplexModel n → E') (C : ℝ), 0 ≤ C → Measurable F →
      (∀ x ∈ c.val.source ∩ c.val ⁻¹' K, ‖F x‖ ≤ C * ‖g (c.val x)‖) →
      (∀ x, x ∉ c.val.source ∩ c.val ⁻¹' K → F x = 0) →
      eLpNorm F 2 μ ≤ ENNReal.ofReal (C * Cρ) * eLpNorm g 2 volume := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hρ.1.continuousOn.mono hKt)
  refine ⟨Real.sqrt (max M 0), Real.sqrt_nonneg _, ?_⟩
  intro E E' _ _ _ _ F g C hC hF hb h0
  have hρM : ∀ z ∈ K, ρ z ≤ max M 0 := fun z hz =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM z hz).trans (le_max_left _ _))
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2']
  have hm : Measurable fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal := hF.enorm.pow_const _
  rw [lintegral_eq_chart c hρ hK hKt hm fun x hx => by simp [h0 x hx]]
  have hpt : ∀ z ∈ K, ENNReal.ofReal (ρ z) * ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ≥0∞).toReal ≤
      ENNReal.ofReal (C * Real.sqrt (max M 0)) ^ (2 : ℝ≥0∞).toReal *
        ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal := by
    intro z hz
    have hx : c.val.symm z ∈ c.val.source ∩ c.val ⁻¹' K :=
      ⟨c.val.map_target (hKt hz), by simp only [mem_preimage, c.val.right_inv (hKt hz)]; exact hz⟩
    have hbz := hb _ hx
    rw [c.val.right_inv (hKt hz)] at hbz
    simp only [ENNReal.toReal_ofNat]
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ← ENNReal.ofReal_mul (hρ.2.1 z (hKt hz)).le,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hρz := hρM z hz
    have hρ0 := (hρ.2.1 z (hKt hz)).le
    have hs : Real.sqrt (max M 0) ^ (2 : ℝ) = max M 0 := by
      rw [Real.rpow_two, Real.sq_sqrt (le_max_right _ _)]
    have hF2 : ‖F (c.val.symm z)‖ ^ (2 : ℝ) ≤ (C * ‖g z‖) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hbz (by norm_num)
    rw [Real.mul_rpow hC (Real.sqrt_nonneg _), hs]
    rw [Real.mul_rpow hC (norm_nonneg _)] at hF2
    calc ρ z * ‖F (c.val.symm z)‖ ^ (2 : ℝ) ≤ max M 0 * (C ^ (2 : ℝ) * ‖g z‖ ^ (2 : ℝ)) :=
          mul_le_mul hρz hF2 (by positivity) (le_max_right _ _)
      _ = C ^ (2 : ℝ) * max M 0 * ‖g z‖ ^ (2 : ℝ) := by ring
  have hle : ∫⁻ z in K, ENNReal.ofReal (ρ z) * ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ≥0∞).toReal ≤
      ENNReal.ofReal (C * Real.sqrt (max M 0)) ^ (2 : ℝ≥0∞).toReal *
        ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal := by
    rw [← lintegral_const_mul' _ _ (by simp)]
    calc ∫⁻ z in K, ENNReal.ofReal (ρ z) * ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ≥0∞).toReal
        ≤ ∫⁻ z in K, ENNReal.ofReal (C * Real.sqrt (max M 0)) ^ (2 : ℝ≥0∞).toReal *
          ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal :=
          setLIntegral_mono' hK.measurableSet hpt
      _ ≤ _ := setLIntegral_le_lintegral K _
  have h12 : (1 / (2 : ℝ≥0∞).toReal) = (2 : ℝ≥0∞).toReal⁻¹ := by norm_num
  calc (∫⁻ z in K, ENNReal.ofReal (ρ z) * ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
        (1 / (2 : ℝ≥0∞).toReal)
      ≤ (ENNReal.ofReal (C * Real.sqrt (max M 0)) ^ (2 : ℝ≥0∞).toReal *
        ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (C * Real.sqrt (max M 0)) *
        (∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

/-- Measurability of `z ↦ f(c⁻¹ z)` on a closed subset of the chart target. -/
theorem measurable_indicator_comp_symm (c : ComplexChart n X) {E : Type*} [MeasurableSpace E]
    [Zero E] {f : X → E} (hf : Measurable f) {K : Set (ComplexModel n)} (hK : IsClosed K)
    (hKt : K ⊆ c.val.target) : Measurable (K.indicator fun z => f (c.val.symm z)) := by
  classical
  have he : Measurable (c.val.target.piecewise c.val.symm fun _ => c.val.symm 0) :=
    c.val.continuousOn_symm.measurable_piecewise continuousOn_const
      c.val.open_target.measurableSet
  have h := (hf.comp he).indicator hK.measurableSet
  convert h using 1
  funext z
  by_cases hz : z ∈ K
  · simp [indicator_of_mem hz, Set.piecewise, hKt hz]
  · simp [indicator_of_notMem hz]

end SGPT.Trace.TwistedL2
