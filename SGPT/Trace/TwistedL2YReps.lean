import SGPT.Trace.TwistedL2YCutoff

/-!
# The `T*`- and `S`-energies of families on a manifold as `L²` norms

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:reps`).  For a finite family `τ` of
local pieces on `X`, read in the unit frame of `L` and, for the `(0,2)`-forms, in the
`σ`-orthonormal coordinates of the reference chart:

* `AFX τ = ∑_i √(a+b) e^{-φ/2} ucX⁻¹ ϑ h_i` and `energy_eqX`: `‖T* τ‖² = ∫ |AFX τ|² dμ`;
* `SFX τ = ∑_i e^{-φ/2} ucX⁻¹ B* (D⁻ᴴ β_i D̄⁻¹) B*ᵀ` with `β_i = (gA_{h_i})ᵀ - gA_{h_i}`, and
  `senergy_eqX`: `‖∂̄σ^♭τ‖² = ½ ∫ ‖SFX τ‖² dμ`.

The pieces are transported to the reference chart by `kahlerAntisym_transport'`; the norms of the
transported `(0,2)`-forms are chart-invariant (`zeroTwoPair_transport'`).
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

/-! ### `L²` helpers on a measure space -/

section Gen

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_norm_sq_eq' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : α → E} (hf : MemLp f 2 μ) : ∫ z, ‖f z‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f), L2.inner_def,
    ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz, inner_self_eq_norm_sq (𝕜 := ℂ)]

theorem tendsto_toLp_of_eLpNorm' {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → α → E} {g : α → E} (hf : ∀ m, MemLp (f m) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun m => eLpNorm (fun z => f m z - g z) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : ∀ m, ‖(hf m).toLp (f m) - hg.toLp g‖ =
      (eLpNorm (fun z => f m z - g z) 2 μ).toReal := by
    intro m
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  simp only [he]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

theorem tendsto_integral_norm_sq' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℕ → α → E} {g : α → E} (hf : ∀ m, MemLp (f m) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun m => eLpNorm (fun z => f m z - g z) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ z, ‖f m z‖ ^ 2 ∂μ) atTop (𝓝 (∫ z, ‖g z‖ ^ 2 ∂μ)) := by
  simp only [integral_norm_sq_eq' (hf _), integral_norm_sq_eq' hg]
  have hL := tendsto_toLp_of_eLpNorm' hf hg h
  exact ((continuous_norm.tendsto _).comp hL).pow 2

theorem tendsto_eLpNorm_of_integral' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℕ → α → E} (hf : ∀ k, MemLp (f k) 2 μ)
    (h : Tendsto (fun k => ∫ z, ‖f k z‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  have he : ∀ k, eLpNorm (f k) 2 μ = ENNReal.ofReal (Real.sqrt (∫ z, ‖f k z‖ ^ 2 ∂μ)) := by
    intro k
    rw [integral_norm_sq_eq' (hf k), Real.sqrt_sq (norm_nonneg _), Lp.norm_toLp,
      ENNReal.ofReal_toReal (hf k).eLpNorm_ne_top]
  simp only [he]
  have := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp h)
  simpa [Function.comp_def] using this

theorem tendsto_eLpNorm_sum'' {ι : Type*} (s : Finset ι) {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] {F : ℕ → α → E} {G : ι → ℕ → α → E'}
    (hG : ∀ i m, AEStronglyMeasurable (G i m) μ) (hb : ∀ m z, ‖F m z‖ ≤ ∑ i ∈ s, ‖G i m z‖)
    (h : ∀ i ∈ s, Tendsto (fun m => eLpNorm (G i m) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (F m) 2 μ) atTop (𝓝 0) := by
  have hle : ∀ m, eLpNorm (F m) 2 μ ≤ ∑ i ∈ s, eLpNorm (G i m) 2 μ := by
    intro m
    refine (eLpNorm_mono_real (g := fun z => ∑ i ∈ s, ‖G i m z‖) (hb m)).trans ?_
    have h1 := eLpNorm_sum_le (f := fun i z => ‖G i m z‖) (s := s) (p := 2) (μ := μ)
      (fun i _ => (hG i m).norm) (by norm_num)
    have h2 : (∑ i ∈ s, fun z => ‖G i m z‖) = fun z => ∑ i ∈ s, ‖G i m z‖ := by
      funext z; simp [Finset.sum_apply]
    rw [h2] at h1
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    exact eLpNorm_norm _
  have hsum : Tendsto (fun m => ∑ i ∈ s, eLpNorm (G i m) 2 μ) atTop (𝓝 0) := by
    have := tendsto_finsetSum s h
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => by positivity)
    hle

end Gen

theorem measurable_flat2' {α : Type*} [MeasurableSpace α] {M : α → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ j k, Measurable fun x => M x j k) : Measurable fun x => flat2 (M x) := by
  classical
  have hfun : (fun x => flat2 (M x)) = fun x => ∑ p : Fin n × Fin n,
      M x p.1 p.2 • (EuclideanSpace.single p (1 : ℂ) : EuclideanSpace ℂ (Fin n × Fin n)) := by
    funext x
    ext q
    simp [flat2, Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  exact Finset.measurable_sum _ fun p _ => (h p.1 p.2).smul_const _

theorem norm_entry_le_flat2 (M : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    ‖M j k‖ ≤ ‖flat2 M‖ :=
  PiLp.norm_apply_le (flat2 M) (j, k)

theorem sum_norm_le_flat2 (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ c, ‖M a c‖ ≤ (n * n : ℝ) * ‖flat2 M‖ := by
  calc ∑ a, ∑ c, ‖M a c‖ ≤ ∑ _a : Fin n, ∑ _c : Fin n, ‖flat2 M‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => norm_entry_le_flat2 M a c
    _ = _ := by simp; ring

/-! ### Transport of `(0,2)`-forms -/

theorem conjTranspose_map_conj (A : Matrix (Fin n) (Fin n) ℂ) : (A.map conj)ᴴ = Aᵀ := by
  ext i j; simp

theorem transpose_conjTranspose' (A : Matrix (Fin n) (Fin n) ℂ) : Aᴴᵀ = A.map conj := by
  ext i j; simp

/-- **The transport of `β = (gA)ᵀ - gA`**: if `g = Mᴴ g' M`, `A' M̄ = t M A` and `J M = 1`, then
`β' = t Jᴴ β J̄`. -/
theorem kahlerAntisym_transport' {M Ji g g' A A' : Matrix (Fin n) (Fin n) ℂ} {t : ℂ}
    (hJ : Ji * M = 1) (hgg : g = Mᴴ * g' * M) (hA : A' * M.map conj = t • (M * A)) :
    kahlerAntisym g' A' = t • (Jiᴴ * kahlerAntisym g A * Ji.map conj) := by
  have hMJ : M * Ji = 1 := mul_eq_one_comm.mp hJ
  have hc : M.map conj * Ji.map conj = 1 := by
    rw [← Matrix.map_mul (f := starRingEnd ℂ), hMJ]; ext i j; simp [one_apply]
  have hA' : A' = t • (M * A * Ji.map conj) := by
    have := congrArg (· * Ji.map conj) hA
    simp only [Matrix.mul_assoc, hc, Matrix.mul_one, Matrix.smul_mul] at this
    rw [this, Matrix.mul_assoc]
  have hg'M : g' * M = Jiᴴ * g := by
    rw [hgg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hMJ, conjTranspose_one,
      Matrix.one_mul]
  have hX : g' * A' = t • (Jiᴴ * (g * A) * Ji.map conj) := by
    rw [hA', Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg'M]
    simp only [Matrix.mul_assoc]
  simp only [kahlerAntisym, hX, transpose_smul, transpose_mul,
    Matrix.mul_sub, Matrix.sub_mul, smul_sub, Matrix.mul_assoc]
  rw [show (Ji.map conj)ᵀ = Jiᴴ from by ext; simp, transpose_conjTranspose']

/-- **Chart invariance of the `σ`-pairing of `(0,2)`-forms.** -/
theorem zeroTwoPair_transport' {M Ji g g' : Matrix (Fin n) (Fin n) ℂ} (hJ : Ji * M = 1)
    (hg : IsUnit g.det) (hgg : g = Mᴴ * g' * M) (β γ : Matrix (Fin n) (Fin n) ℂ) :
    zeroTwoPair g'⁻¹ (Jiᴴ * β * Ji.map conj) (Jiᴴ * γ * Ji.map conj) = zeroTwoPair g⁻¹ β γ := by
  have hMJ : M * Ji = 1 := mul_eq_one_comm.mp hJ
  have hN : g'⁻¹ = M * g⁻¹ * Mᴴ := by
    refine inv_eq_left_inv ?_
    calc M * g⁻¹ * Mᴴ * g' = M * g⁻¹ * Mᴴ * g' * (M * Ji) := by rw [hMJ, Matrix.mul_one]
      _ = M * (g⁻¹ * (Mᴴ * g' * M)) * Ji := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hgg, nonsing_inv_mul g hg, Matrix.mul_one, hMJ]
  set N := g⁻¹
  have h1 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Ji * (M * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Mᴴ * (Jiᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hJ, conjTranspose_one, Matrix.one_mul]
  have h3 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Ji.map conj * (M.map conj * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul (f := starRingEnd ℂ), hJ]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ).map conj = 1 from by
      ext i j; simp [one_apply], Matrix.one_mul]
  have h4 : Mᵀ * Jiᵀ = 1 := by rw [← transpose_mul, hJ, transpose_one]
  simp only [zeroTwoPair]
  congr 1
  rw [hN, conjTranspose_mul, conjTranspose_mul, conjTranspose_map_conj, conjTranspose_conjTranspose,
    transpose_mul, transpose_mul, transpose_conjTranspose']
  simp only [Matrix.mul_assoc, h1, h2, h3]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, h4, Matrix.mul_one]

/-! ### The representatives on `X` -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- `√(a+b) e^{-φ/2}`. -/
def cwX (x : X) : ℝ := Real.sqrt (T.a x + T.b x) * T.hw x

/-- The `T*`-representative of a coefficient function `g` in `(c, e)`: `√(a+b) e^{-φ/2} g/ucX`. -/
def ArX (c : ComplexChart n X) (e : AtlasFrame T.L) (g : ComplexModel n → ℂ) (x : X) : ℂ :=
  (T.cfd c e).indicator (fun x => ((T.cwX x : ℝ) : ℂ) * ((T.ucX e x)⁻¹ * g (c.val x))) x

/-- The `S`-representative of a `(0,2)`-coefficient field `β` in `(c, e)`, transported to the
reference chart and written in its `σ`-orthonormal coordinates. -/
def SrX (c : ComplexChart n X) (e : AtlasFrame T.L) (β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ)
    (x : X) : EuclideanSpace ℂ (Fin n × Fin n) :=
  (T.cfd c e).indicator (fun x => (((T.hw x : ℝ) : ℂ) * (T.ucX e x)⁻¹) •
    flat2 (T.BiR x * ((JiR c x)ᴴ * β (c.val x) * (JiR c x).map conj) * (T.BiR x)ᵀ)) x

/-- The unit-frame value `∑_j ϑ h_j / ucX e_j` of `ϑ τ`. -/
def TepsX (F : T.XFam) (x : X) : ℂ :=
  ∑ j ∈ F.s, (T.cfd (F.c j) (F.e j)).indicator (fun x => (T.ucX (F.e j) x)⁻¹ *
    chartTheta (T.pX (F.c j) (F.e j)) (F.h j) ((F.c j).val x)) x

/-- The `T*`-representative of a family. -/
def AFX (F : T.XFam) (x : X) : ℂ :=
  ∑ i ∈ F.s, T.ArX (F.c i) (F.e i) (chartTheta (T.pX (F.c i) (F.e i)) (F.h i)) x

/-- The `S`-representative of a family. -/
def SFX (F : T.XFam) (x : X) : EuclideanSpace ℂ (Fin n × Fin n) :=
  ∑ i ∈ F.s, T.SrX (F.c i) (F.e i)
    (fun z => kahlerAntisym (gX T.omega T.r (F.c i) z) (Amat (F.h i) z)) x

variable {T}

theorem continuousOn_cwX : ContinuousOn T.cwX T.U := by
  have ha := mainContinuousOn_of_chartSmoothOn T.isOpen_U T.a_smooth
  have hb := mainContinuousOn_of_chartSmoothOn T.isOpen_U T.b_smooth
  exact ((ha.add hb).sqrt).mul continuousOn_hw

theorem cwX_nonneg (x : X) : 0 ≤ T.cwX x :=
  mul_nonneg (Real.sqrt_nonneg _) (hw_pos x).le

/-- `ϑ τ` in the unit frame does not depend on the chart-frame. -/
theorem theta_tot_eq (F : T.XFam) {c : ComplexChart n X} {e : AtlasFrame T.L} {x : X}
    (hx : x ∈ T.cfd c e) :
    (T.ucX e x)⁻¹ * chartTheta (T.pX c e) (F.tot c e) (c.val x) = T.TepsX F x := by
  have hz := chart_mem_pieceDomain hx
  have hsymm : c.val.symm (c.val x) = x := c.val.left_inv hx.1.1
  rw [show F.tot c e = fun y => ∑ i ∈ F.s, transpX T.L (F.c i) (F.e i) c e (F.h i) y from rfl,
    chartTheta_finset_sum F.s fun i _ =>
      (XFam.contDiffAt_of_pd (F.contDiffOn_transp i c e) hz).differentiableAt (by simp),
    Finset.mul_sum, TepsX]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hxi : x ∈ (F.c i).val.source ∩ (F.e i).val.baseSet
  · have hz' : c.val.symm (c.val x) ∈ (F.c i).val.source ∩ (F.e i).val.baseSet := by
      rw [hsymm]; exact hxi
    have hθ := T.chartTheta_transport (T.isOpen_pieceDomain c e)
      (T.isOpen_pieceDomain (F.c i) (F.e i)) subset_rfl subset_rfl (F.contDiffOn_transp i c e)
      (F.spec i).1.contDiffOn hz hz' (chg_mem_pieceDomain hz hz')
      (isTransp_piece (F.spec i).2.1 (F.tsupport_subset i) hz.1 hz')
    rw [chg_chart hx.1.1, hsymm] at hθ
    rw [indicator_of_mem (show x ∈ T.cfd (F.c i) (F.e i) from ⟨hxi, hx.2⟩)]
    rw [hθ, ucX_trans ⟨hx.1.2, hxi.2⟩]
    have h1 := frameTrans_ne_zero e (F.e i) ⟨hx.1.2, hxi.2⟩
    have h2 := ucX_ne_zero (T := T) hx.1.2
    field_simp
  · have hns : c.val.symm (c.val x) ∉ pieceSupport (F.c i) (F.h i) := fun h' =>
      hxi (by rw [← hsymm]; exact mem_of_mem_pieceSupport (F.tsupport_subset i) h')
    have hzero := transpX_eventuallyEq_zero (L := T.L) (e₀ := F.e i) (e := e) (F.spec i).2.1
      ((F.tsupport_subset i).trans fun _ hz => hz.1) hz.1.1 hns
    rw [chartTheta_eq_zero_of_eventuallyEq hzero, mul_zero,
      indicator_of_notMem fun h => hxi h.1]

theorem AFX_eq (F : T.XFam) (x : X) :
    T.AFX F x = ((T.U.indicator T.cwX x : ℝ) : ℂ) * T.TepsX F x := by
  rw [AFX, TepsX, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : x ∈ T.cfd (F.c i) (F.e i)
  · rw [ArX, indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx.2]
  · rw [ArX, indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- **The `T*`-energy as an `L²` norm on `X`.** -/
theorem energy_eqX (F : T.XFam) : F.energy = ∫ x, ‖T.AFX F x‖ ^ 2 ∂T.μ := by
  unfold XFam.energy
  congr 1
  funext x
  by_cases hx : x ∈ T.U
  · set c := cR n x
    set e := atlasFrameAt T.L x
    have he : x ∈ e.val.baseSet := mem_atlasFrameAt_baseSet T.L x
    have hxc : x ∈ T.cfd c e := ⟨⟨mem_cR_source x, he⟩, hx⟩
    rw [F.Φ_eq_diag isGaugeFormX_tstar hx hxc.1, FAX_diag_re, AFX_eq,
      indicator_of_mem hx, ← theta_tot_eq F hxc]
    have hw := wX_chart_eq (T := T) hxc.1
    have hu := ucX_ne_zero (T := T) he
    have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
    have ha : T.aC c (c.val x) = T.a x := by simp only [aC, c.val.left_inv hxc.1.1]
    have hb : T.bC c (c.val x) = T.b x := by simp only [bC, c.val.left_inv hxc.1.1]
    rw [ha, hb, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (cwX_nonneg x),
      cwX, mul_pow, mul_pow, Real.sq_sqrt (T.ab_pos hx).le]
    have hwX : T.wX c e (c.val x) = T.hw x ^ 2 / ‖T.ucX e x‖ ^ 2 := by
      rw [eq_div_iff (by positivity)]; exact hw
    rw [hwX]
    field_simp
  · rw [F.Φ_eq_zero isGaugeFormX_tstar hx, AFX_eq, indicator_of_notMem hx]
    simp

/-- The norm of a transported `(0,2)`-form in the reference chart is its norm in its own chart. -/
theorem norm_flat2_ref {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) (hxU : x ∈ T.U)
    (β : Matrix (Fin n) (Fin n) ℂ) :
    ‖flat2 (T.BiR x * ((JiR c x)ᴴ * β * (JiR c x).map conj) * (T.BiR x)ᵀ)‖ =
      ‖flat2 (BiX T.omega T.r c (c.val x) * β * (BiX T.omega T.r c (c.val x))ᵀ)‖ := by
  have hz : c.val x ∈ c.val.target := c.val.map_source hx
  have hzU : c.val.symm (c.val x) ∈ T.U := by rw [c.val.left_inv hx]; exact hxU
  have hg : IsUnit (gX T.omega T.r c (c.val x)).det :=
    isUnit_iff_ne_zero.mpr (posDef_gX T.isOpen_U T.kahler hz hzU).det_pos.ne'
  have h1 := zeroTwoNormSq_eq_of_inv (BiR_conjTranspose (T := T) x)
    (gX_inv_eq T.isOpen_U T.kahler (cR_mem x) (cR_symm_mem hxU))
    ((JiR c x)ᴴ * β * (JiR c x).map conj)
  have h2 := zeroTwoNormSq_eq_of_inv (BiX_conjTranspose c (c.val x))
    (gX_inv_eq T.isOpen_U T.kahler hz hzU) β
  have h3 := zeroTwoPair_transport' (JiR_mul_JR hx) hg (gX_ref hx hxU) β β
  have e1 : zeroTwoNormSq (T.gR x)⁻¹ ((JiR c x)ᴴ * β * (JiR c x).map conj) = (1 / 2 : ℝ) *
      ‖flat2 (T.BiR x * ((JiR c x)ᴴ * β * (JiR c x).map conj) * (T.BiR x)ᵀ)‖ ^ 2 := h1
  have e3 : zeroTwoNormSq (T.gR x)⁻¹ ((JiR c x)ᴴ * β * (JiR c x).map conj) =
      zeroTwoNormSq (gX T.omega T.r c (c.val x))⁻¹ β := by
    rw [← zeroTwoPair_re, ← zeroTwoPair_re, h3]
  have h4 : ‖flat2 (T.BiR x * ((JiR c x)ᴴ * β * (JiR c x).map conj) * (T.BiR x)ᵀ)‖ ^ 2 =
      ‖flat2 (BiX T.omega T.r c (c.val x) * β * (BiX T.omega T.r c (c.val x))ᵀ)‖ ^ 2 := by
    linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h4

theorem norm_SrX_pt {c : ComplexChart n X} {e : AtlasFrame T.L}
    (β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) {x : X} (hx : x ∈ T.cfd c e) :
    ‖T.SrX c e β x‖ = Real.sqrt (T.wX c e (c.val x)) *
      ‖flat2 (BiX T.omega T.r c (c.val x) * β (c.val x) * (BiX T.omega T.r c (c.val x))ᵀ)‖ := by
  have hu := ucX_ne_zero (T := T) hx.1.2
  have hw := wX_chart_eq (T := T) hx.1
  have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
  have hs : Real.sqrt (T.wX c e (c.val x)) = T.hw x / ‖T.ucX e x‖ := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (hw_pos x) hpos)]
    field_simp
    nlinarith [hw]
  rw [SrX, indicator_of_mem hx, norm_smul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (hw_pos x).le, norm_flat2_ref hx.1.1 hx.2, hs]
  ring

/-- **The transport of the `S`-form of a piece to the reference chart.** -/
theorem kahlerAntisym_transp_ref (F : T.XFam) (i : F.ι) {e : AtlasFrame T.L} {x : X}
    (hx : x ∈ T.U) (he : x ∈ e.val.baseSet)
    (hxi : x ∈ (F.c i).val.source ∩ (F.e i).val.baseSet) :
    kahlerAntisym (T.gR x) (Amat (transpX T.L (F.c i) (F.e i) (cR n x) e (F.h i)) ((cR n x).val x)) =
      frameTrans T.L (F.e i) e x • ((JiR (F.c i) x)ᴴ *
        kahlerAntisym (gX T.omega T.r (F.c i) ((F.c i).val x)) (Amat (F.h i) ((F.c i).val x)) *
          (JiR (F.c i) x).map conj) := by
  set ci := F.c i
  set c := cR n x
  have hxci : x ∈ T.cfd ci (F.e i) := ⟨hxi, hx⟩
  have hz := chart_mem_pieceDomain hxci
  have hz' : ci.val.symm (ci.val x) ∈ c.val.source ∩ e.val.baseSet := by
    rw [ci.val.left_inv hxi.1]; exact ⟨mem_cR_source x, he⟩
  obtain ⟨hzo, hzD, -⟩ := gauge_setup hz hz'
  have hxc : x ∈ T.cfd c e := ⟨⟨mem_cR_source x, he⟩, hx⟩
  set S := T.ovlD ci c (F.e i) e
  have hSo : IsOpen S := T.isOpen_ovlD ci c (F.e i) e
  have hψ : DifferentiableOn ℂ (chg ci c) S :=
    (differentiableOn_chg ci c).mono fun y hy => hy.1.2
  have ht : DifferentiableOn ℂ (fun y => frameTrans T.L (F.e i) e (ci.val.symm y)) S :=
    (differentiableOn_frameTrans ci (F.e i) e).mono fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.2⟩
  have hru : IsTransp T.L ci (F.e i) c e (F.h i) (transpX T.L ci (F.e i) c e (F.h i)) (ci.val x) := by
    have := isTransp_transpX (L := T.L) (c₀ := ci) (e₀ := F.e i) (c := ci) (e := F.e i) (c' := c)
      (e' := e) (F.spec i).2.1 (F.tsupport_subset i) hz.1 hz'
    rwa [transpX_self (F.tsupport_subset i)] at this
  have hd : DifferentiableAt ℝ (F.h i) (ci.val x) := (F.spec i).1.differentiable (by simp) _
  have hd' : DifferentiableAt ℝ (transpX T.L ci (F.e i) c e (F.h i)) (chg ci c (ci.val x)) := by
    rw [chg_chart hxi.1]
    exact (XFam.contDiffAt_of_pd (F.contDiffOn_transp i c e)
      (chart_mem_pieceDomain hxc)).differentiableAt (by simp)
  have hA := Amat_transport hSo hψ ht hzD hd hd' hru
  rw [chg_chart hxi.1, ci.val.left_inv hxi.1] at hA
  exact kahlerAntisym_transport' (JiR_mul_JR hxi.1) (gX_ref hxi.1 hx) hA

/-- **The `S`-energy as an `L²` norm on `X`.** -/
theorem senergy_eqX (F : T.XFam) : F.senergy = ∫ x, (1 / 2 : ℝ) * ‖T.SFX F x‖ ^ 2 ∂T.μ := by
  unfold XFam.senergy
  congr 1
  funext x
  by_cases hx : x ∈ T.U
  · set c := cR n x
    set e := atlasFrameAt T.L x
    have he : x ∈ e.val.baseSet := mem_atlasFrameAt_baseSet T.L x
    have hxc : x ∈ T.cfd c e := ⟨⟨mem_cR_source x, he⟩, hx⟩
    have hz := chart_mem_pieceDomain hxc
    have hu := ucX_ne_zero (T := T) he
    -- the `S`-form of the total field in the reference chart
    have hK : kahlerAntisym (T.gR x) (Amat (F.tot c e) (c.val x)) = ∑ i ∈ F.s,
        (T.cfd (F.c i) (F.e i)).indicator (fun x => frameTrans T.L (F.e i) e x •
          ((JiR (F.c i) x)ᴴ * kahlerAntisym (gX T.omega T.r (F.c i) ((F.c i).val x))
            (Amat (F.h i) ((F.c i).val x)) * (JiR (F.c i) x).map conj)) x := by
      rw [show F.tot c e = fun y => ∑ i ∈ F.s, transpX T.L (F.c i) (F.e i) c e (F.h i) y from rfl,
        Amat_sum F.s fun i _ =>
          (XFam.contDiffAt_of_pd (F.contDiffOn_transp i c e) hz).differentiableAt (by simp),
        kahlerAntisym_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hxi : x ∈ (F.c i).val.source ∩ (F.e i).val.baseSet
      · rw [indicator_of_mem (show x ∈ T.cfd (F.c i) (F.e i) from ⟨hxi, hx⟩)]
        exact kahlerAntisym_transp_ref F i hx he hxi
      · have hsymm : c.val.symm (c.val x) = x := c.val.left_inv hxc.1.1
        have hns : c.val.symm (c.val x) ∉ pieceSupport (F.c i) (F.h i) := fun h' =>
          hxi (by rw [← hsymm]; exact mem_of_mem_pieceSupport (F.tsupport_subset i) h')
        have hzero := transpX_eventuallyEq_zero (L := T.L) (e₀ := F.e i) (e := e) (F.spec i).2.1
          ((F.tsupport_subset i).trans fun _ hz => hz.1) hz.1.1 hns
        rw [Amat_eq_zero hzero, kahlerAntisym_zero', indicator_of_notMem fun h => hxi h.1]
    have hSF : T.SFX F x = (((T.hw x : ℝ) : ℂ) * (T.ucX e x)⁻¹) •
        flat2 (T.BiR x * kahlerAntisym (T.gR x) (Amat (F.tot c e) (c.val x)) * (T.BiR x)ᵀ) := by
      rw [hK, Matrix.mul_sum, Matrix.sum_mul, flat2_sum, Finset.smul_sum, SFX]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hxi : x ∈ T.cfd (F.c i) (F.e i)
      · rw [SrX, indicator_of_mem hxi, indicator_of_mem hxi, Matrix.mul_smul, Matrix.smul_mul,
          flat2_smul, smul_smul, ucX_trans ⟨hxi.1.2, he⟩]
        congr 1
        have h1 := frameTrans_ne_zero (F.e i) e ⟨hxi.1.2, he⟩
        have h2 := ucX_ne_zero (T := T) hxi.1.2
        field_simp
      · rw [SrX, indicator_of_notMem hxi, indicator_of_notMem hxi, Matrix.mul_zero,
          Matrix.zero_mul, flat2_zero, smul_zero]
    rw [F.Φ_eq_diag isGaugeFormX_S hx hxc.1, FSX, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, zeroTwoPair_re,
      zeroTwoNormSq_eq_of_inv (BiR_conjTranspose (T := T) x)
        (gX_inv_eq T.isOpen_U T.kahler (cR_mem x) (cR_symm_mem hx)), hSF, norm_smul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (hw_pos x).le, norm_inv]
    have hw := wX_chart_eq (T := T) hxc.1
    have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
    have hwX : T.wX c e (c.val x) = T.hw x ^ 2 / ‖T.ucX e x‖ ^ 2 := by
      rw [eq_div_iff (by positivity)]; exact hw
    change (1 / 2 : ℝ) * ‖flat2 (T.BiR x * kahlerAntisym (T.gR x) (Amat (F.tot c e) (c.val x)) *
      (T.BiR x)ᵀ)‖ ^ 2 * T.wX c e (c.val x) = _
    rw [hwX]
    field_simp
  · rw [F.Φ_eq_zero isGaugeFormX_S hx]
    have h0 : T.SFX F x = 0 := Finset.sum_eq_zero fun i _ => by
      rw [SrX, indicator_of_notMem fun h => hx h.2]
    simp [h0]

end TwistedDatum

end SGPT.Trace.TwistedL2
