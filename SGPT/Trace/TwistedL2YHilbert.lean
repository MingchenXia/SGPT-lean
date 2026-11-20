import SGPT.Trace.TwistedL2YRef

/-!
# The Hilbert space `H₂` on a manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:hilbert`).  For a twisted datum
`T` on a complex manifold `X`, `H₂ = L²(X, μ; ℂⁿ)` (`H2X`).  At `x ∈ U` the fibre of `L ⊗ T^{1,0}X`
is identified with `ℂⁿ` through the reference chart `c* = cR x`, its `σ`-orthonormal coordinates
`B* = √(g_{c*})` and the measurable unit frame `ε` of `L` (coefficient `ucX e` in a frame `e`):

* `repX c e h x = e^{-φ/2} (ucX e x)⁻¹ B* Jm h(c x)` is the representative of the local piece
  `h ⊗ (c, e)` (`Jm = D(c* ∘ c⁻¹)`);
* `WepsX v = e^{φ/2} B*⁻¹ v` is the unit-frame coefficient field of `v ∈ H₂` in the reference chart,
  and `WeX c e v` its coefficient field in the chart-frame `(c, e)`, a function on the chart.

Main results: `WeX_repX` (the coefficient field of a piece in another chart-frame is its
transport), `inner_repX_pt` (`⟪rep(h), v⟫ = |e|² e^{-φ} ⟨h, g_c W_{ce}(v)⟩`, the `σ`-pairing),
`integral_inner_repX` (its integral is a chart integral), the `L²` bounds `memLp_repX`,
`isLocL2_WeX`, and the data vector `yG` (`memLp_yG`, `integral_inner_repX_yG`).
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

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-! ### Measurability helpers -/

theorem measurable_ref_mv {S : Set X} (hS : IsOpen S)
    {M : ComplexChart n X → X → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ c i j, ContinuousOn (fun x => M c x i j) (S ∩ c.val.source))
    {y : X → ComplexModel n} (hy : Measurable y) :
    Measurable fun x => S.indicator (fun x => mv (M (cR n x) x) (y x)) x := by
  have hE : ∀ i j, Measurable fun x => S.indicator (fun x => M (cR n x) x i j) x := fun i j =>
    measurable_ref_indicator hS fun c => hM c i j
  have h := measurable_mv' (M := fun x => Matrix.of fun i j =>
    S.indicator (fun x => M (cR n x) x i j) x) (fun i j => by simpa using hE i j) hy
  convert h using 1
  funext x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    congr 1
    ext i j
    simp [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    ext i
    simp [mv_apply, indicator_of_notMem hx]

theorem measurable_indicator_comp_chart (c : ComplexChart n X) {E : Type*} [MeasurableSpace E]
    [Zero E] {h : ComplexModel n → E} (hh : Measurable h) :
    Measurable (c.val.source.indicator fun x => h (c.val x)) := by
  classical
  have he : Measurable (c.val.source.piecewise c.val (fun _ => (0 : ComplexModel n))) :=
    c.val.continuousOn.measurable_piecewise continuousOn_const c.val.open_source.measurableSet
  have h := (hh.comp he).indicator c.val.open_source.measurableSet
  convert h using 1
  funext x
  by_cases hx : x ∈ c.val.source <;> simp [hx, Set.piecewise]

theorem measurable_indicator_comp_symm' (c : ComplexChart n X) {E : Type*} [MeasurableSpace E]
    [Zero E] {f : X → E} (hf : Measurable f) {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKt : K ⊆ c.val.target) : Measurable (K.indicator fun z => f (c.val.symm z)) := by
  classical
  have he : Measurable (c.val.target.piecewise c.val.symm fun _ => c.val.symm 0) :=
    c.val.continuousOn_symm.measurable_piecewise continuousOn_const
      c.val.open_target.measurableSet
  have h := (hf.comp he).indicator hK
  convert h using 1
  funext z
  by_cases hz : z ∈ K
  · simp [indicator_of_mem hz, Set.piecewise, hKt hz]
  · simp [indicator_of_notMem hz]

/-- `D(c* ∘ c⁻¹)(c x)`. -/
def JR (c : ComplexChart n X) (x : X) : Matrix (Fin n) (Fin n) ℂ := Jm c (cR n x) (c.val x)

/-- `D(c ∘ c*⁻¹)(c* x)`. -/
def JiR (c : ComplexChart n X) (x : X) : Matrix (Fin n) (Fin n) ℂ :=
  Jm (cR n x) c ((cR n x).val x)

theorem mv_smul_mat (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) :
    mv (c • M) x = c • mv M x := by
  ext i; simp [mv_apply, Finset.mul_sum, mul_assoc]

theorem continuousOn_entry' {α : Type*} [TopologicalSpace α] {S : Set α}
    {M : α → Matrix (Fin n) (Fin n) ℂ} (hM : ContinuousOn M S) (i j : Fin n) :
    ContinuousOn (fun z => M z i j) S :=
  continuousOn_pi.mp (continuousOn_pi.mp hM i) j

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-! ### Weights, unit coefficients and reference coordinates -/

/-- `e^{-φ/2}`. -/
def hw (x : X) : ℝ := Real.exp (-T.φ x / 2)

/-- The unit-frame coefficient in the frame `e` (zero off the base set). -/
def ucX (e : AtlasFrame T.L) (x : X) : ℂ := e.val.baseSet.indicator (unitCoeff e) x

/-- The chart-frame domain `c.source ∩ e.baseSet ∩ U` in `X`. -/
def cfd (c : ComplexChart n X) (e : AtlasFrame T.L) : Set X :=
  c.val.source ∩ e.val.baseSet ∩ T.U

/-- `√(g_{c*})` at `x`, in the reference chart `c* = cR x`. -/
def BR (x : X) : Matrix (Fin n) (Fin n) ℂ := BX T.omega T.r (cR n x) ((cR n x).val x)

/-- `√(g_{c*})⁻¹` at `x`. -/
def BiR (x : X) : Matrix (Fin n) (Fin n) ℂ := BiX T.omega T.r (cR n x) ((cR n x).val x)

/-- `g_{c*}` at `x`. -/
def gR (x : X) : Matrix (Fin n) (Fin n) ℂ := gX T.omega T.r (cR n x) ((cR n x).val x)

variable {T}

theorem hw_pos (x : X) : 0 < T.hw x := Real.exp_pos _

theorem hw_sq (x : X) : T.hw x ^ 2 = Real.exp (-T.φ x) := by
  rw [hw, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem continuousOn_hw : ContinuousOn T.hw T.U :=
  Real.continuous_exp.comp_continuousOn
    ((mainContinuousOn_of_chartSmoothOn T.isOpen_U T.φ_smooth).neg.div_const 2)

theorem measurable_ucX (e : AtlasFrame T.L) : Measurable (T.ucX e) :=
  measurable_indicator_unitCoeff e

theorem ucX_of_mem {e : AtlasFrame T.L} {x : X} (hx : x ∈ e.val.baseSet) :
    T.ucX e x = unitCoeff e x := indicator_of_mem hx _

theorem norm_ucX_sq_mul {e : AtlasFrame T.L} {x : X} (hx : x ∈ e.val.baseSet) :
    ‖T.ucX e x‖ ^ 2 * frameNormSq T.L e x = 1 := by
  rw [ucX_of_mem hx]; exact norm_unitCoeff_mul e hx

theorem ucX_ne_zero {e : AtlasFrame T.L} {x : X} (hx : x ∈ e.val.baseSet) : T.ucX e x ≠ 0 := by
  rw [ucX_of_mem hx]; exact unitCoeff_ne_zero e hx

/-- `ucX e' = t_{e e'} ucX e`. -/
theorem ucX_trans {e e' : AtlasFrame T.L} {x : X} (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) :
    T.ucX e' x = frameTrans T.L e e' x * T.ucX e x := by
  rw [ucX_of_mem hx.1, ucX_of_mem hx.2]
  exact frameCoeff_eq_frameTrans_mul e e' (unitFrame T.L) hx

theorem isOpen_cfd (c : ComplexChart n X) (e : AtlasFrame T.L) : IsOpen (T.cfd c e) :=
  (c.val.open_source.inter e.val.open_baseSet).inter T.isOpen_U

theorem chart_mem_pieceDomain {c : ComplexChart n X} {e : AtlasFrame T.L} {x : X}
    (hx : x ∈ T.cfd c e) : c.val x ∈ T.pieceDomain c e := by
  refine ⟨⟨c.val.map_source hx.1.1, ?_⟩, ?_⟩
  · simp only [mem_preimage, c.val.left_inv hx.1.1]; exact hx.1.2
  · simp only [mem_preimage, c.val.left_inv hx.1.1]; exact hx.2

theorem symm_mem_cfd {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) : c.val.symm z ∈ T.cfd c e :=
  ⟨⟨c.val.map_target hz.1.1, hz.1.2⟩, hz.2⟩

/-- `|e|² e^{-φ} = e^{-φ} / |ucX e|²`. -/
theorem wX_chart_eq {c : ComplexChart n X} {e : AtlasFrame T.L} {x : X}
    (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    T.wX c e (c.val x) * ‖T.ucX e x‖ ^ 2 = T.hw x ^ 2 := by
  simp only [wX, c.val.left_inv hx.1, hw_sq]
  have h := norm_ucX_sq_mul (T := T) hx.2
  calc frameNormSq T.L e x * Real.exp (-T.φ x) * ‖T.ucX e x‖ ^ 2 =
      (‖T.ucX e x‖ ^ 2 * frameNormSq T.L e x) * Real.exp (-T.φ x) := by ring
    _ = _ := by rw [h, one_mul]

theorem chart_mem_ovl_cR {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) :
    c.val x ∈ ovl c (cR n x) := chart_mem_ovl hx (mem_cR_source x)

theorem JiR_mul_JR {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) :
    JiR c x * JR c x = 1 := by
  have h := Jm_inv_mul (chart_mem_ovl_cR hx)
  rwa [chg_chart hx] at h

theorem JR_mul_JiR {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) :
    JR c x * JiR c x = 1 := mul_eq_one_comm.mp (JiR_mul_JR hx)

/-- The chain rule through the reference chart: `D(c ∘ c*⁻¹) D(c* ∘ c'⁻¹) = D(c ∘ c'⁻¹)`. -/
theorem JiR_mul_JR' {c c' : ComplexChart n X} {x : X} (hx : x ∈ c.val.source)
    (hx' : x ∈ c'.val.source) : JiR c x * JR c' x = Jm c' c (c'.val x) := by
  have hz := chart_mem_ovl_cR hx'
  have h := fderiv_chg_comp (c := c') (c' := cR n x) (c'' := c) hz
    (by rw [c'.val.left_inv hx']; exact hx)
  have h1 := congrArg linMat h
  rw [linMat_comp, chg_chart hx'] at h1
  exact h1.symm

theorem gX_ref {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) (hxU : x ∈ T.U) :
    gX T.omega T.r c (c.val x) = (JR c x)ᴴ * T.gR x * JR c x := by
  have h := gX_chg' T.isOpen_U T.kahler (chart_mem_ovl_cR hx)
    (by rw [c.val.left_inv hx]; exact hxU)
  rwa [chg_chart hx] at h

theorem cR_mem (x : X) : (cR n x).val x ∈ (cR n x).val.target :=
  (cR n x).val.map_source (mem_cR_source x)

theorem cR_symm (x : X) : (cR n x).val.symm ((cR n x).val x) = x :=
  (cR n x).val.left_inv (mem_cR_source x)

theorem cR_symm_mem {x : X} (hx : x ∈ T.U) : (cR n x).val.symm ((cR n x).val x) ∈ T.U := by
  rw [cR_symm]; exact hx

theorem BR_mul_BR {x : X} (hx : x ∈ T.U) : T.BR x * T.BR x = T.gR x :=
  BX_mul_BX T.isOpen_U T.kahler (cR_mem x) (cR_symm_mem hx)

theorem BiR_mul_BR {x : X} (hx : x ∈ T.U) : T.BiR x * T.BR x = 1 :=
  BiX_mul_BX T.isOpen_U T.kahler (cR_mem x) (cR_symm_mem hx)

theorem BR_mul_BiR {x : X} (hx : x ∈ T.U) : T.BR x * T.BiR x = 1 :=
  BX_mul_BiX T.isOpen_U T.kahler (cR_mem x) (cR_symm_mem hx)

theorem BR_conjTranspose (x : X) : (T.BR x)ᴴ = T.BR x := BX_conjTranspose _ _

theorem BiR_conjTranspose (x : X) : (T.BiR x)ᴴ = T.BiR x := BiX_conjTranspose _ _

/-- `(B* J)ᴴ (B* J) = g_c`. -/
theorem BRJ_gram {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) (hxU : x ∈ T.U) :
    (T.BR x * JR c x)ᴴ * (T.BR x * JR c x) = gX T.omega T.r c (c.val x) := by
  rw [gX_ref hx hxU, ← BR_mul_BR hxU, conjTranspose_mul, BR_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem inner_mv_gram (B : Matrix (Fin n) (Fin n) ℂ) (a b : ComplexModel n) :
    ⟪mv B a, mv B b⟫_ℂ = ⟪a, mv (Bᴴ * B) b⟫_ℂ := by
  rw [inner_mv_left, mv_mul]

theorem norm_mv_BRJ {c : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) (hxU : x ∈ T.U)
    (a : ComplexModel n) :
    ‖mv (T.BR x * JR c x) a‖ = ‖mv (BX T.omega T.r c (c.val x)) a‖ := by
  have hz : c.val x ∈ c.val.target := c.val.map_source hx
  have hzU : c.val.symm (c.val x) ∈ T.U := by rw [c.val.left_inv hx]; exact hxU
  have h1 : ⟪mv (T.BR x * JR c x) a, mv (T.BR x * JR c x) a⟫_ℂ =
      ⟪mv (BX T.omega T.r c (c.val x)) a, mv (BX T.omega T.r c (c.val x)) a⟫_ℂ := by
    rw [inner_mv_gram, inner_mv_gram, BRJ_gram hx hxU, BX_conjTranspose,
      BX_mul_BX T.isOpen_U T.kahler hz hzU]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖mv (T.BR x * JR c x) a‖ ^ 2 = ‖mv (BX T.omega T.r c (c.val x)) a‖ ^ 2 := by
    exact_mod_cast h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-! ### The representatives -/

variable (T)

/-- The unit-frame coefficient field `e^{φ/2} B*⁻¹ v` of `v` in the reference chart. -/
def WepsX (v : X → ComplexModel n) (x : X) : ComplexModel n :=
  T.U.indicator (fun x => mv ((((T.hw x)⁻¹ : ℝ) : ℂ) • T.BiR x) (v x)) x

/-- The coefficient field of `v` in the chart-frame `(c, e)`, read on `X`. -/
def HX (c : ComplexChart n X) (e : AtlasFrame T.L) (v : X → ComplexModel n) (x : X) :
    ComplexModel n :=
  c.val.source.indicator (fun x => T.ucX e x • mv (JiR c x) (T.WepsX v x)) x

/-- **The coefficient field of `v ∈ H₂` in the chart-frame `(c, e)`**, a function on the chart. -/
def WeX (c : ComplexChart n X) (e : AtlasFrame T.L) (v : X → ComplexModel n) (z : ComplexModel n) :
    ComplexModel n :=
  (T.pieceDomain c e).indicator (fun z => T.HX c e v (c.val.symm z)) z

/-- **The representative of the local piece `h ⊗ (c, e)`**: `e^{-φ/2} ucX⁻¹ B* D(c* ∘ c⁻¹) h`. -/
def repX (c : ComplexChart n X) (e : AtlasFrame T.L) (h : ComplexModel n → ComplexModel n)
    (x : X) : ComplexModel n :=
  (T.cfd c e).indicator (fun x => (T.ucX e x)⁻¹ •
    mv (((T.hw x : ℝ) : ℂ) • (T.BR x * JR c x)) (h (c.val x))) x

variable {T}

theorem WepsX_of_mem {v : X → ComplexModel n} {x : X} (hx : x ∈ T.U) :
    T.WepsX v x = mv ((((T.hw x)⁻¹ : ℝ) : ℂ) • T.BiR x) (v x) := indicator_of_mem hx _

/-- `v = e^{-φ/2} B* WepsX v` on `U`. -/
theorem mv_BR_WepsX {v : X → ComplexModel n} {x : X} (hx : x ∈ T.U) :
    mv (((T.hw x : ℝ) : ℂ) • T.BR x) (T.WepsX v x) = v x := by
  rw [WepsX_of_mem hx, ← mv_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    BR_mul_BiR hx, ← Complex.ofReal_mul, mul_inv_cancel₀ (hw_pos x).ne', Complex.ofReal_one,
    one_smul, mv_one]

theorem WeX_chart {c : ComplexChart n X} {e : AtlasFrame T.L} (v : X → ComplexModel n) {x : X}
    (hx : x ∈ T.cfd c e) :
    T.WeX c e v (c.val x) = T.ucX e x • mv (JiR c x) (T.WepsX v x) := by
  rw [WeX, indicator_of_mem (chart_mem_pieceDomain hx), c.val.left_inv hx.1.1, HX,
    indicator_of_mem hx.1.1]

theorem WeX_eq_zero {c : ComplexChart n X} {e : AtlasFrame T.L} {v : X → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ T.pieceDomain c e) : T.WeX c e v z = 0 :=
  indicator_of_notMem hz _

/-- `WepsX v = ucX⁻¹ D(c* ∘ c⁻¹) W_{ce}(v)`. -/
theorem WepsX_eq_WeX {c : ComplexChart n X} {e : AtlasFrame T.L} (v : X → ComplexModel n) {x : X}
    (hx : x ∈ T.cfd c e) :
    T.WepsX v x = (T.ucX e x)⁻¹ • mv (JR c x) (T.WeX c e v (c.val x)) := by
  rw [WeX_chart v hx, mv_smul, ← mv_mul, JR_mul_JiR hx.1.1, mv_one, smul_smul,
    inv_mul_cancel₀ (ucX_ne_zero hx.1.2), one_smul]

theorem repX_of_mem {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∈ T.cfd c e) :
    T.repX c e h x = (T.ucX e x)⁻¹ • mv (((T.hw x : ℝ) : ℂ) • (T.BR x * JR c x)) (h (c.val x)) :=
  indicator_of_mem hx _

theorem repX_of_notMem {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∉ T.cfd c e) : T.repX c e h x = 0 :=
  indicator_of_notMem hx _

theorem repX_eq_zero {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {x : X} (h0 : h (c.val x) = 0) :
    T.repX c e h x = 0 := by
  by_cases hx' : x ∈ T.cfd c e
  · rw [repX_of_mem hx', h0, mv_zero, smul_zero]
  · exact repX_of_notMem hx'

theorem repX_sub (c : ComplexChart n X) (e : AtlasFrame T.L) (h h' : ComplexModel n → ComplexModel n)
    (x : X) : T.repX c e (fun z => h z - h' z) x = T.repX c e h x - T.repX c e h' x := by
  by_cases hx : x ∈ T.cfd c e
  · simp only [repX_of_mem hx, mv_sub, smul_sub]
  · simp [repX_of_notMem hx]

theorem WepsX_repX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∈ T.cfd c e) :
    T.WepsX (T.repX c e h) x = (T.ucX e x)⁻¹ • mv (JR c x) (h (c.val x)) := by
  rw [WepsX_of_mem hx.2, repX_of_mem hx, mv_smul, ← mv_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Matrix.mul_assoc, BiR_mul_BR hx.2, Matrix.one_mul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (hw_pos x).ne', Complex.ofReal_one, one_smul]

/-- **The coefficient field of a piece in another chart-frame is its transport.** -/
theorem WeX_repX {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∈ T.cfd c e) :
    T.WeX c e (T.repX c' e' h) (c.val x) = transpX T.L c' e' c e h (c.val x) := by
  classical
  rw [WeX_chart _ hx]
  by_cases hx' : x ∈ c'.val.source ∩ e'.val.baseSet
  · have hx'' : x ∈ T.cfd c' e' := ⟨hx', hx.2⟩
    have hzo : c.val x ∈ ovl c c' := chart_mem_ovl hx.1.1 hx'.1
    rw [WepsX_repX hx'', mv_smul, ← mv_mul, JiR_mul_JR' hx.1.1 hx'.1, smul_smul,
      transpX_of_mem hzo (by rw [c.val.left_inv hx.1.1]; exact hx'.2), c.val.left_inv hx.1.1,
      chg_chart hx.1.1, mv_Jm, ucX_trans ⟨hx'.2, hx.1.2⟩]
    congr 1
    field_simp [ucX_ne_zero (T := T) hx'.2]
  · have h0 : T.WepsX (T.repX c' e' h) x = 0 := by
      rw [WepsX_of_mem hx.2, repX_of_notMem fun h => hx' h.1, mv_zero]
    rw [h0, mv_zero, smul_zero, transpX, if_neg]
    rintro ⟨h1, h2⟩
    exact hx' ⟨by simpa [c.val.left_inv hx.1.1] using h1.2,
      by simpa [c.val.left_inv hx.1.1] using h2⟩

/-- **The pointwise pairing of a piece with a field** (`σ`-pairing with weight `|e|² e^{-φ}`). -/
theorem inner_repX_pt {c : ComplexChart n X} {e : AtlasFrame T.L}
    (v : X → ComplexModel n) {hc : ComplexModel n → ComplexModel n} {x : X}
    (hx : x ∈ T.cfd c e) :
    ⟪T.repX c e hc x, v x⟫_ℂ = ((T.wX c e (c.val x) : ℝ) : ℂ) *
      ⟪hc (c.val x), mv (gX T.omega T.r c (c.val x)) (T.WeX c e v (c.val x))⟫_ℂ := by
  have hu := ucX_ne_zero (T := T) hx.1.2
  have hv : v x = mv (((T.hw x : ℝ) : ℂ) • T.BR x)
      ((T.ucX e x)⁻¹ • mv (JR c x) (T.WeX c e v (c.val x))) := by
    rw [← WepsX_eq_WeX v hx, mv_BR_WepsX hx.2]
  rw [hv, repX_of_mem hx]
  simp only [mv_smul_mat, mv_smul, inner_smul_left, inner_smul_right]
  rw [← mv_mul, inner_mv_gram, BRJ_gram hx.1.1 hx.2]
  have hw := wX_chart_eq (T := T) hx.1
  have hnorm : ((‖T.ucX e x‖ ^ 2 : ℝ) : ℂ) = conj (T.ucX e x) * T.ucX e x := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwC : ((T.wX c e (c.val x) : ℝ) : ℂ) * (conj (T.ucX e x) * T.ucX e x) =
      ((T.hw x : ℝ) : ℂ) * ((T.hw x : ℝ) : ℂ) := by
    rw [← hnorm, ← Complex.ofReal_mul, hw, ← Complex.ofReal_mul, sq]
  have hc0 : conj (T.ucX e x) ≠ 0 := by simpa using hu
  simp only [Complex.conj_ofReal, map_inv₀]
  have hW : ((T.wX c e (c.val x) : ℝ) : ℂ) = ((T.hw x : ℝ) : ℂ) * ((T.hw x : ℝ) : ℂ) /
      (conj (T.ucX e x) * T.ucX e x) := by
    rw [eq_div_iff (mul_ne_zero hc0 hu)]; exact hwC
  rw [hW]
  field_simp

theorem norm_repX_pt {c : ComplexChart n X} {e : AtlasFrame T.L}
    (hc : ComplexModel n → ComplexModel n) {x : X} (hx : x ∈ T.cfd c e) :
    ‖T.repX c e hc x‖ = Real.sqrt (T.wX c e (c.val x)) *
      ‖mv (BX T.omega T.r c (c.val x)) (hc (c.val x))‖ := by
  have hu := ucX_ne_zero (T := T) hx.1.2
  have hw := wX_chart_eq (T := T) hx.1
  have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
  have hs : Real.sqrt (T.wX c e (c.val x)) = T.hw x / ‖T.ucX e x‖ := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (hw_pos x) hpos)]
    field_simp
    nlinarith [hw]
  rw [repX_of_mem hx, norm_smul, mv_smul_mat, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (hw_pos x).le, norm_mv_BRJ hx.1.1 hx.2, norm_inv, hs]
  ring

theorem norm_WeX_le {c : ComplexChart n X} {e : AtlasFrame T.L} (v : X → ComplexModel n) {x : X}
    (hx : x ∈ T.cfd c e) :
    ‖T.WeX c e v (c.val x)‖ ≤ mnorm (BiX T.omega T.r c (c.val x)) *
      (Real.sqrt (T.wX c e (c.val x)))⁻¹ * ‖v x‖ := by
  have hz : c.val x ∈ c.val.target := c.val.map_source hx.1.1
  have hzU : c.val.symm (c.val x) ∈ T.U := by rw [c.val.left_inv hx.1.1]; exact hx.2
  have hu := ucX_ne_zero (T := T) hx.1.2
  have hw := wX_chart_eq (T := T) hx.1
  have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
  have hs : Real.sqrt (T.wX c e (c.val x)) = T.hw x / ‖T.ucX e x‖ := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (hw_pos x) hpos)]
    field_simp
    nlinarith [hw]
  -- `‖B_c W‖ = ‖ucX‖ e^{φ/2} ‖v‖`
  have hB : ‖mv (BX T.omega T.r c (c.val x)) (T.WeX c e v (c.val x))‖ =
      ‖T.ucX e x‖ * (T.hw x)⁻¹ * ‖v x‖ := by
    rw [← norm_mv_BRJ hx.1.1 hx.2, WeX_chart v hx, mv_smul, ← mv_mul, Matrix.mul_assoc,
      JR_mul_JiR hx.1.1, Matrix.mul_one, norm_smul, WepsX_of_mem hx.2, ← mv_mul,
      Matrix.mul_smul, BR_mul_BiR hx.2, mv_smul_mat, mv_one, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (hw_pos x).le)]
    ring
  have h1 : T.WeX c e v (c.val x) = mv (BiX T.omega T.r c (c.val x))
      (mv (BX T.omega T.r c (c.val x)) (T.WeX c e v (c.val x))) :=
    (mv_BiX_BX T.isOpen_U T.kahler hz hzU _).symm
  rw [h1]
  refine (norm_mv_le _ _).trans (le_of_eq ?_)
  rw [hB, hs]
  field_simp

/-! ### Measurability -/

theorem measurable_WepsX {v : X → ComplexModel n} (hv : Measurable v) : Measurable (T.WepsX v) :=
  measurable_ref_mv (M := fun c x => (((T.hw x)⁻¹ : ℝ) : ℂ) • BiX T.omega T.r c (c.val x))
    T.isOpen_U (fun c i j => by
      have h1 : ContinuousOn (fun x => BiX T.omega T.r c (c.val x)) (T.U ∩ c.val.source) :=
        (continuousOn_BiX T.isOpen_U T.kahler c).comp (c.val.continuousOn.mono inter_subset_right)
          fun x hx => ⟨c.val.map_source hx.2, by rw [mem_preimage, c.val.left_inv hx.2]; exact hx.1⟩
      have h2 : ContinuousOn (fun x => (((T.hw x)⁻¹ : ℝ) : ℂ)) (T.U ∩ c.val.source) :=
        Complex.continuous_ofReal.comp_continuousOn
          ((continuousOn_hw.mono inter_subset_left).inv₀ fun x _ => (hw_pos x).ne')
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact h2.mul (continuousOn_entry' h1 i j)) hv

theorem measurable_HX (c : ComplexChart n X) (e : AtlasFrame T.L) {v : X → ComplexModel n}
    (hv : Measurable v) : Measurable (T.HX c e v) := by
  have h := measurable_ref_mv (M := fun c' x => Jm c' c (c'.val x)) c.val.open_source
    (fun c' i j => by
      have h1 : ContinuousOn (fun x => Jm c' c (c'.val x)) (c.val.source ∩ c'.val.source) :=
        (continuousOn_Jm c' c).comp (c'.val.continuousOn.mono inter_subset_right)
          fun x hx => chart_mem_ovl hx.2 hx.1
      exact continuousOn_entry' h1 i j) (measurable_WepsX (T := T) hv)
  have h2 := (measurable_ucX (T := T) e).smul h
  convert h2 using 1
  funext x
  by_cases hx : x ∈ c.val.source
  · simp [HX, indicator_of_mem hx, JiR]
  · simp [HX, indicator_of_notMem hx]

theorem measurable_WeX (c : ComplexChart n X) (e : AtlasFrame T.L) {v : X → ComplexModel n}
    (hv : Measurable v) : Measurable (T.WeX c e v) :=
  measurable_indicator_comp_symm' c (measurable_HX c e hv)
    (T.isOpen_pieceDomain c e).measurableSet (T.pieceDomain_subset_target c e)

theorem measurable_repX (c : ComplexChart n X) (e : AtlasFrame T.L)
    {h : ComplexModel n → ComplexModel n} (hh : Measurable h) : Measurable (T.repX c e h) := by
  have hS := T.isOpen_cfd c e
  have h1 := measurable_ref_mv (M := fun c' x => ((T.hw x : ℝ) : ℂ) •
      (BX T.omega T.r c' (c'.val x) * Jm c c' (c.val x))) hS
    (fun c' i j => by
      have hB : ContinuousOn (fun x => BX T.omega T.r c' (c'.val x)) (T.cfd c e ∩ c'.val.source) :=
        (continuousOn_BX T.isOpen_U T.kahler c').comp (c'.val.continuousOn.mono inter_subset_right)
          fun x hx => ⟨c'.val.map_source hx.2, by
            rw [mem_preimage, c'.val.left_inv hx.2]; exact hx.1.2⟩
      have hJ : ContinuousOn (fun x => Jm c c' (c.val x)) (T.cfd c e ∩ c'.val.source) :=
        (continuousOn_Jm c c').comp (c.val.continuousOn.mono fun x hx => hx.1.1.1)
          fun x hx => chart_mem_ovl hx.1.1.1 hx.2
      have hw' : ContinuousOn (fun x => ((T.hw x : ℝ) : ℂ)) (T.cfd c e ∩ c'.val.source) :=
        Complex.continuous_ofReal.comp_continuousOn (continuousOn_hw.mono fun x hx => hx.1.2)
      simp only [Matrix.smul_apply, smul_eq_mul, mul_apply]
      exact hw'.mul (continuousOn_finsetSum _ fun k _ =>
        (continuousOn_entry' hB i k).mul (continuousOn_entry' hJ k j)))
    (measurable_indicator_comp_chart c hh)
  have h2 := ((measurable_ucX (T := T) e).inv).smul h1
  convert h2 using 1
  funext x
  by_cases hx : x ∈ T.cfd c e
  · simp [repX_of_mem hx, indicator_of_mem hx, indicator_of_mem hx.1.1, BR, JR]
  · simp [repX_of_notMem hx, indicator_of_notMem hx]

/-! ### `L²` bounds -/

/-- `L²(X, μ; ℂⁿ)`. -/
abbrev H2X (T : TwistedDatum n X) := X →₂[T.μ] ComplexModel n

theorem measurable_coe (v : H2X T) : Measurable (v : X → ComplexModel n) :=
  (Lp.stronglyMeasurable v).measurable

theorem continuousOn_repX_coeff (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (fun z => Real.sqrt (T.wX c e z) * mnorm (BX T.omega T.r c z))
      (T.pieceDomain c e) :=
  ((continuousOn_wX c e).sqrt).mul (continuous_mnorm.comp_continuousOn
    ((continuousOn_BX T.isOpen_U T.kahler c).mono (T.pieceDomain_subset_chartSmooth c e)))

/-- A uniform `L²` bound for pieces supported in a compact subset of the chart-frame domain. -/
theorem exists_eLpNorm_repX_le (c : ComplexChart n X) (e : AtlasFrame T.L)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e) :
    ∃ C : ℝ, ∀ h : ComplexModel n → ComplexModel n, Measurable h → (∀ z ∉ K, h z = 0) →
      eLpNorm (T.repX c e h) 2 T.μ ≤ ENNReal.ofReal C * eLpNorm h 2 volume := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_repX_coeff c e).mono hKd)
  have hKt : K ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  obtain ⟨Cρ, -, hρ⟩ := exists_eLpNorm_le_chart c (T.isChartDensity_ρX c) hK hKt
  refine ⟨max C 0 * Cρ, fun h hh h0 => ?_⟩
  refine hρ (T.repX c e h) h (max C 0) (le_max_right _ _) (measurable_repX c e hh)
    (fun x hx => ?_) fun x hx => ?_
  · by_cases hxd : x ∈ T.cfd c e
    · rw [norm_repX_pt h hxd]
      have hb := (norm_mv_le (BX T.omega T.r c (c.val x)) (h (c.val x)))
      have hCx := (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC _ hx.2).trans (le_max_left C 0))
      calc Real.sqrt (T.wX c e (c.val x)) * ‖mv (BX T.omega T.r c (c.val x)) (h (c.val x))‖
          ≤ Real.sqrt (T.wX c e (c.val x)) * (mnorm (BX T.omega T.r c (c.val x)) *
            ‖h (c.val x)‖) := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
        _ = (Real.sqrt (T.wX c e (c.val x)) * mnorm (BX T.omega T.r c (c.val x))) *
            ‖h (c.val x)‖ := by ring
        _ ≤ max C 0 * ‖h (c.val x)‖ := mul_le_mul_of_nonneg_right hCx (norm_nonneg _)
    · rw [repX_of_notMem hxd, norm_zero]; positivity
  · by_cases hxs : x ∈ c.val.source
    · exact repX_eq_zero (h0 _ fun h' => hx ⟨hxs, h'⟩)
    · exact repX_of_notMem fun h' => hxs h'.1.1

theorem memLp_repX {c : ComplexChart n X} {e : AtlasFrame T.L} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e) {h : ComplexModel n → ComplexModel n}
    (hh : MemLp h 2 volume) (hhm : Measurable h) (h0 : ∀ z ∉ K, h z = 0) :
    MemLp (T.repX c e h) 2 T.μ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_repX_le (T := T) c e hK hKd
  exact ⟨(measurable_repX c e hhm).aestronglyMeasurable,
    (hC h hhm h0).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2)⟩

/-- Chart norms are controlled by `X`-norms on compact subsets of a chart. -/
theorem exists_eLpNorm_chart_le (c : ComplexChart n X) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ c.val.target) : ∃ C : ℝ, ∀ {E : Type} [NormedAddCommGroup E]
      [MeasurableSpace E] [BorelSpace E] (F : X → E), Measurable F →
      eLpNorm (K.indicator fun z => F (c.val.symm z)) 2 volume ≤
        ENNReal.ofReal C * eLpNorm F 2 T.μ := by
  have hρ := T.isChartDensity_ρX c
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, fun F _ => ?_⟩
    subst hKe
    simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (hρ.1.continuousOn.mono hKt)
  set m := T.ρX c z₀
  have hm : 0 < m := hρ.2.1 z₀ (hKt hz₀)
  refine ⟨Real.sqrt m⁻¹, fun {E} _ _ _ F hF => ?_⟩
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2']
  simp only [ENNReal.toReal_ofNat]
  have hm2 : Measurable fun x => ‖F x‖ₑ ^ (2 : ℝ) := hF.enorm.pow_const _
  have hset := setLIntegral_source_inter_preimage c hρ.1.continuousOn hρ.2.2 hK hKt hm2
  have hle : ∫⁻ z, ‖K.indicator (fun z => F (c.val.symm z)) z‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂T.μ := by
    calc ∫⁻ z, ‖K.indicator (fun z => F (c.val.symm z)) z‖ₑ ^ (2 : ℝ)
        = ∫⁻ z in K, ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ) := by
          rw [← lintegral_indicator hK.measurableSet]
          refine lintegral_congr fun z => ?_
          by_cases hz : z ∈ K
          · simp [indicator_of_mem hz]
          · simp [indicator_of_notMem hz]
      _ ≤ ∫⁻ z in K, ENNReal.ofReal m⁻¹ * (ENNReal.ofReal (T.ρX c z) *
          ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ)) := by
          refine setLIntegral_mono' hK.measurableSet fun z hz => ?_
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
          have h1 : 1 ≤ m⁻¹ * T.ρX c z := by
            rw [inv_mul_eq_div, one_le_div hm]; exact hmin hz
          have h1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (m⁻¹ * T.ρX c z) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
          calc ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ) = 1 * ‖F (c.val.symm z)‖ₑ ^ (2 : ℝ) := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right h1' (by positivity)
      _ = ENNReal.ofReal m⁻¹ * ∫⁻ x in c.val.source ∩ c.val ⁻¹' K, ‖F x‖ₑ ^ (2 : ℝ) ∂T.μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hset]
      _ ≤ _ := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (by positivity)
  calc (∫⁻ z, ‖K.indicator (fun z => F (c.val.symm z)) z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal m⁻¹ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂T.μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt m⁻¹) * (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂T.μ) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hm.le) (by norm_num)]

/-- **The coefficient field of `v ∈ H₂` is locally `L²` on the chart-frame domain.** -/
theorem isLocL2_WeX (c : ComplexChart n X) (e : AtlasFrame T.L) (v : H2X T) :
    IsLocL2 (T.pieceDomain c e) (T.WeX c e v) := by
  intro K hK hKd
  have hKt : K ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun z =>
    mnorm (BiX T.omega T.r c z) * (Real.sqrt (T.wX c e z))⁻¹)
    ((continuous_mnorm.comp_continuousOn ((continuousOn_BiX T.isOpen_U T.kahler c).mono
      ((T.pieceDomain_subset_chartSmooth c e)))).mul ((continuousOn_wX c e).sqrt.inv₀
        fun z hz => (Real.sqrt_pos.mpr (wX_pos hz.1)).ne') |>.mono hKd)
  obtain ⟨C', hC'⟩ := exists_eLpNorm_chart_le (T := T) c hK hKt
  have hv : MemLp (K.indicator fun z => v (c.val.symm z)) 2 volume := by
    refine ⟨(measurable_indicator_comp_symm' c (measurable_coe v) hK.measurableSet
      hKt).aestronglyMeasurable, ?_⟩
    exact (hC' (v : X → ComplexModel n) (measurable_coe v)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top v))
  refine hv.of_le_mul (c := max C 0)
    ((measurable_WeX c e (measurable_coe v)).indicator hK.measurableSet).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    have hzd := hKd hz
    have hx := symm_mem_cfd hzd
    have hb := norm_WeX_le (v : X → ComplexModel n) hx
    rw [c.val.right_inv hzd.1.1] at hb
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _))
  · simp [indicator_of_notMem hz]

/-! ### Pairings as chart integrals -/

/-- **The pairing of a piece with a field is a chart integral.** -/
theorem integral_inner_repX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e)
    {h : ComplexModel n → ComplexModel n} (hhm : Measurable h) (h0 : ∀ z ∉ K, h z = 0)
    {f : X → ComplexModel n} (hf : Measurable f) :
    ∫ x, ⟪T.repX c e h x, f x⟫_ℂ ∂T.μ = ∫ z, (T.pieceDomain c e).indicator (fun z =>
      cweight (T.pX c e) z * ⟪h z, mv (gX T.omega T.r c z) (T.WeX c e f z)⟫_ℂ) z := by
  have hKt : K ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  have hmeas : Measurable fun x => ⟪T.repX c e h x, f x⟫_ℂ :=
    (continuous_inner : Continuous fun p : ComplexModel n × ComplexModel n => ⟪p.1, p.2⟫_ℂ).measurable2
      (measurable_repX c e hhm) hf
  rw [integral_eq_chart c (T.isChartDensity_ρX c) hK hKt hmeas fun x hx => ?_]
  · have hR : ∫ z, (T.pieceDomain c e).indicator (fun z =>
        cweight (T.pX c e) z * ⟪h z, mv (gX T.omega T.r c z) (T.WeX c e f z)⟫_ℂ) z =
        ∫ z in K, (T.pieceDomain c e).indicator (fun z =>
        cweight (T.pX c e) z * ⟪h z, mv (gX T.omega T.r c z) (T.WeX c e f z)⟫_ℂ) z := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      by_cases hzd : z ∈ T.pieceDomain c e
      · simp [indicator_of_mem hzd, h0 z hz]
      · simp [indicator_of_notMem hzd]
    rw [hR]
    refine setIntegral_congr_fun hK.measurableSet fun z hz => ?_
    have hzd := hKd hz
    have hx := symm_mem_cfd hzd
    rw [inner_repX_pt f hx, c.val.right_inv hzd.1.1, indicator_of_mem hzd,
      cweight_pX hzd.1]
    ring
  · by_cases hxs : x ∈ c.val.source
    · rw [repX_eq_zero (h0 _ fun h' => hx ⟨hxs, h'⟩), inner_zero_left]
    · rw [repX_of_notMem fun h' => hxs h'.1.1, inner_zero_left]

end TwistedDatum

end SGPT.Trace.TwistedL2
