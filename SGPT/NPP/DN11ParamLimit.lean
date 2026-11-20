import SGPT.NPP.DN3ParamIntegral
import Mathlib.Analysis.Distribution.TestFunction

/-!
# Parametric integrals against a rough factor, and their limits

Lane DN11 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 6: "for a general local
plurisubharmonic `p` we mollify, `p_ε ↓ p`, and pass to the limit in the Levi forms of the
smoothings, which depend continuously on `p` in `L¹_loc` because the kernel is smooth").

For a kernel `K(q, y)`, smooth in `(q, y)` on `S × E` (`S` open in a finite-dimensional parameter
space) and vanishing for `y` outside a fixed compact set `C`, and a factor `f` that is only
integrable on `C`, the function `G_f(q) = ∫ f(y) K(q, y) dy` is differentiated under the integral
sign (`hasFDerivAt_integral_smul_kernel`, dominated convergence: the derivative of `K` in `q` is
bounded on compacts), so that (`realHessian_integral_mul_kernel`)

  `D²G_f(q₀)[v, w] = ∫ f(y) D²_q K(q₀, y)[v, w] dy`.

For fixed `q₀, v, w` the function `y ↦ D²_q K(q₀, y)[v, w]` is a test function supported in `C`
(`testFunctionHessian`).  Hence, if `f_j → g` weakly on an open set `U ⊇ C`
(`∫ φ f_j → ∫ φ g` for every test function `φ` on `U`), the values, first derivatives, real
Hessians and Levi forms of `G_{f_j}` at `q₀` converge to those of `G_g`
(`tendsto_integral_mul_kernel`, `tendsto_fderiv_integral_mul_kernel`,
`tendsto_realHessian_integral_mul_kernel`, `tendsto_leviForm_integral_mul_kernel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.NPP.DN11

open SGPT.Foundations.Analysis

section Param

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The parameter derivative of `K(·, y)` vanishes for `y ∉ C`. -/
theorem fderiv_param_eq_zero_of_notMem {K : P → E → G} {C : Set E}
    (hKC : ∀ q y, y ∉ C → K q y = 0) {y : E} (hy : y ∉ C) (q : P) :
    fderiv ℝ (fun q => K q y) q = 0 := by
  have : (fun q => K q y) = fun _ => (0 : G) := funext fun q => hKC q y hy
  rw [this]
  exact fderiv_const_apply 0

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] in
/-- `f y • K q y = (C.indicator f) y • K q y` when `K q` vanishes off `C`. -/
theorem smul_kernel_eq_indicator {K : P → E → G} {C : Set E}
    (hKC : ∀ q y, y ∉ C → K q y = 0) (f : E → ℝ) (q : P) (y : E) :
    f y • K q y = C.indicator f y • K q y := by
  by_cases hy : y ∈ C
  · rw [indicator_of_mem hy]
  · rw [hKC q y hy, smul_zero, smul_zero]

omit [FiniteDimensional ℝ P] [CompleteSpace G] in
/-- Integrability of `y ↦ f(y) K(q, y)` for `K(q, ·)` continuous and vanishing off the compact `C`,
`f` integrable on `C`. -/
theorem integrable_smul_kernel {k : E → G} (hk : Continuous k) {C : Set E} (hC : IsCompact C)
    (hkC : ∀ y, y ∉ C → k y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ) :
    Integrable (fun y => f y • k y) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hfi : Integrable (C.indicator f) μ := hf.integrable_indicator hC.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hk.continuousOn
  have heq : (fun y => f y • k y) = fun y => C.indicator f y • k y := by
    funext y
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy]
    · rw [hkC y hy, smul_zero, smul_zero]
  rw [heq]
  refine Integrable.mono' (hfi.norm.const_mul M)
    (hfi.aestronglyMeasurable.smul hk.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  by_cases hy : y ∈ C
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM y hy) (norm_nonneg _)
  · simp [indicator_of_notMem hy]

omit [CompleteSpace G] in
/-- **Differentiation under the integral sign against a rough factor**: for `K` jointly `C¹` on
`S × E`, vanishing for `y ∉ C` (`C` compact), and `f` integrable on `C`,
`D_q ∫ f(y) K(q, y) dy = ∫ f(y) D_q K(q, y) dy`. -/
theorem hasFDerivAt_integral_smul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → G}
    (hK : ContDiffOn ℝ 1 (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hKC : ∀ q y, y ∉ C → K q y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ)
    {q₀ : P} (hq₀ : q₀ ∈ S) :
    HasFDerivAt (fun q => ∫ y, f y • K q y ∂μ)
      (∫ y, f y • fderiv ℝ (fun q => K q y) q₀ ∂μ) q₀ := by
  have hW : IsOpen (S ×ˢ (univ : Set E)) := hS.prod isOpen_univ
  set g : E → ℝ := C.indicator f with hg
  have hgi : Integrable g μ := hf.integrable_indicator hC.isClosed.measurableSet
  set K' : P → E → P →L[ℝ] G := fun p s =>
    (fderiv ℝ (fun q : P × E => K q.1 q.2) (p, s)).comp (ContinuousLinearMap.inl ℝ P E) with hK'
  have hpart : ∀ p ∈ S, ∀ s, HasFDerivAt (fun q => K q s) (K' p s) p := by
    intro p hp s
    have h1 : HasFDerivAt (fun q : P × E => K q.1 q.2)
        (fderiv ℝ (fun q : P × E => K q.1 q.2) (p, s)) (p, s) :=
      ((hK.differentiableOn one_ne_zero) (p, s) ⟨hp, mem_univ _⟩).differentiableAt
        (hW.mem_nhds ⟨hp, mem_univ _⟩) |>.hasFDerivAt
    exact h1.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p s)
  have hK'c : ContinuousOn (fun q : P × E => K' q.1 q.2) (S ×ˢ univ) := by
    have h := hK.continuousOn_fderiv_of_isOpen hW le_rfl
    exact h.clm_comp continuousOn_const
  have hKc : ∀ p ∈ S, Continuous fun s => K p s := by
    intro p hp
    exact continuousOn_univ.mp (hK.continuousOn.comp
      (Continuous.prodMk continuous_const continuous_id).continuousOn fun s _ => ⟨hp, mem_univ s⟩)
  have hK'0c : Continuous fun s => K' q₀ s :=
    continuousOn_univ.mp (hK'c.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      fun s _ => ⟨hq₀, mem_univ s⟩)
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hS q₀ hq₀
  have hε2 : closedBall q₀ (ε / 2) ⊆ S :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεS
  obtain ⟨M, hM⟩ := ((isCompact_closedBall q₀ (ε / 2)).prod hC).exists_bound_of_continuousOn
    (hK'c.mono (prod_mono hε2 (subset_univ _)))
  have hK'zero : ∀ p ∈ S, ∀ s, s ∉ C → K' p s = 0 := by
    intro p hp s hs
    rw [← (hpart p hp s).fderiv]
    exact fderiv_param_eq_zero_of_notMem hKC hs p
  have hball : ball q₀ (ε / 2) ∈ 𝓝 q₀ := ball_mem_nhds q₀ (half_pos hε)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun q y => g y • K q y) (F' := fun q y => g y • K' q y)
    (bound := fun y => M * ‖g y‖) hball
    (by
      filter_upwards [hS.mem_nhds hq₀] with p hp
      exact hgi.aestronglyMeasurable.smul (hKc p hp).aestronglyMeasurable)
    (integrable_smul_kernel (hKc q₀ hq₀) hC (fun y hy => hKC q₀ y hy) hf |>.congr
      (Eventually.of_forall fun y => smul_kernel_eq_indicator hKC f q₀ y))
    (hgi.aestronglyMeasurable.smul hK'0c.aestronglyMeasurable) ?_ (hgi.norm.const_mul M) ?_
  · have heq1 : (fun q => ∫ y, f y • K q y ∂μ) = fun q => ∫ y, g y • K q y ∂μ := by
      funext q
      exact integral_congr_ae (Eventually.of_forall fun y => smul_kernel_eq_indicator hKC f q y)
    have heq2 : ∫ y, f y • fderiv ℝ (fun q => K q y) q₀ ∂μ = ∫ y, g y • K' q₀ y ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [(hpart q₀ hq₀ y).fderiv]
      by_cases hy : y ∈ C
      · rw [hg, indicator_of_mem hy]
      · rw [hK'zero q₀ hq₀ y hy, smul_zero, smul_zero]
    rw [heq1, heq2]
    exact hmain
  · refine Eventually.of_forall fun s p hp => ?_
    have hpS : p ∈ S := hε2 (ball_subset_closedBall hp)
    rw [norm_smul]
    by_cases hs : s ∈ C
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM (p, s) ⟨ball_subset_closedBall hp, hs⟩)
        (norm_nonneg _)
    · simp [hK'zero p hpS s hs, hg, indicator_of_notMem hs]
  · exact Eventually.of_forall fun s p hp =>
      (hpart p (hε2 (ball_subset_closedBall hp)) s).const_smul (g s)

omit [CompleteSpace G] in
/-- The derivative of `q ↦ ∫ f(y) K(q, y) dy` on the open set `S`. -/
theorem fderiv_integral_smul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → G}
    (hK : ContDiffOn ℝ 1 (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hKC : ∀ q y, y ∉ C → K q y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ)
    {q : P} (hq : q ∈ S) :
    fderiv ℝ (fun q => ∫ y, f y • K q y ∂μ) q = ∫ y, f y • fderiv ℝ (fun q => K q y) q ∂μ :=
  (hasFDerivAt_integral_smul_kernel hS hK hC hKC hf hq).fderiv

omit [CompleteSpace G] in
/-- **Second derivative under the integral sign against a rough factor.** -/
theorem hasFDerivAt_fderiv_integral_smul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → G}
    (hK : ContDiffOn ℝ 2 (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hKC : ∀ q y, y ∉ C → K q y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ)
    {q₀ : P} (hq₀ : q₀ ∈ S) :
    HasFDerivAt (fderiv ℝ (fun q => ∫ y, f y • K q y ∂μ))
      (∫ y, f y • fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q₀ ∂μ) q₀ := by
  have hK1 : ContDiffOn ℝ 1 (fun q : P × E => fderiv ℝ (fun p => K p q.2) q.1) (S ×ˢ univ) :=
    SGPT.NPP.DN3.contDiffOn_fderiv_param (m := 1) hS (hK.of_le (by norm_num))
  have hKC' : ∀ q y, y ∉ C → fderiv ℝ (fun p => K p y) q = 0 :=
    fun q y hy => fderiv_param_eq_zero_of_notMem hKC hy q
  have h := hasFDerivAt_integral_smul_kernel (μ := μ) (K := fun q y => fderiv ℝ (fun p => K p y) q)
    hS hK1 hC hKC' hf hq₀
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hS.mem_nhds hq₀] with q hq
  exact fderiv_integral_smul_kernel hS (hK.of_le (by norm_num)) hC hKC hf hq

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
/-- The second parameter derivative of a jointly `C^{m+2}` family is jointly `C^m`. -/
theorem contDiffOn_fderiv2_param {S : Set P} (hS : IsOpen S) {K : P → E → G} {m : ℕ}
    (hK : ContDiffOn ℝ (m + 2) (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) :
    ContDiffOn ℝ m (fun q : P × E => fderiv ℝ (fun p => fderiv ℝ (fun p => K p q.2) p) q.1)
      (S ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun q : P × E => fderiv ℝ (fun p => K p q.2) q.1) (S ×ˢ univ) := by
    refine SGPT.NPP.DN3.contDiffOn_fderiv_param (m := m + 1) hS ?_
    have : ((m + 1 : ℕ) : WithTop ℕ∞) + 1 = (m : WithTop ℕ∞) + 2 := by
      push_cast; ring
    rw [this]; exact hK
  have h1' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
      (fun q : P × E => fderiv ℝ (fun p => K p q.2) q.1) (S ×ˢ univ) := by
    have : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [← this]; exact h1
  exact SGPT.NPP.DN3.contDiffOn_fderiv_param (F := fun p s => fderiv ℝ (fun p => K p s) p)
    (m := m) hS h1'

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
theorem natCast_add_two_le_infty (m : ℕ) : ((m : WithTop ℕ∞) + 2) ≤ ∞ := by
  have : ((m : WithTop ℕ∞) + 2) = ((m + 2 : ℕ) : WithTop ℕ∞) := by push_cast; rfl
  rw [this]; exact WithTop.coe_le_coe.mpr le_top

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
theorem natCast_add_one_le_infty (m : ℕ) : ((m : WithTop ℕ∞) + 1) ≤ ∞ := by
  have : ((m : WithTop ℕ∞) + 1) = ((m + 1 : ℕ) : WithTop ℕ∞) := by push_cast; rfl
  rw [this]; exact WithTop.coe_le_coe.mpr le_top

/-! ### Real-valued kernels: values, derivatives and Hessians as integrals -/

/-- `D G_f(q)[v] = ∫ f(y) D_qK(q, y)[v] dy`. -/
theorem fderiv_integral_mul_kernel_apply {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ 1 (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hKC : ∀ q y, y ∉ C → K q y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ)
    {q : P} (hq : q ∈ S) (v : P) :
    fderiv ℝ (fun q => ∫ y, f y * K q y ∂μ) q v =
      ∫ y, f y * fderiv ℝ (fun q => K q y) q v ∂μ := by
  have hW : IsOpen (S ×ˢ (univ : Set E)) := hS.prod isOpen_univ
  have h := fderiv_integral_smul_kernel (μ := μ) hS hK hC hKC hf hq
  simp only [smul_eq_mul] at h
  rw [h]
  have hc : Continuous fun y => fderiv ℝ (fun q => K q y) q := by
    have h1 : ContinuousOn (fun q : P × E => fderiv ℝ (fun p => K p q.2) q.1) (S ×ˢ univ) :=
      (SGPT.NPP.DN3.contDiffOn_fderiv_param (m := 0) hS (by simpa using hK)).continuousOn
    exact continuousOn_univ.mp (h1.comp
      (Continuous.prodMk continuous_const continuous_id).continuousOn fun s _ => ⟨hq, mem_univ s⟩)
  have hint := integrable_smul_kernel (μ := μ) (G := P →L[ℝ] ℝ)
    (k := fun y => fderiv ℝ (fun q => K q y) q) hc hC
    (fun y hy => fderiv_param_eq_zero_of_notMem hKC hy q) hf
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

/-- `D²G_f(q)[v, w] = ∫ f(y) D²_qK(q, y)[v, w] dy`. -/
theorem realHessian_integral_mul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ 2 (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hKC : ∀ q y, y ∉ C → K q y = 0) {f : E → ℝ} (hf : IntegrableOn f C μ)
    {q : P} (hq : q ∈ S) (v w : P) :
    realHessian (fun q => ∫ y, f y * K q y ∂μ) q v w =
      ∫ y, f y * fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q v w ∂μ := by
  have h := (hasFDerivAt_fderiv_integral_smul_kernel (μ := μ) hS hK hC hKC hf hq).fderiv
  simp only [smul_eq_mul] at h
  rw [realHessian_eq_fderiv, h]
  have hc : Continuous fun y => fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q := by
    have h1 := contDiffOn_fderiv2_param (m := 0) hS (by simpa using hK)
    exact continuousOn_univ.mp (h1.continuousOn.comp
      (Continuous.prodMk continuous_const continuous_id).continuousOn fun s _ => ⟨hq, mem_univ s⟩)
  have hKC2 : ∀ y, y ∉ C → fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q = 0 := by
    intro y hy
    exact fderiv_param_eq_zero_of_notMem (K := fun q y => fderiv ℝ (fun q => K q y) q)
      (fun q y hy => fderiv_param_eq_zero_of_notMem hKC hy q) hy q
  have hint := integrable_smul_kernel (μ := μ) (G := P →L[ℝ] P →L[ℝ] ℝ)
    (k := fun y => fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q) hc hC hKC2 hf
  rw [ContinuousLinearMap.integral_apply hint]
  have hint2 : Integrable (fun y => (f y • fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q) v)
      μ := hint.apply_continuousLinearMap v
  rw [ContinuousLinearMap.integral_apply hint2]
  rfl

/-! ### Test functions from the kernel -/

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] in
/-- A function vanishing off a compact subset `C` of the open `U` has compact support inside `U`. -/
theorem tsupport_subset_of_vanish {k : E → ℝ} {C : Set E} (hC : IsCompact C)
    (hkC : ∀ y, y ∉ C → k y = 0) : tsupport k ⊆ C := by
  refine closure_minimal (fun y hy => ?_) hC.isClosed
  by_contra h
  exact hy (hkC y h)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] in
theorem hasCompactSupport_of_vanish {k : E → ℝ} {C : Set E} (hC : IsCompact C)
    (hkC : ∀ y, y ∉ C → k y = 0) : HasCompactSupport k :=
  HasCompactSupport.intro hC hkC

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The test function `y ↦ k(y)` (smooth, vanishing off the compact `C ⊆ U`). -/
def testFunctionOf (U : Opens E) {k : E → ℝ} (hk : ContDiff ℝ ∞ k) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hkC : ∀ y, y ∉ C → k y = 0) : 𝓓(U, ℝ) where
  toFun := k
  contDiff' := hk
  hasCompactSupport' := hasCompactSupport_of_vanish hC hkC
  tsupport_subset' := (tsupport_subset_of_vanish hC hkC).trans hCU

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem testFunctionOf_apply (U : Opens E) {k : E → ℝ} (hk : ContDiff ℝ ∞ k) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hkC : ∀ y, y ∉ C → k y = 0) (y : E) :
    testFunctionOf U hk hC hCU hkC y = k y := rfl

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
/-- Slices of a jointly smooth family are smooth. -/
theorem contDiff_slice {S : Set P} {K : P → E → G} {m : WithTop ℕ∞}
    (hK : ContDiffOn ℝ m (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {q : P} (hq : q ∈ S) :
    ContDiff ℝ m fun y => K q y := by
  have h := hK.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨hq, mem_univ y⟩)
  exact h

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `y ↦ D_qK(q, y)[v]` is smooth. -/
theorem contDiff_fderiv_param_apply {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {q : P} (hq : q ∈ S) (v : P) :
    ContDiff ℝ ∞ fun y => fderiv ℝ (fun q => K q y) q v := by
  refine contDiff_infty.mpr fun m => ?_
  have h := SGPT.NPP.DN3.contDiffOn_fderiv_param (F := K) (m := m) hS
    (hK.of_le (natCast_add_one_le_infty m))
  exact (contDiff_slice (K := fun p s => fderiv ℝ (fun p => K p s) p) h hq).clm_apply
    contDiff_const

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `y ↦ D²_qK(q, y)[v, w]` is smooth. -/
theorem contDiff_fderiv2_param_apply {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {q : P} (hq : q ∈ S)
    (v w : P) :
    ContDiff ℝ ∞ fun y => fderiv ℝ (fun q => fderiv ℝ (fun q => K q y) q) q v w := by
  refine contDiff_infty.mpr fun m => ?_
  have h := contDiffOn_fderiv2_param (K := K) (m := m) hS
    (hK.of_le (natCast_add_two_le_infty m))
  exact ((contDiff_slice (K := fun p s => fderiv ℝ (fun p => fderiv ℝ (fun p => K p s) p) p)
    h hq).clm_apply contDiff_const).clm_apply contDiff_const

/-! ### Limits under weak convergence of the factor -/

variable {U : Opens E} {f : ℕ → E → ℝ} {g : E → ℝ}

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [CompleteSpace G] [BorelSpace E] in
/-- Weak convergence against one smooth function vanishing off `C ⊆ U`. -/
theorem tendsto_integral_mul_of_weak
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)))
    {k : E → ℝ} (hk : ContDiff ℝ ∞ k) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U)
    (hkC : ∀ y, y ∉ C → k y = 0) :
    Tendsto (fun j => ∫ y, f j y * k y ∂μ) atTop (𝓝 (∫ y, g y * k y ∂μ)) := by
  have h := hweak (testFunctionOf U hk hC hCU hkC)
  simp only [testFunctionOf_apply] at h
  simp_rw [mul_comm (f _ _), mul_comm (g _)]
  exact h

omit [CompleteSpace G] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Values converge.** -/
theorem tendsto_integral_mul_kernel {S : Set P} {K : P → E → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hKC : ∀ q y, y ∉ C → K q y = 0)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)))
    {q : P} (hq : q ∈ S) :
    Tendsto (fun j => ∫ y, f j y * K q y ∂μ) atTop (𝓝 (∫ y, g y * K q y ∂μ)) :=
  tendsto_integral_mul_of_weak hweak (contDiff_slice hK hq) hC hCU (fun y hy => hKC q y hy)

omit [CompleteSpace G] in
/-- **First derivatives converge.** -/
theorem tendsto_fderiv_integral_mul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hKC : ∀ q y, y ∉ C → K q y = 0)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)))
    (hf : ∀ j, IntegrableOn (f j) C μ) (hg : IntegrableOn g C μ) {q : P} (hq : q ∈ S) (v : P) :
    Tendsto (fun j => fderiv ℝ (fun q => ∫ y, f j y * K q y ∂μ) q v) atTop
      (𝓝 (fderiv ℝ (fun q => ∫ y, g y * K q y ∂μ) q v)) := by
  have hK1 : ContDiffOn ℝ 1 (fun q : P × E => K q.1 q.2) (S ×ˢ univ) :=
    hK.of_le (by norm_cast)
  simp_rw [fderiv_integral_mul_kernel_apply hS hK1 hC hKC (hf _) hq,
    fderiv_integral_mul_kernel_apply hS hK1 hC hKC hg hq]
  exact tendsto_integral_mul_of_weak hweak (contDiff_fderiv_param_apply hS hK hq v) hC hCU
    (fun y hy => by rw [fderiv_param_eq_zero_of_notMem hKC hy q]; rfl)

omit [CompleteSpace G] in
/-- **Real Hessians converge.** -/
theorem tendsto_realHessian_integral_mul_kernel {S : Set P} (hS : IsOpen S) {K : P → E → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hKC : ∀ q y, y ∉ C → K q y = 0)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)))
    (hf : ∀ j, IntegrableOn (f j) C μ) (hg : IntegrableOn g C μ) {q : P} (hq : q ∈ S)
    (v w : P) :
    Tendsto (fun j => realHessian (fun q => ∫ y, f j y * K q y ∂μ) q v w) atTop
      (𝓝 (realHessian (fun q => ∫ y, g y * K q y ∂μ) q v w)) := by
  have hK2 : ContDiffOn ℝ 2 (fun q : P × E => K q.1 q.2) (S ×ˢ univ) :=
    hK.of_le (by norm_cast)
  simp_rw [realHessian_integral_mul_kernel hS hK2 hC hKC (hf _) hq,
    realHessian_integral_mul_kernel hS hK2 hC hKC hg hq]
  refine tendsto_integral_mul_of_weak hweak (contDiff_fderiv2_param_apply hS hK hq v w) hC hCU
    (fun y hy => ?_)
  have h1 : (fun q => fderiv ℝ (fun q => K q y) q) = fun _ => 0 :=
    funext fun q => fderiv_param_eq_zero_of_notMem hKC hy q
  simp [h1]

omit [CompleteSpace G] in
/-- **Levi forms converge.** -/
theorem tendsto_leviForm_integral_mul_kernel [NormedSpace ℂ P] {S : Set P} (hS : IsOpen S)
    {K : P → E → ℝ} (hK : ContDiffOn ℝ ∞ (fun q : P × E => K q.1 q.2) (S ×ˢ univ)) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hKC : ∀ q y, y ∉ C → K q y = 0)
    (hweak : ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => ∫ x, φ x * f j x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)))
    (hf : ∀ j, IntegrableOn (f j) C μ) (hg : IntegrableOn g C μ) {q : P} (hq : q ∈ S) (v : P) :
    Tendsto (fun j => leviForm (fun q => ∫ y, f j y * K q y ∂μ) q v) atTop
      (𝓝 (leviForm (fun q => ∫ y, g y * K q y ∂μ) q v)) := by
  simp only [leviForm]
  exact ((tendsto_realHessian_integral_mul_kernel hS hK hC hCU hKC hweak hf hg hq v v).add
    (tendsto_realHessian_integral_mul_kernel hS hK hC hCU hKC hweak hf hg hq _ _)).div_const 4

end Param

end SGPT.NPP.DN11
