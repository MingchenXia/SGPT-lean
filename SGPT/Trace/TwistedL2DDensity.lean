import SGPT.Trace.TwistedL2DLocal

/-!
# The density lemma `TwistedDatum.SigmaGraphDensity` on `ℂⁿ`

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:density`, `claude-tl2-dens:main`).  For a twisted
datum `T` on `ℂⁿ` and a test family `τ`, the projected field `v` (`exists_v`) is cut off with the
complete cut-offs `χ_k`, localized into frame domains (`exists_localization`) and approximated by
Friedrichs' lemma (`exists_approx`).  The three quantities of `SigmaGraphDensity` are read as `L²`
norms of unit-frame representatives:

* `energy_eq`: `‖T*τ‖² = ∫ ‖AF τ‖²`, `AF τ = ∑_i uc_i⁻¹ √(a+b) s ϑ h_i`;
* `senergy_eq`: `‖∂̄σ^♭τ‖² = ½ ∫ ‖SF τ‖²`, `SF τ = ∑_i uc_i⁻¹ s √σ⁻ᵀ ∂̄σ^♭h_i √σ⁻¹`;
* `inner_repFam_yd`: `⟨τ, ∂̄G⟩ = ⟪repFam τ, ydF⟫`.

The approximations converge in `L²` (`m → ∞`) to the cut-off of `v`, whose quantities converge
(`k → ∞`) to those of `τ`, except for the `S`-energy, which is `O(1/k²)`; a diagonal choice gives
`sigmaGraphDensity`, hence `twistedFunctionalBoundStatement_complexModel` and
`twistedL2CorrectionStatement_complexModel`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### `L²` helpers -/

theorem integral_norm_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ComplexModel n → E} (hf : MemLp f 2 volume) :
    ∫ z, ‖f z‖ ^ 2 = ‖hf.toLp f‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f), L2.inner_def,
    ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz, inner_self_eq_norm_sq (𝕜 := ℂ)]

theorem tendsto_toLp_of_eLpNorm {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → ComplexModel n → E} {g : ComplexModel n → E} (hf : ∀ m, MemLp (f m) 2 volume)
    (hg : MemLp g 2 volume)
    (h : Tendsto (fun m => eLpNorm (fun z => f m z - g z) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : ∀ m, ‖(hf m).toLp (f m) - hg.toLp g‖ =
      (eLpNorm (fun z => f m z - g z) 2 volume).toReal := by
    intro m
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  simp only [he]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using this

/-- A sequence dominated by `C · aₘ` with `aₘ → 0` tends to `0` (in `ℝ≥0∞`). -/
theorem tendsto_zero_of_le_const_mul {a b : ℕ → ℝ≥0∞} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ m, b m ≤ ENNReal.ofReal C * a m) :
    Tendsto b atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) ha
    (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => by positivity) hb

theorem norm_euclid_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℂ ι) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have h : x = ∑ i, x i • (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ ι) := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one]

theorem norm_entry_le_mnorm (B : Matrix (Fin n) (Fin n) ℂ) (j a : Fin n) : ‖B j a‖ ≤ mnorm B := by
  unfold mnorm
  calc ‖B j a‖ ≤ ∑ b, ‖B j b‖ :=
        Finset.single_le_sum (f := fun b => ‖B j b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    _ ≤ ∑ i, ∑ b, ‖B i b‖ :=
        Finset.single_le_sum (f := fun i => ∑ b, ‖B i b‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- `‖B M Bᵀ‖ ≤ n² |B|² ∑ |M_{ac}|`. -/
theorem norm_flat2_mul_le (B M : Matrix (Fin n) (Fin n) ℂ) :
    ‖flat2 (B * M * Bᵀ)‖ ≤ (n * n : ℝ) * (mnorm B ^ 2 * ∑ a, ∑ c, ‖M a c‖) := by
  set S := ∑ a, ∑ c, ‖M a c‖
  have hentry : ∀ j k, ‖(B * M * Bᵀ) j k‖ ≤ mnorm B ^ 2 * S := by
    intro j k
    simp only [mul_apply, transpose_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c, ‖∑ a, B j a * M a c * B k c‖ ≤ ∑ c, ∑ a, ‖B j a * M a c * B k c‖ :=
          Finset.sum_le_sum fun c _ => norm_sum_le _ _
      _ ≤ ∑ c, ∑ a, mnorm B * ‖M a c‖ * mnorm B := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_right (norm_entry_le_mnorm B j a)
            (norm_nonneg _)) (norm_entry_le_mnorm B k c) (norm_nonneg _)
            (mul_nonneg (mnorm_nonneg B) (norm_nonneg _))
      _ = mnorm B ^ 2 * S := by
          simp only [S, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          ring
  refine (norm_euclid_le_sum _).trans ?_
  rw [Fintype.sum_prod_type]
  calc ∑ j, ∑ k, ‖flat2 (B * M * Bᵀ) (j, k)‖ ≤ ∑ _j : Fin n, ∑ _k : Fin n, mnorm B ^ 2 * S :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = _ := by simp; ring

theorem tendsto_integral_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℕ → ComplexModel n → E} {g : ComplexModel n → E} (hf : ∀ m, MemLp (f m) 2 volume)
    (hg : MemLp g 2 volume)
    (h : Tendsto (fun m => eLpNorm (fun z => f m z - g z) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ z, ‖f m z‖ ^ 2) atTop (𝓝 (∫ z, ‖g z‖ ^ 2)) := by
  simp only [integral_norm_sq_eq (hf _), integral_norm_sq_eq hg]
  have hL := tendsto_toLp_of_eLpNorm hf hg h
  exact ((continuous_norm.tendsto _).comp hL).pow 2

theorem tendsto_eLpNorm_of_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℕ → ComplexModel n → E} (hf : ∀ k, MemLp (f k) 2 volume)
    (h : Tendsto (fun k => ∫ z, ‖f k z‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 volume) atTop (𝓝 0) := by
  have he : ∀ k, eLpNorm (f k) 2 volume = ENNReal.ofReal (Real.sqrt (∫ z, ‖f k z‖ ^ 2)) := by
    intro k
    rw [integral_norm_sq_eq (hf k), Real.sqrt_sq (norm_nonneg _), Lp.norm_toLp,
      ENNReal.ofReal_toReal (hf k).eLpNorm_ne_top]
  simp only [he]
  have := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp h)
  simpa [Function.comp_def] using this

theorem memLp_of_bound_on_compact {E : Type*} [NormedAddCommGroup E] {f : ComplexModel n → E}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hb : ∀ z ∈ K, ‖f z‖ ≤ C) (h0 : ∀ z ∉ K, f z = 0) : MemLp f 2 volume := by
  have hI : MemLp (K.indicator fun _ => C) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet C (Or.inr hK.measure_lt_top.ne)
  refine hI.of_le hf (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz, Real.norm_eq_abs]; exact (hb z hz).trans (le_abs_self _)
  · rw [h0 z hz, norm_zero]; exact norm_nonneg _

theorem eLpNorm_le_restrict {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ComplexModel n → E} {g : ComplexModel n → F} {D : Set (ComplexModel n)}
    (hD : MeasurableSet D) (h0 : ∀ z ∉ D, f z = 0) {C : ℝ} (hb : ∀ z ∈ D, ‖f z‖ ≤ C * ‖g z‖) :
    eLpNorm f 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 (volume.restrict D) := by
  rw [← eLpNorm_restrict_eq_of_support_subset (s := D) fun z hz => by
    by_contra h; exact hz (h0 z h)]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((ae_restrict_iff' hD).mpr (Eventually.of_forall hb)) 2

theorem flat2_add (M N : Matrix (Fin n) (Fin n) ℂ) : flat2 (M + N) = flat2 M + flat2 N := by
  ext p; simp [flat2]

theorem flat2_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : flat2 (c • M) = c • flat2 M := by
  ext p; simp [flat2]

theorem flat2_zero : flat2 (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  ext p; simp [flat2]

theorem flat2_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    flat2 (∑ i ∈ s, M i) = ∑ i ∈ s, flat2 (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [flat2_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, flat2_add, ih]

theorem continuousOn_mul_conj {S : Set (ComplexModel n)} {B β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hB : ContinuousOn B S) (hβ : ContinuousOn β S) :
    ContinuousOn (fun z => B z * β z * (B z)ᵀ) S := by
  refine continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => ?_
  simp only [mul_apply, transpose_apply]
  exact continuousOn_finsetSum _ fun c _ => (continuousOn_finsetSum _ fun a _ =>
    (continuousOn_entry hB j a).mul (continuousOn_entry hβ a c)).mul (continuousOn_entry hB k c)

theorem continuous_flat2 : Continuous (flat2 (n := n)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p =>
    (continuous_apply p.2).comp (continuous_apply p.1))

theorem aestronglyMeasurable_flat2 {μ : Measure (ComplexModel n)}
    {X : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ j k, AEStronglyMeasurable (fun z => X z j k) μ) :
    AEStronglyMeasurable (fun z => flat2 (X z)) μ := by
  classical
  have hfun : (fun z => flat2 (X z)) = fun z => ∑ p : Fin n × Fin n,
      X z p.1 p.2 • (EuclideanSpace.single p (1 : ℂ) : EuclideanSpace ℂ (Fin n × Fin n)) := by
    funext z
    ext q
    simp [flat2, Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  exact Finset.aestronglyMeasurable_fun_sum _ fun p _ => (h p.1 p.2).smul_const _

theorem aestronglyMeasurable_conj_mul {μ : Measure (ComplexModel n)}
    {B β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hB : ∀ j k, AEStronglyMeasurable (fun z => B z j k) μ)
    (hβ : ∀ j k, AEStronglyMeasurable (fun z => β z j k) μ) (j k : Fin n) :
    AEStronglyMeasurable (fun z => (B z * β z * (B z)ᵀ) j k) μ := by
  simp only [mul_apply, transpose_apply]
  exact Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
    (Finset.aestronglyMeasurable_fun_sum _ fun a _ => (hB j a).mul (hβ a c)).mul (hB k c)

/-- Componentwise `L²` convergence of a sum bound (vector-valued pieces). -/
theorem tendsto_eLpNorm_sum' {ι : Type*} (s : Finset ι) {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] {μ : Measure (ComplexModel n)} {F : ℕ → ComplexModel n → E}
    {G : ι → ℕ → ComplexModel n → E'}
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

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

/-! ### Unit-frame representatives of the `T*`- and `S`-energies -/

variable (T ρ) in
/-- `√(a+b) s`. -/
def cw2 (z : ComplexModel n) : ℝ := Real.sqrt (T.a z + T.b z) * T.sw ρ z

variable (T ρ) in
/-- The `T*`-representative `√(a+b) s g` of a coefficient function in the frame `e`. -/
def AFp (e : AtlasFrame T.L) (g : ComplexModel n → ℂ) (z : ComplexModel n) : ℂ :=
  (T.dom e).indicator (fun z => ((T.cw2 ρ z : ℝ) : ℂ) * g z) z

variable (T ρ) in
/-- The `T*`-representative of a family in the unit frame. -/
def AF (F : T.FrameFamily) (z : ComplexModel n) : ℂ :=
  ∑ i ∈ F.s, (uc (F.e i) z)⁻¹ * T.AFp ρ (F.e i) (chartTheta (T.pW ρ (F.e i)) (F.h i)) z

variable (T ρ) in
/-- The `S`-representative `s √σ⁻ᵀ β √σ⁻¹` of a `(0,2)`-coefficient matrix in the frame `e`. -/
def SFp (e : AtlasFrame T.L) (β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (z : ComplexModel n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  (T.dom e).indicator (fun z => flat2 (((T.sw ρ z : ℝ) : ℂ) •
    (Bi T.omega T.r z * β z * (Bi T.omega T.r z)ᵀ))) z

variable (T ρ) in
/-- The `S`-representative of a family in the unit frame. -/
def SF (F : T.FrameFamily) (z : ComplexModel n) : EuclideanSpace ℂ (Fin n × Fin n) :=
  ∑ i ∈ F.s, (uc (F.e i) z)⁻¹ • T.SFp ρ (F.e i) (sigmaDbar T.omega T.r (F.h i)) z

variable (hρ : IsChartDensity T.μ chart0 ρ)
include hρ

/-- **The `T*`-energy as an `L²` norm.** -/
theorem energy_eq (F : T.FrameFamily) : F.energy ρ = ∫ z, ‖T.AF ρ F z‖ ^ 2 := by
  unfold FrameFamily.energy
  congr 1
  funext z
  by_cases hz : z ∈ T.U
  · rw [FA_re_eq hρ F hz]
    have hAF : T.AF ρ F z = ((T.cw2 ρ z : ℝ) : ℂ) *
        ∑ i ∈ F.s, (uc (F.e i) z)⁻¹ * chartTheta (T.pW ρ (F.e i)) (F.h i) z := by
      rw [AF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hzi : z ∈ T.dom (F.e i)
      · rw [AFp, indicator_of_mem hzi]; ring
      · have h0 : chartTheta (T.pW ρ (F.e i)) (F.h i) z = 0 :=
          chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport
            fun h => hzi (T.tsupport_subset_dom F.spec i h))
        rw [AFp, indicator_of_notMem hzi, h0]; ring
    rw [hAF, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, cw2, mul_pow,
      Real.sq_sqrt (T.ab_pos hz).le]
  · have hAF : T.AF ρ F z = 0 := Finset.sum_eq_zero fun i _ => by
      rw [AFp, indicator_of_notMem fun h => hz (dom_subset_U _ h), mul_zero]
    rw [Φ_eq_zero F.spec (isGaugeForm_tstar hρ) hz, hAF]
    simp

/-- **The `S`-energy as an `L²` norm.** -/
theorem senergy_eq (F : T.FrameFamily) :
    F.senergy ρ = ∫ z, (1 / 2 : ℝ) * ‖T.SF ρ F z‖ ^ 2 := by
  unfold FrameFamily.senergy
  congr 1
  funext z
  by_cases hz : z ∈ T.U
  · rw [FS_re_eq hρ F hz, zeroTwoNormSq_eq_of_inv (Bi_conjTranspose z)
      (sigmaInv_eq T.isOpen_U T.kahler hz)]
    have hSF : T.SF ρ F z = ((T.sw ρ z : ℝ) : ℂ) • flat2 (Bi T.omega T.r z *
        (∑ i ∈ F.s, (uc (F.e i) z)⁻¹ • sigmaDbar T.omega T.r (F.h i) z) *
          (Bi T.omega T.r z)ᵀ) := by
      rw [Matrix.mul_sum, Matrix.sum_mul, flat2_sum, Finset.smul_sum, SF]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, flat2_smul, smul_comm]
      by_cases hzi : z ∈ T.dom (F.e i)
      · rw [SFp, indicator_of_mem hzi, flat2_smul]
      · have h0 : sigmaDbar T.omega T.r (F.h i) z = 0 :=
          sigmaDbar_zero (eventuallyEq_zero_of_notMem_tsupport
            fun h => hzi (T.tsupport_subset_dom F.spec i h))
        rw [SFp, indicator_of_notMem hzi, h0, Matrix.mul_zero, Matrix.zero_mul, flat2_zero]
        simp
    rw [hSF, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  · have hSF : T.SF ρ F z = 0 := Finset.sum_eq_zero fun i _ => by
      rw [SFp, indicator_of_notMem fun h => hz (dom_subset_U _ h), smul_zero]
    rw [Φ_eq_zero F.spec (isGaugeForm_S hρ) hz, hSF]
    simp

omit hρ in
theorem f0_eq_zero_of_notMem (F : T.FrameFamily) {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ}
    (x : ComplexModel n → ComplexModel n) {z : ComplexModel n} (hz : z ∉ tsupport ζ) :
    T.f0 ρ F e ζ x z = 0 := by
  have hz' : z ∉ tsupport (fun y => (ζ y : ℂ)) := fun h =>
    hz ((tsupport_comp_subset Complex.ofReal_zero ζ) h)
  simp [f0, image_eq_zero_of_notMem_tsupport hz, dDir_eq_zero_of_notMem hz']

omit hρ in
theorem fS_eq_zero_of_notMem {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ}
    (x : ComplexModel n → ComplexModel n) {z : ComplexModel n} (hz : z ∉ tsupport ζ) (j k : Fin n) :
    T.fS ρ e ζ x j k z = 0 := by
  have hz' : z ∉ tsupport (fun y => (ζ y : ℂ)) := fun h =>
    hz ((tsupport_comp_subset Complex.ofReal_zero ζ) h)
  simp [fS, dbarDir_eq_zero_of_notMem hz']

variable (T ρ) in
/-- The unit-frame coefficient `∑_j ϑ h_j / uc e_j` of `T* τ / (a+b)`. -/
def Teps (F : T.FrameFamily) (z : ComplexModel n) : ℂ :=
  ∑ j ∈ F.s, (uc (F.e j) z)⁻¹ * chartTheta (T.pW ρ (F.e j)) (F.h j) z

/-- The frame value of `ϑ τ` in the unit frame. -/
theorem chartTheta_tot_eq (F : T.FrameFamily) {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.dom e) :
    chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z = uc e z * T.Teps ρ F z := by
  have h := cov_sum (isCovariant_theta hρ) F.spec (s := F.s) hz
  simp only [smul_eq_mul] at h
  rw [h, Teps]

/-- **The `T*`-limit of a localized piece.** -/
theorem uc_AFp_f0 (F : T.FrameFamily) (x : ComplexModel n → ComplexModel n) {e : AtlasFrame T.L}
    {ζ : ComplexModel n → ℝ} (_hζ : ContDiff ℝ ∞ ζ) (hζd : tsupport ζ ⊆ T.dom e) (z : ComplexModel n) :
    (uc e z)⁻¹ * T.AFp ρ e (T.f0 ρ F e ζ x) z = ((T.U.indicator (T.cw2 ρ) z : ℝ) : ℂ) *
      ((ζ z : ℂ) * T.Teps ρ F z - ∑ l, dDir (coordVec l) (fun y => (ζ y : ℂ)) z * T.Weps ρ x z l) := by
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    have hu := uc_ne_zero (T := T) ((T.mem_dom).mp hz).1
    rw [AFp, indicator_of_mem hz, indicator_of_mem hzU, f0, chartTheta_tot_eq hρ F hz]
    simp only [We, PiLp.smul_apply, smul_eq_mul]
    have hs : ∑ l, dDir (coordVec l) (fun y => (ζ y : ℂ)) z * (uc e z * T.Weps ρ x z l) =
        uc e z * ∑ l, dDir (coordVec l) (fun y => (ζ y : ℂ)) z * T.Weps ρ x z l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [hs]
    field_simp
  · have hzζ : z ∉ tsupport ζ := fun h => hz (hζd h)
    have hzζ' : z ∉ tsupport (fun y => (ζ y : ℂ)) := fun h =>
      hzζ ((tsupport_comp_subset Complex.ofReal_zero ζ) h)
    rw [AFp, indicator_of_notMem hz]
    simp [image_eq_zero_of_notMem_tsupport hzζ, dDir_eq_zero_of_notMem hzζ']

omit hρ in
theorem wedgeM_zero_left (y : ComplexModel n) : wedgeM 0 y = 0 := by
  ext j k; simp [wedgeM]

omit hρ in
theorem wedgeM_sum_left {ι : Type*} (s : Finset ι) (x : ι → ComplexModel n) (y : ComplexModel n) :
    wedgeM (∑ i ∈ s, x i) y = ∑ i ∈ s, wedgeM (x i) y := by
  ext j k
  simp only [wedgeM, of_apply, Matrix.sum_apply, euclid_sum_apply, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]

omit hρ in
/-- **The `S`-limit of a localized piece.** -/
theorem uc_SFp_fS (_hρ : IsChartDensity T.μ chart0 ρ) (x : ComplexModel n → ComplexModel n)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} (hζd : tsupport ζ ⊆ T.dom e) (z : ComplexModel n) :
    (uc e z)⁻¹ • T.SFp ρ e (fun z => Matrix.of fun j k => T.fS ρ e ζ x j k z) z =
      T.U.indicator (fun z => flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z *
        wedgeM (dbarV (fun y => (ζ y : ℂ)) z) (mv (sT T.omega T.r z) (T.Weps ρ x z)) *
          (Bi T.omega T.r z)ᵀ))) z := by
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    have hu := uc_ne_zero (T := T) ((T.mem_dom).mp hz).1
    have hM : (Matrix.of fun j k => T.fS ρ e ζ x j k z) = uc e z •
        wedgeM (dbarV (fun y => (ζ y : ℂ)) z) (mv (sT T.omega T.r z) (T.Weps ρ x z)) := by
      ext j k
      simp only [of_apply, fS, We, mv_smul, PiLp.smul_apply, smul_eq_mul, wedgeM, Matrix.smul_apply,
        dbarV, PiLp.toLp_apply]
      ring
    rw [SFp, indicator_of_mem hz, indicator_of_mem hzU, hM, Matrix.mul_smul, Matrix.smul_mul,
      smul_comm, flat2_smul, smul_smul, inv_mul_cancel₀ hu, one_smul]
  · have hzζ : z ∉ tsupport ζ := fun h => hζd h |> hz
    have hzζ' : z ∉ tsupport (fun y => (ζ y : ℂ)) := fun h =>
      hzζ ((tsupport_comp_subset Complex.ofReal_zero ζ) h)
    have h0 : dbarV (fun y => (ζ y : ℂ)) z = 0 := by
      ext l; simp [dbarV, dbarDir_eq_zero_of_notMem hzζ']
    rw [SFp, indicator_of_notMem hz, smul_zero]
    by_cases hzU : z ∈ T.U
    · rw [indicator_of_mem hzU, h0, wedgeM_zero_left, Matrix.mul_zero, Matrix.zero_mul, smul_zero,
        flat2_zero]
    · rw [indicator_of_notMem hzU]

/-- **The data limit of a localized piece**: `repF e (ζ W_e(x)) = ζ x`. -/
theorem repF_wsys (x : ComplexModel n → ComplexModel n) {e : AtlasFrame T.L}
    {ζ : ComplexModel n → ℝ} (hζd : tsupport ζ ⊆ T.dom e) (z : ComplexModel n) :
    T.repF ρ e (ofComps (T.wsys ρ e ζ x)) z = (ζ z : ℂ) • x z := by
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    have hu := uc_ne_zero (T := T) ((T.mem_dom).mp hz).1
    have hw : ofComps (T.wsys ρ e ζ x) z = ((ζ z : ℂ) * uc e z) • T.Weps ρ x z := by
      ext i; simp [ofComps, wsys, We]; ring
    have hc : (uc e z)⁻¹ * ((ζ z : ℂ) * uc e z) = (ζ z : ℂ) := by field_simp
    rw [repF, indicator_of_mem hz, hw, smul_smul, hc, mv_smul, smul_comm, sw_Bm_Weps hρ hzU]
  · have hzζ : z ∉ tsupport ζ := fun h => hζd h |> hz
    rw [repF, indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hzζ]
    simp

/-! ### Piecewise convergence -/

theorem continuousOn_cw2 : ContinuousOn (T.cw2 ρ) T.U := by
  have ha := (T.contDiffOn_U T.a_smooth).continuousOn
  have hb := (T.contDiffOn_U T.b_smooth).continuousOn
  exact ((ha.add hb).sqrt).mul (continuousOn_sw hρ)

theorem cw2_nonneg (z : ComplexModel n) : 0 ≤ T.cw2 ρ z :=
  mul_nonneg (Real.sqrt_nonneg _) (sw_pos hρ z).le

omit hρ in
theorem exists_bound_on {e : AtlasFrame T.L} {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKd : K ⊆ T.dom e) {κ : ComplexModel n → ℝ} (hκ : ContinuousOn κ (T.dom e)) :
    ∃ C, ∀ z ∈ K, κ z ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hκ.mono hKd)
  exact ⟨C, fun z hz => (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC z hz))⟩

omit hρ in
theorem AFp_eq_zero {e : AtlasFrame T.L} {g : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : g z = 0) : T.AFp ρ e g z = 0 := by
  by_cases h : z ∈ T.dom e
  · simp [AFp, indicator_of_mem h, hz]
  · simp [AFp, indicator_of_notMem h]

omit hρ in
theorem continuousOn_sqrt_frameNormSq (e : AtlasFrame T.L) :
    ContinuousOn (fun z => Real.sqrt (frameNormSq T.L e z)) (T.dom e) :=
  ((continuousOn_frameNormSq e).mono fun _ hz => ((T.mem_dom).mp hz).1).sqrt

/-- **Convergence of the `T*`-pieces.** -/
theorem tendsto_AFp_piece (F : T.FrameFamily) (x : ComplexModel n → ComplexModel n)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} {D K : Set (ComplexModel n)} (hD : IsOpen D)
    (hζD : tsupport ζ ⊆ D) (hKc : IsCompact K) (hDK : D ⊆ K) (hKd : K ⊆ T.dom e)
    {hs : ℕ → ComplexModel n → ComplexModel n} (hsD : ∀ m, tsupport (hs m) ⊆ D)
    (hc : Tendsto (fun m => eLpNorm (fun z => chartTheta (T.pW ρ e) (hs m) z - T.f0 ρ F e ζ x z) 2
      (volume.restrict D)) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun z => (uc e z)⁻¹ * T.AFp ρ e (chartTheta (T.pW ρ e) (hs m)) z -
      (uc e z)⁻¹ * T.AFp ρ e (T.f0 ρ F e ζ x) z) 2 volume) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_bound_on hKc hKd ((continuousOn_sqrt_frameNormSq e).mul
    ((continuousOn_cw2 hρ).mono (dom_subset_U e)))
  refine tendsto_zero_of_le_const_mul (C := C) hc fun m =>
    eLpNorm_le_restrict (C := C) hD.measurableSet ?_ ?_
  · intro z hz
    have h1 : chartTheta (T.pW ρ e) (hs m) z = 0 :=
      chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport
        fun h => hz (hsD m h))
    have h2 : T.f0 ρ F e ζ x z = 0 := f0_eq_zero_of_notMem F x fun h => hz (hζD h)
    rw [AFp_eq_zero h1, AFp_eq_zero h2, mul_zero, sub_zero]
  · intro z hz
    have hzd := hKd (hDK hz)
    rw [AFp, AFp, indicator_of_mem hzd, indicator_of_mem hzd, ← mul_sub, ← mul_sub, norm_mul,
      norm_mul, norm_inv_uc ((T.mem_dom).mp hzd).1, Complex.norm_real,
      Real.norm_of_nonneg (cw2_nonneg hρ z), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC z (hDK hz)) (norm_nonneg _)

omit hρ in
theorem SFp_eq_zero {e : AtlasFrame T.L} {β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {z : ComplexModel n} (hz : β z = 0) : T.SFp ρ e β z = 0 := by
  by_cases h : z ∈ T.dom e
  · simp [SFp, indicator_of_mem h, hz, flat2_zero]
  · simp [SFp, indicator_of_notMem h]

theorem continuousOn_kS (e : AtlasFrame T.L) :
    ContinuousOn (fun z => Real.sqrt (frameNormSq T.L e z) * T.sw ρ z *
      ((n * n : ℝ) * mnorm (Bi T.omega T.r z) ^ 2)) (T.dom e) :=
  ((continuousOn_sqrt_frameNormSq e).mul ((continuousOn_sw hρ).mono (dom_subset_U e))).mul
    (continuousOn_const.mul (((continuous_mnorm.comp_continuousOn
      (continuousOn_Bi T.isOpen_U T.kahler)).mono (dom_subset_U e)).pow 2))

/-- **Convergence of the `S`-pieces.** -/
theorem tendsto_SFp_piece (x : ComplexModel n → ComplexModel n)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} {D K : Set (ComplexModel n)} (hD : IsOpen D)
    (hζD : tsupport ζ ⊆ D) (hKc : IsCompact K) (hDK : D ⊆ K) (hKd : K ⊆ T.dom e)
    {hs : ℕ → ComplexModel n → ComplexModel n} (hsT : ∀ m, ContDiff ℝ ∞ (hs m))
    (hsD : ∀ m, tsupport (hs m) ⊆ D) (hfS : ∀ j k, MemLp (T.fS ρ e ζ x j k) 2 volume)
    (hc : ∀ j k, Tendsto (fun m => eLpNorm (fun z => sigmaDbar T.omega T.r (hs m) z j k -
      T.fS ρ e ζ x j k z) 2 (volume.restrict D)) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun z => (uc e z)⁻¹ • T.SFp ρ e (sigmaDbar T.omega T.r (hs m)) z -
      (uc e z)⁻¹ • T.SFp ρ e (fun z => Matrix.of fun j k => T.fS ρ e ζ x j k z) z) 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_bound_on hKc hKd (continuousOn_kS hρ e)
  have hDU : D ⊆ T.U := (hDK.trans hKd).trans (dom_subset_U e)
  set G : Fin n × Fin n → ℕ → ComplexModel n → ℂ := fun p m z =>
    sigmaDbar T.omega T.r (hs m) z p.1 p.2 - T.fS ρ e ζ x p.1 p.2 z
  have hG : ∀ p m, AEStronglyMeasurable (G p m) (volume.restrict D) := by
    intro p m
    have h1 : ContinuousOn (sigmaDbar T.omega T.r (hs m)) D :=
      continuousOn_sigmaDbar hD hDU (hsT m).contDiffOn
    exact ((continuousOn_entry h1 p.1 p.2).aestronglyMeasurable hD.measurableSet).sub
      (hfS p.1 p.2).1.restrict
  have hsum : Tendsto (fun m => eLpNorm (fun z => ∑ p : Fin n × Fin n, ‖G p m z‖) 2
      (volume.restrict D)) atTop (𝓝 0) :=
    tendsto_eLpNorm_sum' Finset.univ hG (fun m z => by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)])
      fun p _ => hc p.1 p.2
  refine tendsto_zero_of_le_const_mul (C := C) hsum fun m =>
    eLpNorm_le_restrict (C := C) hD.measurableSet ?_ ?_
  · intro z hz
    have h1 : sigmaDbar T.omega T.r (hs m) z = 0 :=
      sigmaDbar_zero (eventuallyEq_zero_of_notMem_tsupport fun h => hz (hsD m h))
    have h2 : (Matrix.of fun j k => T.fS ρ e ζ x j k z) = 0 := by
      ext j k; simp [fS_eq_zero_of_notMem x (fun h => hz (hζD h)) j k]
    rw [SFp_eq_zero h1, SFp_eq_zero h2, smul_zero, sub_self]
  · intro z hz
    have hzd := hKd (hDK hz)
    have hzb := ((T.mem_dom).mp hzd).1
    have hdiff : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z * A * (Bi T.omega T.r z)ᵀ)) -
          flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z * B * (Bi T.omega T.r z)ᵀ)) =
        ((T.sw ρ z : ℝ) : ℂ) • flat2 (Bi T.omega T.r z * (A - B) * (Bi T.omega T.r z)ᵀ) := by
      intro A B
      ext p
      simp only [flat2, PiLp.sub_apply, PiLp.smul_apply, Matrix.smul_apply, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.sub_apply, smul_eq_mul]
      ring
    rw [SFp, SFp, indicator_of_mem hzd, indicator_of_mem hzd, ← smul_sub, hdiff, norm_smul,
      norm_smul, norm_inv_uc hzb, Complex.norm_real, Real.norm_of_nonneg (sw_pos hρ z).le,
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    have hb := norm_flat2_mul_le (Bi T.omega T.r z)
      (sigmaDbar T.omega T.r (hs m) z - Matrix.of fun j k => T.fS ρ e ζ x j k z)
    have hS : ∑ a, ∑ c, ‖(sigmaDbar T.omega T.r (hs m) z -
        Matrix.of fun j k => T.fS ρ e ζ x j k z) a c‖ = ∑ p : Fin n × Fin n, ‖G p m z‖ := by
      rw [Fintype.sum_prod_type]
      rfl
    rw [hS] at hb
    have hC' := hC z (hDK hz)
    have h0 : 0 ≤ ∑ p : Fin n × Fin n, ‖G p m z‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsq : 0 ≤ Real.sqrt (frameNormSq T.L e z) * T.sw ρ z :=
      mul_nonneg (Real.sqrt_nonneg _) (sw_pos hρ z).le
    calc Real.sqrt (frameNormSq T.L e z) * (T.sw ρ z * ‖flat2 (Bi T.omega T.r z *
          (sigmaDbar T.omega T.r (hs m) z - Matrix.of fun j k => T.fS ρ e ζ x j k z) *
            (Bi T.omega T.r z)ᵀ)‖)
        ≤ Real.sqrt (frameNormSq T.L e z) * (T.sw ρ z * ((n * n : ℝ) *
          (mnorm (Bi T.omega T.r z) ^ 2 * ∑ p : Fin n × Fin n, ‖G p m z‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (sw_pos hρ z).le)
            (Real.sqrt_nonneg _)
      _ = (Real.sqrt (frameNormSq T.L e z) * T.sw ρ z *
          ((n * n : ℝ) * mnorm (Bi T.omega T.r z) ^ 2)) * ∑ p : Fin n × Fin n, ‖G p m z‖ := by
          ring
      _ ≤ C * ∑ p : Fin n × Fin n, ‖G p m z‖ := mul_le_mul_of_nonneg_right hC' h0

/-- **Convergence of the data pieces.** -/
theorem tendsto_repF_piece (x : ComplexModel n → ComplexModel n) {e : AtlasFrame T.L}
    {ζ : ComplexModel n → ℝ} {K : Set (ComplexModel n)} (hKc : IsCompact K) (hKd : K ⊆ T.dom e)
    (hζK : tsupport ζ ⊆ K) {hs : ℕ → ComplexModel n → ComplexModel n}
    (hsK : ∀ m, tsupport (hs m) ⊆ K)
    (hc : Tendsto (fun m => eLpNorm (fun z => hs m z - ofComps (T.wsys ρ e ζ x) z) 2 volume)
      atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun z => T.repF ρ e (hs m) z -
      T.repF ρ e (ofComps (T.wsys ρ e ζ x)) z) 2 volume) atTop (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := exists_kap_bound hρ hKc hKd
  refine tendsto_zero_of_le_const_mul (C := C) hc fun m => ?_
  have h1 : (fun z => T.repF ρ e (hs m) z - T.repF ρ e (ofComps (T.wsys ρ e ζ x)) z) =
      T.repF ρ e (fun z => hs m z - ofComps (T.wsys ρ e ζ x) z) := by
    rw [show (fun z => hs m z - ofComps (T.wsys ρ e ζ x) z) = hs m - ofComps (T.wsys ρ e ζ x)
      from rfl, repF_sub]
    rfl
  rw [h1]
  refine eLpNorm_repF_le hρ hC fun z hz => ?_
  have h2 : hs m z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hsK m h)
  have h3 : ofComps (T.wsys ρ e ζ x) z = 0 := by
    ext i
    simp [ofComps, wsys, image_eq_zero_of_notMem_tsupport fun h => hz (hζK h)]
  rw [h2, h3, sub_zero]

theorem memLp_AFp_test {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U chart0 e h) :
    MemLp (fun z => (uc e z)⁻¹ * T.AFp ρ e (chartTheta (T.pW ρ e) h) z) 2 volume := by
  have hd : tsupport h ⊆ T.dom e := hh.2.2
  have hO := T.isOpen_dom e
  have h0 : ∀ z ∉ tsupport h, T.AFp ρ e (chartTheta (T.pW ρ e) h) z = 0 := fun z hz =>
    AFp_eq_zero (chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport hz))
  have hcont : Continuous (T.AFp ρ e (chartTheta (T.pW ρ e) h)) := by
    refine continuous_of_continuousOn_of_eq_zero' hO ?_ (isClosed_tsupport h) hd h0
    have h1 : ContinuousOn (fun z => ((T.cw2 ρ z : ℝ) : ℂ) * chartTheta (T.pW ρ e) h z) (T.dom e) :=
      (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_cw2 hρ).mono
        (dom_subset_U e))).mul (continuousOn_chartTheta' hO (T.contDiffOn_pW hρ e)
          hh.1.contDiffOn)
    exact h1.congr fun z hz => by simp [AFp, indicator_of_mem hz]
  obtain ⟨C, hC⟩ := exists_bound_on hh.2.1 hd ((continuousOn_sqrt_frameNormSq e).mul
    (continuous_norm.comp hcont).continuousOn)
  refine memLp_of_bound_on_compact hh.2.1 ((measurable_uc e).inv.aestronglyMeasurable.mul
    hcont.aestronglyMeasurable) (C := C) (fun z hz => ?_) fun z hz => by rw [h0 z hz, mul_zero]
  rw [norm_mul, norm_inv_uc ((T.mem_dom).mp (hd hz)).1]
  exact hC z hz

theorem memLp_AFp_f0 (F : T.FrameFamily) (x : ComplexModel n → ComplexModel n)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} {K : Set (ComplexModel n)} (hKc : IsCompact K)
    (hKd : K ⊆ T.dom e) (hζK : tsupport ζ ⊆ K) (hf0 : MemLp (T.f0 ρ F e ζ x) 2 volume) :
    MemLp (fun z => (uc e z)⁻¹ * T.AFp ρ e (T.f0 ρ F e ζ x) z) 2 volume := by
  have hO := T.isOpen_dom e
  obtain ⟨C, hC⟩ := exists_bound_on hKc hKd ((continuousOn_sqrt_frameNormSq e).mul
    ((continuousOn_cw2 hρ).mono (dom_subset_U e)))
  have hm : AEStronglyMeasurable (T.AFp ρ e (T.f0 ρ F e ζ x)) volume := by
    have hr : T.AFp ρ e (T.f0 ρ F e ζ x) = (T.dom e).indicator
        (fun z => ((T.cw2 ρ z : ℝ) : ℂ) * T.f0 ρ F e ζ x z) := rfl
    rw [hr]
    refine (aestronglyMeasurable_indicator_iff hO.measurableSet).mpr ?_
    exact ((Complex.continuous_ofReal.comp_continuousOn ((continuousOn_cw2 hρ).mono
      (dom_subset_U e))).aestronglyMeasurable hO.measurableSet).mul hf0.1.restrict
  refine hf0.of_le_mul (c := max C 0) ((measurable_uc e).inv.aestronglyMeasurable.mul hm)
    (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · have hzd := hKd hz
    rw [AFp, indicator_of_mem hzd, norm_mul, norm_mul, norm_inv_uc ((T.mem_dom).mp hzd).1,
      Complex.norm_real, Real.norm_of_nonneg (cw2_nonneg hρ z), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _)
  · have h3 := f0_eq_zero_of_notMem (ρ := ρ) (e := e) F x fun h => hz (hζK h)
    rw [AFp_eq_zero h3, h3]
    simp

theorem memLp_SFp_test {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U chart0 e h) :
    MemLp (fun z => (uc e z)⁻¹ • T.SFp ρ e (sigmaDbar T.omega T.r h) z) 2 volume := by
  have hd : tsupport h ⊆ T.dom e := hh.2.2
  have hO := T.isOpen_dom e
  have h0 : ∀ z ∉ tsupport h, T.SFp ρ e (sigmaDbar T.omega T.r h) z = 0 := fun z hz =>
    SFp_eq_zero (sigmaDbar_zero (eventuallyEq_zero_of_notMem_tsupport hz))
  have hcont : Continuous (T.SFp ρ e (sigmaDbar T.omega T.r h)) := by
    refine continuous_of_continuousOn_of_eq_zero' hO ?_ (isClosed_tsupport h) hd h0
    have h1 : ContinuousOn (fun z => flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z *
        sigmaDbar T.omega T.r h z * (Bi T.omega T.r z)ᵀ))) (T.dom e) :=
      continuous_flat2.comp_continuousOn ((Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_sw hρ).mono (dom_subset_U e))).smul (continuousOn_mul_conj
          ((continuousOn_Bi T.isOpen_U T.kahler).mono (dom_subset_U e))
          (continuousOn_sigmaDbar hO (dom_subset_U e) hh.1.contDiffOn)))
    exact h1.congr fun z hz => by simp [SFp, indicator_of_mem hz]
  obtain ⟨C, hC⟩ := exists_bound_on hh.2.1 hd ((continuousOn_sqrt_frameNormSq e).mul
    (continuous_norm.comp hcont).continuousOn)
  refine memLp_of_bound_on_compact hh.2.1 ((measurable_uc e).inv.aestronglyMeasurable.smul
    hcont.aestronglyMeasurable) (C := C) (fun z hz => ?_) fun z hz => by rw [h0 z hz, smul_zero]
  rw [norm_smul, norm_inv_uc ((T.mem_dom).mp (hd hz)).1]
  exact hC z hz

theorem memLp_SFp_fS (x : ComplexModel n → ComplexModel n) {e : AtlasFrame T.L}
    {ζ : ComplexModel n → ℝ} {K : Set (ComplexModel n)} (hKc : IsCompact K) (hKd : K ⊆ T.dom e)
    (hζK : tsupport ζ ⊆ K) (hfS : ∀ j k, MemLp (T.fS ρ e ζ x j k) 2 volume) :
    MemLp (fun z => (uc e z)⁻¹ • T.SFp ρ e (fun z => Matrix.of fun j k => T.fS ρ e ζ x j k z) z)
      2 volume := by
  have hO := T.isOpen_dom e
  obtain ⟨C, hC⟩ := exists_bound_on hKc hKd (continuousOn_kS hρ e)
  set g : ComplexModel n → ℝ := fun z => ∑ a, ∑ c, ‖T.fS ρ e ζ x a c z‖
  have hg : MemLp g 2 volume :=
    memLp_finsetSum _ fun a _ => memLp_finsetSum _ fun c _ => (hfS a c).norm
  have hm : AEStronglyMeasurable (T.SFp ρ e (fun z => Matrix.of fun j k => T.fS ρ e ζ x j k z))
      volume := by
    have hr : T.SFp ρ e (fun z => Matrix.of fun j k => T.fS ρ e ζ x j k z) = (T.dom e).indicator
        (fun z => flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z *
          (Matrix.of fun j k => T.fS ρ e ζ x j k z) * (Bi T.omega T.r z)ᵀ))) := rfl
    rw [hr]
    refine (aestronglyMeasurable_indicator_iff hO.measurableSet).mpr ?_
    refine aestronglyMeasurable_flat2 fun j k => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hsw : AEStronglyMeasurable (fun z => ((T.sw ρ z : ℝ) : ℂ)) (volume.restrict (T.dom e)) :=
      (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_sw hρ).mono
        (dom_subset_U e))).aestronglyMeasurable hO.measurableSet
    refine hsw.mul (aestronglyMeasurable_conj_mul (fun a b => ?_) (fun a b => ?_) j k)
    · exact ((continuousOn_entry (continuousOn_Bi T.isOpen_U T.kahler) a b).mono
        (dom_subset_U e)).aestronglyMeasurable hO.measurableSet
    · simpa using (hfS a b).1.restrict
  refine hg.of_le_mul (c := max C 0) ((measurable_uc e).inv.aestronglyMeasurable.smul hm)
    (Eventually.of_forall fun z => ?_)
  have hg0 : 0 ≤ g z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_of_nonneg hg0]
  by_cases hz : z ∈ K
  · have hzd := hKd hz
    rw [SFp, indicator_of_mem hzd, norm_smul, norm_inv_uc ((T.mem_dom).mp hzd).1, flat2_smul,
      norm_smul, Complex.norm_real, Real.norm_of_nonneg (sw_pos hρ z).le]
    have hb := norm_flat2_mul_le (Bi T.omega T.r z) (Matrix.of fun j k => T.fS ρ e ζ x j k z)
    simp only [of_apply] at hb
    calc Real.sqrt (frameNormSq T.L e z) * (T.sw ρ z * ‖flat2 (Bi T.omega T.r z *
          (Matrix.of fun j k => T.fS ρ e ζ x j k z) * (Bi T.omega T.r z)ᵀ)‖)
        ≤ Real.sqrt (frameNormSq T.L e z) * (T.sw ρ z * ((n * n : ℝ) *
          (mnorm (Bi T.omega T.r z) ^ 2 * g z))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (sw_pos hρ z).le)
            (Real.sqrt_nonneg _)
      _ = (Real.sqrt (frameNormSq T.L e z) * T.sw ρ z *
          ((n * n : ℝ) * mnorm (Bi T.omega T.r z) ^ 2)) * g z := by ring
      _ ≤ max C 0 * g z := mul_le_mul_of_nonneg_right ((hC z hz).trans (le_max_left _ _)) hg0
  · have h2 : (Matrix.of fun j k => T.fS ρ e ζ x j k z) = 0 := by
      ext j k; simp [fS_eq_zero_of_notMem x (fun h => hz (hζK h)) j k]
    rw [SFp_eq_zero h2, smul_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) hg0

/-! ### One cut-off level -/

variable (T ρ) in
/-- The `T*`-representative of the cut-off `χ v` of the projected field. -/
def Alim (F : T.FrameFamily) (χ : ComplexModel n → ℝ) (x : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  ((T.U.indicator (T.cw2 ρ) z : ℝ) : ℂ) * ((χ z : ℂ) * T.Teps ρ F z -
    ⟪dbarV (fun y => (χ y : ℂ)) z, T.Weps ρ x z⟫_ℂ)

variable (T ρ) in
/-- The `S`-representative `∂̄χ ∧ σ^♭ v` of the cut-off of the projected field. -/
def Slim (χ : ComplexModel n → ℝ) (x : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  T.U.indicator (fun z => flat2 (((T.sw ρ z : ℝ) : ℂ) • (Bi T.omega T.r z *
    wedgeM (dbarV (fun y => (χ y : ℂ)) z) (mv (sT T.omega T.r z) (T.Weps ρ x z)) *
      (Bi T.omega T.r z)ᵀ))) z

omit hρ in
theorem sum_derivs {N : ℕ} {ζ : Fin N → ComplexModel n → ℝ} {χ : ComplexModel n → ℝ}
    (hζ : ∀ i, ContDiff ℝ ∞ (ζ i)) (hsum : ∀ z, ∑ i, ζ i z = χ z) (z : ComplexModel n) :
    (∀ l, dDir (coordVec l) (fun y => (χ y : ℂ)) z =
      ∑ i, dDir (coordVec l) (fun y => (ζ i y : ℂ)) z) ∧
    dbarV (fun y => (χ y : ℂ)) z = ∑ i, dbarV (fun y => (ζ i y : ℂ)) z := by
  have hfun : (fun y => (χ y : ℂ)) = fun y => ∑ i, (ζ i y : ℂ) := by
    funext y; rw [← hsum y]; push_cast; rfl
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin N)), DifferentiableAt ℝ (fun y => (ζ i y : ℂ)) z :=
    fun i _ => ((Complex.ofRealCLM.contDiff.comp (hζ i)).differentiable (by simp)) z
  refine ⟨fun l => ?_, ?_⟩
  · rw [hfun, dDir_finset_sum_fun' _ hd]
  · ext l
    simp only [dbarV, PiLp.toLp_apply, euclid_sum_apply]
    rw [hfun, dbarDir_finset_sum_fun _ hd]

/-- **One cut-off level** (`claude-tl2-dens:level`): for a cut-off `χ` there are test families
whose data pairing, `T*`-energy and `S`-energy converge to those of `χ v`. -/
theorem exists_level (F : T.FrameFamily) (v : H2 n)
    (hW1 : ∀ (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) ψ →
      ∀ j k : Fin n, ∫ z, (T.dom e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
        conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z = 0)
    (hW2 : ∀ (e : AtlasFrame T.L) (u : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) u →
      ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
        ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z)
    {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ T.U) :
    ∃ Fs : ℕ → T.FrameFamily,
      Tendsto (fun m => (Fs m).data ρ) atTop (𝓝 (∫ z, (χ z : ℂ) * ⟪v z, T.ydF ρ z⟫_ℂ)) ∧
      Tendsto (fun m => (Fs m).energy ρ) atTop (𝓝 (∫ z, ‖T.Alim ρ F χ v z‖ ^ 2)) ∧
      Tendsto (fun m => (Fs m).senergy ρ) atTop (𝓝 ((1 / 2 : ℝ) * ∫ z, ‖T.Slim ρ χ v z‖ ^ 2)) ∧
      MemLp (T.Alim ρ F χ v) 2 volume ∧ MemLp (T.Slim ρ χ v) 2 volume := by
  obtain ⟨N, e, ζ, D, hζ, hζc, hDo, hζD, hK, hsum⟩ := exists_localization hχ hχc hχU
  choose K hKc hDK hKd using hK
  have hζK : ∀ i, tsupport (ζ i) ⊆ K i := fun i => (hζD i).trans (hDK i)
  have hζd : ∀ i, tsupport (ζ i) ⊆ T.dom (e i) := fun i => (hζK i).trans (hKd i)
  have happ := fun i => exists_approx hρ F v hW1 hW2 (hζ i) (hζc i) (hDo i) (hζD i)
    ((hDK i).trans (hKd i))
  choose hs hsT hsD hc1 hc2 hc3 hf0 hfS using happ
  let Fs : ℕ → T.FrameFamily := fun m =>
    ⟨Fin N, Finset.univ, e, fun i => hs i m, fun i => hsT i m⟩
  have hder := sum_derivs hζ hsum
  -- bounds for the localizing functions
  have hζb : ∀ i, ∃ M, 0 ≤ M ∧ ∀ z, ‖ζ i z‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := (hζc i).isCompact.exists_bound_of_continuousOn (hζ i).continuous.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ tsupport (ζ i)
    · exact (hM z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]; exact le_max_right _ _
  have hAeq : ∀ z, T.Alim ρ F χ v z =
      ∑ i, (uc (e i) z)⁻¹ * T.AFp ρ (e i) (T.f0 ρ F (e i) (ζ i) v) z := by
    intro z
    rw [Finset.sum_congr rfl fun i _ => uc_AFp_f0 hρ F v (hζ i) (hζd i) z, ← Finset.mul_sum, Alim]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, inner_eq_sum]
    have h1 : ((χ z : ℝ) : ℂ) = ∑ i, (ζ i z : ℂ) := by rw [← hsum z]; push_cast; rfl
    have h2 : ∑ l, conj ((dbarV (fun y => (χ y : ℂ)) z) l) * T.Weps ρ v z l =
        ∑ i, ∑ l, dDir (coordVec l) (fun y => (ζ i y : ℂ)) z * T.Weps ρ v z l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_mul, ← (hder z).1 l]
      simp only [dbarV, PiLp.toLp_apply, conj_dbarDir_ofReal (hχ.differentiable (by simp) z)]
    rw [h1, h2]
  have hAl : MemLp (T.Alim ρ F χ v) 2 volume := by
    rw [show T.Alim ρ F χ v = fun z => ∑ i, (uc (e i) z)⁻¹ *
        T.AFp ρ (e i) (T.f0 ρ F (e i) (ζ i) v) z from funext hAeq]
    exact memLp_finsetSum _ fun i _ => memLp_AFp_f0 hρ F v (hKc i) (hKd i) (hζK i) (hf0 i)
  have hSeq : ∀ z, T.Slim ρ χ v z = ∑ i, (uc (e i) z)⁻¹ •
      T.SFp ρ (e i) (fun z => Matrix.of fun j k => T.fS ρ (e i) (ζ i) v j k z) z := by
    intro z
    rw [Finset.sum_congr rfl fun i _ => uc_SFp_fS hρ v (hζd i) z, Slim]
    by_cases hz : z ∈ T.U
    · simp only [indicator_of_mem hz]
      rw [(hder z).2, wedgeM_sum_left, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum,
        flat2_sum]
    · simp [indicator_of_notMem hz]
  have hSl : MemLp (T.Slim ρ χ v) 2 volume := by
    rw [show T.Slim ρ χ v = fun z => ∑ i, (uc (e i) z)⁻¹ •
        T.SFp ρ (e i) (fun z => Matrix.of fun j k => T.fS ρ (e i) (ζ i) v j k z) z
      from funext hSeq]
    exact memLp_finsetSum _ fun i _ => memLp_SFp_fS hρ v (hKc i) (hKd i) (hζK i) (hfS i)
  refine ⟨Fs, ?_, ?_, ?_, hAl, hSl⟩
  · -- the data pairing
    have hwL : ∀ i, MemLp (T.repF ρ (e i) (ofComps (T.wsys ρ (e i) (ζ i) v))) 2 volume := by
      intro i
      have hfun : T.repF ρ (e i) (ofComps (T.wsys ρ (e i) (ζ i) v)) = fun z => (ζ i z : ℂ) • v z :=
        funext (repF_wsys hρ v (hζd i))
      rw [hfun]
      obtain ⟨M, hM0, hM⟩ := hζb i
      refine (Lp.memLp v).of_le_mul (c := M) (((Complex.continuous_ofReal.comp
        (hζ i).continuous).aestronglyMeasurable).smul (Lp.aestronglyMeasurable v))
        (Eventually.of_forall fun z => ?_)
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _)
    have hR : Tendsto (fun m => repFam hρ (Fs m)) atTop (𝓝 (∑ i, (hwL i).toLp _)) := by
      change Tendsto (fun m => ∑ i, (memLp_piece hρ (hsT i m)).toLp _) atTop _
      refine tendsto_finsetSum _ fun i _ => ?_
      exact tendsto_toLp_of_eLpNorm (fun m => memLp_piece hρ (hsT i m)) (hwL i)
        (tendsto_repF_piece hρ v (hKc i) (hKd i) (hζK i) (fun m => (hsD i m).trans (hDK i))
          (hc1 i))
    have hl := (hR.inner (tendsto_const_nhds (x := (memLp_ydF hρ).toLp (T.ydF ρ)))).congr
      fun m => inner_repFam_yd hρ (Fs m)
    convert hl using 2
    have hI : Integrable (fun z => ⟪v z, T.ydF ρ z⟫_ℂ) := by
      refine (L2.integrable_inner (𝕜 := ℂ) v ((memLp_ydF hρ).toLp (T.ydF ρ))).congr ?_
      filter_upwards [(memLp_ydF hρ).coeFn_toLp] with z hz
      rw [hz]
    have hIi : ∀ i, Integrable (fun z => (ζ i z : ℂ) * ⟪v z, T.ydF ρ z⟫_ℂ) := by
      intro i
      obtain ⟨M, -, hM⟩ := hζb i
      exact hI.bdd_mul (c := M) ((Complex.continuous_ofReal.comp
        (hζ i).continuous).aestronglyMeasurable) (Eventually.of_forall fun z => by
          rw [Complex.norm_real]; exact hM z)
    have hterm : ∀ i, ⟪(hwL i).toLp _, (memLp_ydF hρ).toLp (T.ydF ρ)⟫_ℂ =
        ∫ z, (ζ i z : ℂ) * ⟪v z, T.ydF ρ z⟫_ℂ := by
      intro i
      rw [inner_toLp_toLp]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [repF_wsys hρ v (hζd i), inner_smul_left, Complex.conj_ofReal]
    rw [sum_inner, Finset.sum_congr rfl fun i _ => hterm i,
      ← integral_finsetSum _ fun i _ => hIi i]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [← Finset.sum_mul]
    congr 1
    rw [← hsum z]; push_cast; rfl
  · -- the `T*`-energy
    have hAF : ∀ m, MemLp (T.AF ρ (Fs m)) 2 volume := fun m =>
      memLp_finsetSum _ fun i _ => memLp_AFp_test hρ (hsT i m)
    simp only [energy_eq hρ]
    refine tendsto_integral_norm_sq hAF hAl ?_
    refine tendsto_eLpNorm_sum' Finset.univ (G := fun i m z =>
      (uc (e i) z)⁻¹ * T.AFp ρ (e i) (chartTheta (T.pW ρ (e i)) (hs i m)) z -
        (uc (e i) z)⁻¹ * T.AFp ρ (e i) (T.f0 ρ F (e i) (ζ i) v) z)
      (fun i m => (memLp_AFp_test hρ (hsT i m)).1.sub
        (memLp_AFp_f0 hρ F v (hKc i) (hKd i) (hζK i) (hf0 i)).1)
      (fun m z => ?_) fun i _ => tendsto_AFp_piece hρ F v (hDo i) (hζD i) (hKc i) (hDK i)
        (hKd i) (hsD i) (hc2 i)
    rw [hAeq]
    have hA : T.AF ρ (Fs m) z = ∑ i, (uc (e i) z)⁻¹ *
        T.AFp ρ (e i) (chartTheta (T.pW ρ (e i)) (hs i m)) z := rfl
    rw [hA, ← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  · -- the `S`-energy
    have hSF : ∀ m, MemLp (T.SF ρ (Fs m)) 2 volume := fun m =>
      memLp_finsetSum _ fun i _ => memLp_SFp_test hρ (hsT i m)
    simp only [senergy_eq hρ, integral_const_mul]
    refine Tendsto.const_mul _ (tendsto_integral_norm_sq hSF hSl ?_)
    refine tendsto_eLpNorm_sum' Finset.univ (G := fun i m z =>
      (uc (e i) z)⁻¹ • T.SFp ρ (e i) (sigmaDbar T.omega T.r (hs i m)) z -
        (uc (e i) z)⁻¹ • T.SFp ρ (e i) (fun z => Matrix.of fun j k => T.fS ρ (e i) (ζ i) v j k z) z)
      (fun i m => (memLp_SFp_test hρ (hsT i m)).1.sub
        (memLp_SFp_fS hρ v (hKc i) (hKd i) (hζK i) (hfS i)).1)
      (fun m z => ?_) fun i _ => tendsto_SFp_piece hρ v (hDo i) (hζD i) (hKc i) (hDK i)
        (hKd i) (fun m => (hsT i m).1) (hsD i) (hfS i) (hc3 i)
    rw [hSeq]
    have hS : T.SF ρ (Fs m) z = ∑ i, (uc (e i) z)⁻¹ •
        T.SFp ρ (e i) (sigmaDbar T.omega T.r (hs i m)) z := rfl
    rw [hS, ← Finset.sum_sub_distrib]
    exact norm_sum_le _ _

/-! ### Letting the cut-off tend to `1` -/

omit hρ in
theorem AF_eq (F : T.FrameFamily) (z : ComplexModel n) :
    T.AF ρ F z = ((T.U.indicator (T.cw2 ρ) z : ℝ) : ℂ) * T.Teps ρ F z := by
  rw [AF, Teps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hzi : z ∈ T.dom (F.e i)
  · rw [AFp, indicator_of_mem hzi, indicator_of_mem (dom_subset_U _ hzi)]; ring
  · have h0 : chartTheta (T.pW ρ (F.e i)) (F.h i) z = 0 :=
      chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport
        fun h => hzi (T.tsupport_subset_dom F.spec i h))
    rw [AFp_eq_zero h0, h0]; ring

theorem memLp_AF (F : T.FrameFamily) : MemLp (T.AF ρ F) 2 volume :=
  memLp_finsetSum _ fun i _ => memLp_AFp_test hρ (F.spec i)

/-- `‖Bi ∂̄χ‖ · s ‖Bm W(x)‖ ≤ |c| ‖x‖` for a cut-off with `|dχ|_σ ≤ c`. -/
theorem norm_cut_le {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hc : ∀ z ∈ T.U, ∀ w, fderiv ℝ χ z w ^ 2 ≤ c ^ 2 * sigmaQ T.omega T.r z w)
    (x : ComplexModel n → ComplexModel n) {z : ComplexModel n} (hz : z ∈ T.U) :
    T.sw ρ z * (‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ *
      ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖) ≤ |c| * ‖x z‖ := by
  have h1 := norm_mv_Bi_dbarV_sq_le (hχ.differentiable (by simp) z) hz (hc z hz)
  have h2 : ‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ ≤ |c| := by
    have : ‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ ^ 2 ≤ |c| ^ 2 := by
      rw [sq_abs]; nlinarith [sq_nonneg c]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg c) two_ne_zero).mp this
  have h3 : ‖x z‖ = T.sw ρ z * ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖ := by
    conv_lhs => rw [← sw_Bm_Weps hρ (x := x) hz]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (sw_pos hρ z).le]
  rw [h3]
  calc T.sw ρ z * (‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ *
        ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖)
      = ‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ *
        (T.sw ρ z * ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖) := by ring
    _ ≤ |c| * (T.sw ρ z * ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg (sw_pos hρ z).le (norm_nonneg _))

/-- The cut-off term of the `T*`-energy is `O(|dχ|_σ)`. -/
theorem norm_cut_tstar_le {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hc : ∀ z ∈ T.U, ∀ w, fderiv ℝ χ z w ^ 2 ≤ c ^ 2 * sigmaQ T.omega T.r z w) {M : ℝ}
    (hM : ∀ z ∈ T.U, T.a z + T.b z ≤ 2 * M) (x : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    ‖((T.U.indicator (T.cw2 ρ) z : ℝ) : ℂ) * ⟪dbarV (fun y => (χ y : ℂ)) z, T.Weps ρ x z⟫_ℂ‖ ≤
      Real.sqrt (2 * M) * |c| * ‖x z‖ := by
  by_cases hz : z ∈ T.U
  · rw [indicator_of_mem hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cw2_nonneg hρ z)]
    have hinner : ⟪dbarV (fun y => (χ y : ℂ)) z, T.Weps ρ x z⟫_ℂ =
        ⟪mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z),
          mv (Bm T.omega T.r z) (T.Weps ρ x z)⟫_ℂ := by
      rw [inner_mv_left, Bi_conjTranspose, mv_Bi_Bm T.isOpen_U T.kahler hz]
    rw [hinner]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z))
      (mv (Bm T.omega T.r z) (T.Weps ρ x z))
    have h2 := norm_cut_le hρ hχ hc x hz
    have h3 : Real.sqrt (T.a z + T.b z) ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt (hM z hz)
    unfold cw2
    calc Real.sqrt (T.a z + T.b z) * T.sw ρ z * ‖⟪mv (Bi T.omega T.r z)
          (dbarV (fun y => (χ y : ℂ)) z), mv (Bm T.omega T.r z) (T.Weps ρ x z)⟫_ℂ‖
        ≤ Real.sqrt (2 * M) * (T.sw ρ z * (‖mv (Bi T.omega T.r z)
          (dbarV (fun y => (χ y : ℂ)) z)‖ * ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖)) := by
          rw [mul_assoc]
          exact mul_le_mul h3 (mul_le_mul_of_nonneg_left h1 (sw_pos hρ z).le)
            (mul_nonneg (sw_pos hρ z).le (norm_nonneg _)) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (2 * M) * (|c| * ‖x z‖) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [indicator_of_notMem hz]
    simp only [Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

/-- The `S`-representative of the cut-off is `O(|dχ|_σ)`. -/
theorem norm_Slim_le {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hc : ∀ z ∈ T.U, ∀ w, fderiv ℝ χ z w ^ 2 ≤ c ^ 2 * sigmaQ T.omega T.r z w)
    (x : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    ‖T.Slim ρ χ x z‖ ≤ 2 * |c| * ‖x z‖ := by
  by_cases hz : z ∈ T.U
  · rw [Slim, indicator_of_mem hz, flat2_smul, mul_wedgeM_mul_transpose, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg (sw_pos hρ z).le]
    have hB : mv (Bi T.omega T.r z) (mv (sT T.omega T.r z) (T.Weps ρ x z)) =
        mv (Bm T.omega T.r z) (T.Weps ρ x z) := by
      rw [← mv_Bm_Bm T.isOpen_U T.kahler hz, mv_Bi_Bm T.isOpen_U T.kahler hz]
    rw [hB]
    have h1 := norm_flat2_wedge_le (mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z))
      (mv (Bm T.omega T.r z) (T.Weps ρ x z))
    have h2 := norm_cut_le hρ hχ hc x hz
    calc T.sw ρ z * ‖flat2 (wedgeM (mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z))
          (mv (Bm T.omega T.r z) (T.Weps ρ x z)))‖
        ≤ T.sw ρ z * (2 * (‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ *
          ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖)) :=
          mul_le_mul_of_nonneg_left h1 (sw_pos hρ z).le
      _ = 2 * (T.sw ρ z * (‖mv (Bi T.omega T.r z) (dbarV (fun y => (χ y : ℂ)) z)‖ *
          ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖)) := by ring
      _ ≤ 2 * (|c| * ‖x z‖) := by linarith
      _ = _ := by ring
  · rw [Slim, indicator_of_notMem hz, norm_zero]
    positivity

omit hρ in
/-- **The density lemma on `ℂⁿ`** (`claude-tl2-dens:main`, `claude-tl2-main:sigma-density`):
every twisted datum on `ℂⁿ` satisfies `SigmaGraphDensity`. -/
theorem sigmaGraphDensity (T : TwistedDatum n (ComplexModel n)) : T.SigmaGraphDensity := by
  intro ρ hρ F ε hε
  obtain ⟨v, hW1, hW2, hW3⟩ := exists_v hρ F
  obtain ⟨χ, C, hχ, hχc, hχU, hχ01, hχlim, hχd⟩ := exists_cutoffs T
  obtain ⟨mm, M, -, hb⟩ := T.bounds
  have hM : ∀ z ∈ T.U, T.a z + T.b z ≤ 2 * M := fun z hz => by
    linarith [(hb z hz).2.1, (hb z hz).2.2.2]
  set c : ℕ → ℝ := fun k => C / ((k : ℝ) + 1) with hc_def
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [hc_def, div_eq_mul_inv] using this
  have hca : Tendsto (fun k => |c k|) atTop (𝓝 0) := by simpa using hc0.abs
  have hlev := fun k => exists_level hρ F v hW1 hW2 (hχ k) (hχc k) (hχU k)
  have hAl : ∀ k, MemLp (T.Alim ρ F (χ k) v) 2 volume := fun k => (hlev k).choose_spec.2.2.2.1
  have hSl : ∀ k, MemLp (T.Slim ρ (χ k) v) 2 volume := fun k => (hlev k).choose_spec.2.2.2.2
  have hχb : ∀ k z, ‖((χ k z : ℝ) : ℂ)‖ ≤ 1 := fun k z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hχ01 k z).1]; exact (hχ01 k z).2
  -- the data pairings
  have hI : Integrable (fun z => ⟪v z, T.ydF ρ z⟫_ℂ) := by
    refine (L2.integrable_inner (𝕜 := ℂ) v ((memLp_ydF hρ).toLp (T.ydF ρ))).congr ?_
    filter_upwards [(memLp_ydF hρ).coeFn_toLp] with z hz
    rw [hz]
  have hdk : Tendsto (fun k => ∫ z, (χ k z : ℂ) * ⟪v z, T.ydF ρ z⟫_ℂ) atTop (𝓝 (F.data ρ)) := by
    rw [← hW3, inner_toLp_right]
    refine tendsto_integral_of_dominated_convergence (fun z => ‖⟪v z, T.ydF ρ z⟫_ℂ‖)
      (fun k => ((Complex.continuous_ofReal.comp (hχ k).continuous).aestronglyMeasurable).mul
        hI.1) hI.norm (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχb k z)
    · by_cases hz : z ∈ T.U
      · have := ((Complex.continuous_ofReal.tendsto _).comp (hχlim z hz)).mul_const
          (⟪v z, T.ydF ρ z⟫_ℂ)
        simpa using this
      · have h0 : T.ydF ρ z = 0 := by simp [ydF, indicator_of_notMem hz]
        simp [h0]
  -- the `T*`-energies
  have hek : Tendsto (fun k => ∫ z, ‖T.Alim ρ F (χ k) v z‖ ^ 2) atTop (𝓝 (F.energy ρ)) := by
    rw [energy_eq hρ F]
    refine tendsto_integral_norm_sq hAl (memLp_AF hρ F) ?_
    have hAFm := memLp_AF hρ F
    have hm : ∀ k, MemLp (fun z => ((χ k z : ℂ) - 1) * T.AF ρ F z) 2 volume := fun k =>
      hAFm.of_le_mul (c := 2) ((((Complex.continuous_ofReal.comp (hχ k).continuous).sub
        continuous_const).aestronglyMeasurable).mul hAFm.1) (Eventually.of_forall fun z => by
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact (norm_sub_le _ _).trans (by linarith [hχb k z, norm_one (α := ℂ)]))
    have h1 : Tendsto (fun k => eLpNorm (fun z => ((χ k z : ℂ) - 1) * T.AF ρ F z) 2 volume)
        atTop (𝓝 0) := by
      refine tendsto_eLpNorm_of_integral hm ?_
      have hInt : Integrable (fun z => 4 * ‖T.AF ρ F z‖ ^ 2) :=
        (hAFm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top |>.congr
          (Eventually.of_forall fun z => by simp)).const_mul 4
      have := tendsto_integral_of_dominated_convergence (fun z => 4 * ‖T.AF ρ F z‖ ^ 2)
        (F := fun k z => ‖((χ k z : ℂ) - 1) * T.AF ρ F z‖ ^ 2) (f := fun _ => (0 : ℝ))
        (fun k => ((hm k).1.norm).pow 2) hInt (fun k => Eventually.of_forall fun z => ?_)
        (Eventually.of_forall fun z => ?_)
      · simpa using this
      · rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
        have : ‖((χ k z : ℂ) - 1)‖ ^ 2 ≤ 4 := by
          have h := (norm_sub_le ((χ k z : ℂ)) 1).trans
            (by linarith [hχb k z, norm_one (α := ℂ)] : ‖((χ k z : ℂ))‖ + ‖(1 : ℂ)‖ ≤ 2)
          nlinarith [norm_nonneg ((χ k z : ℂ) - 1)]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · by_cases hz : z ∈ T.U
        · have h2 : Tendsto (fun k => ((χ k z : ℂ) - 1)) atTop (𝓝 0) := by
            have := ((Complex.continuous_ofReal.tendsto _).comp (hχlim z hz)).sub_const 1
            simpa using this
          have := ((h2.mul_const (T.AF ρ F z)).norm).pow 2
          simpa using this
        · have h0 : T.AF ρ F z = 0 := by
            rw [AF_eq]; simp [indicator_of_notMem hz]
          simp [h0]
    have h2 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (2 * M) * |c k|) * eLpNorm v 2 volume)
        atTop (𝓝 0) := by
      have h3 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (2 * M) * |c k|)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (hca.const_mul (Real.sqrt (2 * M)))
        simpa using this
      have := ENNReal.Tendsto.mul_const h3 (Or.inr (Lp.eLpNorm_ne_top v))
      simpa using this
    have h12 := h1.add h2
    rw [add_zero] at h12
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
      (fun _ => by positivity) fun k => ?_
    have hpt : ∀ z, ‖T.Alim ρ F (χ k) v z - T.AF ρ F z‖ ≤
        ‖((χ k z : ℂ) - 1) * T.AF ρ F z‖ + Real.sqrt (2 * M) * |c k| * ‖v z‖ := by
      intro z
      have hdiff : T.Alim ρ F (χ k) v z - T.AF ρ F z = ((χ k z : ℂ) - 1) * T.AF ρ F z -
          ((T.U.indicator (T.cw2 ρ) z : ℝ) : ℂ) *
            ⟪dbarV (fun y => (χ k y : ℂ)) z, T.Weps ρ v z⟫_ℂ := by
        rw [Alim, AF_eq]; ring
      rw [hdiff]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_cut_tstar_le hρ (hχ k) (hχd k) hM v z))
    refine (eLpNorm_mono_real hpt).trans ?_
    refine (eLpNorm_add_le (hm k).1.norm
      ((Lp.aestronglyMeasurable v).norm.const_mul _) (by norm_num)).trans (add_le_add ?_ ?_)
    · exact le_of_eq (eLpNorm_norm _)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
      rw [Real.norm_of_nonneg (by positivity)]
  -- the `S`-energies
  have hsk : Tendsto (fun k => (1 / 2 : ℝ) * ∫ z, ‖T.Slim ρ (χ k) v z‖ ^ 2) atTop (𝓝 0) := by
    have hle : ∀ k, (1 / 2 : ℝ) * ∫ z, ‖T.Slim ρ (χ k) v z‖ ^ 2 ≤
        (1 / 2 : ℝ) * (2 * |c k| * ‖v‖) ^ 2 := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [integral_norm_sq_eq (hSl k), Lp.norm_toLp]
      have hb : eLpNorm (T.Slim ρ (χ k) v) 2 volume ≤ ENNReal.ofReal (2 * |c k|) * eLpNorm v 2 volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z =>
          norm_Slim_le hρ (hχ k) (hχd k) v z) 2
      have hb' : (eLpNorm (T.Slim ρ (χ k) v) 2 volume).toReal ≤ 2 * |c k| * ‖v‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * |c k|),
          ← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (Lp.eLpNorm_ne_top v)) hb
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg hb' 2
    have hlim : Tendsto (fun k => (1 / 2 : ℝ) * (2 * |c k| * ‖v‖) ^ 2) atTop (𝓝 0) := by
      have := ((hca.const_mul 2).mul_const ‖v‖).pow 2 |>.const_mul (1 / 2 : ℝ)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_) hle
    exact mul_nonneg (by norm_num) (integral_nonneg fun z => sq_nonneg _)
  -- the diagonal choice
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hdk.eventually (Metric.ball_mem_nhds _ hε2)).and
    ((hek.eventually (Iio_mem_nhds (by linarith : F.energy ρ < F.energy ρ + ε / 2))).and
      (hsk.eventually (Iio_mem_nhds hε2)))).exists
  obtain ⟨Fs, h1, h2, h3, -, -⟩ := hlev k
  obtain ⟨m, hm1, hm2, hm3⟩ := ((h1.eventually (Metric.ball_mem_nhds _ hε2)).and
    ((h2.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε2))).and
      (h3.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε2))))).exists
  replace hk1 := Metric.mem_ball.mp hk1
  replace hm1 := Metric.mem_ball.mp hm1
  refine ⟨Fs m, ?_, by linarith, by linarith⟩
  have := dist_triangle ((Fs m).data ρ) (∫ z, (χ k z : ℂ) * ⟪v z, T.ydF ρ z⟫_ℂ) (F.data ρ)
  rw [← dist_eq_norm]
  linarith

end TwistedDatum










variable (n : ℕ)

/-- **The functional bound of the twisted `L²` estimate on open sets of `ℂⁿ`**
(`claude-tl2-dens:main`). -/
theorem twistedFunctionalBoundStatement_complexModel :
    TwistedFunctionalBoundStatement n (ComplexModel n) :=
  twistedFunctionalBoundStatement_of_sigmaGraphDensity n TwistedDatum.sigmaGraphDensity

/-- **The main twisted `L²` estimate on open sets of `ℂⁿ`** (`claude-twisted-l2:main` for
`X = ℂⁿ`; FPT `lem:twisted-kahler-line-estimate`): `TwistedL2CorrectionStatement n ℂⁿ`, the `ℂⁿ`
input of `thm:OT_ext`. -/
theorem twistedL2CorrectionStatement_complexModel :
    TwistedL2CorrectionStatement n (ComplexModel n) :=
  twistedL2CorrectionStatement_complexModel_of_sigmaGraphDensity n TwistedDatum.sigmaGraphDensity


end SGPT.Trace.TwistedL2
