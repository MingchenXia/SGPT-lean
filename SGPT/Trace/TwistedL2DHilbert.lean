import SGPT.Trace.TwistedL2DUnit

/-!
# The Hilbert space of `L`-valued vector fields with the fibre metric `σ`

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:hilbert`).  A local piece `h ⊗ e` (or any
`L`-valued `(1,0)`-vector field) is represented in `H₂ = L²(ℂⁿ; ℂⁿ)` by its unit-frame
coefficient normalized by `s √σᵀ` (`repF`): `‖repF e h‖²_{L²} = ∫ σ(h, h) |e|² e^{-φ} dμ`.
Conversely an element `x` of `H₂` has the unit-frame coefficient field `Weps x = s⁻¹ (√σᵀ)⁻¹ x`
on `U`.

* `inner_repF`: the pairing of a piece with any field, `⟪repF e h, x⟫ = s² σ(Weps x, h / uc e)`;
* `memLp_repF`: pieces with compact support in the frame domain are in `H₂`, with an explicit
  bound (`eLpNorm_repF_le`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

theorem aestronglyMeasurable_mv {μ : Measure (ComplexModel n)}
    {M : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {y : ComplexModel n → ComplexModel n}
    (hM : ∀ i j, AEStronglyMeasurable (fun z => M z i j) μ) (hy : AEStronglyMeasurable y μ) :
    AEStronglyMeasurable (fun z => mv (M z) (y z)) μ := by
  have hfun : (fun z => mv (M z) (y z)) = fun z => ∑ i, ∑ j,
      (M z i j * y z j) • (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) := by
    funext z
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  have hyj : AEStronglyMeasurable (fun z => y z j) μ :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable hy
  exact ((hM i j).mul hyj).smul_const _

theorem continuousOn_entry {S : Set (ComplexModel n)} {M : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContinuousOn M S) (i j : Fin n) : ContinuousOn (fun z => M z i j) S :=
  continuousOn_pi.mp (continuousOn_pi.mp hM i) j

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

variable (T ρ) in
/-- The `σ`-normalized unit-frame representative `s √σᵀ (h / uc e)` of the field `h ⊗ e`. -/
def repF (e : AtlasFrame T.L) (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    ComplexModel n :=
  (T.dom e).indicator
    (fun z => ((T.sw ρ z : ℝ) : ℂ) • mv (Bm T.omega T.r z) ((uc e z)⁻¹ • h z)) z

variable (T ρ) in
/-- The unit-frame coefficient field `s⁻¹ (√σᵀ)⁻¹ x` of an element of `H₂`. -/
def Weps (x : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ComplexModel n :=
  T.U.indicator (fun z => (((T.sw ρ z)⁻¹ : ℝ) : ℂ) • mv (Bi T.omega T.r z) (x z)) z

variable (T ρ) in
/-- The pointwise operator norm bound `s · |Bm| · |e|` of `repF e`. -/
def kap (e : AtlasFrame T.L) (z : ComplexModel n) : ℝ :=
  T.sw ρ z * mnorm (Bm T.omega T.r z) * Real.sqrt (frameNormSq T.L e z)

theorem repF_sub (e : AtlasFrame T.L) (h h' : ComplexModel n → ComplexModel n) :
    T.repF ρ e (h - h') = T.repF ρ e h - T.repF ρ e h' := by
  funext z
  by_cases hz : z ∈ T.dom e
  · simp only [repF, indicator_of_mem hz, Pi.sub_apply, smul_sub, mv_sub]
  · simp [repF, indicator_of_notMem hz]

theorem repF_add (e : AtlasFrame T.L) (h h' : ComplexModel n → ComplexModel n) :
    T.repF ρ e (h + h') = T.repF ρ e h + T.repF ρ e h' := by
  funext z
  by_cases hz : z ∈ T.dom e
  · simp only [repF, indicator_of_mem hz, Pi.add_apply, smul_add, mv_add]
  · simp [repF, indicator_of_notMem hz]

theorem repF_eq_zero {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : h z = 0) : T.repF ρ e h z = 0 := by
  by_cases hz' : z ∈ T.dom e
  · simp [repF, indicator_of_mem hz', hz]
  · simp [repF, indicator_of_notMem hz']

variable (hρ : IsChartDensity T.μ chart0 ρ)
include hρ

theorem Weps_repF {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hz : z ∈ T.dom e) : T.Weps ρ (T.repF ρ e h) z = (uc e z)⁻¹ • h z := by
  have hzU := dom_subset_U e hz
  rw [Weps, indicator_of_mem hzU, repF, indicator_of_mem hz, mv_smul,
    mv_Bi_Bm T.isOpen_U T.kahler hzU, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sw_pos hρ z).ne', Complex.ofReal_one, one_smul]

omit hρ in
theorem Weps_repF_of_notMem (_hρ : IsChartDensity T.μ chart0 ρ) {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} {z : ComplexModel n} (hz : z ∉ T.dom e) :
    T.Weps ρ (T.repF ρ e h) z = 0 := by
  by_cases hzU : z ∈ T.U
  · rw [Weps, indicator_of_mem hzU, repF, indicator_of_notMem hz, mv_zero, smul_zero]
  · rw [Weps, indicator_of_notMem hzU]

/-- `s √σᵀ (Weps x) = x` on `U`. -/
theorem sw_Bm_Weps {x : ComplexModel n → ComplexModel n} {z : ComplexModel n} (hz : z ∈ T.U) :
    ((T.sw ρ z : ℝ) : ℂ) • mv (Bm T.omega T.r z) (T.Weps ρ x z) = x z := by
  rw [Weps, indicator_of_mem hz, mv_smul, mv_Bm_Bi T.isOpen_U T.kahler hz, smul_smul,
    ← Complex.ofReal_mul, mul_inv_cancel₀ (sw_pos hρ z).ne', Complex.ofReal_one, one_smul]

theorem norm_sq_x_eq {x : ComplexModel n → ComplexModel n} {z : ComplexModel n} (hz : z ∈ T.U) :
    ‖x z‖ ^ 2 = T.sw ρ z ^ 2 * ‖mv (Bm T.omega T.r z) (T.Weps ρ x z)‖ ^ 2 := by
  rw [← sw_Bm_Weps hρ (x := x) hz, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (sw_pos hρ z).le, mul_pow]

/-- **The pairing of a piece with a field.** -/
theorem inner_repF (e : AtlasFrame T.L) (h x : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    ⟪T.repF ρ e h z, x z⟫_ℂ = (T.dom e).indicator (fun z => ((T.sw ρ z ^ 2 : ℝ) : ℂ) *
      ⟪(uc e z)⁻¹ • h z, mv (sT T.omega T.r z) (T.Weps ρ x z)⟫_ℂ) z := by
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    rw [repF, indicator_of_mem hz, indicator_of_mem hz, inner_smul_left, Complex.conj_ofReal,
      inner_mv_left, Bm_conjTranspose, ← mv_Bm_Bm T.isOpen_U T.kahler hzU]
    conv_lhs => rw [← sw_Bm_Weps hρ (x := x) hzU]
    rw [mv_smul, inner_smul_right]
    push_cast
    ring
  · rw [repF, indicator_of_notMem hz, indicator_of_notMem hz, inner_zero_left]

omit hρ in
theorem continuousOn_kap (e : AtlasFrame T.L) (hρ : IsChartDensity T.μ chart0 ρ) :
    ContinuousOn (T.kap ρ e) (T.dom e) := by
  have h1 := (continuousOn_sw hρ).mono (dom_subset_U e)
  have h2 := (continuous_mnorm.comp_continuousOn
    (continuousOn_Bm T.isOpen_U T.kahler)).mono (dom_subset_U e)
  have h3 := ((continuousOn_frameNormSq e).mono fun z hz => ((T.mem_dom).mp hz).1).sqrt
  exact (h1.mul h2).mul h3

theorem norm_repF_le (e : AtlasFrame T.L) (h : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ‖T.repF ρ e h z‖ ≤ T.kap ρ e z * ‖h z‖ := by
  by_cases hz : z ∈ T.dom e
  · have hzb := ((T.mem_dom).mp hz).1
    rw [repF, indicator_of_mem hz, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (sw_pos hρ z).le, kap]
    have h1 := norm_mv_le (Bm T.omega T.r z) ((uc e z)⁻¹ • h z)
    rw [norm_smul, norm_inv_uc hzb] at h1
    have hs := (sw_pos hρ z).le
    calc T.sw ρ z * ‖mv (Bm T.omega T.r z) ((uc e z)⁻¹ • h z)‖
        ≤ T.sw ρ z * (mnorm (Bm T.omega T.r z) * (Real.sqrt (frameNormSq T.L e z) * ‖h z‖)) :=
          mul_le_mul_of_nonneg_left h1 hs
      _ = _ := by ring
  · rw [repF, indicator_of_notMem hz, norm_zero]
    have : 0 ≤ T.kap ρ e z := by
      unfold kap
      exact mul_nonneg (mul_nonneg (sw_pos hρ z).le (mnorm_nonneg _)) (Real.sqrt_nonneg _)
    exact mul_nonneg this (norm_nonneg _)

theorem exists_kap_bound {e : AtlasFrame T.L} {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKd : K ⊆ T.dom e) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, T.kap ρ e z ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_kap e hρ).mono hKd)
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _))

theorem aestronglyMeasurable_repF (e : AtlasFrame T.L) {h : ComplexModel n → ComplexModel n}
    (hh : AEStronglyMeasurable h volume) : AEStronglyMeasurable (T.repF ρ e h) volume := by
  have hO := (T.isOpen_dom e).measurableSet
  have hr : T.repF ρ e h = (T.dom e).indicator
      (fun z => ((T.sw ρ z : ℝ) : ℂ) • mv (Bm T.omega T.r z) ((uc e z)⁻¹ • h z)) := rfl
  rw [hr]
  refine (aestronglyMeasurable_indicator_iff hO).mpr ?_
  have h1 : AEStronglyMeasurable (fun z => ((T.sw ρ z : ℝ) : ℂ)) (volume.restrict (T.dom e)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_sw hρ).mono (dom_subset_U e))).aestronglyMeasurable hO
  have h2 : ∀ i j, AEStronglyMeasurable (fun z => Bm T.omega T.r z i j)
      (volume.restrict (T.dom e)) := fun i j =>
    ((continuousOn_entry (continuousOn_Bm T.isOpen_U T.kahler) i j).mono
      (dom_subset_U e)).aestronglyMeasurable hO
  have h3 : AEStronglyMeasurable (fun z => (uc e z)⁻¹ • h z) (volume.restrict (T.dom e)) :=
    ((measurable_uc e).inv.aestronglyMeasurable).smul hh.restrict
  exact h1.smul (aestronglyMeasurable_mv h2 h3)

/-- **Pieces with compact support in the frame domain are in `H₂`.** -/
theorem memLp_repF {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKd : K ⊆ T.dom e) (hh : MemLp h 2 volume)
    (h0 : ∀ z ∉ K, h z = 0) : MemLp (T.repF ρ e h) 2 volume := by
  obtain ⟨C, -, hC⟩ := exists_kap_bound hρ hK hKd
  refine hh.of_le_mul (c := C) (aestronglyMeasurable_repF hρ e hh.1) (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · exact (norm_repF_le hρ e h z).trans (mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _))
  · rw [repF_eq_zero (h0 z hz), h0 z hz]; simp

theorem eLpNorm_repF_le {e : AtlasFrame T.L} {K : Set (ComplexModel n)} {C : ℝ}
    (hC : ∀ z ∈ K, T.kap ρ e z ≤ C) {h : ComplexModel n → ComplexModel n}
    (h0 : ∀ z ∉ K, h z = 0) :
    eLpNorm (T.repF ρ e h) 2 volume ≤ ENNReal.ofReal C * eLpNorm h 2 volume := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  by_cases hz : z ∈ K
  · exact (norm_repF_le hρ e h z).trans (mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _))
  · rw [repF_eq_zero (h0 z hz), h0 z hz]; simp

theorem memLp_repF_of_continuous {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hts : tsupport h ⊆ T.dom e) :
    MemLp (T.repF ρ e h) 2 volume :=
  memLp_repF hρ hcs hts (hc.memLp_of_hasCompactSupport hcs)
    fun _ hz => image_eq_zero_of_notMem_tsupport hz

omit hρ

theorem aestronglyMeasurable_Weps (hρ : IsChartDensity T.μ chart0 ρ)
    {x : ComplexModel n → ComplexModel n} (hx : AEStronglyMeasurable x volume) :
    AEStronglyMeasurable (T.Weps ρ x) volume := by
  have hO := T.isOpen_U.measurableSet
  have hr : T.Weps ρ x = T.U.indicator
      (fun z => (((T.sw ρ z)⁻¹ : ℝ) : ℂ) • mv (Bi T.omega T.r z) (x z)) := rfl
  rw [hr]
  refine (aestronglyMeasurable_indicator_iff hO).mpr ?_
  have h1 : AEStronglyMeasurable (fun z => (((T.sw ρ z)⁻¹ : ℝ) : ℂ)) (volume.restrict T.U) :=
    (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_sw hρ).inv₀ fun z _ =>
      (sw_pos hρ z).ne')).aestronglyMeasurable hO
  have h2 : ∀ i j, AEStronglyMeasurable (fun z => Bi T.omega T.r z i j) (volume.restrict T.U) :=
    fun i j => (continuousOn_entry (continuousOn_Bi T.isOpen_U T.kahler) i j).aestronglyMeasurable hO
  exact h1.smul (aestronglyMeasurable_mv h2 hx.restrict)

end TwistedDatum

/-! ### `L²` helpers -/

/-- The Hilbert space `L²(ℂⁿ; ℂⁿ)`. -/
abbrev H2 (n : ℕ) := ComplexModel n →₂[(volume : Measure (ComplexModel n))] ComplexModel n

theorem inner_toLp_right (x : H2 n) {f : ComplexModel n → ComplexModel n} (hf : MemLp f 2 volume) :
    ⟪x, hf.toLp f⟫_ℂ = ∫ z, ⟪x z, f z⟫_ℂ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

theorem inner_toLp_left (x : H2 n) {f : ComplexModel n → ComplexModel n} (hf : MemLp f 2 volume) :
    ⟪hf.toLp f, x⟫_ℂ = ∫ z, ⟪f z, x z⟫_ℂ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

end SGPT.Trace.TwistedL2
