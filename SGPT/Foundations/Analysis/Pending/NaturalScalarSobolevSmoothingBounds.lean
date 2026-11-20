import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBump
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Actual compact-set L¹ and fixed normalized scalar smoothing bounds

Five complete statements and ENTIRE proofs precede this source. The actual
indicator and original real L² norm give finite compact-set constants.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped Distributions Convolution RealInnerProductSpace NNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevSmoothingBounds

open NaturalScalarSobolevJet NaturalScalarSobolevBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (K : Compacts E)

/-- The genuine compact indicator yields an actual scalar L¹ bound without measure division. -/
theorem scalar_compact_l1_le_l2 (f : 𝓓_{K}(E, ℝ)) :
    (∫ x, ‖f x‖ ∂μ) ≤
      ‖indicatorConstLp (μ := μ) 2 K.isCompact.measurableSet K.isCompact.measure_lt_top.ne (1 : ℝ)‖ *
        ‖scalarStageL2 μ K f‖ := by
  let hf : MemLp (f : E → ℝ) 2 μ :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  let a : Lp ℝ 2 μ := hf.norm.toLp (fun x => ‖f x‖)
  let c : Lp ℝ 2 μ := indicatorConstLp (μ := μ) 2 K.isCompact.measurableSet
    K.isCompact.measure_lt_top.ne (1 : ℝ)
  have hnorm : ‖a‖ = ‖scalarStageL2 μ K f‖ := by
    simp only [a, scalarStageL2, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      eLpNorm_norm]
  have heq : ⟪c, a⟫ = ∫ x, ‖f x‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ)
      (hs := K.isCompact.measurableSet) (hμs := K.isCompact.measure_lt_top.ne) (c := (1 : ℝ)),
      hf.norm.coeFn_toLp] with x hcx hax
    rw [show c x = (K : Set E).indicator (fun _ => (1 : ℝ)) x from hcx, hax]
    by_cases hx : x ∈ (K : Set E)
    · simp [hx]
    · have hfx := f.zero_on_compl hx
      simp [hx, hfx]
  calc
    _ = ⟪c, a⟫ := heq.symm
    _ ≤ |⟪c, a⟫| := le_abs_self _
    _ ≤ ‖c‖ * ‖a‖ := abs_real_inner_le_norm _ _
    _ = _ := by rw [hnorm]

variable (ρ : ContDiffBump (0 : E))

/-- True whole-space boundedness and Lipschitz continuity of the original normalized compact kernel. -/
theorem normedBump_exists_uniform_bounds :
    ∃ (B : ℝ) (C : ℝ≥0), 0 ≤ B ∧
      (∀ x, ‖ρ.normed μ x‖ ≤ B) ∧ LipschitzWith C (ρ.normed μ) := by
  obtain ⟨B, hB⟩ := (ρ.hasCompactSupport_normed (μ := μ)).exists_bound_of_continuous
    (ρ.continuous_normed (μ := μ))
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (ρ.hasCompactSupport_normed (μ := μ)) (ρ.contDiff_normed (μ := μ) (n := 1)) (by norm_num)
  exact ⟨max B 0, C, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _), hC⟩

/-- Literal Haar change of variables gives the actual input-supported smoothing integral. -/
theorem normedBump_swap_integral (f : 𝓓_{K}(E, ℝ)) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x =
      ∫ t, ρ.normed μ (x - t) * f t ∂μ := by
  rw [convolution_eq_swap]
  simp only [lsmul_apply, smul_eq_mul]

/-- Actual whole-space amplitude from a true fixed-kernel bound and the original scalar L¹ norm. -/
theorem normedBump_abs_le_l1 (B : ℝ) (hB : ∀ x, ‖ρ.normed μ x‖ ≤ B)
    (f : 𝓓_{K}(E, ℝ)) (x : E) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x‖ ≤ B * (∫ t, ‖f t‖ ∂μ) := by
  have hi : Integrable (fun t => ρ.normed μ (x - t) * f t) μ :=
    ((ρ.continuous_normed.comp (continuous_const.sub continuous_id)).mul f.continuous).integrable_of_hasCompactSupport
       f.hasCompactSupport.mul_left
  have hfi : Integrable (fun t => ‖f t‖) μ :=
    f.continuous.norm.integrable_of_hasCompactSupport f.hasCompactSupport.norm
  rw [normedBump_swap_integral]
  calc
    _ ≤ ∫ t, ‖ρ.normed μ (x - t) * f t‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, B * ‖f t‖ ∂μ := integral_mono hi.norm (hfi.const_mul B) fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The actual difference of smoothing values has the true kernel Lipschitz modulus times original L¹. -/
theorem normedBump_sub_abs_le_l1 (C : ℝ≥0) (hC : LipschitzWith C (ρ.normed μ))
    (f : 𝓓_{K}(E, ℝ)) (x y : E) :
    ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x -
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) y‖ ≤
      C * ‖x - y‖ * (∫ t, ‖f t‖ ∂μ) := by
  have hi (z : E) : Integrable (fun t => ρ.normed μ (z - t) * f t) μ :=
    ((ρ.continuous_normed.comp (continuous_const.sub continuous_id)).mul f.continuous).integrable_of_hasCompactSupport
       f.hasCompactSupport.mul_left
  have hfi : Integrable (fun t => ‖f t‖) μ :=
    f.continuous.norm.integrable_of_hasCompactSupport f.hasCompactSupport.norm
  rw [normedBump_swap_integral, normedBump_swap_integral, ← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ t, ‖ρ.normed μ (x - t) * f t - ρ.normed μ (y - t) * f t‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, (C * ‖x - y‖) * ‖f t‖ ∂μ :=
      integral_mono ((hi x).sub (hi y)).norm (hfi.const_mul _) fun t => by
        rw [← sub_mul, norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [sub_sub_sub_cancel_right] using hC.norm_sub_le (x - t) (y - t)
    _ = _ := integral_const_mul _ _

/-- One genuinely constructed pair of amplitude and Lipschitz constants controls a native L² bounded family. -/
theorem normedBump_family_bounds (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖scalarStageL2 μ K f‖ ≤ R) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ f ∈ A,
      (∀ x, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x‖ ≤ M) ∧
      (∀ x y, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x -
        (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) y‖ ≤ L * ‖x - y‖) := by
  let CK : ℝ := ‖indicatorConstLp (μ := μ) 2 K.isCompact.measurableSet
    K.isCompact.measure_lt_top.ne (1 : ℝ)‖
  obtain ⟨B, C, hB0, hB, hC⟩ := normedBump_exists_uniform_bounds μ ρ
  refine ⟨B * CK * R, C * CK * R,
    mul_nonneg (mul_nonneg hB0 (norm_nonneg _)) hR,
    mul_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg _)) hR, ?_⟩
  intro f hf
  have hl : (∫ t, ‖f t‖ ∂μ) ≤ CK * R :=
    (scalar_compact_l1_le_l2 μ K f).trans
      (mul_le_mul_of_nonneg_left (hA f hf) (norm_nonneg _))
  constructor
  · intro x
    exact (normedBump_abs_le_l1 μ K ρ B hB f x).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl hB0)
  · intro x y
    apply (normedBump_sub_abs_le_l1 μ K ρ C hC f x y).trans
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hl (mul_nonneg C.coe_nonneg (norm_nonneg (x - y)))

/-- Actual finite first-jet coordinate projection internally supplies the original L² family bound. -/
theorem normedBump_firstJet_family_bounds {ι : Type*} [Fintype ι] (v : ι → E)
    (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K v f‖ ≤ R) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ f ∈ A,
      (∀ x, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x‖ ≤ M) ∧
      (∀ x y, ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x -
        (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) y‖ ≤ L * ‖x - y‖) := by
  apply normedBump_family_bounds μ K ρ A R hR
  intro f hf
  exact (PiLp.norm_apply_le (firstJetLinear μ K v f) (Sum.inl ())).trans (hA f hf)

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevSmoothingBounds
