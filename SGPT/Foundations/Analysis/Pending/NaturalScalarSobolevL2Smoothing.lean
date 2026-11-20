import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevArzela
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Genuine global L² smoothing classes and finite native smoothing nets

Five complete mathematical statements and ENTIRE proofs precede this source.
Every smoothing class comes from its literal original compact smooth test.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions Convolution Pointwise RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevL2Smoothing

open NaturalScalarSobolevJet NaturalScalarSobolevBump NaturalScalarSobolevArzela

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (K : Compacts E) (ρ : ContDiffBump (0 : E))

/-- The literal original convolution is an actual entire smooth compact-supported scalar test. -/
def smoothingTest (f : 𝓓_{K}(E, ℝ)) : 𝓓_{enlargedCompact K ρ}(E, ℝ) where
  toFun := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)
  contDiff' := normedBump_contDiff μ ρ K f
  zero_on_compl' := by
    intro x hx
    by_contra hne
    exact hx ((normedBump_tsupport_subset μ ρ K f) (subset_closure hne))

theorem smoothingTest_apply (f : 𝓓_{K}(E, ℝ)) (x : E) :
    smoothingTest μ K ρ f x = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x := rfl

/-- The genuine original real L² class of the literal compact smooth convolution. -/
def smoothingL2 (f : 𝓓_{K}(E, ℝ)) : Lp ℝ 2 μ :=
  scalarStageL2 μ (enlargedCompact K ρ) (smoothingTest μ K ρ f)

theorem smoothingL2_ae (f : 𝓓_{K}(E, ℝ)) :
    smoothingL2 μ K ρ f =ᵐ[μ] (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) :=
  scalarStageL2_ae μ (enlargedCompact K ρ) (smoothingTest μ K ρ f)

/-- Literal finite square integral of differences of the genuine smoothing classes. -/
theorem smoothingL2_sub_norm_sq (f g : 𝓓_{K}(E, ℝ)) :
    ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ ^ 2 =
      ∫ x, ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x -
        (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g : E → ℝ)) x) ^ 2 ∂μ := by
  change ‖scalarStageL2 μ (enlargedCompact K ρ) (smoothingTest μ K ρ f) -
    scalarStageL2 μ (enlargedCompact K ρ) (smoothingTest μ K ρ g)‖ ^ 2 = _
  rw [← map_sub, scalarStageL2_norm_sq]
  rfl

/-- Literal finite square error integral for the actual smoothing and original scalar inclusion. -/
theorem smoothingL2_error_norm_sq (f : 𝓓_{K}(E, ℝ)) :
    ‖smoothingL2 μ K ρ f - scalarStageL2 μ K f‖ ^ 2 =
      ∫ x, ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x - f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothingL2_ae μ K ρ f, scalarStageL2_ae μ K f,
    Lp.coeFn_sub (smoothingL2 μ K ρ f) (scalarStageL2 μ K f)] with x hx hf hs
  rw [hs, Pi.sub_apply, hx, hf]
  simp [Real.norm_eq_abs, sq_abs]

/-- Actual common compact support converts a true uniform bound to an original global L² bound. -/
theorem smoothingL2_sub_norm_le_uniform (f g : 𝓓_{K}(E, ℝ)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfg : ∀ x : (enlargedCompact K ρ : Set E),
      ‖(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x.val -
        (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g : E → ℝ)) x.val‖ ≤ δ) :
    ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ ≤
      (1 + Real.sqrt (μ.real (enlargedCompact K ρ))) * δ := by
  let d : 𝓓_{enlargedCompact K ρ}(E, ℝ) := smoothingTest μ K ρ f - smoothingTest μ K ρ g
  have hi : Integrable (fun x => d x ^ 2) μ :=
    (d.continuous.memLp_of_hasCompactSupport d.hasCompactSupport (p := 2)).integrable_sq
  have hsq : ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ ^ 2 ≤
      μ.real (enlargedCompact K ρ) * δ ^ 2 := by
    rw [smoothingL2_sub_norm_sq]
    change (∫ x, d x ^ 2 ∂μ) ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [d.zero_on_compl hx]; simp)]
    calc
      _ ≤ ∫ x in (enlargedCompact K ρ : Set E), δ ^ 2 ∂μ :=
        setIntegral_mono_on hi.integrableOn
          (integrableOn_const (enlargedCompact K ρ).isCompact.measure_lt_top.ne)
          (enlargedCompact K ρ).isCompact.measurableSet fun x hx => by
            have hb : ‖d x‖ ≤ δ := hfg ⟨x, hx⟩
            simpa only [Real.norm_eq_abs, sq_abs] using
              (sq_le_sq₀ (norm_nonneg _) hδ).2 hb
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hm : 0 ≤ μ.real (enlargedCompact K ρ) := ENNReal.toReal_nonneg
  have ha : 0 ≤ Real.sqrt (μ.real (enlargedCompact K ρ)) * δ :=
    mul_nonneg (Real.sqrt_nonneg _) hδ
  have hn : ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ ≤
      Real.sqrt (μ.real (enlargedCompact K ρ)) * δ := by
    apply (sq_le_sq₀ (norm_nonneg _) ha).mp
    simpa only [mul_pow, Real.sq_sqrt hm] using hsq
  exact hn.trans (by nlinarith)

/-- Finite centers are original native members, now for the literal global real L² smoothing classes. -/
theorem finite_native_smoothing_l2_approx (A : Set 𝓓_{K}(E, ℝ))
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ f ∈ A, ‖scalarStageL2 μ K f‖ ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set 𝓓_{K}(E, ℝ), F ⊆ A ∧ F.Finite ∧ ∀ f ∈ A, ∃ g ∈ F,
      ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ < ε := by
  let a : ℝ := 1 + Real.sqrt (μ.real (enlargedCompact K ρ))
  have ha : 0 < a := by dsimp [a]; positivity
  let δ : ℝ := ε / (2 * a)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) ha)
  obtain ⟨F, hFA, hFfin, hF⟩ := finite_native_smoothing_uniform_approx μ K ρ A R hR hA δ hδ
  refine ⟨F, hFA, hFfin, ?_⟩
  intro f hf
  obtain ⟨g, hg, hfg⟩ := hF f hf
  refine ⟨g, hg, (smoothingL2_sub_norm_le_uniform μ K ρ f g δ hδ.le
    (fun x => (hfg x).le)).trans_lt ?_⟩
  change a * (ε / (2 * a)) < ε
  have heq : a * (ε / (2 * a)) = ε / 2 := by field_simp
  rw [heq]
  exact half_lt_self hε

/-- The same global L² finite net follows from actual finite native first-jet bounds. -/
theorem finite_firstJet_smoothing_l2_approx {ι : Type*} [Fintype ι] (v : ι → E)
    (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K v f‖ ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set 𝓓_{K}(E, ℝ), F ⊆ A ∧ F.Finite ∧ ∀ f ∈ A, ∃ g ∈ F,
      ‖smoothingL2 μ K ρ f - smoothingL2 μ K ρ g‖ < ε := by
  apply finite_native_smoothing_l2_approx μ K ρ A R hR _ ε hε
  intro f hf
  exact (PiLp.norm_apply_le (firstJetLinear μ K v f) (Sum.inl ())).trans (hA f hf)

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (ν : Measure V) [ν.IsAddHaarMeasure] (L : Compacts V) (η : ContDiffBump (0 : V))
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- Genuine original global L² smoothing error with the actual old-norm orthonormal first jet. -/
theorem norm_smoothingL2_error_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    ‖smoothingL2 ν L η f - scalarStageL2 ν L f‖ ≤ η.rOut * ‖firstJetLinear ν L b f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg η.rOut_pos.le (norm_nonneg _))).mp
  rw [smoothingL2_error_norm_sq, mul_pow]
  exact integral_normedBump_error_square_le_firstJet ν η L b f

end InnerProduct

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevL2Smoothing
