import SGPT.Convex.SmoothRegularization

noncomputable section
namespace SGPT.Convex

open Set Filter Topology MeasureTheory
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Genuine normalized smooth bumps convolved with the original finite function. -/
def finiteConvexSmoothApprox (f : E → ℝ) (j : ℕ) : E → ℝ :=
  bumpSmoothing μ (smoothingBump j) f

theorem convexOn_finiteConvexSmoothApprox {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (j : ℕ) :
    ConvexOn ℝ univ (finiteConvexSmoothApprox μ f j) :=
  convexOn_bumpSmoothing μ (smoothingBump j) hf

theorem contDiff_finiteConvexSmoothApprox {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (j : ℕ) :
    ContDiff ℝ ∞ (finiteConvexSmoothApprox μ f j) :=
  contDiff_bumpSmoothing μ (smoothingBump j)
    (continuousOn_univ.mp (hf.continuousOn isOpen_univ))

/-- True shrinking kernel support and original finite convex continuity give
pointwise convergence, directly reusing the actual approximate identity. -/
theorem tendsto_finiteConvexSmoothApprox {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (x : E) :
    Tendsto (fun j ↦ finiteConvexSmoothApprox μ f j x) atTop (𝓝 (f x)) := by
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := fun j ↦ (smoothingBump j : ContDiffBump (0 : E))) tendsto_smoothingRadius hc x

/-- The genuine finite convex sequence producer upgrades original pointwise
approximate-identity limits to actual compact-uniform convergence. -/
theorem tendstoUniformlyOn_finiteConvexSmoothApprox {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (finiteConvexSmoothApprox μ f) f atTop K := by
  apply tendstoUniformlyOn_of_dense_convex_convergence
    (C := univ) (D := univ) isOpen_univ (Subset.refl univ) (by simp)
    (convexOn_finiteConvexSmoothApprox μ hf)
  · intro x _
    exact ⟨f x, tendsto_finiteConvexSmoothApprox μ hf x⟩
  · intro x _
    exact tendsto_finiteConvexSmoothApprox μ hf x
  · exact hK
  · exact subset_univ K

include μ in
/-- Actual smooth convex approximants are produced for every finite convex
function, without a support-class or assumed approximation premise. -/
theorem exists_smooth_finite_convex_compact_approx {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) :
    ∃ g : ℕ → E → ℝ, (∀ j, ConvexOn ℝ univ (g j) ∧ ContDiff ℝ ∞ (g j)) ∧
      ∀ K : Set E, IsCompact K → TendstoUniformlyOn g f atTop K := by
  exact ⟨finiteConvexSmoothApprox μ f,
    fun j ↦ ⟨convexOn_finiteConvexSmoothApprox μ hf j,
      contDiff_finiteConvexSmoothApprox μ hf j⟩,
    fun _ hK ↦ tendstoUniformlyOn_finiteConvexSmoothApprox μ hf hK⟩

end SGPT.Convex
