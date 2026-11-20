import SGPT.Bergman.SourceSmoothMetricPolynomialBound

/-!
# Rescaling the Hermitian metric of a holomorphic line bundle

Lane T-METRIC, blueprint `claude-t-metric`, node `claude-t-metric:rescale`. Used for
`thm:DXmain1` (chapter *`𝓘`-good singularities*), where the twist `T` is an arbitrary holomorphic
line bundle: the space `H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` does not involve any metric on `T`, while the
analytic arguments need a smooth one.

A `HermitianHolomorphicLineBundle` bundles a holomorphic line bundle with a continuous Hermitian
metric. For a continuous function `ρ > 0` on the base, `rescale T ρ` is the SAME holomorphic line
bundle (same fibres, same total-space topology, same fibre-bundle, vector-bundle and holomorphic
structure, hence the same atlas) with the metric `h' = ρ h`, i.e. `⟪v, w⟫' = ρ(x) ⟪v, w⟫`. The
fibre norms are built with `InnerProductSpace.Core.toNormedAddCommGroupOfTopology`, which keeps
the fibre topology, so the bundle structure of `T` is reused verbatim.

* `rescale T ρ hρc hρ`: the bundle `(T, ρ h_T)`.
* `toRescale`: the identity map `T_x → (rescale T ρ)_x`, a linear equivalence.
* `norm_toRescale`: `‖v‖' = √ρ(x) ‖v‖`.
* `toAtlasFrame`, `ofAtlasFrame`: the atlas frames of `T` and of `rescale T ρ` are the same
  trivializations.
* `isSourceSmoothHermitianMetric_rescale_iff`: `ρ h_T` is smooth iff `ρ |e(x)|²_{h_T}` is smooth
  in every chart for every atlas frame `e`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle.TMetric

open Bundle Set Filter
open scoped Topology Manifold ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.PolynomialH0Growth

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The rescaled fibre inner products -/

/-- The inner product `ρ(x) ⟪v, w⟫` on the fibre `T_x`, as an `InnerProductSpace.Core`. -/
@[instance_reducible]
def rescaleCore (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ) (hρ : ∀ x, 0 < ρ x)
    (x : M) : InnerProductSpace.Core ℂ (T.Fiber x) where
  inner v w := (ρ x : ℂ) * inner ℂ v w
  conj_inner_symm v w := by
    simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]
  re_inner_nonneg v := by
    change 0 ≤ ((ρ x : ℂ) * inner ℂ v v).re
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (hρ x).le (inner_self_nonneg (𝕜 := ℂ) (x := v))
  add_left v w z := by rw [inner_add_left, mul_add]
  smul_left v w r := by rw [inner_smul_left]; ring
  definite v h := by
    have h' : inner ℂ v v = 0 :=
      (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (hρ x).ne')
    exact inner_self_eq_zero.mp h'

theorem rescaleCore_re (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : M) (w : T.Fiber x) :
    RCLike.re ((rescaleCore T ρ hρ x).inner w w) = ρ x * ‖w‖ ^ 2 := by
  change ((ρ x : ℂ) * inner ℂ w w).re = _
  rw [Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) w

theorem rescaleCore_continuousAt (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : M) :
    ContinuousAt (fun w : T.Fiber x => (rescaleCore T ρ hρ x).inner w w) 0 :=
  (continuous_const.mul (continuous_id.inner continuous_id)).continuousAt

theorem rescaleCore_isVonNBounded (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : M) :
    Bornology.IsVonNBounded ℂ
      {w : T.Fiber x | RCLike.re ((rescaleCore T ρ hρ x).inner w w) < 1} := by
  rw [NormedSpace.isVonNBounded_iff]
  refine isBounded_iff_forall_norm_le.mpr ⟨max 1 (1 / ρ x), fun w hw => ?_⟩
  have hw' : ρ x * ‖w‖ ^ 2 < 1 := by rw [← rescaleCore_re]; exact hw
  by_cases h1 : ‖w‖ ≤ 1
  · exact h1.trans (le_max_left _ _)
  · push Not at h1
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (hρ x)]
    nlinarith [hρ x]

/-- The rescaled fibre norm `√ρ(x) ‖·‖`, with the fibre topology of `T` kept definitionally. -/
@[instance_reducible]
def rescaleNormed (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ) (hρ : ∀ x, 0 < ρ x)
    (x : M) : NormedAddCommGroup (T.Fiber x) :=
  (rescaleCore T ρ hρ x).toNormedAddCommGroupOfTopology
    (rescaleCore_continuousAt T ρ hρ x) (rescaleCore_isVonNBounded T ρ hρ x)

/-- The rescaled fibre inner product space `(T_x, ρ(x) ⟪·, ·⟫)`. -/
@[instance_reducible]
def rescaleInner (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ) (hρ : ∀ x, 0 < ρ x)
    (x : M) : letI := rescaleNormed T ρ hρ x; InnerProductSpace ℂ (T.Fiber x) :=
  InnerProductSpace.ofCoreOfTopology (rescaleCore T ρ hρ x)
    (rescaleCore_continuousAt T ρ hρ x) (rescaleCore_isVonNBounded T ρ hρ x)

theorem rescaleNormed_norm (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : M) (w : T.Fiber x) :
    @Norm.norm (T.Fiber x) (rescaleNormed T ρ hρ x).toNorm w = Real.sqrt (ρ x) * ‖w‖ := by
  change Real.sqrt (RCLike.re ((rescaleCore T ρ hρ x).inner w w)) = _
  rw [rescaleCore_re, Real.sqrt_mul (hρ x).le, Real.sqrt_sq (norm_nonneg w)]

theorem continuous_rescaleNormed_norm (T : HermitianHolomorphicLineBundle.{u, v} n M)
    (ρ : M → ℝ) (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) :
    Continuous (fun p : TotalSpace ℂ T.Fiber =>
      @Norm.norm (T.Fiber p.proj) (rescaleNormed T ρ hρ p.proj).toNorm p.2) := by
  have h : (fun p : TotalSpace ℂ T.Fiber =>
      @Norm.norm (T.Fiber p.proj) (rescaleNormed T ρ hρ p.proj).toNorm p.2) =
      fun p => Real.sqrt (ρ p.proj) * ‖p.2‖ := by
    funext p
    exact rescaleNormed_norm T ρ hρ p.proj p.2
  rw [h]
  exact ((hρc.comp (FiberBundle.continuous_proj ℂ T.Fiber)).sqrt).mul
    (SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous)

/-! ### The rescaled bundle -/

/-- **The bundle `(T, ρ h_T)`**: the same holomorphic line bundle as `T` (same fibres, total-space
topology, fibre-bundle, vector-bundle and holomorphic structure), with the Hermitian metric
multiplied by the continuous positive function `ρ`. -/
def rescale (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ) (hρc : Continuous ρ)
    (hρ : ∀ x, 0 < ρ x) : HermitianHolomorphicLineBundle.{u, v} n M where
  Fiber := T.Fiber
  normedFiber := rescaleNormed T ρ hρ
  hermitianFiber := rescaleInner T ρ hρ
  totalTopology := T.totalTopology
  fiberBundle := T.fiberBundle
  vectorBundle := T.vectorBundle
  holomorphic := T.holomorphic
  normContinuous := @SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.mk M _
    T.Fiber (rescaleNormed T ρ hρ) T.totalTopology (continuous_rescaleNormed_norm T ρ hρc hρ)

variable (T : HermitianHolomorphicLineBundle.{u, v} n M) (ρ : M → ℝ) (hρc : Continuous ρ)
  (hρ : ∀ x, 0 < ρ x)

/-- The identity map `T_x → (rescale T ρ)_x`. -/
def toRescale (x : M) : T.Fiber x ≃ₗ[ℂ] (rescale T ρ hρc hρ).Fiber x where
  toFun w := w
  invFun w := w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem inner_toRescale (x : M) (w w' : T.Fiber x) :
    inner ℂ (toRescale T ρ hρc hρ x w) (toRescale T ρ hρc hρ x w') =
      (ρ x : ℂ) * inner ℂ w w' :=
  rfl

theorem norm_toRescale (x : M) (w : T.Fiber x) :
    ‖toRescale T ρ hρc hρ x w‖ = Real.sqrt (ρ x) * ‖w‖ :=
  rescaleNormed_norm T ρ hρ x w

theorem norm_toRescale_sq (x : M) (w : T.Fiber x) :
    ‖toRescale T ρ hρc hρ x w‖ ^ 2 = ρ x * ‖w‖ ^ 2 := by
  rw [norm_toRescale, mul_pow, Real.sq_sqrt (hρ x).le]

/-- An atlas frame of `T` is an atlas frame of `rescale T ρ` (the same trivialization). -/
def toAtlasFrame (e : AtlasFrame T) : AtlasFrame (rescale T ρ hρc hρ) :=
  ⟨e.val, e.property⟩

/-- An atlas frame of `rescale T ρ` is an atlas frame of `T` (the same trivialization). -/
def ofAtlasFrame (e : AtlasFrame (rescale T ρ hρc hρ)) : AtlasFrame T :=
  ⟨e.val, e.property⟩

theorem toAtlasFrame_ofAtlasFrame (e : AtlasFrame (rescale T ρ hρc hρ)) :
    toAtlasFrame T ρ hρc hρ (ofAtlasFrame T ρ hρc hρ e) = e :=
  rfl

theorem toAtlasFrame_baseSet (e : AtlasFrame T) :
    (toAtlasFrame T ρ hρc hρ e).val.baseSet = e.val.baseSet :=
  rfl

/-- Coordinates in corresponding frames agree. -/
theorem toAtlasFrame_apply (e : AtlasFrame T) (x : M) (w : T.Fiber x) :
    ((toAtlasFrame T ρ hρc hρ e).val ⟨x, toRescale T ρ hρc hρ x w⟩).2 = (e.val ⟨x, w⟩).2 :=
  rfl

/-- Frame vectors in corresponding frames agree. -/
theorem toAtlasFrame_symm (e : AtlasFrame T) (x : M) (z : ℂ) :
    (toAtlasFrame T ρ hρc hρ e).val.symm x z = toRescale T ρ hρc hρ x (e.val.symm x z) :=
  rfl

/-- **Smoothness criterion**: the rescaled metric `ρ h_T` is smooth iff for every chart `c` and
every atlas frame `e` of `T`, `ρ |e|²_{h_T}` is smooth in `c` on the frame domain. -/
theorem isSourceSmoothHermitianMetric_rescale_iff :
    IsSourceSmoothHermitianMetric (rescale T ρ hρc hρ) ↔
      ∀ (c : ComplexChart n M) (e : AtlasFrame T),
        ContDiffOn ℝ ∞ (fun z => ρ (c.val.symm z) * ‖e.val.symm (c.val.symm z) 1‖ ^ 2)
          (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  constructor
  · intro h c e
    have h' := h c (toAtlasFrame T ρ hρc hρ e)
    refine h'.congr fun z _ => ?_
    rw [toAtlasFrame_symm, norm_toRescale_sq]
  · intro h c e
    have h' := h c (ofAtlasFrame T ρ hρc hρ e)
    refine h'.congr fun z _ => ?_
    rw [← toAtlasFrame_ofAtlasFrame T ρ hρc hρ e, toAtlasFrame_symm, norm_toRescale_sq]
    rfl

end SGPT.LineBundle.TMetric
