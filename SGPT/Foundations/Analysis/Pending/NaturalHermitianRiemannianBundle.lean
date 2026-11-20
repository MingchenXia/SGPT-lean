import SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Actual smooth Riemannian tangent metric from an original Hermitian form

The original complex atlas supplies its real smooth structure internally.
The actual metric tensor supplies a smooth Riemannian tangent metric while
preserving all existing fiber topologies.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianRiemannianBundle

open FirstPass NaturalHermitianMetricCoefficients

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original positive metric unit ball is bounded in the original model topology. -/
theorem metric_unit_ball_bounded {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) :
    Bornology.IsVonNBounded ℝ {u : ComplexModel n | associatedMetricCLM a u u < 1} := by
  obtain ⟨c, hc, hbound⟩ := associatedMetric_coercive ha
  apply (NormedSpace.isVonNBounded_iff' (𝕜 := ℝ)).mpr
  refine ⟨1 + c⁻¹, ?_⟩
  intro u hu
  change associatedMetricCLM a u u < 1 at hu
  have hquad : ‖u‖ ^ 2 < c⁻¹ := by
    have h : c * ‖u‖ ^ 2 < 1 := (hbound u).trans_lt (by
      simpa only [associatedMetricCLM_apply] using hu)
    rw [← one_div]
    apply (lt_div_iff₀ hc).mpr
    simpa only [mul_comm] using h
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  nlinarith [norm_nonneg u, sq_nonneg (‖u‖ - 1), sq_nonneg (c⁻¹)]

/-- The original holomorphic atlas genuinely induces the real smooth manifold structure. -/
theorem real_smooth_manifold : IsManifold 𝓘(ℝ, ComplexModel n) ∞ M := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexModel n) ∞ M
  intro e f he hf
  have h : ContDiffOn ℝ ∞ (chartTransition (n := n) ⟨e, he⟩ ⟨f, hf⟩)
      (chartTransition (n := n) ⟨e, he⟩ ⟨f, hf⟩).source :=
    fun z hz => (HolomorphicMaps.chartTransition_contDiffAt_real ⟨e, he⟩ ⟨f, hf⟩ hz).contDiffWithinAt
  simpa only [chartTransition, mfld_simps] using h

local instance realSmoothManifold : IsManifold 𝓘(ℝ, ComplexModel n) ∞ M := real_smooth_manifold

/-- All literal metric coefficient properties follow from the actual original Hermitian form. -/
theorem metric_coefficients_data (w : SmoothRealForm n M 2) (hw : w.IsHermitian) :
    (∀ e, ContDiffOn ℝ ∞ (metricCoefficients w e) e.val.target) ∧
    (∀ e z, z ∈ e.val.target →
      (∀ u v, metricCoefficients w e z u v = metricCoefficients w e z v u) ∧
      (∀ u, u ≠ 0 → 0 < metricCoefficients w e z u u) ∧
      (∀ u v, metricCoefficients w e z (Complex.I • u) (Complex.I • v) = metricCoefficients w e z u v) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ metricCoefficients w e z u u) ∧
    ∀ e f z, z ∈ (chartTransition e f).source → ∀ u v,
      metricCoefficients w e z u v = metricCoefficients w f (chartTransition e f z)
        (chartTransitionDerivative e f z u) (chartTransitionDerivative e f z v) := by
  obtain ⟨G, hread, hs, hp, ht⟩ := exists_smooth_compatible_positive_metric w hw
  have heq : G = metricCoefficients w := by
    funext e z
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    rw [hread]
    exact (associatedMetricCLM_apply _ _ _).symm
  subst G
  exact ⟨hs, hp, ht⟩

/-- The literal original Hermitian metric in the preferred original real tangent coordinates. -/
def metricFiber (w : SmoothRealForm n M 2) (x : M) :
    TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexModel n) x →L[ℝ] ℝ :=
  metricCoefficients w (complexChartAt x) ((complexChartAt (n := n) x).val x)

/-- The actual inverse preferred tangent trivialization is exactly the original real chart derivative. -/
theorem preferred_trivialization_inverse (x₀ x : M)
    (hx : x ∈ (complexChartAt (n := n) x₀).val.source) :
    (trivializationAt (ComplexModel n) (TangentSpace 𝓘(ℝ, ComplexModel n)) x₀).symmL ℝ x =
      chartTransitionDerivative (complexChartAt x₀) (complexChartAt x)
        ((complexChartAt (n := n) x₀).val x) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  simp only [tangentBundleCore_coordChange_achart, chartTransitionDerivative,
    chartTransition, complexChartAt, mfld_simps, fderivWithin_univ]
  rfl

/-- Genuine full arbitrary original chart calibration of the actual tangent metric. -/
theorem metricFiber_chart_readback (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (x : M) (e : ComplexChart n M) (hx : x ∈ e.val.source) (u v : ComplexModel n) :
    metricFiber w x
      (chartTransitionDerivative e (complexChartAt x) (e.val x) u)
      (chartTransitionDerivative e (complexChartAt x) (e.val x) v) =
        associatedMetric (w.coeff e (e.val x)) u v := by
  have hz : e.val x ∈ (chartTransition e (complexChartAt (n := n) x)).source := by
    refine ⟨e.val.map_source hx, ?_⟩
    change e.val.symm (e.val x) ∈ (complexChartAt (n := n) x).val.source
    rw [e.val.left_inv hx]
    exact mem_complexChartAt_source x
  have h := (metric_coefficients_data w hw).2.2 e (complexChartAt x) (e.val x) hz u v
  have hF : chartTransition e (complexChartAt x) (e.val x) =
      (complexChartAt (n := n) x).val x := by
    change (complexChartAt (n := n) x).val (e.val.symm (e.val x)) = _
    rw [e.val.left_inv hx]
  rw [hF] at h
  exact h.symm.trans (associatedMetricCLM_apply _ _ _)

/-- Original metric coefficient smoothness and full tensor transport give actual bundle section smoothness. -/
theorem metric_section_contMDiff (w : SmoothRealForm n M 2) (hw : w.IsHermitian) :
    ContMDiff 𝓘(ℝ, ComplexModel n)
      ((𝓘(ℝ, ComplexModel n)).prod
        𝓘(ℝ, ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
        x (metricFiber w x)) := by
  intro x₀
  rw [contMDiffAt_section]
  let e₀ := complexChartAt (n := n) x₀
  have hx₀ : x₀ ∈ e₀.val.source := mem_complexChartAt_source x₀
  have heq : (fun x => (trivializationAt
      (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, ComplexModel n) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ComplexModel n) y →L[ℝ] ℝ) x₀
      ⟨x, metricFiber w x⟩).2) =ᶠ[𝓝 x₀]
      (fun x => metricCoefficients w e₀ (e₀.val x)) := by
    filter_upwards [e₀.val.open_source.mem_nhds hx₀] with x hx
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    rw [preferred_trivialization_inverse x₀ x hx]
    have hxcot : x ∈ (trivializationAt (ComplexModel n →L[ℝ] ℝ)
        (fun y => TangentSpace 𝓘(ℝ, ComplexModel n) y →L[ℝ] ℝ) x₀).baseSet := by
      change x ∈ (complexChartAt (n := n) x₀).val.source ∩ Set.univ
      exact ⟨hx, mem_univ _⟩
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hxcot]
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    rw [preferred_trivialization_inverse x₀ x hx]
    have hscalar : (trivializationAt ℝ (fun _ : M => ℝ) x₀).continuousLinearMapAt ℝ x =
        ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization ℝ M ℝ x
    rw [hscalar, ContinuousLinearMap.id_apply]
    exact metricFiber_chart_readback w hw x e₀ hx u v |>.trans
      (associatedMetricCLM_apply _ _ _).symm
  have ht : e₀.val x₀ ∈ e₀.val.target := e₀.val.map_source hx₀
  have hc := ((metric_coefficients_data w hw).1 e₀).contDiffAt
    (e₀.val.open_target.mem_nhds ht)
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, ComplexModel n) ∞ e₀.val x₀ :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e₀.property) hx₀
  exact (hc.contMDiffAt.comp x₀ hchart).congr_of_eventuallyEq heq

/-- The genuine actual smooth Riemannian tangent metric, constructed from original Hermitian data only. -/
def originalHermitianRiemannianMetric (w : SmoothRealForm n M 2) (hw : w.IsHermitian) :
    ContMDiffRiemannianMetric 𝓘(ℝ, ComplexModel n) ∞ (ComplexModel n)
      (TangentSpace 𝓘(ℝ, ComplexModel n) : M → Type) where
  inner := metricFiber w
  symm x u v := (metric_coefficients_data w hw).2.1 (complexChartAt x)
    ((complexChartAt (n := n) x).val x)
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)) |>.1 u v
  pos x u hu := (metric_coefficients_data w hw).2.1 (complexChartAt x)
    ((complexChartAt (n := n) x).val x)
    ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)) |>.2.1 u hu
  isVonNBounded x := metric_unit_ball_bounded
    ((hw (complexChartAt x) ((complexChartAt (n := n) x).val x)
      ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))).2)
  contMDiff := metric_section_contMDiff w hw

/-- Original Hermitian data alone internally supplies the actual smooth Riemannian tangent metric. -/
theorem exists_original_hermitian_riemannian_metric (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, ComplexModel n) ∞ (ComplexModel n)
        (TangentSpace 𝓘(ℝ, ComplexModel n) : M → Type),
      (∀ x (u v : TangentSpace 𝓘(ℝ, ComplexModel n) x),
        g.inner x u v = associatedMetric
          (w.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x)) u v) ∧
      ∀ x e, x ∈ e.val.source → ∀ u v : ComplexModel n,
        g.inner x
          (chartTransitionDerivative e (complexChartAt x) (e.val x) u)
          (chartTransitionDerivative e (complexChartAt x) (e.val x) v) =
            associatedMetric (w.coeff e (e.val x)) u v := by
  refine ⟨originalHermitianRiemannianMetric w hw, ?_, ?_⟩
  · intro x u v
    exact associatedMetricCLM_apply _ _ _
  · intro x e hx u v
    exact metricFiber_chart_readback w hw x e hx u v

end SGPT.Foundations.Analysis.Pending.NaturalHermitianRiemannianBundle
