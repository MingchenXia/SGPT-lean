import SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity

set_option autoImplicit false

/-! # Actual chart compatibility of the Poisson coordinate distributions -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoPoissonChartCompatibility

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  IntegrationCurrent TopDegreeDensity ClosedTopCurrents ThetaPshChartLimitGluing
  XiaoPoissonLocalDistribution XiaoPoissonLeviPositivity HolderAtlas.HolderMap
  ChartPartition PositiveProductCurrents XiaoPoissonTraceTranspose

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] {r : ℝ≥0}

/-- The actual Kähler volume transforms by the actual nonnegative real transition Jacobian. -/
theorem volDensity_eq_transitionJac (w : KahlerBackground (m + 1) M)
    (e f : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ (chartTransition e f).source) :
    volDensity w e z = transitionJac e f z * volDensity w f (chartTransition e f z) := by
  rw [transitionJac, abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hz)]
  exact topDensity_coeff_transition (formPow w.form.val (m + 1)) hz

/-- Positivity of the actual Kähler densities forces a strictly positive actual Jacobian. -/
theorem transitionJac_pos (w : KahlerBackground (m + 1) M)
    (e f : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ (chartTransition e f).source) : 0 < transitionJac e f z := by
  have hve := volDensity_pos w e hz.1
  have hvf := volDensity_pos w f ((chartTransition e f).map_source hz).1
  have hv := volDensity_eq_transitionJac w e f hz
  nlinarith

/-- Jacobian-weighted actual pullback tests give identical actual global normalized inputs. -/
theorem volumeNormalizedTestCLM_pullTest (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (e f : ComplexChart (m + 1) M)
    (ψ : 𝓓(chartTarget f, ℝ)) (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    volumeNormalizedTestCLM w A hr f ψ =
      volumeNormalizedTestCLM w A hr e
        (pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ)) := by
  ext x
  by_cases he : x ∈ e.val.source
  · by_cases hf : x ∈ f.val.source
    · have hF : e.val x ∈ (chartTransition e f).source := by
        change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source
        exact ⟨e.val.map_source he, by simpa only [e.val.left_inv he] using hf⟩
      have hFx : chartTransition e f (e.val x) = f.val x := by
        rw [chartTransition_apply_eq, e.val.left_inv he]
      rw [volumeNormalizedTestCLM_apply_of_mem w A hr f ψ hf,
        volumeNormalizedTestCLM_apply_of_mem w A hr e _ he, pullTest_apply,
        pullFun_of_mem e f ψ hF, hFx, volDensity_eq_transitionJac w e f hF, hFx]
      exact (mul_div_mul_left (ψ (f.val x)) (volDensity w f (f.val x))
        (transitionJac_pos w e f hF).ne').symm
    · have hnF : e.val x ∉ (chartTransition e f).source := by
        intro hx
        change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source at hx
        exact hf (by simpa only [e.val.left_inv he] using hx.2)
      rw [volumeNormalizedTestCLM_apply_of_notMem w A hr f ψ hf,
        volumeNormalizedTestCLM_apply_of_mem w A hr e _ he, pullTest_apply,
        pullFun_of_notMem e f ψ hnF, zero_div]
  · rw [volumeNormalizedTestCLM_apply_of_notMem w A hr e _ he]
    by_cases hf : x ∈ f.val.source
    · have hψ0 : ψ (f.val x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        have hh := hψ hxs
        change f.val x ∈ f.val.target ∧ f.val.symm (f.val x) ∈ e.val.source at hh
        exact he (by simpa only [f.val.left_inv hf] using hh.2)
      rw [volumeNormalizedTestCLM_apply_of_mem w A hr f ψ hf, hψ0, zero_div]
    · exact volumeNormalizedTestCLM_apply_of_notMem w A hr f ψ hf

/-- Ordinary coordinate distributions produced from one actual global functional are compatible. -/
theorem coordinateDistribution_apply_pullTest (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ)
    (e f : ComplexChart (m + 1) M) (ψ : 𝓓(chartTarget f, ℝ))
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    coordinateDistribution w A hr Ψ f ψ =
      coordinateDistribution w A hr Ψ e
        (pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ)) := by
  rw [coordinateDistribution_apply, coordinateDistribution_apply,
    volumeNormalizedTestCLM_pullTest w A hr e f ψ hψ]

/-- Genuine overlap compatibility for ordinary coordinate distributions. -/
def IsCoordinateCompatible (U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ)) : Prop :=
  ∀ (e f : ComplexChart (m + 1) M) (ψ : 𝓓(chartTarget f, ℝ))
    (hψ : tsupport ψ ⊆ (chartTransition e f).target),
    U f ψ = U e (pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ))

/-- The actual normalized local inputs produce genuine overlap-compatible distributions. -/
theorem isCoordinateCompatible_coordinateDistribution (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ) :
    IsCoordinateCompatible (coordinateDistribution w A hr Ψ) :=
  coordinateDistribution_apply_pullTest w A hr Ψ

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- The actual numerical gap produces compatible genuinely locally theta-PSH distributions. -/
theorem exists_gap_compatible_locally_theta_psh_distributions
    (w B : KahlerBackground (m + 1) M) (A : HolderAtlas (m + 1) M)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hM : 0 < NefMixedMass.slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral w
      (Fin.cons B.form (fun _ : Fin m => w.form)) < (kahlerVolume w).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ),
        IsCoordinateCompatible U ∧ ∀ e, IsLocallyThetaPshDistribution volume
          (((1 - δ) • w.form - B.form : ClosedRealOneOneForm (m + 1) M).val) e (U e) := by
  obtain ⟨δ, hδ0, hδ1, T, hT, Ψ, hΨ⟩ :=
    exists_gap_positive_current_continuous_transpose w B A hr0 hr1 hM hgap
  refine ⟨δ, hδ0, hδ1, coordinateDistribution w A hr1.le Ψ,
    isCoordinateCompatible_coordinateDistribution w A hr1.le Ψ, ?_⟩
  intro e
  apply isLocallyThetaPshDistribution_of_continuous_transpose w A hr1.le
    ((1 - δ) • w.form - B.form) T hT Ψ
  intro G
  rw [closedForm_smul_sub_val]
  exact hΨ G

end

end SGPT.Foundations.Analysis.Pending.XiaoPoissonChartCompatibility
