import SGPT.Foundations.Analysis.Pending.SignedPotentialNaturalSmoothOverlap
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth

set_option autoImplicit false

/-! Original signed partition-weighted potential differences. The actual LF
multiplier is used only in its arbitrary smooth-input scope; no positive
Bedford--Taylor assertion or integrable potential density is required. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.SignedPotentialWeightedSmoothDifference
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DistributionFullChartCutoffTransport LocalBedfordTaylorSmooth LelongPoincareDivisor
  SignedPotentialNaturalSmoothOverlap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal whole-chart transport factorization on an actual unit patch,
retaining the original LF smooth multiplier and every compact smooth test. -/
theorem full_transport_weight_factor (e f : ComplexChart n M)
    (χ ξ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hξ : ChartSmooth (n := n) ξ)
    (hc : IsCompact (tsupport χ)) (hξc : IsCompact (tsupport ξ))
    (hs : tsupport χ ⊆ f.val.source) (hξs : tsupport ξ ⊆ f.val.source)
    {U : Opens (ComplexModel n)} (hUe : U ≤ chartTarget e)
    (_hUF : (U : Set (ComplexModel n)) ⊆ (chartTransition e f).source)
    (hunit : ∀ y ∈ U, ξ (f.val.symm ((chartTransition e f) y)) = 1)
    (φ : 𝓓(U, ℝ)) :
    fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ φ) =
      fullChartTestCLM e f ξ hξ hξc hξs
        (TestFunction.monoCLM ℝ (mulSmoothOnCLM ((hχ e).mono hUe) φ)) := by
  classical
  apply TestFunction.ext
  intro z
  rw [fullChartTestCLM_value, fullChartTestCLM_value]
  by_cases hz : z ∈ (chartTransition f e).source
  · rw [if_pos hz, if_pos hz]
    rw [testFunction_inclusion_coe hUe,
      testFunction_inclusion_coe hUe, mulSmoothOnCLM_apply]
    by_cases hφ : φ ((chartTransition f e) z) = 0
    · simp [hφ]
    have hy : (chartTransition f e) z ∈ U := φ.tsupport_subset (subset_tsupport _ hφ)
    have hback : (chartTransition e f) ((chartTransition f e) z) = z :=
      (chartTransition f e).left_inv hz
    have hξone : ξ (f.val.symm z) = 1 := by
      have h := hunit _ hy
      rw [hback] at h
      exact h
    have heinv : e.val.symm ((chartTransition f e) z) = f.val.symm z :=
      e.val.left_inv hz.2
    rw [hξone, heinv]
    ring
  · rw [if_neg hz, if_neg hz]

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- SAME original T internally produces the smooth difference of the original
weighted terms, without an auxiliary unit cutoff or regular representative. -/
theorem exists_weighted_smooth_difference
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent n M (degreeTwo hn)) (e f : ComplexChart n M)
    {Ω P : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    (R : 𝓓'(chartTarget e, ℝ)) (S : 𝓓'(chartTarget f, ℝ))
    (hR : ddC (restrictDistribution R hΩ) = restrictForm (T.coefficients b e) hΩ)
    (hS : ddC (restrictDistribution S hP) = restrictForm (T.coefficients b f) hP)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source)
    (x : ComplexModel n) (hxΩ : x ∈ Ω)
    (hxf : x ∈ (chartTransition e f).source) (hxp : (chartTransition e f) x ∈ P) :
    ∃ (W : Opens (ComplexModel n)) (hWe : W ≤ chartTarget e)
      (ha : ContDiffOn ℝ ∞ (fun y => χ (e.val.symm y)) W) (k : ComplexModel n → ℝ),
      x ∈ W ∧ W ≤ Ω ∧
      (W : Set (ComplexModel n)) ⊆ (chartTransition e f).source ∩
        (chartTransition e f) ⁻¹' (P : Set (ComplexModel n)) ∧
      ContDiffOn ℝ ∞ k W ∧
      ∃ hk : LocallyIntegrableOn k W μ,
        precompLM (mulSmoothOnCLM ha) (restrictDistribution R hWe) -
            restrictDistribution (weightedChartDistribution e f χ hχ hc hs S) hWe =
          regularDistribution μ k hk := by
  obtain ⟨ξ, hξ, hξc, hξs, P₀, hP₀, hx₀, _hrange, hunit⟩ :=
    exists_unit_chart_patch e f hP x hxf hxp
  have hS₀ : ddC (restrictDistribution S (hP₀.trans hP)) =
      restrictForm (T.coefficients b f) (hP₀.trans hP) := by
    calc
      ddC (restrictDistribution S (hP₀.trans hP)) =
          ddC (restrictDistribution (restrictDistribution S hP) hP₀) :=
        congrArg ddC (restrictDistribution_trans S hP₀ hP).symm
      _ = restrictForm (ddC (restrictDistribution S hP)) hP₀ :=
        (restrictForm_ddC _ hP₀).symm
      _ = restrictForm (restrictForm (T.coefficients b f) hP) hP₀ :=
        congrArg (fun A => restrictForm A hP₀) hS
      _ = restrictForm (T.coefficients b f) (hP₀.trans hP) := by
        ext w φ
        change restrictDistribution (restrictDistribution ((T.coefficients b f) w) hP)
            hP₀ φ = restrictDistribution ((T.coefficients b f) w) (hP₀.trans hP) φ
        rw [restrictDistribution_trans]
  let F := chartTransition e f
  let U : Opens (ComplexModel n) :=
    ⟨Ω ∩ (F.source ∩ F ⁻¹' P₀), Ω.isOpen.inter (F.isOpen_inter_preimage P₀.isOpen)⟩
  have hUe : U ≤ chartTarget e := fun _ hz => hΩ hz.1
  have hxU : x ∈ U := ⟨hxΩ, hxf, hx₀⟩
  obtain ⟨_hddC, hsm⟩ :=
    SignedPotentialChartSmoothDifference.exists_smooth_difference_in_unit_patch b hn μ T
      e f hΩ (hP₀.trans hP) R S hR hS₀ ξ hξ hξc hξs hunit
  obtain ⟨W, hWU, h, hxW, hcont, hh, hreg, _hlevi⟩ := hsm x hxU
  let hWe : W ≤ chartTarget e := hWU.trans hUe
  have ha : ContDiffOn ℝ ∞ (fun y => χ (e.val.symm y)) W := (hχ e).mono hWe
  let k := fun y => χ (e.val.symm y) * h y
  have hkcont : ContDiffOn ℝ ∞ k W := ha.mul hcont.contDiffOn
  have hk : LocallyIntegrableOn k W μ :=
    hkcont.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  refine ⟨W, hWe, ha, k, hxW, (fun z hz => (hWU hz).1),
    (fun z hz => ⟨(hWU hz).2.1, hP₀ (hWU hz).2.2⟩), hkcont, hk, ?_⟩
  ext φ
  let ψ := mulSmoothOnCLM ha φ
  have hfactor := full_transport_weight_factor e f χ ξ hχ hξ hc hξc hs hξs hWe
    (fun z hz => (hWU hz).2.1) (fun z hz => hunit _ (hWU hz).2.2) φ
  have heval := congrArg (fun D : 𝓓'(W, ℝ) => D ψ) hreg
  change R (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ ψ)) -
      S (fullChartTestCLM e f ξ hξ hξc hξs
        (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ ψ))) =
    regularDistribution μ h hh ψ at heval
  have hi : (TestFunction.monoCLM ℝ
      (TestFunction.monoCLM ℝ ψ : 𝓓(U, ℝ)) : 𝓓(chartTarget e, ℝ)) =
      (TestFunction.monoCLM ℝ ψ : 𝓓(chartTarget e, ℝ)) := by
    apply TestFunction.ext
    intro z
    rw [testFunction_inclusion_coe hUe, testFunction_inclusion_coe hWU,
      testFunction_inclusion_coe hWe]
  rw [hi] at heval
  change R (TestFunction.monoCLM ℝ ψ) -
      S (fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ φ)) = _
  rw [hfactor]
  refine heval.trans ?_
  rw [regularDistribution_apply, regularDistribution_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change (φ z * χ (e.val.symm z)) * h z = φ z * (χ (e.val.symm z) * h z)
    exact mul_assoc _ _ _

end SGPT.Foundations.Analysis.Pending.SignedPotentialWeightedSmoothDifference
