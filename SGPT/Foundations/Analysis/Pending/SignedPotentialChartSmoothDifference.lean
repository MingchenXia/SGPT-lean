import SGPT.Foundations.Analysis.Pending.SignedCurrentPotentialFullOverlap
import SGPT.Foundations.Analysis.Pending.DistributionPotentialSmoothOverlap
import SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport

set_option autoImplicit false

/-! Arbitrary signed chart distribution potentials of the same original current
have a genuinely smooth pluriharmonic difference on a natural unit-cutoff patch.
The full ddC equality is produced from original tests, not supplied. Unit weight
normalization is natural modular data; the next internal bump consumer will
supply it near any original overlap point. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.SignedPotentialChartSmoothDifference
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  ThetaPshChartLimitGluing DistributionFullChartCutoffTransport DistributionCutoffExtension
  FiniteScalarDistributionGluing DistributionDdcChartCovariance DistributionChartPullback
  DDCOverlap LelongPoincareDivisor SignedCurrentPotentialFullOverlap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem transitionJac_self (f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ f.val.target) : transitionJac f f z = 1 := by
  have heq : (chartTransition f f : ComplexModel n → ComplexModel n) =ᶠ[𝓝 z] id := by
    filter_upwards [f.val.open_target.mem_nhds hz] with y hy
    exact f.val.right_inv hy
  have hd : chartTransitionDerivative f f z = ContinuousLinearMap.id ℝ (ComplexModel n) :=
    ((hasFDerivAt_id z).congr_of_eventuallyEq heq).fderiv
  change |(chartTransitionDerivative f f z).det| = 1
  rw [hd]
  change |LinearMap.det (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)| = 1
  rw [LinearMap.det_id, abs_one]

/-- Actual full-chart self transport is the original LF cutoff map, alln0. -/
theorem fullChartTestCLM_self (f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (φ : 𝓓(chartTarget f, ℝ)) :
    fullChartTestCLM f f χ hχ hc hs φ = cutoffTestCLM (chartWeightTest f χ hχ hc hs) φ := by
  classical
  apply TestFunction.ext
  intro z
  rw [fullChartTestCLM_value]
  change (if z ∈ (chartTransition f f).source then
      χ (f.val.symm z) * transitionJac f f z * φ ((chartTransition f f) z) else 0) =
    φ z * chartWeightTest f χ hχ hc hs z
  by_cases hz : z ∈ f.val.target
  · have hzs : z ∈ (chartTransition f f).source := ⟨hz, f.val.map_target hz⟩
    rw [if_pos hzs, transitionJac_self f hz]
    change χ (f.val.symm z) * 1 * φ (f.val (f.val.symm z)) =
      φ z * f.val.target.indicator (fun y => χ (f.val.symm y)) z
    rw [f.val.right_inv hz, indicator_of_mem hz, mul_one, mul_comm]
  · have hzs : z ∉ (chartTransition f f).source := fun h => hz h.1
    rw [if_neg hzs]
    change 0 = φ z * f.val.target.indicator (fun y => χ (f.val.symm y)) z
    rw [indicator_of_notMem hz, mul_zero]

/-- Native tensor-related tests internally give the literal weighted adjoint
transport, without any supplied adjoint or distribution covariance equality. -/
theorem adjoint_weighted_transport {q : ℕ}
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (e f : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ f.val.source)
    (η : TestForm (overlapSource e f) q) (ζ : TestForm (overlapTarget e f) q)
    (hrel : OverlapTestRelated e f η ζ) :
    fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ (ddcAdjoint B η)) =
      cutoffTestCLM (chartWeightTest f χ hχ hc hs)
        (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(chartTarget f, ℝ)) := by
  have hscalar : ∀ z ∈ (chartTransition e f).source,
      ddcAdjoint B η z = transitionJac e f z * ddcAdjoint B ζ ((chartTransition e f) z) := by
    intro z hz
    have h := congrArg (fun φ : 𝓓(overlapSource e f, ℝ) => φ z)
      (weighted_adjoint_eq B e f η ζ hrel)
    change pullFun e f (ddcAdjoint B ζ) z = ddcAdjoint B η z at h
    rw [pullFun_of_mem e f _ hz] at h
    exact h.symm
  exact (fullChartTestCLM_overlap e f f χ hχ hc hs
    (ddcAdjoint B η) (ddcAdjoint B ζ) hscalar).trans
      (fullChartTestCLM_self f χ hχ hc hs _)

private theorem adjoint_mono {Ω U : Opens (ComplexModel n)} {q : ℕ}
    (hU : U ≤ Ω) (B : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm U q) :
    ddcAdjoint B (TestFunction.monoCLM ℝ η : TestForm Ω q) =
      (TestFunction.monoCLM ℝ (ddcAdjoint B η) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro z
  rw [ddcAdjoint_monoCLM_apply hU, testFunction_inclusion_coe hU]

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

private theorem coefficient_pairing {Ω : Opens (ComplexModel n)}
    (A : DistributionForm Ω 2) (w : Fin 2 → ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    A w φ = wedgePairing (currentPairingBasis b (degreeTwo hn)) A
      (constantTestFormCLM (contractVolume (basisVolume (currentPairingBasis b (degreeTwo hn))) w) φ) := by
  exact (congrArg (fun C : DistributionForm Ω 2 => C w φ)
    (CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) A)).symm

/-- SAME original signed T and natural full-chart scalar potentials internally
supply actual ddC equality and a smooth pluriharmonic distribution difference.
Only natural unit-patch cutoff normalization is given, no difference certificate. -/
theorem exists_smooth_difference_in_unit_patch
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent n M (degreeTwo hn)) (e f : ComplexChart n M)
    {Ω P : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    (R : 𝓓'(chartTarget e, ℝ)) (S : 𝓓'(chartTarget f, ℝ))
    (hR : ddC (restrictDistribution R hΩ) = restrictForm (T.coefficients b e) hΩ)
    (hS : ddC (restrictDistribution S hP) = restrictForm (T.coefficients b f) hP)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (hunit : ∀ z ∈ P, χ (f.val.symm z) = 1) :
    let F := chartTransition e f
    let U : Opens (ComplexModel n) :=
      ⟨Ω ∩ (F.source ∩ F ⁻¹' P), Ω.isOpen.inter (F.isOpen_inter_preimage P.isOpen)⟩
    let hUe : U ≤ chartTarget e := fun _ hz => hΩ hz.1
    let Q := weightedChartDistribution e f χ hχ hc hs S
    ddC (restrictDistribution R hUe) = ddC (restrictDistribution Q hUe) ∧
      ∀ x ∈ U, ∃ (W : Opens (ComplexModel n)) (hWU : W ≤ U) (k : ComplexModel n → ℝ),
        x ∈ W ∧ ContDiff ℝ (⊤ : ℕ∞) k ∧
        ∃ hk : LocallyIntegrableOn k W μ,
          restrictDistribution (restrictDistribution R hUe - restrictDistribution Q hUe) hWU =
            regularDistribution μ k hk ∧
          ∀ z ∈ W, ∀ v : ComplexModel n, leviForm k z v = 0 := by
  intro F U hUe Q
  have hUΩ : U ≤ Ω := fun _ hz => hz.1
  have hUS : U ≤ overlapSource e f := fun _ hz => hz.2.1
  have hUΩS : U ≤ Ω ⊓ overlapSource e f := fun _ hz => ⟨hz.1, hz.2.1⟩
  let B := currentPairingBasis b (degreeTwo hn)
  have heq : ddC (restrictDistribution R hUe) = ddC (restrictDistribution Q hUe) := by
    ext w φ
    let γ := contractVolume (basisVolume B) w
    let η := constantTestFormCLM γ φ
    obtain ⟨ζ, _hsupp, _hval, hζ⟩ :=
      ActualChartOverlapTestTransport.exists_constant_form_counterpart e f Ω P
        (Module.finrank ℝ (ComplexModel n) - 2) φ γ
    let ηO : TestForm (Ω ⊓ overlapSource e f) _ := TestFunction.monoCLM ℝ η
    let ηS : TestForm (overlapSource e f) _ := TestFunction.monoCLM ℝ η
    let ζT : TestForm (overlapTarget e f) _ := TestFunction.monoCLM ℝ ζ
    have hrelO : ∀ x ∈ F.source, ∀ v : Fin (Module.finrank ℝ (ComplexModel n) - 2) →
        ComplexModel n, ηO x v = ζ (F x) (fun i => chartTransitionDerivative e f x (v i)) := by
      intro x hx v
      rw [testForm_inclusion_apply hUΩS]
      exact hζ x hx v
    have hrelS : OverlapTestRelated e f ηS ζT := by
      intro x hx v
      rw [testForm_inclusion_apply hUS, testForm_inclusion_apply inf_le_right]
      exact hζ x hx v
    have hpaired := (original_signed_potential_full_overlap b hn T e f hΩ hP
      (restrictDistribution R hΩ) (restrictDistribution S hP) hR hS).2.2 ηO ζ hrelO
    change R (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ (ddcAdjoint B ηO) : 𝓓(Ω, ℝ))) =
      S (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(P, ℝ))) at hpaired
    have hRtest : (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ (ddcAdjoint B ηO) : 𝓓(Ω, ℝ)) : 𝓓(chartTarget e, ℝ)) =
        TestFunction.monoCLM ℝ (ddcAdjoint B η) := by
      apply TestFunction.ext
      intro z
      rw [testFunction_inclusion_coe hΩ, testFunction_inclusion_coe inf_le_left,
        ddcAdjoint_monoCLM_apply hUΩS, testFunction_inclusion_coe hUe]
    have hζtest : (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(P, ℝ)) : 𝓓(chartTarget f, ℝ)) =
        TestFunction.monoCLM ℝ (ddcAdjoint B ζ) := by
      apply TestFunction.ext
      intro z
      rw [testFunction_inclusion_coe hP, testFunction_inclusion_coe inf_le_left,
        testFunction_inclusion_coe (inf_le_left.trans hP)]
    rw [hRtest, hζtest] at hpaired
    have ht := adjoint_weighted_transport B e f χ hχ hc hs ηS ζT hrelS
    have hηtest : (TestFunction.monoCLM ℝ (ddcAdjoint B ηS) : 𝓓(chartTarget e, ℝ)) =
        TestFunction.monoCLM ℝ (ddcAdjoint B η) := by
      apply TestFunction.ext
      intro z
      rw [testFunction_inclusion_coe (overlapSource_le e f),
        ddcAdjoint_monoCLM_apply hUS, testFunction_inclusion_coe hUe]
    have hζtest' : (TestFunction.monoCLM ℝ (ddcAdjoint B ζT) : 𝓓(chartTarget f, ℝ)) =
        TestFunction.monoCLM ℝ (ddcAdjoint B ζ) := by
      apply TestFunction.ext
      intro z
      rw [testFunction_inclusion_coe (overlapTarget_le e f),
        ddcAdjoint_monoCLM_apply inf_le_right,
        testFunction_inclusion_coe (inf_le_left.trans hP)]
    have hcut : cutoffTestCLM (chartWeightTest f χ hχ hc hs)
        (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(chartTarget f, ℝ)) =
        (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(chartTarget f, ℝ)) := by
      apply TestFunction.ext
      intro z
      change (TestFunction.monoCLM ℝ (ddcAdjoint B ζ) : 𝓓(chartTarget f, ℝ)) z *
          chartWeightTest f χ hχ hc hs z = _
      rw [testFunction_inclusion_coe (inf_le_left.trans hP)]
      by_cases hz : z ∈ P
      · have hκ : chartWeightTest f χ hχ hc hs z = 1 := by
          change f.val.target.indicator (fun y => χ (f.val.symm y)) z = 1
          have hz' : z ∈ f.val.target := hP hz
          rw [indicator_of_mem hz', hunit z hz]
        rw [hκ, mul_one]
      · have hzero : ddcAdjoint B ζ z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hz ((ddcAdjoint B ζ).tsupport_subset h).1)
        rw [hzero, zero_mul]
    rw [hηtest, hζtest', hcut] at ht
    rw [coefficient_pairing b hn, coefficient_pairing b hn, wedgePairing_ddC, wedgePairing_ddC]
    change R (TestFunction.monoCLM ℝ (ddcAdjoint B η)) =
      S (fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ (ddcAdjoint B η)))
    exact hpaired.trans (congrArg S ht).symm
  refine ⟨heq, ?_⟩
  intro x hx
  exact DistributionPotentialSmoothOverlap.exists_smooth_difference_of_equal_ddC μ
    (restrictDistribution R hUe) (restrictDistribution Q hUe) heq x hx

end SGPT.Foundations.Analysis.Pending.SignedPotentialChartSmoothDifference
