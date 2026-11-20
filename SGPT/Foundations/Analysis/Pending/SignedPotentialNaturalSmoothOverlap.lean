import SGPT.Foundations.Analysis.Pending.SignedPotentialChartSmoothDifference
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! SAME original signed current and arbitrary full-chart LF potentials receive
an internally constructed unit cutoff and genuine smooth local difference.
No quasi-PSH/L1 representative or supplied difference equation is used. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.SignedPotentialNaturalSmoothOverlap
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DistributionFullChartCutoffTransport LelongPoincareDivisor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Natural chart point and neighborhood internally supply all unit-cutoff data,
including compact support, the smaller open patch and its point membership. -/
theorem exists_unit_chart_patch (e f : ComplexChart n M)
    {P : Opens (ComplexModel n)} (hP : P ≤ chartTarget f)
    (x : ComplexModel n) (hx : x ∈ (chartTransition e f).source)
    (hxp : (chartTransition e f) x ∈ P) :
    ∃ (χ : M → ℝ) (_hχ : ChartSmooth (n := n) χ)
      (_hc : IsCompact (tsupport χ)) (_hs : tsupport χ ⊆ f.val.source)
      (P₀ : Opens (ComplexModel n)) (_hP₀ : P₀ ≤ P),
      (chartTransition e f) x ∈ P₀ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        ∀ z ∈ P₀, χ (f.val.symm z) = 1 := by
  let p := e.val.symm x
  let O : Opens M := ⟨f.val.source ∩ f.val ⁻¹' P,
    f.val.isOpen_inter_preimage P.isOpen⟩
  have hp : p ∈ O := ⟨hx.2, hxp⟩
  obtain ⟨χ, hχ, hnon, hle, hsO, hc, hone⟩ :=
    ChartPartition.exists_chartSmooth_bump (n := n) p O hp
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hone
  let P₀ : Opens (ComplexModel n) :=
    ⟨f.val.target ∩ f.val.symm ⁻¹' (V ∩ O),
      f.val.symm.isOpen_inter_preimage (hVo.inter O.isOpen)⟩
  have hP₀ : P₀ ≤ P := by
    intro z hz
    have h := hz.2.2.2
    change f.val (f.val.symm z) ∈ P at h
    rw [f.val.right_inv hz.1] at h
    exact h
  have hx₀ : (chartTransition e f) x ∈ P₀ := by
    refine ⟨hP hxp, ?_⟩
    change f.val.symm (f.val p) ∈ V ∩ O
    have hpfs : p ∈ f.val.source := hx.2
    rw [f.val.left_inv hpfs]
    exact ⟨hpV, hp⟩
  refine ⟨χ, hχ, hc, (hsO.trans inter_subset_left), P₀, hP₀, hx₀,
    (fun y => ⟨hnon y, hle y⟩), ?_⟩
  intro z hz
  exact hV hz.2.1

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- All cutoffs and neighborhoods are outputs. The input is only SAME original
signed T, natural local potential equations and an actual overlap point. -/
theorem exists_natural_smooth_overlap
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent n M (degreeTwo hn)) (e f : ComplexChart n M)
    {Ω P : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    (R : 𝓓'(chartTarget e, ℝ)) (S : 𝓓'(chartTarget f, ℝ))
    (hR : ddC (restrictDistribution R hΩ) = restrictForm (T.coefficients b e) hΩ)
    (hS : ddC (restrictDistribution S hP) = restrictForm (T.coefficients b f) hP)
    (x : ComplexModel n) (hxΩ : x ∈ Ω)
    (hxf : x ∈ (chartTransition e f).source) (hxp : (chartTransition e f) x ∈ P) :
    ∃ (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
      (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ f.val.source)
      (W : Opens (ComplexModel n)) (hWe : W ≤ chartTarget e) (h : ComplexModel n → ℝ),
      x ∈ W ∧ W ≤ Ω ∧
      (W : Set (ComplexModel n)) ⊆ (chartTransition e f).source ∩
        (chartTransition e f) ⁻¹' (P : Set (ComplexModel n)) ∧
      ContDiff ℝ (⊤ : ℕ∞) h ∧
      ∃ hh : LocallyIntegrableOn h W μ,
        restrictDistribution R hWe -
            restrictDistribution (weightedChartDistribution e f χ hχ hc hs S) hWe =
          regularDistribution μ h hh ∧
        ∀ z ∈ W, ∀ v : ComplexModel n, leviForm h z v = 0 := by
  obtain ⟨χ, hχ, hc, hs, P₀, hP₀, hx₀, _hrange, hunit⟩ :=
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
      e f hΩ (hP₀.trans hP) R S hR hS₀ χ hχ hc hs hunit
  obtain ⟨W, hWU, h, hxW, hcont, hh, hreg, hlevi⟩ := hsm x hxU
  let hWe : W ≤ chartTarget e := hWU.trans hUe
  refine ⟨χ, hχ, hc, hs, W, hWe, h, hxW,
    (fun z hz => (hWU hz).1), (fun z hz => ⟨(hWU hz).2.1, hP₀ (hWU hz).2.2⟩),
    hcont, hh, ?_, hlevi⟩
  have hcollapse :
      restrictDistribution
        (restrictDistribution R hUe -
          restrictDistribution (weightedChartDistribution e f χ hχ hc hs S) hUe) hWU =
      restrictDistribution R hWe -
        restrictDistribution (weightedChartDistribution e f χ hχ hc hs S) hWe := by
    ext φ
    change R (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ)) -
        S (fullChartTestCLM e f χ hχ hc hs
          (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ))) =
      R (TestFunction.monoCLM ℝ φ) -
        S (fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ φ))
    have hi : (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) : 𝓓(chartTarget e, ℝ)) =
        (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) := by
      apply TestFunction.ext
      intro z
      rw [testFunction_inclusion_coe hUe, testFunction_inclusion_coe hWU,
        testFunction_inclusion_coe hWe]
    rw [hi]
  exact hcollapse.symm.trans hreg

end SGPT.Foundations.Analysis.Pending.SignedPotentialNaturalSmoothOverlap
