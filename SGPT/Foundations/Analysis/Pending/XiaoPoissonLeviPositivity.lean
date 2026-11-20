import SGPT.Foundations.Analysis.Pending.XiaoPoissonLocalDistribution
import SGPT.Foundations.Analysis.Pending.XiaoLeviTestDDCDensity

set_option autoImplicit false

/-! # The actual Poisson coordinate distributions satisfy the genuine Levi identity -/

open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions NNReal

namespace SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  PositiveProductCurrents IntegrationCurrent TopDegreeDensity SmoothCurrentTraceMeasure
  ChartPartition SlotTestForms PositivityLeviLink ThetaPshChartLimitGluing
  XiaoComplexDifferential XiaoPositiveGauduchonExtension XiaoPoissonTraceTranspose
  XiaoPoissonLocalDistribution XiaoLeviTestDDCDensity HolderAtlas.HolderMap TopBidimensionCurrents

noncomputable section

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {Ω : TopologicalSpace.Opens E}

/-- The actual infinite-order scalar test-function directional Levi operator. -/
def testLeviCLM (a : E) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  (1 / 4 : ℝ) •
    ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a) +
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • a)).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • a)))

@[simp] theorem testLeviCLM_apply (a : E) (φ : 𝓓(Ω, ℝ)) (x : E) :
    testLeviCLM a φ x = leviForm φ x a := by
  simp only [testLeviCLM, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    testFunction_lineDerivCLM_lineDerivCLM_apply, smul_eq_mul, leviForm]
  ring

/-- The actual distributional Levi derivative is the transpose of the actual test Levi map. -/
theorem distributionalLeviCLM_eq_testLevi (U : 𝓓'(Ω, ℝ)) (a : E) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM a U φ = U (testLeviCLM a φ) := by
  rw [distributionalLeviCLM_apply]
  simp only [testLeviCLM, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    map_smul, map_add, smul_eq_mul]

end Adjoint

section Inputs

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] {r : ℝ≥0}

/-- The genuine intrinsic `ddᶜ` ratio is the actual normalized ordinary Levi test input. -/
theorem normalizedInput_ddc_leviTest (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (e : ComplexChart (m + 1) M)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1)
    (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (m + 1) → ℝ) =ᶠ[𝓝 z] 1) :
    ofChartSmooth (A := A) (k := 0) hr
      (topRatio w.form.val (ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))))
      (chartSmooth_topRatio w.isKahler.1 _) =
        ((m.factorial : ℝ) / Real.pi ^ (m + 1)) •
          volumeNormalizedTestCLM w A hr e (testLeviCLM a φ) := by
  ext x
  change topRatio w.form.val (ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))) x =
    ((m.factorial : ℝ) / Real.pi ^ (m + 1)) *
      volumeNormalizedTestCLM w A hr e (testLeviCLM a φ) x
  by_cases hx : x ∈ e.val.source
  · rw [topRatio_eq_chartRatio w.isKahler.1 _ hx, chartRatio,
      topDensity_ddc_leviTest e ψ φ a ha hψ (e.val.map_source hx),
      volumeNormalizedTestCLM_apply_of_mem w A hr e _ hx, testLeviCLM_apply]
    change (_ * leviForm φ (e.val x) a) / ClosedTopCurrents.volDensity w e (e.val x) = _
    ring
  · have hxI : x ∉ e.val.symm '' tsupport φ := fun h =>
      hx (image_symm_subset_source φ.tsupport_subset h)
    rw [topRatio_ddc_leviTest_eq_zero_of_notMem_image w e ψ φ a hxI,
      volumeNormalizedTestCLM_apply_of_notMem w A hr e _ hx, mul_zero]

end Inputs

section Positivity

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {r : ℝ≥0}

/-- The actual tensor pairing with a closed real `(1,1)`-form is the existing one-slot smooth current. -/
theorem smoothTestPairing_eq_smoothCurrent (w : KahlerBackground (m + 1) M)
    (θ : ClosedRealOneOneForm (m + 1) M) (G : testSpace (m + 1) M m) :
    smoothTestPairing w θ.val G = smoothCurrent (q := m) (p := 1) w ![θ] G := by
  rfl

/-- The genuine continuous transpose yields the actual Levi identity on actual Levi tests. -/
theorem leviTestIdentity_of_continuous_transpose (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (θ : ClosedRealOneOneForm (m + 1) M)
    (T : ProductCurrent (m + 1) M m) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ)
    (hΨ : ∀ G : testSpace (m + 1) M m,
      Ψ (ofChartSmooth (A := A) (k := 0) hr
        (topRatio w.form.val (ddc (G : SmoothRealForm (m + 1) M (2 * m))))
        (chartSmooth_topRatio w.isKahler.1 _)) = T G - smoothTestPairing w θ.val G) :
    LeviTestIdentity w T θ (coordinateDistribution w A hr Ψ) := by
  intro e ψ φ a ha _hφ hψ
  have hh := hΨ (leviTest e ψ a φ)
  rw [normalizedInput_ddc_leviTest w A hr e ψ φ a ha hψ, map_smul,
    smul_eq_mul, ← coordinateDistribution_apply w A hr Ψ e (testLeviCLM a φ),
    ← distributionalLeviCLM_eq_testLevi, smoothTestPairing_eq_smoothCurrent] at hh
  change T (leviTest e ψ a φ) =
    smoothCurrent (q := m) (p := 1) w ![θ] (leviTest e ψ a φ) +
      ((m.factorial : ℝ) / Real.pi ^ (m + 1)) *
        distributionalLeviCLM a (coordinateDistribution w A hr Ψ e) φ
  linarith

/-- Positivity and the actual continuous transpose give actual local theta-PSH distributions. -/
theorem isLocallyThetaPshDistribution_of_continuous_transpose (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (θ : ClosedRealOneOneForm (m + 1) M)
    (T : ProductCurrent (m + 1) M m) (hT : IsPositive T) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ)
    (hΨ : ∀ G : testSpace (m + 1) M m,
      Ψ (ofChartSmooth (A := A) (k := 0) hr
        (topRatio w.form.val (ddc (G : SmoothRealForm (m + 1) M (2 * m))))
        (chartSmooth_topRatio w.isKahler.1 _)) = T G - smoothTestPairing w θ.val G)
    (e : ComplexChart (m + 1) M) :
    IsLocallyThetaPshDistribution volume θ.val e (coordinateDistribution w A hr Ψ e) :=
  isLocallyThetaPshDistribution_of_leviTest w hT θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
    _ (leviTestIdentity_of_continuous_transpose w A hr θ T Ψ hΨ) e

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The closed-form scalar difference has exactly the actual smooth-form scalar difference. -/
theorem closedForm_smul_sub_val (c : ℝ) (α β : ClosedRealOneOneForm (m + 1) M) :
    (c • α - β).val = c • α.val - β.val := by
  apply smoothRealForm_ext
  intro e z
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg,
    ProductTestForms.coeff_add, ProductTestForms.coeff_smul, ProductTestForms.coeff_neg]

variable [ConnectedSpace M]

/-- The numerical gap produces genuinely locally theta-PSH ordinary coordinate distributions. -/
theorem exists_gap_locally_theta_psh_distributions (w B : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (hM : 0 < NefMixedMass.slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral w
      (Fin.cons B.form (fun _ : Fin m => w.form)) < (kahlerVolume w).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ),
        ∀ e, IsLocallyThetaPshDistribution volume
          (((1 - δ) • w.form - B.form : ClosedRealOneOneForm (m + 1) M).val) e (U e) := by
  obtain ⟨δ, hδ0, hδ1, T, hT, Ψ, hΨ⟩ :=
    exists_gap_positive_current_continuous_transpose w B A hr0 hr1 hM hgap
  refine ⟨δ, hδ0, hδ1, coordinateDistribution w A hr1.le Ψ, ?_⟩
  intro e
  apply isLocallyThetaPshDistribution_of_continuous_transpose w A hr1.le
    ((1 - δ) • w.form - B.form) T hT Ψ
  intro G
  rw [closedForm_smul_sub_val]
  exact hΨ G

end Positivity

end

end SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity
