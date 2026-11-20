import SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
import SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalPotentialPartition
import SGPT.Foundations.Analysis.Pending.CurrentPairing

set_option autoImplicit false

/-! Internally glued scalar distributions are realized in the ORIGINAL
GlobalCurrent degree-zero space. Full tensor overlap compatibility is produced,
not supplied. Entire BP preceded this source. Global ddC/smooth BC is subsequent. -/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarCurrent
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  ThetaPshChartLimitGluing FiniteScalarDistributionGluing
  DistributionFullChartCutoffTransport ClosedCurrentLocalPotentialPartition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- Original tensor overlap of top-form tests gives the true scalar-density
Jacobian relation; n0 uses the genuine empty basis/determinant convention. -/
theorem top_test_scalar_overlap (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n)))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n)))
    (hrel : OverlapTestRelated e f η θ) :
    ∀ z ∈ (chartTransition e f).source,
      testCoefficientCLM b η z = transitionJac e f z *
        testCoefficientCLM b θ ((chartTransition e f) z) := by
  intro z hz
  rw [testCoefficientCLM_apply, testCoefficientCLM_apply, hrel z hz b]
  let D := chartTransitionDerivative e f z
  let W := θ ((chartTransition e f) z)
  have ht := congrArg
    (fun A : (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n))]→ₗ[ℝ] ℝ =>
      A (D ∘ b)) (W.eq_smul_basis_det b)
  have hd : b.det (D ∘ b) = LinearMap.det D.toLinearMap := by
    change b.det (D.toLinearMap ∘ b) = _
    rw [b.det_comp, b.det_self, mul_one]
  calc
    W (D ∘ b) = ((W b) • b.det) (D ∘ b) := ht
    _ = W b * b.det (D ∘ b) := by simp
    _ = D.det * W b := by rw [hd]; exact mul_comm _ _
    _ = transitionJac e f z * W b := by
      unfold transitionJac
      rw [abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hz)]

private theorem testCoefficient_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω U : Opens E} {q : ℕ} (hU : U ≤ Ω) (v : Fin q → E) (η : TestForm U q) :
    testCoefficientCLM v (TestFunction.monoCLM ℝ η : TestForm Ω q) =
      (TestFunction.monoCLM ℝ (testCoefficientCLM v η) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro z
  rw [testCoefficientCLM_apply, testForm_inclusion_apply hU,
    testFunction_inclusion_coe hU]
  rfl

private def scalarCurrentFamily
    (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)) :
    ChartCurrentFamily n M (0 : CurrentDegree n) :=
  fun e => S e |>.comp (testCoefficientCLM b)

private theorem scalarCurrentFamily_compatible
    (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hS : ScalarFamilyCompatible S) : CurrentFamilyCompatible (scalarCurrentFamily b S) := by
  intro e f η θ hrel
  change S e (testCoefficientCLM b (TestFunction.monoCLM ℝ η)) =
    S f (testCoefficientCLM b (TestFunction.monoCLM ℝ θ))
  have he := congrArg (S e) (testCoefficient_mono (overlapSource_le e f) b η)
  have hf := congrArg (S f) (testCoefficient_mono (overlapTarget_le e f) b θ)
  exact he.trans ((hS e f (testCoefficientCLM b η) (testCoefficientCLM b θ)
    (top_test_scalar_overlap b e f η θ hrel)).trans hf.symm)

/-- The output is the ORIGINAL compatible-current submodule of degree zero;
finite scalar compatibility is supplied internally by the true construction. -/
def finiteGlobalScalarCurrent {ι : Type*} [Fintype ι] (g : ι → ComplexChart n M)
    (χ : ι → M → ℝ) (hχ : ∀ a, ChartSmooth (n := n) (χ a))
    (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) : GlobalCurrent n M (0 : CurrentDegree n) :=
  ⟨scalarCurrentFamily b (finiteScalarFamily g χ hχ hc hs R),
    scalarCurrentFamily_compatible b _ (finiteScalarFamily_compatible g χ hχ hc hs R)⟩

/-- Literal pairing of the original global scalar current with every whole-chart
top-form test; all terms are genuine original continuous functionals. -/
theorem finiteGlobalScalarCurrent_apply {ι : Type*} [Fintype ι]
    (g : ι → ComplexChart n M) (χ : ι → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n))) :
    (finiteGlobalScalarCurrent b g χ hχ hc hs R).inChart e η =
      ∑ a, R a (fullChartTestCLM e (g a) (χ a) (hχ a) (hc a) (hs a)
        (testCoefficientCLM b η)) := by
  change (∑ a, weightedChartDistribution e (g a) (χ a) (hχ a) (hc a) (hs a) (R a))
    (testCoefficientCLM b η) = _
  simp only [_root_.sum_apply]
  rfl

/-- Original signed closed (1,1) input internally produces local potentials,
its actual finite partition, and an ORIGINAL global scalar degree-zero current. -/
theorem exists_global_scalar_partition [CompactSpace M] (hn : 0 < n)
    (T : GlobalCurrent n M (degreeTwo hn))
    (hclosed : T.IsClosed b) (h11 : T.IsTypeOneOne b hn) :
    ∃ (m : ℕ) (g : Fin m → ComplexChart n M) (W : Fin m → Opens (ComplexModel n))
      (hW : ∀ a, W a ≤ chartTarget (g a)) (R : ∀ a, 𝓓'(chartTarget (g a), ℝ))
      (χ : Fin m → M → ℝ) (hχ : ∀ a, ChartSmooth (n := n) (χ a))
      (hc : ∀ a, IsCompact (tsupport (χ a)))
      (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
      (Q : GlobalCurrent n M (0 : CurrentDegree n)),
      (∀ a y, 0 ≤ χ a y) ∧
      (∀ a, tsupport (χ a) ⊆ {y | y ∈ (g a).val.source ∧ (g a).val y ∈ W a}) ∧
      (∀ y, ∑ a, χ a y = 1) ∧
      (∀ a, ddC (restrictDistribution (R a) (hW a)) =
        LelongPoincareDivisor.restrictForm (T.coefficients b (g a)) (hW a)) ∧
      ∀ e (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n))),
        Q.inChart e η = ∑ a, R a (fullChartTestCLM e (g a) (χ a) (hχ a) (hc a) (hs a)
          (testCoefficientCLM b η)) := by
  obtain ⟨m, g, W, hW, R, χ, hχ, hnon, hsupp, hc, hsum, hpot⟩ :=
    exists_local_potential_partition b hn T hclosed h11
  have hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source := fun a y hy => (hsupp a hy).1
  refine ⟨m, g, W, hW, R, χ, hχ, hc, hs,
    finiteGlobalScalarCurrent b g χ hχ hc hs R, hnon, hsupp, hsum, hpot, ?_⟩
  exact fun e η => finiteGlobalScalarCurrent_apply b g χ hχ hc hs R e η

end SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarCurrent
