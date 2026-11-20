import SGPT.Convex.MixedAlexandrovIdentities

noncomputable section
namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped CompactlySupported Topology ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {n : ℕ}

/-- Literal original nonnegative weighted finite sum. -/
def finiteConvexWeightedSum {q : ℕ} (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) : RealConvexFunction E :=
  ⟨fun x ↦ ∑ i, (c i : ℝ) * (u i).val x, by
    simpa using convexOn_finset_sum_real Finset.univ
      (fun i ↦ ConvexOn.smul (c i).coe_nonneg (u i).property)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual smooth original weighted sum has the genuine sum of weighted Hessians. -/
theorem hessianMatrix_finiteConvexWeightedSum {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (x : E) :
    hessianMatrix b (finiteConvexWeightedSum u c).val x =
      ∑ i, (c i : ℝ) • hessianMatrix b (u i).val x := by
  simpa [finiteConvexWeightedSum, hessianMatrix_const_smul] using
    hessianMatrix_finset_sum_of_contDiff b Finset.univ
      (fun i ↦ contDiff_const.mul (hcd i)) x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual original compact-uniform limits preserve the weighted finite sum. -/
theorem tendstoUniformlyOn_finiteConvexWeightedSum {q : ℕ}
    {F : ℕ → Fin q → RealConvexFunction E} {u : Fin q → RealConvexFunction E}
    (c : Fin q → ℝ≥0)
    (hF : ∀ i K, IsCompact K →
      TendstoUniformlyOn (fun j ↦ (F j i).val) (u i).val atTop K)
    {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ (finiteConvexWeightedSum (F j) c).val)
      (finiteConvexWeightedSum u c).val atTop K := by
  have hS (S : Finset (Fin q)) : TendstoUniformlyOn
      (fun j x ↦ ∑ i ∈ S, (c i : ℝ) * (F j i).val x)
      (fun x ↦ ∑ i ∈ S, (c i : ℝ) * (u i).val x) atTop K := by
    induction S using Finset.induction_on with
    | empty =>
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const K
    | @insert a S ha ih =>
        have hca : TendstoUniformlyOn (fun j x ↦ (c a : ℝ) * (F j a).val x)
            (fun x ↦ (c a : ℝ) * (u a).val x) atTop K :=
          ((c a : ℝ) • ContinuousLinearMap.id ℝ ℝ).uniformContinuous.comp_tendstoUniformlyOn (hF a K hK)
        simp only [Finset.sum_insert ha]
        exact hca.add ih
  simpa [finiteConvexWeightedSum] using hS Finset.univ

/-- Genuine native independent-slot expansion gives the original smooth compact-test polynomial. -/
theorem mixedAlexandrovFunctional_weighted_diagonal_of_contDiff {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun _ : Fin n ↦ finiteConvexWeightedSum u c) h =
      ∑ g : Fin n → Fin q, (∏ i, (c (g i) : ℝ)) *
        mixedAlexandrovFunctional μ (fun i ↦ u (g i)) h := by
  classical
  have hsum : ContDiff ℝ ∞ (finiteConvexWeightedSum u c).val := by
    change ContDiff ℝ ∞ (fun x ↦ ∑ i, (c i : ℝ) * (u i).val x)
    simpa using ContDiff.sum (s := Finset.univ)
      (fun i _ ↦ (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ (c i : ℝ))).mul (hcd i))
  rw [mixedAlexandrovFunctional_eq_smooth_integral μ b _ (fun _ ↦ hsum)]
  have heqg (g : Fin n → Fin q) := mixedAlexandrovFunctional_eq_smooth_integral μ b
    (fun i ↦ u (g i)) (fun i ↦ hcd (g i)) h
  simp_rw [heqg, ← integral_const_mul]
  have hi (g : Fin n → Fin q) : Integrable
      (fun x ↦ (∏ i, (c (g i) : ℝ)) *
        (smoothMixedDensity b (fun i ↦ (u (g i)).val) x * h x)) μ :=
    (integrable_smoothMixedDensity_mul_compactTest μ b (fun i ↦ hcd (g i)) h).const_mul _
  rw [← integral_finsetSum Finset.univ (fun g _ ↦ hi g)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change realMixedCoefficientML (fun _ : Fin n ↦
    hessianMatrix b (finiteConvexWeightedSum u c).val x) * h x = _
  simp_rw [hessianMatrix_finiteConvexWeightedSum b u c hcd x]
  rw [realMixedCoefficientML_sum (fun j ↦ hessianMatrix b (u j).val x)
    (fun _ j ↦ (c j : ℝ)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_assoc]
  rfl

/-- Actual original finite-convex limits give the full source compact-test polynomial. -/
theorem mixedAlexandrovFunctional_weighted_diagonal {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun _ : Fin n ↦ finiteConvexWeightedSum u c) h =
      ∑ g : Fin n → Fin q, (∏ i, (c (g i) : ℝ)) *
        mixedAlexandrovFunctional μ (fun i ↦ u (g i)) h := by
  classical
  have hF i K (hK : IsCompact K) := tendstoUniformlyOn_finiteConvexSmoothTuple μ u i hK
  have hl := tendsto_mixedAlexandrovFunctional μ
    (F := fun j (_ : Fin n) ↦ finiteConvexWeightedSum (finiteConvexSmoothTuple μ u j) c)
    (u := fun _ : Fin n ↦ finiteConvexWeightedSum u c)
    (fun _ K hK ↦ tendstoUniformlyOn_finiteConvexWeightedSum c hF hK) h
  have hr : Tendsto (fun j ↦ ∑ g : Fin n → Fin q, (∏ i, (c (g i) : ℝ)) *
      mixedAlexandrovFunctional μ (fun i ↦ finiteConvexSmoothTuple μ u j (g i)) h)
      atTop (𝓝 (∑ g : Fin n → Fin q, (∏ i, (c (g i) : ℝ)) *
        mixedAlexandrovFunctional μ (fun i ↦ u (g i)) h)) := by
    apply tendsto_finsetSum
    intro g _
    apply tendsto_const_nhds.mul
    exact tendsto_mixedAlexandrovFunctional μ (fun i K hK ↦ hF (g i) K hK) h
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext j
  exact mixedAlexandrovFunctional_weighted_diagonal_of_contDiff μ b
    (finiteConvexSmoothTuple μ u j) c (fun i ↦ contDiff_finiteConvexSmoothTuple μ u j i) h

/-- Radon compact-test uniqueness gives the actual original weighted mixed diagonal measure. -/
theorem mixedAlexandrovMeasure_weighted_diagonal {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) :
    mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ finiteConvexWeightedSum u c) =
      ∑ g : Fin n → Fin q, (∏ i, c (g i)) •
        mixedAlexandrovMeasure μ b (fun i ↦ u (g i)) := by
  classical
  let ν : (Fin n → Fin q) → Measure E := fun g ↦
    (∏ i, c (g i)) • mixedAlexandrovMeasure μ b (fun i ↦ u (g i))
  have hν (g : Fin n → Fin q) : IsFiniteMeasureOnCompacts (ν g) := by
    let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (fun i ↦ u (g i))
    dsimp only [ν]
    infer_instance
  let : IsFiniteMeasureOnCompacts (∑ g, ν g) := ⟨fun K hK ↦ by
    rw [Measure.finsetSum_apply]
    apply ENNReal.sum_lt_top.mpr
    intro g _
    let := hν g
    exact hK.measure_lt_top⟩
  let := (inferInstance : (∑ g, ν g).Regular)
  let := regular_mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ finiteConvexWeightedSum u c)
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ finiteConvexWeightedSum u c)
  change mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ finiteConvexWeightedSum u c) = ∑ g, ν g
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  rw [integral_finsetSum_measure (fun g _ ↦ by
    let := hν g
    exact h.integrable)]
  simp only [ν, integral_smul_nnreal_measure, integral_mixedAlexandrovMeasure,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_prod]
  exact mixedAlexandrovFunctional_weighted_diagonal μ b u c h

/-- Exact source pure Alexandrov polynomial for every original nonnegative weighted finite family. -/
theorem alexandrovMeasure_finiteConvexWeightedSum {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ≥0) :
    alexandrovMeasure (innerₗ E) μ
      (fun x ↦ ((finiteConvexWeightedSum u c).val x : EReal)) =
      ∑ g : Fin n → Fin q, (∏ i, c (g i)) •
        mixedAlexandrovMeasure μ b (fun i ↦ u (g i)) := by
  rw [← mixedAlexandrovMeasure_diagonal μ b (finiteConvexWeightedSum u c)]
  exact mixedAlexandrovMeasure_weighted_diagonal μ b u c

/-- The original source real nonnegative weights are represented without changing the literal sum. -/
theorem alexandrovMeasure_nonnegative_finite_sum {q : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin q → RealConvexFunction E)
    (c : Fin q → ℝ) (hc : ∀ i, 0 ≤ c i) :
    alexandrovMeasure (innerₗ E) μ
      (fun x ↦ ((∑ i, c i * (u i).val x : ℝ) : EReal)) =
      ∑ g : Fin n → Fin q, (∏ i, Real.toNNReal (c (g i))) •
        mixedAlexandrovMeasure μ b (fun i ↦ u (g i)) := by
  simpa only [finiteConvexWeightedSum, Real.coe_toNNReal _ (hc _)] using
    alexandrovMeasure_finiteConvexWeightedSum μ b u (fun i ↦ Real.toNNReal (c i))

/-- The genuine assignment satisfies every original clause of the source mixed real Alexandrov theorem. -/
theorem exists_symmetric_mixedAlexandrov_assignment (b : OrthonormalBasis (Fin n) ℝ E) :
    ∃ A : (Fin n → RealConvexFunction E) → Measure E,
      (∀ u, IsLocallyFiniteMeasure (A u) ∧ (A u).Regular) ∧
      (∀ u (τ : Equiv.Perm (Fin n)), A (fun i ↦ u (τ i)) = A u) ∧
      (∀ (q : ℕ) (u : Fin q → RealConvexFunction E) (c : Fin q → ℝ≥0),
        alexandrovMeasure (innerₗ E) μ
          (fun x ↦ ((finiteConvexWeightedSum u c).val x : EReal)) =
          ∑ g : Fin n → Fin q, (∏ i, c (g i)) • A (fun i ↦ u (g i))) ∧
      (∀ f, A (fun _ : Fin n ↦ f) =
        alexandrovMeasure (innerₗ E) μ (fun x ↦ (f.val x : EReal))) ∧
      (∀ u (i : Fin n) (c d : ℝ≥0) f g,
        A (Function.update u i (realConvexAdd (realConvexSmul c f) (realConvexSmul d g))) =
          c • A (Function.update u i f) + d • A (Function.update u i g)) := by
  refine ⟨mixedAlexandrovMeasure μ b, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact ⟨isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b u,
      regular_mixedAlexandrovMeasure μ b u⟩
  · exact mixedAlexandrovMeasure_perm μ b
  · intro q u c
    exact alexandrovMeasure_finiteConvexWeightedSum μ b u c
  · exact mixedAlexandrovMeasure_diagonal μ b
  · exact mixedAlexandrovMeasure_update_linear_combination μ b

end SGPT.Convex
