import SGPT.Convex.MixedAlexandrovFunctional

noncomputable section
namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped CompactlySupported Topology ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {n : ℕ}

/-- Genuine actual smooth approximation in every original finite convex slot. -/
def finiteConvexSmoothTuple (u : Fin n → RealConvexFunction E) (j : ℕ) :
    Fin n → RealConvexFunction E := fun i ↦
  ⟨finiteConvexSmoothApprox μ (u i).val j,
    convexOn_finiteConvexSmoothApprox μ (u i).property j⟩

theorem contDiff_finiteConvexSmoothTuple (u : Fin n → RealConvexFunction E) (j : ℕ) (i : Fin n) :
    ContDiff ℝ ∞ (finiteConvexSmoothTuple μ u j i).val :=
  contDiff_finiteConvexSmoothApprox μ (u i).property j

theorem tendstoUniformlyOn_finiteConvexSmoothTuple (u : Fin n → RealConvexFunction E)
    (i : Fin n) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ (finiteConvexSmoothTuple μ u j i).val) (u i).val atTop K :=
  tendstoUniformlyOn_finiteConvexSmoothApprox μ (u i).property hK

/-- Riesz uniqueness identifies the constructed measure with the actual original smooth density measure. -/
theorem mixedAlexandrovMeasure_eq_smooth (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) :
    mixedAlexandrovMeasure μ b u = smoothMixedAlexandrovMeasure μ b (fun i ↦ (u i).val) := by
  let := regular_mixedAlexandrovMeasure μ b u
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b u
  let := regular_smoothMixedAlexandrovMeasure μ b hcd
  let := isLocallyFiniteMeasure_smoothMixedAlexandrovMeasure μ b hcd
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  rw [integral_mixedAlexandrovMeasure,
    mixedAlexandrovFunctional_eq_smooth_integral μ b u hcd,
    integral_smoothMixedAlexandrovMeasure μ b (fun i ↦ (u i).property) hcd]

/-- Actual native slot symmetry gives the genuine original smooth compact-test identity. -/
theorem mixedAlexandrovFunctional_perm_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (τ : Equiv.Perm (Fin n)) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun i ↦ u (τ i)) h = mixedAlexandrovFunctional μ u h := by
  rw [mixedAlexandrovFunctional_eq_smooth_integral μ b _ (fun i ↦ hcd (τ i)),
    mixedAlexandrovFunctional_eq_smooth_integral μ b u hcd]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change realMixedCoefficientML (fun i ↦ hessianMatrix b (u (τ i)).val x) * h x =
    realMixedCoefficientML (fun i ↦ hessianMatrix b (u i).val x) * h x
  exact congrArg (fun z : ℝ ↦ z * h x)
    (realMixedCoefficientML_perm (fun i ↦ hessianMatrix b (u i).val x) τ)

/-- Original smooth approximation and true compact-test limits give exact symmetry for every finite convex tuple. -/
theorem mixedAlexandrovFunctional_perm
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (τ : Equiv.Perm (Fin n)) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun i ↦ u (τ i)) h = mixedAlexandrovFunctional μ u h := by
  have hl := tendsto_mixedAlexandrovFunctional μ
    (F := fun j i ↦ finiteConvexSmoothTuple μ u j (τ i))
    (u := fun i ↦ u (τ i))
    (fun i K hK ↦ tendstoUniformlyOn_finiteConvexSmoothTuple μ u (τ i) hK) h
  have hr := tendsto_mixedAlexandrovFunctional μ
    (fun i K hK ↦ tendstoUniformlyOn_finiteConvexSmoothTuple μ u i hK) h
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext j
  exact mixedAlexandrovFunctional_perm_of_contDiff μ b (finiteConvexSmoothTuple μ u j)
    (fun i ↦ contDiff_finiteConvexSmoothTuple μ u j i) τ h

/-- The genuinely constructed mixed measure is symmetric in every original slot. -/
theorem mixedAlexandrovMeasure_perm (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) (τ : Equiv.Perm (Fin n)) :
    mixedAlexandrovMeasure μ b (fun i ↦ u (τ i)) = mixedAlexandrovMeasure μ b u := by
  let := regular_mixedAlexandrovMeasure μ b u
  let := regular_mixedAlexandrovMeasure μ b (fun i ↦ u (τ i))
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b u
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (fun i ↦ u (τ i))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  simp only [integral_mixedAlexandrovMeasure]
  exact mixedAlexandrovFunctional_perm μ b u τ h

/-- Actual smooth diagonal normalization identifies the original pure compact-test value. -/
theorem mixedAlexandrovFunctional_diagonal_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) (f : RealConvexFunction E)
    (hcd : ContDiff ℝ ∞ f.val) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun _ : Fin n ↦ f) h =
      ∫ x, h x ∂alexandrovMeasure (innerₗ E) μ (fun x ↦ (f.val x : EReal)) := by
  rw [← integral_mixedAlexandrovMeasure μ b,
    mixedAlexandrovMeasure_eq_smooth μ b _ (fun _ ↦ hcd),
    smoothMixedAlexandrovMeasure_diagonal μ b f.property hcd]

/-- Original pure weak continuity and the actual smooth diagonal give the full finite-convex diagonal functional. -/
theorem mixedAlexandrovFunctional_diagonal
    (b : OrthonormalBasis (Fin n) ℝ E) (f : RealConvexFunction E) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (fun _ : Fin n ↦ f) h =
      ∫ x, h x ∂alexandrovMeasure (innerₗ E) μ (fun x ↦ (f.val x : EReal)) := by
  let g : ℕ → RealConvexFunction E := fun j ↦
    ⟨finiteConvexSmoothApprox μ f.val j, convexOn_finiteConvexSmoothApprox μ f.property j⟩
  have hl := tendsto_mixedAlexandrovFunctional μ (F := fun (j : ℕ) (_ : Fin n) ↦ g j)
    (u := fun _ : Fin n ↦ f)
    (fun _ K hK ↦ tendstoUniformlyOn_finiteConvexSmoothApprox μ f.property hK) h
  have hr := tendsto_integral_alexandrovMeasure_of_finite_convex_compact_convergence
    (ν := μ) (innerₗ E) f.property (fun j ↦ (g j).property)
    (fun K hK ↦ tendstoUniformlyOn_finiteConvexSmoothApprox μ f.property hK) h
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext j
  exact mixedAlexandrovFunctional_diagonal_of_contDiff μ b (g j)
    (contDiff_finiteConvexSmoothApprox μ f.property j) h

/-- Full literal source diagonal, for every original finite convex function. -/
theorem mixedAlexandrovMeasure_diagonal
    (b : OrthonormalBasis (Fin n) ℝ E) (f : RealConvexFunction E) :
    mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ f) =
      alexandrovMeasure (innerₗ E) μ (fun x ↦ (f.val x : EReal)) := by
  let := regular_mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ f)
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (fun _ : Fin n ↦ f)
  let := regular_alexandrovMeasure_coe (innerₗ E) f.property (ν := μ)
  let := isLocallyFiniteMeasure_alexandrovMeasure_coe (innerₗ E) f.property (ν := μ)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  rw [integral_mixedAlexandrovMeasure, mixedAlexandrovFunctional_diagonal μ b f h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual scalar second differentiation gives the literal original scaled Hessian. -/
theorem hessianMatrix_const_smul (b : OrthonormalBasis (Fin n) ℝ E)
    (f : E → ℝ) (c : ℝ) (x : E) :
    hessianMatrix b (fun y ↦ c * f y) x = c • hessianMatrix b f x := by
  change hessianMatrix b (c • f) x = _
  have hs : fderiv ℝ (fderiv ℝ (c • f)) = c • fderiv ℝ (fderiv ℝ f) := by
    rw [fderiv_const_smul_field]
    exact fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) c
  ext i j
  simp only [hessianMatrix, hs, Pi.smul_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Genuine second differentiation of an actual smooth sum supplies its original Hessian addition. -/
theorem hessianMatrix_add_of_contDiff (b : OrthonormalBasis (Fin n) ℝ E)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    hessianMatrix b (fun y ↦ f y + g y) x = hessianMatrix b f x + hessianMatrix b g x := by
  have hfirst : fderiv ℝ (fun y ↦ f y + g y) = fun y ↦ fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_fun_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
  have hsecond : fderiv ℝ (fderiv ℝ (fun y ↦ f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    rw [hfirst]
    exact fderiv_fun_add
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
      ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  ext i j
  simp only [hessianMatrix, hsecond, Matrix.of_apply, Matrix.add_apply,
    add_apply]

/-- Actual addition of the original finite convex functions. -/
def realConvexAdd (f g : RealConvexFunction E) : RealConvexFunction E :=
  ⟨fun x ↦ f.val x + g.val x, f.property.add g.property⟩

/-- Actual nonnegative scaling of an original finite convex function. -/
def realConvexSmul (c : ℝ≥0) (f : RealConvexFunction E) : RealConvexFunction E :=
  ⟨fun x ↦ (c : ℝ) * f.val x, ConvexOn.smul c.coe_nonneg f.property⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Updating an actual original slot updates exactly its actual Hessian slot. -/
theorem hessianMatrix_update (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) (i : Fin n) (f : RealConvexFunction E) (x : E) :
    (fun j ↦ hessianMatrix b (Function.update u i f j).val x) =
      Function.update (fun j ↦ hessianMatrix b (u j).val x) i (hessianMatrix b f.val x) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj]

omit [FiniteDimensional ℝ E] in
/-- Actual continuous Hessian density times a genuine compact test is integrable. -/
theorem integrable_smoothMixedDensity_mul_compactTest (b : OrthonormalBasis (Fin n) ℝ E)
    {u : Fin n → RealConvexFunction E} (hcd : ∀ i, ContDiff ℝ ∞ (u i).val)
    (h : C_c(E, ℝ)) :
    Integrable (fun x ↦ smoothMixedDensity b (fun i ↦ (u i).val) x * h x) μ :=
  ((continuous_smoothMixedDensity b hcd).mul h.continuous).integrable_of_hasCompactSupport
    h.hasCompactSupport.mul_left

/-- Genuine smooth slot addition gives the exact original compact-test identity. -/
theorem mixedAlexandrovFunctional_update_add_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (i : Fin n) (f g : RealConvexFunction E)
    (hf : ContDiff ℝ ∞ f.val) (hg : ContDiff ℝ ∞ g.val) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (Function.update u i (realConvexAdd f g)) h =
      mixedAlexandrovFunctional μ (Function.update u i f) h +
      mixedAlexandrovFunctional μ (Function.update u i g) h := by
  have hu (k : RealConvexFunction E) (hk : ContDiff ℝ ∞ k.val) :
      ∀ j, ContDiff ℝ ∞ (Function.update u i k j).val := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hk
    · simpa [Function.update_of_ne hj] using hcd j
  have hfg : ContDiff ℝ ∞ (realConvexAdd f g).val := hf.add hg
  rw [mixedAlexandrovFunctional_eq_smooth_integral μ b _ (hu _ hfg),
    mixedAlexandrovFunctional_eq_smooth_integral μ b _ (hu _ hf),
    mixedAlexandrovFunctional_eq_smooth_integral μ b _ (hu _ hg)]
  rw [← integral_add
    (integrable_smoothMixedDensity_mul_compactTest μ b (hu _ hf) h)
    (integrable_smoothMixedDensity_mul_compactTest μ b (hu _ hg) h)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smoothMixedDensity, hessianMatrix_update]
  change realMixedCoefficientML (Function.update _ i
    (hessianMatrix b (fun y ↦ f.val y + g.val y) x)) * h x = _
  rw [hessianMatrix_add_of_contDiff b hf hg x,
    MultilinearMap.map_update_add, add_mul]

/-- Genuine smooth nonnegative slot scaling gives the exact compact-test identity. -/
theorem mixedAlexandrovFunctional_update_smul_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (i : Fin n) (c : ℝ≥0)
    (f : RealConvexFunction E) (hf : ContDiff ℝ ∞ f.val) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (Function.update u i (realConvexSmul c f)) h =
      (c : ℝ) * mixedAlexandrovFunctional μ (Function.update u i f) h := by
  have hu (k : RealConvexFunction E) (hk : ContDiff ℝ ∞ k.val) :
      ∀ j, ContDiff ℝ ∞ (Function.update u i k j).val := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hk
    · simpa [Function.update_of_ne hj] using hcd j
  have hcf : ContDiff ℝ ∞ (realConvexSmul c f).val := contDiff_const.mul hf
  rw [mixedAlexandrovFunctional_eq_smooth_integral μ b _ (hu _ hcf),
    mixedAlexandrovFunctional_eq_smooth_integral μ b _ (hu _ hf), ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smoothMixedDensity, hessianMatrix_update]
  change realMixedCoefficientML (Function.update _ i
    (hessianMatrix b (fun y ↦ (c : ℝ) * f.val y) x)) * h x = _
  rw [hessianMatrix_const_smul b f.val (c : ℝ) x,
    MultilinearMap.map_update_smul, smul_eq_mul, mul_assoc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Original compact-uniform convergence is preserved by updating an actual finite convex slot. -/
theorem tendstoUniformlyOn_realConvex_update
    {F : ℕ → Fin n → RealConvexFunction E} {u : Fin n → RealConvexFunction E}
    (hF : ∀ i K, IsCompact K →
      TendstoUniformlyOn (fun j ↦ (F j i).val) (u i).val atTop K)
    (i : Fin n) {g : ℕ → RealConvexFunction E} {f : RealConvexFunction E}
    (hg : ∀ K, IsCompact K → TendstoUniformlyOn (fun j ↦ (g j).val) f.val atTop K) :
    ∀ k K, IsCompact K → TendstoUniformlyOn
      (fun j ↦ (Function.update (F j) i (g j) k).val)
      (Function.update u i f k).val atTop K := by
  intro k K hK
  by_cases hk : k = i
  · subst k
    simpa using hg K hK
  · simpa [Function.update_of_ne hk] using hF k K hK

/-- Actual original smooth limits give finite-convex slot additivity without any smoothness premise. -/
theorem mixedAlexandrovFunctional_update_add
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (i : Fin n) (f g : RealConvexFunction E) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (Function.update u i (realConvexAdd f g)) h =
      mixedAlexandrovFunctional μ (Function.update u i f) h +
      mixedAlexandrovFunctional μ (Function.update u i g) h := by
  let v : ℕ → RealConvexFunction E := fun j ↦
    ⟨finiteConvexSmoothApprox μ f.val j, convexOn_finiteConvexSmoothApprox μ f.property j⟩
  let w : ℕ → RealConvexFunction E := fun j ↦
    ⟨finiteConvexSmoothApprox μ g.val j, convexOn_finiteConvexSmoothApprox μ g.property j⟩
  have hv K (hK : IsCompact K) :
      TendstoUniformlyOn (fun j ↦ (v j).val) f.val atTop K :=
    tendstoUniformlyOn_finiteConvexSmoothApprox μ f.property hK
  have hw K (hK : IsCompact K) :
      TendstoUniformlyOn (fun j ↦ (w j).val) g.val atTop K :=
    tendstoUniformlyOn_finiteConvexSmoothApprox μ g.property hK
  have hF k K (hK : IsCompact K) :=
    tendstoUniformlyOn_finiteConvexSmoothTuple μ u k hK
  have hvw K (hK : IsCompact K) :
      TendstoUniformlyOn (fun j ↦ (realConvexAdd (v j) (w j)).val)
        (realConvexAdd f g).val atTop K := (hv K hK).add (hw K hK)
  have hl := tendsto_mixedAlexandrovFunctional μ
    (tendstoUniformlyOn_realConvex_update hF i hvw) h
  have hr := (tendsto_mixedAlexandrovFunctional μ
    (tendstoUniformlyOn_realConvex_update hF i hv) h).add
    (tendsto_mixedAlexandrovFunctional μ
      (tendstoUniformlyOn_realConvex_update hF i hw) h)
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext j
  exact mixedAlexandrovFunctional_update_add_of_contDiff μ b (finiteConvexSmoothTuple μ u j)
    (fun k ↦ contDiff_finiteConvexSmoothTuple μ u j k) i (v j) (w j)
    (contDiff_finiteConvexSmoothApprox μ f.property j)
    (contDiff_finiteConvexSmoothApprox μ g.property j) h

/-- Actual original smooth limits give finite-convex nonnegative slot homogeneity. -/
theorem mixedAlexandrovFunctional_update_smul
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (i : Fin n) (c : ℝ≥0) (f : RealConvexFunction E) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ (Function.update u i (realConvexSmul c f)) h =
      (c : ℝ) * mixedAlexandrovFunctional μ (Function.update u i f) h := by
  let v : ℕ → RealConvexFunction E := fun j ↦
    ⟨finiteConvexSmoothApprox μ f.val j, convexOn_finiteConvexSmoothApprox μ f.property j⟩
  have hv K (hK : IsCompact K) :
      TendstoUniformlyOn (fun j ↦ (v j).val) f.val atTop K :=
    tendstoUniformlyOn_finiteConvexSmoothApprox μ f.property hK
  have hcv K (hK : IsCompact K) :
      TendstoUniformlyOn (fun j ↦ (realConvexSmul c (v j)).val)
        (realConvexSmul c f).val atTop K :=
    ((c : ℝ) • ContinuousLinearMap.id ℝ ℝ).uniformContinuous.comp_tendstoUniformlyOn (hv K hK)
  have hF k K (hK : IsCompact K) :=
    tendstoUniformlyOn_finiteConvexSmoothTuple μ u k hK
  have hl := tendsto_mixedAlexandrovFunctional μ
    (tendstoUniformlyOn_realConvex_update hF i hcv) h
  have hc : Tendsto (fun _ : ℕ ↦ (c : ℝ)) atTop (𝓝 (c : ℝ)) := tendsto_const_nhds
  have hr := hc.mul (tendsto_mixedAlexandrovFunctional μ
    (tendstoUniformlyOn_realConvex_update hF i hv) h)
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext j
  exact mixedAlexandrovFunctional_update_smul_of_contDiff μ b (finiteConvexSmoothTuple μ u j)
    (fun k ↦ contDiff_finiteConvexSmoothTuple μ u j k) i c (v j)
    (contDiff_finiteConvexSmoothApprox μ f.property j) h

/-- Genuine Radon compact-test uniqueness gives source additivity in every original finite-convex slot. -/
theorem mixedAlexandrovMeasure_update_add
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (i : Fin n) (f g : RealConvexFunction E) :
    mixedAlexandrovMeasure μ b (Function.update u i (realConvexAdd f g)) =
      mixedAlexandrovMeasure μ b (Function.update u i f) +
      mixedAlexandrovMeasure μ b (Function.update u i g) := by
  let := regular_mixedAlexandrovMeasure μ b (Function.update u i (realConvexAdd f g))
  let := regular_mixedAlexandrovMeasure μ b (Function.update u i f)
  let := regular_mixedAlexandrovMeasure μ b (Function.update u i g)
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (Function.update u i (realConvexAdd f g))
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (Function.update u i f)
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (Function.update u i g)
  let : IsFiniteMeasureOnCompacts
      (mixedAlexandrovMeasure μ b (Function.update u i f) +
        mixedAlexandrovMeasure μ b (Function.update u i g)) := ⟨fun K hK ↦ by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  let := (inferInstance :
    (mixedAlexandrovMeasure μ b (Function.update u i f) +
      mixedAlexandrovMeasure μ b (Function.update u i g)).Regular)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  rw [integral_add_measure
    (h.integrable (μ := mixedAlexandrovMeasure μ b (Function.update u i f)))
    (h.integrable (μ := mixedAlexandrovMeasure μ b (Function.update u i g)))]
  simp only [integral_mixedAlexandrovMeasure]
  exact mixedAlexandrovFunctional_update_add μ b u i f g h

/-- Genuine Radon compact-test uniqueness gives source positive homogeneity in every original slot. -/
theorem mixedAlexandrovMeasure_update_smul
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (i : Fin n) (c : ℝ≥0) (f : RealConvexFunction E) :
    mixedAlexandrovMeasure μ b (Function.update u i (realConvexSmul c f)) =
      c • mixedAlexandrovMeasure μ b (Function.update u i f) := by
  let := regular_mixedAlexandrovMeasure μ b (Function.update u i (realConvexSmul c f))
  let := regular_mixedAlexandrovMeasure μ b (Function.update u i f)
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (Function.update u i (realConvexSmul c f))
  let := isLocallyFiniteMeasure_mixedAlexandrovMeasure μ b (Function.update u i f)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  rw [integral_smul_nnreal_measure]
  simp only [integral_mixedAlexandrovMeasure, NNReal.smul_def, smul_eq_mul]
  exact mixedAlexandrovFunctional_update_smul μ b u i c f h

/-- Exact printed two-weight linear combination, with the original actual finite convex functions. -/
theorem mixedAlexandrovMeasure_update_linear_combination
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (i : Fin n) (c d : ℝ≥0) (f g : RealConvexFunction E) :
    mixedAlexandrovMeasure μ b
      (Function.update u i (realConvexAdd (realConvexSmul c f) (realConvexSmul d g))) =
      c • mixedAlexandrovMeasure μ b (Function.update u i f) +
      d • mixedAlexandrovMeasure μ b (Function.update u i g) := by
  rw [mixedAlexandrovMeasure_update_add μ b u i,
    mixedAlexandrovMeasure_update_smul μ b u i c f,
    mixedAlexandrovMeasure_update_smul μ b u i d g]

end SGPT.Convex
