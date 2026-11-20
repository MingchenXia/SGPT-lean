import SGPT.Foundations.Analysis.Pending.NaturalHermitianFirstOrderCoefficients
import SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenPrincipalEnergy

set_option autoImplicit false

/-! Actual frozen original d/codifferential integral energy in the unchanged original norms. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenHodgeEnergy

open FirstPass FirstPass.MongeAmpere NaturalHermitianFirstOrderCoefficients
  NaturalHermitianFrozenPrincipalEnergy NaturalHermitianExteriorCliffordSymbol
  NaturalHermitianSmoothFormMetric NaturalHermitianOriginalFormMetric
  NaturalHermitianMusicalInverse NaturalHermitianMetricCoefficients
  NaturalHermitianOrthonormalFormBasis NaturalHermitianUnitVolume
  NaturalHermitianHodgeStarSquare ConstantFormProducts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

/-- Literal frozen first-order part of the actual original codifferential. -/
def frozenCodifferential (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (A : ComplexModel n → FormCoefficients n q)
    (x : ComplexModel n) : FormCoefficients n (q - 1) :=
  principalJetCLM w e q z (fderiv ℝ A x)

/-- Genuine negative insertion expansion of the entire original frozen principal first jet. -/
theorem frozenCodifferential_succ_eq_sum (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (A : ComplexModel n → FormCoefficients n (p + 1)) (x : ComplexModel n) :
    castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x) =
      -(∑ i, interiorSuccCLM p ((associatedMetricCLM (w.coeff e z)).inverse
        (coordinateCovector b i)) (fderiv ℝ A x (b i))) := by
  simp only [frozenCodifferential, principalJetCLM, dif_pos hp]
  change principalJetSuccCLM w e p hp z (fderiv ℝ A x) = _
  rw [principalJetSucc_eq_coordinate_sum w e p hp z b (fderiv ℝ A x)]
  simp_rw [codifferentialCoefficientSymbolSucc_eq_neg_interior w hw e z hz]
  simp only [neg_apply, Finset.sum_neg_distrib]

/-- Degree zero has its actual original frozen zero operator. -/
theorem frozenCodifferential_zero (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (A : ComplexModel n → FormCoefficients n 0) (x : ComplexModel n) :
    frozenCodifferential w e z 0 A x = 0 := rfl

/-- The actual excessive degree branch is zero before any energy statement is made. -/
theorem frozenCodifferential_above (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (hq : 2 * n < q)
    (A : ComplexModel n → FormCoefficients n q) (x : ComplexModel n) :
    frozenCodifferential w e z q A x = 0 := by
  cases q with
  | zero => omega
  | succ p => simp [frozenCodifferential, principalJetCLM, not_le.mpr hq]

/-- Symmetry is the actual original exterior Gram symmetry in the already fixed chart coefficients. -/
theorem frozenMetric_symm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (η θ : FormCoefficients n q) :
    formMetricCoefficients w e z q η θ = formMetricCoefficients w e z q θ η := by
  rw [formMetricCoefficients_eq_original w hw e z hz]
  exact (originalFormMetric_symm_positive (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q).1 η θ

/-- Actual insertion and exterior multiplication remain genuine whole metric adjoints. -/
theorem frozenMetric_interior_adjoint (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (η : FormCoefficients n (q + 1)) (θ : FormCoefficients n q) :
    formMetricCoefficients w e z q
      (interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η) θ =
      formMetricCoefficients w e z (q + 1) η (covectorExteriorCLM q ℓ θ) := by
  rw [formMetricCoefficients_eq_original w hw e z hz,
    formMetricCoefficients_eq_original w hw e z hz]
  exact interior_metric_adjoint (w.coeff e z) (hw e z hz).1 (hw e z hz).2 ℓ η θ

/-- The reverse whole exterior-adjoint orientation needed by the actual exterior energy expansion. -/
theorem frozenMetric_exterior_adjoint (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (θ : FormCoefficients n q) (η : FormCoefficients n (q + 1)) :
    formMetricCoefficients w e z (q + 1) (covectorExteriorCLM q ℓ θ) η =
      formMetricCoefficients w e z q θ
        (interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η) := by
  rw [frozenMetric_symm w hw e z hz (q + 1),
    ← frozenMetric_interior_adjoint w hw e z hz q ℓ η θ,
    frozenMetric_symm w hw e z hz q]

section FiniteBilinearIntegration

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
/-- Actual linear coefficient maps preserve actual compact support. -/
theorem hasCompactSupport_clm (L : F →L[ℝ] G) {A : E → F} (hc : HasCompactSupport A) :
    HasCompactSupport (fun x => L (A x)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Finite actual compact-support fields give all bilinear cross integrability and their entire integral expansion. -/
theorem integral_bilinear_finite_sum (B : F →L[ℝ] G →L[ℝ] ℝ)
    (f : ι → E → F) (g : κ → E → G)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ j, Continuous (g j))
    (hc : ∀ i, HasCompactSupport (f i)) :
    (Integrable (fun x => B (∑ i, f i x) (∑ j, g j x)) μ ∧
      ∀ i j, Integrable (fun x => B (f i x) (g j x)) μ) ∧
    (∫ x, B (∑ i, f i x) (∑ j, g j x) ∂μ) =
      ∑ i, ∑ j, ∫ x, B (f i x) (g j x) ∂μ := by
  classical
  have hcross (i : ι) (j : κ) := integrable_bilinear_of_compact_support μ B
    (hf i) (hg j) (Or.inl (hc i))
  have hi (i : ι) := integrable_finsetSum Finset.univ (fun j _ => hcross i j)
  have he : (fun x => B (∑ i, f i x) (∑ j, g j x)) =
      (fun x => ∑ i, ∑ j, B (f i x) (g j x)) := by
    funext x
    simp only [map_sum, sum_apply]
    exact Finset.sum_comm
  refine ⟨⟨?_, hcross⟩, ?_⟩
  · rw [he]
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  · rw [he, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hcross i j)

end FiniteBilinearIntegration

/-- Actual exterior energy expansion through the genuine original whole metric adjoint. -/
theorem integral_frozen_exterior_energy_expansion
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x)) μ ∧
      ∀ i j, Integrable (fun x => formMetricCoefficients w e z q (fderiv ℝ A x (b i))
        (interiorSuccCLM q (b i)
          (covectorExteriorCLM q (coordinateCovector b j) (fderiv ℝ A x (b j))))) μ) ∧
    (∫ x, formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x) ∂μ) =
      ∑ i, ∑ j, ∫ x, formMetricCoefficients w e z q (fderiv ℝ A x (b i))
        (interiorSuccCLM q (b i)
          (covectorExteriorCLM q (coordinateCovector b j) (fderiv ℝ A x (b j)))) ∂μ := by
  classical
  let V (i : Fin (n * 2)) (x : ComplexModel n) := fderiv ℝ A x (b i)
  let E (i : Fin (n * 2)) (x : ComplexModel n) :=
    covectorExteriorCLM q (coordinateCovector b i) (V i x)
  have hV (i : Fin (n * 2)) : Continuous (V i) :=
    (hA.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hE (i : Fin (n * 2)) : Continuous (E i) :=
    (covectorExteriorCLM q (coordinateCovector b i)).continuous.comp (hV i)
  have hcE (i : Fin (n * 2)) : HasCompactSupport (E i) :=
    hasCompactSupport_clm _ (hc.fderiv_apply (𝕜 := ℝ) (b i))
  have H := integral_bilinear_finite_sum μ (formMetricCoefficients w e z (q + 1)) E E hE hE hcE
  have he : (fun x => formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x)) =
      (fun x => formMetricCoefficients w e z (q + 1) (∑ i, E i x) (∑ i, E i x)) := by
    funext x
    simp only [extDeriv_eq_coordinate_sum b q A x]
    rfl
  have hterm (i j : Fin (n * 2)) (x : ComplexModel n) :
      formMetricCoefficients w e z (q + 1) (E i x) (E j x) =
        formMetricCoefficients w e z q (V i x) (interiorSuccCLM q (b i) (E j x)) := by
    change formMetricCoefficients w e z (q + 1)
      (covectorExteriorCLM q (coordinateCovector b i) (V i x)) (E j x) = _
    rw [frozenMetric_exterior_adjoint w hw e z hz,
      coordinateCovector_inverse (hw e z hz).2 b hb]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [he]
    exact H.1.1
  · intro i j
    exact (H.1.2 i j).congr (Eventually.of_forall (hterm i j))
  · rw [he, H.2]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_congr_ae (Eventually.of_forall (hterm i j))

/-- Genuine mixed Haar integration by parts gives the whole transposed frozen insertion energy sum. -/
theorem integral_frozen_codifferential_energy_expansion_succ
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (A : ComplexModel n → FormCoefficients n (p + 1))
    (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z p
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))) μ ∧
      ∀ i j, Integrable (fun x => formMetricCoefficients w e z (p + 1) (fderiv ℝ A x (b i))
        (covectorExteriorCLM p (coordinateCovector b j)
          (interiorSuccCLM p (b i) (fderiv ℝ A x (b j))))) μ) ∧
    (∫ x, formMetricCoefficients w e z p
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x)) ∂μ) =
      ∑ i, ∑ j, ∫ x, formMetricCoefficients w e z (p + 1) (fderiv ℝ A x (b i))
        (covectorExteriorCLM p (coordinateCovector b j)
          (interiorSuccCLM p (b i) (fderiv ℝ A x (b j)))) ∂μ := by
  classical
  let V (i : Fin (n * 2)) (x : ComplexModel n) := fderiv ℝ A x (b i)
  let I (i : Fin (n * 2)) (x : ComplexModel n) := interiorSuccCLM p (b i) (V i x)
  let G := formMetricCoefficients w e z (p + 1)
  have hV (i : Fin (n * 2)) : ContDiff ℝ 1 (V i) :=
    (hA.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hcV (i : Fin (n * 2)) : HasCompactSupport (V i) := hc.fderiv_apply (𝕜 := ℝ) (b i)
  have hI (i : Fin (n * 2)) : Continuous (I i) :=
    (interiorSuccCLM p (b i)).continuous.comp (hV i).continuous
  have hcI (i : Fin (n * 2)) : HasCompactSupport (I i) := hasCompactSupport_clm _ (hcV i)
  have H := integral_bilinear_finite_sum μ (formMetricCoefficients w e z p) I I hI hI hcI
  have he : (fun x => formMetricCoefficients w e z p
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))
      (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))) =
      (fun x => formMetricCoefficients w e z p (∑ i, I i x) (∑ i, I i x)) := by
    funext x
    simp only [frozenCodifferential_succ_eq_sum w hw e z hz p hp b A x,
      coordinateCovector_inverse (hw e z hz).2 b hb, map_neg, neg_apply, neg_neg]
    rfl
  have hterm (i j : Fin (n * 2)) (x : ComplexModel n) :
      formMetricCoefficients w e z p (I i x) (I j x) =
        G (V i x) (covectorExteriorCLM p (coordinateCovector b i) (I j x)) := by
    simpa only [coordinateCovector_inverse (hw e z hz).2 b hb] using
      frozenMetric_interior_adjoint w hw e z hz p (coordinateCovector b i) (V i x) (I j x)
  have hmixed (i j : Fin (n * 2)) :
      (∫ x, G (V i x) (covectorExteriorCLM p (coordinateCovector b i) (I j x)) ∂μ) =
        ∫ x, G (V j x)
          (covectorExteriorCLM p (coordinateCovector b i) (interiorSuccCLM p (b j) (V i x))) ∂μ :=
    integral_mixed_directional_transfer μ
      ((G.flip.comp ((covectorExteriorCLM p (coordinateCovector b i)).comp
        (interiorSuccCLM p (b j)))).flip) (hA.of_le (by norm_num)) hA (Or.inl hc) (b i) (b j)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [he]
    exact H.1.1
  · intro i j
    exact integrable_bilinear_of_compact_support μ
      ((G.flip.comp ((covectorExteriorCLM p (coordinateCovector b j)).comp
        (interiorSuccCLM p (b i)))).flip) (hV i).continuous (hV j).continuous (Or.inl (hcV i))
  · rw [he, H.2]
    calc
      _ = ∑ i, ∑ j, ∫ x, G (V j x)
          (covectorExteriorCLM p (coordinateCovector b i) (interiorSuccCLM p (b j) (V i x))) ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (integral_congr_ae (Eventually.of_forall (hterm i j))).trans (hmixed i j)
      _ = _ := Finset.sum_comm

/-- The entire original cross coefficient sum is the actual coordinate Kronecker diagonal. -/
theorem frozen_cross_energy_diagonal
    (w : SmoothRealForm n M 2) (e : ComplexChart n M) (z : ComplexModel n) (p : ℕ)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (i j : Fin (n * 2)) (η θ : FormCoefficients n (p + 1)) :
    formMetricCoefficients w e z (p + 1) η (interiorSuccCLM (p + 1) (b i)
      (covectorExteriorCLM (p + 1) (coordinateCovector b j) θ)) +
    formMetricCoefficients w e z (p + 1) η (covectorExteriorCLM p (coordinateCovector b j)
      (interiorSuccCLM p (b i) θ)) =
      if i = j then formMetricCoefficients w e z (p + 1) η θ else 0 := by
  rw [← map_add, interior_covector_clifford]
  by_cases hij : i = j
  · subst j
    simp [coordinateCovector, Module.Basis.coord_apply]
  · simp [coordinateCovector, Module.Basis.coord_apply, hij, eq_comm]

/-- Actual Haar integral energy of both frozen original differentials, with genuine cross term cancellation. -/
theorem integral_frozen_hodge_energy_succ
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (A : ComplexModel n → FormCoefficients n (p + 1))
    (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z (p + 2) (extDeriv A x) (extDeriv A x)) μ ∧
      Integrable (fun x => formMetricCoefficients w e z p
        (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))
        (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))) μ ∧
      ∀ i, Integrable (fun x => formMetricCoefficients w e z (p + 1)
        (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i))) μ) ∧
    (∫ x, formMetricCoefficients w e z (p + 2) (extDeriv A x) (extDeriv A x) ∂μ) +
      (∫ x, formMetricCoefficients w e z p
        (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x))
        (castForm (Nat.add_sub_cancel p 1) (frozenCodifferential w e z (p + 1) A x)) ∂μ) =
      ∑ i, ∫ x, formMetricCoefficients w e z (p + 1)
        (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ := by
  classical
  have HP := integral_frozen_exterior_energy_expansion μ w hw e z hz (p + 1) b hb A
    (hA.of_le (by norm_num)) hc
  have HC := integral_frozen_codifferential_energy_expansion_succ μ w hw e z hz p hp b hb A hA hc
  let V (i : Fin (n * 2)) (x : ComplexModel n) := fderiv ℝ A x (b i)
  let G := formMetricCoefficients w e z (p + 1)
  have hgrad (i : Fin (n * 2)) : Integrable (fun x => G (V i x) (V i x)) μ :=
    integrable_bilinear_of_compact_support μ G
      ((hA.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ((hA.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (Or.inl (hc.fderiv_apply (𝕜 := ℝ) (b i)))
  refine ⟨⟨HP.1.1, HC.1.1, hgrad⟩, ?_⟩
  rw [HP.2, HC.2]
  calc
    _ = ∑ i, ∑ j, ((∫ x, G (V i x) (interiorSuccCLM (p + 1) (b i)
        (covectorExteriorCLM (p + 1) (coordinateCovector b j) (V j x))) ∂μ) +
        ∫ x, G (V i x) (covectorExteriorCLM p (coordinateCovector b j)
          (interiorSuccCLM p (b i) (V j x))) ∂μ) := by
      simp only [Finset.sum_add_distrib]
      rfl
    _ = ∑ i, ∑ j, ∫ x, if i = j then G (V i x) (V j x) else 0 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_add (HP.1.2 i j) (HC.1.2 i j)]
      exact integral_congr_ae (Eventually.of_forall fun x =>
        frozen_cross_energy_diagonal w e z p b i j (V i x) (V j x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [ite_true]
        rfl
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

/-- Actual zero-degree energy needs the original zero-degree Clifford identity and no negative degree space. -/
theorem integral_frozen_hodge_energy_zero
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (A : ComplexModel n → FormCoefficients n 0) (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z 1 (extDeriv A x) (extDeriv A x)) μ ∧
      ∀ i, Integrable (fun x => formMetricCoefficients w e z 0
        (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i))) μ) ∧
    (∫ x, formMetricCoefficients w e z 1 (extDeriv A x) (extDeriv A x) ∂μ) =
      ∑ i, ∫ x, formMetricCoefficients w e z 0 (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ := by
  classical
  have H := integral_frozen_exterior_energy_expansion μ w hw e z hz 0 b hb A
    (hA.of_le (by norm_num)) hc
  have hgrad (i : Fin (n * 2)) := integrable_bilinear_of_compact_support μ
    (formMetricCoefficients w e z 0)
    ((hA.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := b i)))
    ((hA.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := b i)))
    (Or.inl (hc.fderiv_apply (𝕜 := ℝ) (b i)))
  refine ⟨⟨H.1.1, hgrad⟩, ?_⟩
  rw [H.2]
  have hdiag (i j : Fin (n * 2)) (x : ComplexModel n) :
      formMetricCoefficients w e z 0 (fderiv ℝ A x (b i))
        (interiorSuccCLM 0 (b i)
          (covectorExteriorCLM 0 (coordinateCovector b j) (fderiv ℝ A x (b j)))) =
        if i = j then formMetricCoefficients w e z 0 (fderiv ℝ A x (b i))
          (fderiv ℝ A x (b j)) else 0 := by
    rw [interior_covector_zero]
    by_cases hij : i = j
    · subst j
      simp [coordinateCovector, Module.Basis.coord_apply]
    · simp [coordinateCovector, Module.Basis.coord_apply, hij, eq_comm]
  calc
    _ = ∑ i, ∑ j, ∫ x, if i = j then formMetricCoefficients w e z 0
        (fderiv ℝ A x (b i)) (fderiv ℝ A x (b j)) else 0 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact integral_congr_ae (Eventually.of_forall (hdiag i j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

/-- Genuine natural-degree frozen Hodge energy, including actual excessive source zero and dimension zero. -/
theorem integral_frozen_hodge_energy
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x)) μ ∧
      Integrable (fun x => formMetricCoefficients w e z (q - 1)
        (frozenCodifferential w e z q A x) (frozenCodifferential w e z q A x)) μ ∧
      ∀ i, Integrable (fun x => formMetricCoefficients w e z q
        (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i))) μ) ∧
    (∫ x, formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x) ∂μ) +
      (∫ x, formMetricCoefficients w e z (q - 1)
        (frozenCodifferential w e z q A x) (frozenCodifferential w e z q A x) ∂μ) =
      ∑ i, ∫ x, formMetricCoefficients w e z q (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ := by
  cases q with
  | zero =>
    have H := integral_frozen_hodge_energy_zero μ w hw e z hz b hb A hA hc
    simpa only [frozenCodifferential_zero, map_zero, zero_apply, integral_zero, add_zero] using
      (show (_ ∧ Integrable (fun _ : ComplexModel n => (0 : ℝ)) μ ∧ _) ∧ _ from
        ⟨⟨H.1.1, integrable_zero _ _ _, H.1.2⟩, H.2⟩)
  | succ p =>
    by_cases hp : p + 1 ≤ 2 * n
    · simpa using integral_frozen_hodge_energy_succ μ w hw e z hz p hp b hb A hA hc
    · have hq : 2 * n < p + 1 := not_le.mp hp
      have hAz : A = fun _ => 0 := by
        funext x
        exact (degreeStar_above_source w e z (p + 1) hq (A x)).1
      rw [hAz]
      simp [frozenCodifferential_above w e z (p + 1) hq, extDeriv,
        ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

/-- A genuine internally produced original positive frame calibrates both actual first-order and trace energies. -/
theorem exists_actual_frozen_hodge_energy_model
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∀ (q : ℕ) (A : ComplexModel n → FormCoefficients n q),
        ContDiff ℝ 2 A → HasCompactSupport A →
        (Integrable (fun x => formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x)) μ ∧
          Integrable (fun x => formMetricCoefficients w e z (q - 1)
            (frozenCodifferential w e z q A x) (frozenCodifferential w e z q A x)) μ ∧
          Integrable (fun x => formMetricCoefficients w e z q (A x) (frozenPrincipalTrace b A x)) μ ∧
          ∀ i, Integrable (fun x => formMetricCoefficients w e z q
            (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i))) μ) ∧
        ((∫ x, formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x) ∂μ) +
          (∫ x, formMetricCoefficients w e z (q - 1)
            (frozenCodifferential w e z q A x) (frozenCodifferential w e z q A x) ∂μ) =
            ∑ i, ∫ x, formMetricCoefficients w e z q (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ) ∧
        ((∑ i, ∫ x, formMetricCoefficients w e z q (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ) =
          ∫ x, formMetricCoefficients w e z q (A x) (frozenPrincipalTrace b A x) ∂μ) := by
  obtain ⟨b, hb, ho⟩ := exists_positive_metric_orthonormal_basis (hw e z hz).1 (hw e z hz).2
  refine ⟨b, hb, ho, ?_⟩
  intro q A hA hc
  have H := integral_frozen_hodge_energy μ w hw e z hz q b hb A hA hc
  have T := integral_frozenPrincipalTrace_energy μ w e z q b A hA hc
  exact ⟨⟨H.1.1, H.1.2.1, T.1.1, H.1.2.2⟩, H.2, T.2.symm⟩

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenHodgeEnergy
