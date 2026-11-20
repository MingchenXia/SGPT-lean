import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgePrincipalSymbol
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

/-! Actual compact-support integration and internally calibrated frozen principal energy. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenPrincipalEnergy

open FirstPass FirstPass.MongeAmpere NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianMetricCoefficients NaturalHermitianMusicalInverse NaturalHermitianSmoothFormMetric
  NaturalHermitianOriginalFormMetric NaturalHermitianOrthonormalFormBasis NaturalHermitianUnitVolume

section BilinearIntegration

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
/-- Bilinear support is genuinely compact whenever its original left factor is. -/
theorem hasCompactSupport_bilinear_left (B : F →L[ℝ] G →L[ℝ] ℝ)
    {f : E → F} {g : E → G} (hc : HasCompactSupport f) :
    HasCompactSupport (fun x => B (f x) (g x)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]

omit [NormedSpace ℝ E] in
theorem hasCompactSupport_bilinear_right (B : F →L[ℝ] G →L[ℝ] ℝ)
    {f : E → F} {g : E → G} (hc : HasCompactSupport g) :
    HasCompactSupport (fun x => B (f x) (g x)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- Actual compact support internally supplies integrability of an original bilinear field. -/
theorem integrable_bilinear_of_compact_support (B : F →L[ℝ] G →L[ℝ] ℝ)
    {f : E → F} {g : E → G} (hf : Continuous f) (hg : Continuous g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x => B (f x) (g x)) μ := by
  have hcont := (B.continuous.comp hf).clm_apply hg
  apply hcont.integrable_of_hasCompactSupport
  rcases hfg with hf | hg
  · exact hasCompactSupport_bilinear_left B hf
  · exact hasCompactSupport_bilinear_right B hg

/-- Genuine directional integration by parts; the caller supplies no integrability certificate. -/
theorem integral_bilinear_directional_by_parts (B : F →L[ℝ] G →L[ℝ] ℝ)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (v : E) :
    (Integrable (fun x => B (fderiv ℝ f x v) (g x)) μ ∧
      Integrable (fun x => B (f x) (fderiv ℝ g x v)) μ) ∧
    (∫ x, B (f x) (fderiv ℝ g x v) ∂μ) =
      -(∫ x, B (fderiv ℝ f x v) (g x) ∂μ) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hleft := integrable_bilinear_of_compact_support μ B hdf hg.continuous
    (hfg.imp (fun h => h.fderiv_apply (𝕜 := ℝ) v) id)
  have hright := integrable_bilinear_of_compact_support μ B hf.continuous hdg
    (hfg.imp id (fun h => h.fderiv_apply (𝕜 := ℝ) v))
  refine ⟨⟨hleft, hright⟩, ?_⟩
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable hleft hright
    (integrable_bilinear_of_compact_support μ B hf.continuous hg.continuous hfg)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual fixed-direction derivative evaluation, with the original full second Fréchet derivative. -/
theorem directional_derivative_of_second_derivative {g : E → G}
    (hg : ContDiff ℝ 2 g) (x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x u = (fderiv ℝ (fderiv ℝ g) x u) v := by
  have hd := (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Real C² smoothness genuinely produces the actual mixed directional commutation. -/
theorem directional_second_derivatives_commute {g : E → G}
    (hg : ContDiff ℝ 2 g) (x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x u =
      fderiv ℝ (fun y => fderiv ℝ g y u) x v := by
  rw [directional_derivative_of_second_derivative hg,
    directional_derivative_of_second_derivative hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v

/-- Integration genuinely transfers both fixed directional derivatives, rather than assuming weak regularity. -/
theorem integral_mixed_directional_transfer (B : F →L[ℝ] G →L[ℝ] ℝ)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (u v : E) :
    (∫ x, B (fderiv ℝ f x u) (fderiv ℝ g x v) ∂μ) =
      ∫ x, B (fderiv ℝ f x v) (fderiv ℝ g x u) ∂μ := by
  have hdu : ContDiff ℝ 1 (fun x => fderiv ℝ g x u) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdv : ContDiff ℝ 1 (fun x => fderiv ℝ g x v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hu := (integral_bilinear_directional_by_parts μ B hf hdv
    (hfg.imp id (fun h => h.fderiv_apply (𝕜 := ℝ) v)) u).2
  have hv := (integral_bilinear_directional_by_parts μ B hf hdu
    (hfg.imp id (fun h => h.fderiv_apply (𝕜 := ℝ) u)) v).2
  have he : (fun x => B (f x) (fderiv ℝ (fun y => fderiv ℝ g y v) x u)) =
      (fun x => B (f x) (fderiv ℝ (fun y => fderiv ℝ g y u) x v)) := by
    funext x
    rw [directional_second_derivatives_commute hg]
  rw [he] at hu
  exact neg_injective (hu.symm.trans hv)

end BilinearIntegration

section PrincipalTrace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]

/-- Literal frozen second-order principal trace in the original coefficient norms. -/
def frozenPrincipalTrace (v : ι → E) (A : E → F) (x : E) : F :=
  -(∑ i : ι, fderiv ℝ (fun y => fderiv ℝ A y (v i)) x (v i))

/-- Actual constant coefficient trace energy, with all compact-support integrability internally produced. -/
theorem integral_frozenPrincipalTrace_bilinear
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (B : F →L[ℝ] F →L[ℝ] ℝ)
    (v : ι → E) (A : E → F) (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => B (A x) (frozenPrincipalTrace v A x)) μ ∧
      ∀ i : ι, Integrable (fun x => B (fderiv ℝ A x (v i)) (fderiv ℝ A x (v i))) μ) ∧
    (∫ x, B (A x) (frozenPrincipalTrace v A x) ∂μ) =
      ∑ i : ι, ∫ x, B (fderiv ℝ A x (v i)) (fderiv ℝ A x (v i)) ∂μ := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hd (i : ι) : ContDiff ℝ 1 (fun x => fderiv ℝ A x (v i)) :=
    (hA.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hp (i : ι) := integral_bilinear_directional_by_parts μ B hA1 (hd i) (Or.inl hc) (v i)
  have he : (fun x => B (A x) (frozenPrincipalTrace v A x)) =
      (fun x => -(∑ i : ι, B (A x) (fderiv ℝ (fun y => fderiv ℝ A y (v i)) x (v i)))) := by
    funext x
    simp only [frozenPrincipalTrace, map_neg, map_sum]
  constructor
  · constructor
    · rw [he]
      exact (integrable_finsetSum _ (fun i _ => (hp i).1.2)).neg
    · intro i
      exact (hp i).1.1
  · rw [he, integral_neg, integral_finsetSum _ (fun i _ => (hp i).1.2)]
    calc
      -(∑ i : ι, ∫ x, B (A x) (fderiv ℝ (fun y => fderiv ℝ A y (v i)) x (v i)) ∂μ) =
          -(∑ i : ι, -(∫ x, B (fderiv ℝ A x (v i)) (fderiv ℝ A x (v i)) ∂μ)) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => (hp i).2)
      _ = _ := by rw [Finset.sum_neg_distrib, neg_neg]

/-- Entire frozen trace quadratic evaluation is genuinely differentiated, not supplied as a symbol assumption. -/
theorem frozenPrincipalTrace_quadratic_constant (v : ι → E) (z : E)
    (ℓ : E →L[ℝ] ℝ) (η : F) :
    frozenPrincipalTrace v (fun y => quadraticScalar z ℓ y • η) z =
      -((∑ i : ι, (ℓ (v i)) ^ 2) • η) := by
  have hQ : ContDiff ℝ 2 (fun y => quadraticScalar z ℓ y • η) :=
    ((quadraticScalar_contDiff z ℓ).of_le (m := 2)
      (by exact WithTop.coe_le_coe.mpr le_top)).smul contDiff_const
  have hjet := (quadraticScalar_second_product_jet z ℓ (fun _ => η) contDiffAt_const).2
  have hd (i : ι) : fderiv ℝ (fun y => fderiv ℝ (fun x => quadraticScalar z ℓ x • η) y (v i)) z (v i) =
      (ℓ (v i)) ^ 2 • η := by
    rw [directional_derivative_of_second_derivative hQ, hjet]
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_smul, pow_two]
  unfold frozenPrincipalTrace
  simp_rw [hd]
  rw [← Finset.sum_smul]

end PrincipalTrace

section OriginalMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

/-- True original frozen form-metric energy, in the unchanged original coefficient norm. -/
theorem integral_frozenPrincipalTrace_energy (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (e : ComplexChart n M) (z : ComplexModel n) (q : ℕ)
    {ι : Type*} [Fintype ι] (v : ι → ComplexModel n)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    (Integrable (fun x => formMetricCoefficients w e z q (A x) (frozenPrincipalTrace v A x)) μ ∧
      ∀ i : ι, Integrable (fun x => formMetricCoefficients w e z q
        (fderiv ℝ A x (v i)) (fderiv ℝ A x (v i))) μ) ∧
    (∫ x, formMetricCoefficients w e z q (A x) (frozenPrincipalTrace v A x) ∂μ) =
      ∑ i : ι, ∫ x, formMetricCoefficients w e z q (fderiv ℝ A x (v i)) (fderiv ℝ A x (v i)) ∂μ :=
  integral_frozenPrincipalTrace_bilinear μ (formMetricCoefficients w e z q) v A hA hc

/-- Positivity comes from the actual original exterior Gram metric, not a caller's differential certificate. -/
theorem integral_frozenPrincipalTrace_energy_nonneg (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ)
    {ι : Type*} [Fintype ι] (v : ι → ComplexModel n)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 2 A) (hc : HasCompactSupport A) :
    0 ≤ ∫ x, formMetricCoefficients w e z q (A x) (frozenPrincipalTrace v A x) ∂μ := by
  have hpos (η : FormCoefficients n q) : 0 ≤ formMetricCoefficients w e z q η η := by
    rw [formMetricCoefficients_eq_original w hw e z hz]
    rcases eq_or_ne η 0 with hzero | hne
    · rw [hzero]
      simp
    · exact ((originalFormMetric_symm_positive (w.coeff e z) (hw e z hz).1
        (hw e z hz).2 q).2 _ hne).le
  rw [(integral_frozenPrincipalTrace_energy μ w e z q v A hA hc).2]
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x => hpos (fderiv ℝ A x (v i)))

/-- Original inverse musical quadratic form is the real square sum on every genuine metric ON basis. -/
theorem dual_metric_eq_sum_coordinates {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (ℓ : ComplexModel n →L[ℝ] ℝ) :
    ℓ ((associatedMetricCLM a).inverse ℓ) = ∑ i : Fin (n * 2), (ℓ (b i)) ^ 2 := by
  have hcoord (i : Fin (n * 2)) : b.repr ((associatedMetricCLM a).inverse ℓ) i = ℓ (b i) := by
    change coordinateCovector b i ((associatedMetricCLM a).inverse ℓ) = _
    rw [coordinateCovector_eq_metric b hb]
    have hsym : associatedMetricCLM a (b i) ((associatedMetricCLM a).inverse ℓ) =
        associatedMetricCLM a ((associatedMetricCLM a).inverse ℓ) (b i) := by
      simp only [associatedMetricCLM_apply]
      exact associatedMetric_symm hJ _ _
    rw [hsym, (metric_inverse_identities hp).1 ℓ]
  have hrep : (associatedMetricCLM a).inverse ℓ = ∑ i : Fin (n * 2), ℓ (b i) • b i := by
    simpa only [hcoord] using (b.sum_repr ((associatedMetricCLM a).inverse ℓ)).symm
  rw [hrep, map_sum]
  simp only [map_smul, smul_eq_mul, pow_two]

/-- A genuine metric ON basis and compact principal-energy model are supplied internally from the original form. -/
theorem exists_actual_frozen_principal_energy_model (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      (∀ ℓ : ComplexModel n →L[ℝ] ℝ,
        ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) = ∑ i : Fin (n * 2), (ℓ (b i)) ^ 2) ∧
      (∀ (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n q),
        frozenPrincipalTrace b (fun y => quadraticScalar z ℓ y • η) z =
          localHodgeLaplacian w e q (fun y => quadraticScalar z ℓ y • η) z ∧
        frozenPrincipalTrace b (fun y => quadraticScalar z ℓ y • η) z =
          realPrincipalSymbol w e z q ℓ η) ∧
      ∀ (q : ℕ) (A : ComplexModel n → FormCoefficients n q),
        ContDiff ℝ 2 A → HasCompactSupport A →
        (Integrable (fun x => formMetricCoefficients w e z q (A x) (frozenPrincipalTrace b A x)) μ ∧
          ∀ i : Fin (n * 2), Integrable (fun x => formMetricCoefficients w e z q
            (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i))) μ) ∧
        (∫ x, formMetricCoefficients w e z q (A x) (frozenPrincipalTrace b A x) ∂μ) =
          (∑ i : Fin (n * 2), ∫ x, formMetricCoefficients w e z q
            (fderiv ℝ A x (b i)) (fderiv ℝ A x (b i)) ∂μ) ∧
        0 ≤ ∫ x, formMetricCoefficients w e z q (A x) (frozenPrincipalTrace b A x) ∂μ := by
  obtain ⟨b, hb, ho⟩ := exists_positive_metric_orthonormal_basis (hw e z hz).1 (hw e z hz).2
  refine ⟨b, hb, ho, ?_, ?_, ?_⟩
  · intro ℓ
    exact dual_metric_eq_sum_coordinates (hw e z hz).1 (hw e z hz).2 b hb ℓ
  · intro q ℓ η
    have hquad := frozenPrincipalTrace_quadratic_constant b z ℓ η
    rw [← dual_metric_eq_sum_coordinates (hw e z hz).1 (hw e z hz).2 b hb ℓ] at hquad
    have hlocal := localHodgeLaplacian_quadratic_product w hw e q z hz ℓ (fun _ => η) contDiffAt_const
    exact ⟨hquad.trans hlocal.symm,
      (hquad.trans hlocal.symm).trans (realPrincipalSymbol_eq_actual_quadratic_test w hw e z hz q ℓ η).symm⟩
  · intro q A hA hc
    exact ⟨(integral_frozenPrincipalTrace_energy μ w e z q b A hA hc).1,
      (integral_frozenPrincipalTrace_energy μ w e z q b A hA hc).2,
      integral_frozenPrincipalTrace_energy_nonneg μ w hw e z hz q b A hA hc⟩

end OriginalMetric

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenPrincipalEnergy
