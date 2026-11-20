import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.ExceptionalMetric
import SGPT.Foundations.Analysis.PshRegularizationData
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

/-!
# The Lelong--Poincaré equation for a metered effective `ℚ`-divisor

Let `E` be an effective `ℚ`-divisor with a smooth Hermitian metric on a complex manifold `M`
(`MeteredEffectiveQDivisor`): a global weight `ψ_E` which near every point is
`Σ aᵢ log |gᵢ|² + h` (`aᵢ ∈ ℚ_{≥0}`, `gᵢ` holomorphic and vanishing identically on no open set,
`h` smooth), and the curvature form `Θ_E`, equal to `-ddᶜ h` there.  We prove
(`lelongPoincare`):

* `ψ_E` is locally integrable in every chart (`chartLocallyIntegrable_weight`);
* the global current `[E] := ddᶜ ψ_E + Θ_E` (`integrationCurrent`) is closed, of type `(1,1)` and
  positive (`isClosed_integrationCurrent`, `isTypeOneOne_integrationCurrent`,
  `isSquarePositive_integrationCurrent`);
* on the domain of every local presentation, read in any chart, `[E] = Σ aᵢ [div gᵢ]`
  (`restrictForm_coefficients_eq_sum`), where `[div g]` is the integration current over the regular
  part of the zero set (`DivisorIntegrationCurrent.divisorCurrent`); the factor `c_b` there is the
  density of the Haar measure normalized by the chosen basis `b` with respect to Lebesgue measure,
  the normalization of all chart coefficients (`c_b = 1` for an orthonormal basis);
* hence `ddᶜ ψ_E = [E] - Θ_E` (`ddCWeight_eq`): `[E]` and `Θ_E` differ by `ddᶜ` of a global locally
  integrable function and define the same class.

For a modification `π : Y → X` of a compact Kähler manifold, the exceptional divisor `F` of
`ExceptionalMetric` gives a Kähler form `ω̃ = π^* ω - Θ_F` with
`ω̃ = π^* ω - [F] + ddᶜ ψ_F` as currents (`exists_exceptional_correction_class`).

## Proof

On the domain `W` of a presentation in a chart, `ψ_E = Σ aᵢ log |Gᵢ|² + H` almost everywhere
(`LocalPresentation.ae_chartFunction_eq`: the zero sets of the `Gᵢ` are null), so
`ddᶜ ψ_E = c_b Σ aᵢ [div Gᵢ] + ddᶜ H` on `W` by the flat Lelong--Poincaré equation
(`ddC_eq_sum_divisorCurrent_add`, from `DivisorIntegrationCurrent`), and `ddᶜ H = -Θ_E` there
(`restrictForm_smoothFormDistribution_curvature`, through a cutoff:
`ddC_regularDistribution_apply_of_contDiffOn`).  Restriction to open subsets commutes with
`ddᶜ` and the exterior derivative (`restrictForm_ddC`, `restrictForm_exteriorDerivative`), and
distributions are determined, and positive, locally (`eq_of_forall_restrict_eq`,
`positiveDistribution_of_forall_restrict`, by a smooth partition of unity); so the global
properties of `[E]` follow from the local ones.
-/

open Set Filter Function MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal Distributions Manifold

noncomputable section

open SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

open FirstPass DivisorRegularLocus DivisorIntegrationCurrent

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω U : Opens E}

/-- Restriction of distributions to a smaller open set, as a linear map. -/
def restrictLM (hUΩ : U ≤ Ω) : 𝓓'(Ω, ℝ) →ₗ[ℝ] 𝓓'(U, ℝ) where
  toFun T := restrictDistribution T hUΩ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of a distribution-valued form to a smaller open set. -/
def restrictForm {k : ℕ} (A : DistributionForm Ω k) (hUΩ : U ≤ Ω) : DistributionForm U k :=
  (restrictLM hUΩ).compAlternatingMap A

@[simp] theorem restrictForm_apply {k : ℕ} (A : DistributionForm Ω k) (hUΩ : U ≤ Ω)
    (v : Fin k → E) (φ : 𝓓(U, ℝ)) :
    restrictForm A hUΩ v φ = A v (TestFunction.monoCLM ℝ φ) := rfl

theorem restrictForm_apply' {k : ℕ} (A : DistributionForm Ω k) (hUΩ : U ≤ Ω)
    (v : Fin k → E) : restrictForm A hUΩ v = restrictDistribution (A v) hUΩ := rfl

theorem restrictForm_add {k : ℕ} (A B : DistributionForm Ω k) (hUΩ : U ≤ Ω) :
    restrictForm (A + B) hUΩ = restrictForm A hUΩ + restrictForm B hUΩ := by
  ext v φ
  rfl

theorem monoCLM_lineDerivCLM (hUΩ : U ≤ Ω) (v : E) (φ : 𝓓(U, ℝ)) :
    (TestFunction.monoCLM ℝ (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) : 𝓓(Ω, ℝ)) =
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (TestFunction.monoCLM ℝ φ) := by
  apply TestFunction.ext
  intro x
  rw [congrFun (testFunction_inclusion_coe hUΩ _) x, testFunction_lineDerivCLM_apply_eq_fderiv,
    testFunction_lineDerivCLM_apply_eq_fderiv, testFunction_inclusion_coe hUΩ φ]

theorem restrictDistribution_lineDerivCLM (T : 𝓓'(Ω, ℝ)) (hUΩ : U ≤ Ω) (v : E) :
    restrictDistribution (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) hUΩ =
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (restrictDistribution T hUΩ) := by
  ext φ
  rw [restrictDistribution_apply, Distribution.lineDerivCLM_apply, Distribution.lineDerivCLM_apply,
    restrictDistribution_apply, monoCLM_lineDerivCLM hUΩ]

/-- Restriction commutes with the exterior derivative. -/
theorem restrictForm_exteriorDerivative {k : ℕ} (A : DistributionForm Ω k) (hUΩ : U ≤ Ω) :
    restrictForm (exteriorDerivative A) hUΩ = exteriorDerivative (restrictForm A hUΩ) := by
  ext v : 1
  rw [restrictForm_apply', exteriorDerivative_apply, exteriorDerivative_apply]
  change restrictLM hUΩ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  exact restrictDistribution_lineDerivCLM _ hUΩ _

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Restriction commutes with `ddᶜ`. -/
theorem restrictForm_ddC (T : 𝓓'(Ω, ℝ)) (hUΩ : U ≤ Ω) :
    restrictForm (ddC T) hUΩ = ddC (restrictDistribution T hUΩ) := by
  ext v : 1
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, restrictForm_apply', ddC_apply, ddC_apply]
  change restrictLM hUΩ _ = _
  rw [map_smul, map_sub]
  change (-1 / (4 * Real.pi) : ℝ) • (restrictDistribution _ hUΩ - restrictDistribution _ hUΩ) = _
  rw [restrictDistribution_lineDerivCLM, restrictDistribution_lineDerivCLM,
    restrictDistribution_lineDerivCLM, restrictDistribution_lineDerivCLM]

/-- `ddᶜ` as a linear map. -/
def ddCLM : 𝓓'(Ω, ℝ) →ₗ[ℝ] DistributionForm Ω 2 where
  toFun := ddC
  map_add' S T := by
    ext v : 1
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, AlternatingMap.add_apply, ddC_apply, ddC_apply, ddC_apply]
    simp only [map_add]
    module
  map_smul' c T := by
    ext v : 1
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, AlternatingMap.smul_apply, ddC_apply, ddC_apply]
    simp only [map_smul, RingHom.id_apply]
    module

@[simp] theorem ddCLM_apply (T : 𝓓'(Ω, ℝ)) : ddCLM T = ddC T := rfl

end Restriction

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-- **Splitting a test function along an open cover** (smooth partition of unity): every test
function on `Ω` is a finite sum of test functions supported in members of the cover, nonnegative
when it is. -/
theorem exists_sum_monoCLM {ι : Type*} (U : ι → Opens E) (hUΩ : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i) (φ : 𝓓(Ω, ℝ)) :
    ∃ (s : Finset ι) (ψ : ∀ i, 𝓓(U i, ℝ)), φ = ∑ i ∈ s, TestFunction.monoCLM ℝ (ψ i) ∧
      ((∀ x, 0 ≤ φ x) → ∀ i x, 0 ≤ ψ i x) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_closure (fun i ↦ (U i : Set E))
    (fun i ↦ (U i).isOpen) (by
      intro x hx
      obtain ⟨i, hi⟩ := hcover x (φ.tsupport_subset hx)
      exact mem_iUnion.mpr ⟨i, hi⟩)
  let active : Set ι := {i | (Function.support (ρ i) ∩ tsupport φ).Nonempty}
  have hactive : active.Finite := by
    simpa only [active] using ρ.locallyFinite.finite_nonempty_inter_compact φ.hasCompactSupport
  let ψ (i : ι) : 𝓓(U i, ℝ) :=
    ⟨fun x ↦ ρ i x * φ x, (ρ i).contMDiff.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_left (f := fun x ↦ ρ i x) (g := fun x ↦ φ x)).trans (hρ i)⟩
  refine ⟨hactive.toFinset, ψ, ?_, fun h0 i x => mul_nonneg (ρ.nonneg i x) (h0 x)⟩
  apply TestFunction.ext
  intro x
  have hsum_apply : ∀ s : Finset ι,
      (∑ i ∈ s, (TestFunction.monoCLM ℝ (ψ i) : 𝓓(Ω, ℝ))) x = ∑ i ∈ s, ρ i x * φ x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi hs =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change (TestFunction.monoCLM ℝ (ψ i) : 𝓓(Ω, ℝ)) x +
            (∑ j ∈ s, (TestFunction.monoCLM ℝ (ψ j) : 𝓓(Ω, ℝ))) x =
          ρ i x * φ x + ∑ j ∈ s, ρ j x * φ x
        rw [hs]
        exact congrArg₂ (· + ·) (congrFun (testFunction_inclusion_coe (hUΩ i) (ψ i)) x) rfl
  rw [hsum_apply]
  by_cases hx : x ∈ tsupport φ
  · have hsupp : Function.support (fun i ↦ ρ i x) ⊆ active := fun i hi => ⟨x, hi, hx⟩
    rw [← Finset.sum_mul, ← finsum_eq_finsetSum_of_support_subset (fun i ↦ ρ i x)
      (by simpa only [Set.Finite.coe_toFinset] using hsupp), ρ.sum_eq_one hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

/-- Distributions agreeing on the members of an open cover are equal. -/
theorem eq_of_forall_restrict_eq {ι : Type*} (U : ι → Opens E) (hUΩ : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i) {T S : 𝓓'(Ω, ℝ)}
    (h : ∀ i, restrictDistribution T (hUΩ i) = restrictDistribution S (hUΩ i)) : T = S := by
  ext φ
  obtain ⟨s, ψ, hφ, -⟩ := exists_sum_monoCLM U hUΩ hcover φ
  rw [hφ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun R : 𝓓'(U i, ℝ) => R (ψ i)) (h i)

/-- A distribution whose restrictions to the members of an open cover are positive is positive. -/
theorem positiveDistribution_of_forall_restrict {ι : Type*} (U : ι → Opens E)
    (hUΩ : ∀ i, U i ≤ Ω) (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i) {T : 𝓓'(Ω, ℝ)}
    (h : ∀ i, PositiveDistribution (restrictDistribution T (hUΩ i))) : PositiveDistribution T := by
  intro φ hφ
  obtain ⟨s, ψ, hφs, hψ⟩ := exists_sum_monoCLM U hUΩ hcover φ
  rw [hφs, map_sum]
  exact Finset.sum_nonneg fun i _ => h i (ψ i) (hψ hφ i)

/-- Distribution-valued forms agreeing on the members of an open cover are equal. -/
theorem form_eq_of_forall_restrictForm_eq {ι : Type*} (U : ι → Opens E) (hUΩ : ∀ i, U i ≤ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i) {k : ℕ} {A B : DistributionForm Ω k}
    (h : ∀ i, restrictForm A (hUΩ i) = restrictForm B (hUΩ i)) : A = B := by
  ext v : 1
  refine eq_of_forall_restrict_eq U hUΩ hcover fun i => ?_
  rw [← restrictForm_apply', ← restrictForm_apply', h i]

end Gluing

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth cutoff equal to `1` near a compact set and supported in a given open set. -/
theorem exists_cutoff [FiniteDimensional ℝ E] {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x ∈ K, χ =ᶠ[𝓝 x] 1) ∧ tsupport χ ⊆ W := by
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (I := 𝓘(ℝ, E))
    (n := (⊤ : ℕ∞)) hW.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.mpr hKW)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx => ?_, fun x hx => ?_⟩
  · exact (eventually_nhdsSet_iff_forall.mp h1) x hx
  · by_contra hxW
    exact (notMem_tsupport_iff_eventuallyEq.mpr ((eventually_nhdsSet_iff_forall.mp h0) x hxW)) hx

theorem contDiff_mul_of_tsupport_subset {D : Set E} (hD : IsOpen D) {χ ρ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχD : tsupport χ ⊆ D) (hρ : ContDiffOn ℝ ∞ ρ D) :
    ContDiff ℝ ∞ (fun z => χ z * ρ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ D
  · exact hχ.contDiffAt.mul (hρ.contDiffAt (hD.mem_nhds hz))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hχD h)] with y hy
    simp [hy]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {Ω : Opens E}

/-- `ddᶜ` of a regular distribution, tested on `φ`, only sees the density on `supp φ`. -/
theorem ddC_regularDistribution_apply_congr {μ : Measure E} {u u' : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u' Ω μ) (φ : 𝓓(Ω, ℝ))
    (h : ∀ x ∈ tsupport φ, u x = u' x) (v w : E) :
    ddC (regularDistribution μ u hu) ![v, w] φ = ddC (regularDistribution μ u' hu') ![v, w] φ := by
  have key : ∀ a c : E,
      regularDistribution μ u hu (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ c φ)) =
      regularDistribution μ u' hu' (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ c φ)) := by
    intro a c
    rw [regularDistribution_apply, regularDistribution_apply]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · change _ * u x = _ * u' x
      rw [h x hx]
    · change _ * u x = _ * u' x
      rw [testFunction_lineDerivCLM_lineDerivCLM_apply, realHessian_eq_zero_of_notMem_tsupport hx,
        zero_mul, zero_mul]
  rw [ddC_apply, ddC_apply]
  simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
    Pi.sub_apply, Distribution.lineDerivCLM_apply, neg_neg, key]

end Smooth

section Regular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {Ω : Opens E}

omit [NormedSpace ℝ E] [OpensMeasurableSpace E] in
theorem locallyIntegrableOn_smul_measure {μ : Measure E} (c : ℝ≥0) {u : E → ℝ} {s : Set E}
    (hu : LocallyIntegrableOn u s μ) : LocallyIntegrableOn u s (c • μ) := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hu x hx
  exact ⟨t, ht, by simpa only [IntegrableOn, Measure.restrict_smul] using hi.smul_measure_nnreal⟩

theorem regularDistribution_smul_measure {μ : Measure E} (c : ℝ≥0) {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u Ω (c • μ)) :
    regularDistribution (c • μ) u hu' = (c : ℝ) • regularDistribution μ u hu := by
  ext φ
  rw [smul_apply, regularDistribution_apply, regularDistribution_apply,
    integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem regularDistribution_add' {μ : Measure E} {u u' : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u' Ω μ)
    (h : LocallyIntegrableOn (fun x => u x + u' x) Ω μ) :
    regularDistribution μ (fun x => u x + u' x) h =
      regularDistribution μ u hu + regularDistribution μ u' hu' := by
  ext φ
  have h1 : Integrable (fun x => φ x * u x) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu φ
  have h2 : Integrable (fun x => φ x * u' x) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu' φ
  rw [add_apply, regularDistribution_apply, regularDistribution_apply,
    regularDistribution_apply, ← integral_add h1 h2]
  simp only [mul_add]

theorem regularDistribution_const_mul {μ : Measure E} (c : ℝ) {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (h : LocallyIntegrableOn (fun x => c * u x) Ω μ) :
    regularDistribution μ (fun x => c * u x) h = c • regularDistribution μ u hu := by
  ext φ
  rw [smul_apply, regularDistribution_apply, regularDistribution_apply,
    smul_eq_mul, ← integral_const_mul]
  simp only [mul_left_comm]

theorem regularDistribution_sum {ι : Type*} (s : Finset ι) {μ : Measure E} {u : ι → E → ℝ}
    (hu : ∀ i, LocallyIntegrableOn (u i) Ω μ)
    (h : LocallyIntegrableOn (fun x => ∑ i ∈ s, u i x) Ω μ) :
    regularDistribution μ (fun x => ∑ i ∈ s, u i x) h =
      ∑ i ∈ s, regularDistribution μ (u i) (hu i) := by
  ext φ
  rw [regularDistribution_apply, sum_apply]
  simp only [regularDistribution_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i _ =>
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hu i) φ

omit [NormedSpace ℝ E] [OpensMeasurableSpace E] in
theorem locallyIntegrableOn_finsetSum {ι : Type*} (s : Finset ι) {μ : Measure E}
    {u : ι → E → ℝ} {S : Set E} (hu : ∀ i ∈ s, LocallyIntegrableOn (u i) S μ) :
    LocallyIntegrableOn (fun x => ∑ i ∈ s, u i x) S μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x _
      exact ⟨Set.univ, Filter.univ_mem, by simp⟩
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hu i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))

end Regular

section Flat

variable {n : ℕ}

/-- **`ddᶜ` of a function smooth on `Ω`** is the classical `ddᶜ`, coefficientwise. -/
theorem ddC_regularDistribution_apply_of_contDiffOn {Ω : Opens (ComplexModel n)}
    {μ : Measure (ComplexModel n)} [μ.IsAddHaarMeasure] {H : ComplexModel n → ℝ}
    (hH : ContDiffOn ℝ ∞ H Ω) (hloc : LocallyIntegrableOn H Ω μ) (v w : ComplexModel n)
    (φ : 𝓓(Ω, ℝ)) :
    ddC (regularDistribution μ H hloc) ![v, w] φ = ∫ x, φ x * smoothDDC H x ![v, w] ∂μ := by
  obtain ⟨χ, hχ, hχ1, hχW⟩ := exists_cutoff φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  have hH' : ContDiff ℝ ∞ (fun z => χ z * H z) :=
    contDiff_mul_of_tsupport_subset Ω.isOpen hχ hχW hH
  have heq : ∀ x ∈ tsupport φ, H x = χ x * H x := fun x hx => by
    rw [(hχ1 x hx).eq_of_nhds, Pi.one_apply, one_mul]
  rw [ddC_regularDistribution_apply_congr hloc
      (hH'.continuous.locallyIntegrable.locallyIntegrableOn Ω) φ heq,
    DDCOverlap.ddC_regularDistribution_apply (hH'.of_le ENat.LEInfty.out) v w φ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport φ
  · have hev : (fun z => χ z * H z) =ᶠ[𝓝 x] H := (hχ1 x hx).mono fun y hy => by
      simp only [hy, Pi.one_apply, one_mul]
    change φ x * smoothDDC _ x ![v, w] = φ x * smoothDDC H x ![v, w]
    rw [smoothDDC_congr hev]
  · change φ x * _ = φ x * _
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- A holomorphic function vanishing identically near no point of an open set is nonzero almost
everywhere on it. -/
theorem ae_ne_zero {W : Set (ComplexModel n)} (hW : IsOpen W) {G : ComplexModel n → ℂ}
    (hG : DifferentiableOn ℂ G W) (hG0 : ∀ y ∈ W, ∃ᶠ z in 𝓝 y, G z ≠ 0) :
    ∀ᵐ z ∂(volume.restrict W), G z ≠ 0 := by
  rw [ae_restrict_iff' hW.measurableSet]
  have h0 : volume {z | z ∈ W ∧ G z = 0} = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW x hx.1
    obtain ⟨y, hy, hyB⟩ := ((hG0 x hx.1).and_eventually (Metric.ball_mem_nhds x hr)).exists
    refine ⟨{z | z ∈ W ∧ G z = 0} ∩ Metric.ball x r,
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr), ?_⟩
    refine measure_mono_null (fun z hz => (⟨hz.2, hz.1.2⟩ : z ∈ Metric.ball x r ∩ G ⁻¹' {0}))
      (HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume Metric.isOpen_ball
        (convex_ball x r) (hG.mono hball) hyB hy)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with z hz hzW hGz
  exact hz ⟨hzW, hGz⟩

/-- **The local Lelong--Poincaré equation for a metered divisor**, flat form.  On an open
`W ⊆ ℂⁿ`, let `ψ = Σ aᵢ log |Gᵢ|² + H` almost everywhere, with `Gᵢ` holomorphic and vanishing
identically near no point and `H` smooth.  For the Haar measure `c · λ`,

  `ddᶜ ψ = c Σ aᵢ [div Gᵢ] + ddᶜ H`. -/
theorem ddC_eq_sum_divisorCurrent_add {W : Opens (ComplexModel n)} (c : ℝ≥0) {N : ℕ}
    (a : Fin N → ℝ) {G : Fin N → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) W)
    (hG0 : ∀ i, ∀ y ∈ W, ∃ᶠ z in 𝓝 y, G i z ≠ 0) {H : ComplexModel n → ℝ}
    (hH : ContDiffOn ℝ ∞ H W) {ψ : ComplexModel n → ℝ}
    (hψ : ∀ᵐ z ∂(volume.restrict W), ψ z = ∑ i, a i * Real.log (‖G i z‖ ^ 2) + H z)
    (hψloc : LocallyIntegrableOn ψ W (c • volume)) :
    ddC (regularDistribution (c • volume) ψ hψloc) =
      (c : ℝ) • ∑ i, a i • divisorCurrent (hG i) (hG0 i) +
        ddC (regularDistribution (c • volume) H
          (hH.continuousOn.locallyIntegrableOn W.isOpen.measurableSet)) := by
  have hlogc : ∀ i, LocallyIntegrableOn (fun z => a i * Real.log (‖G i z‖ ^ 2)) W volume :=
    fun i => by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (locallyIntegrableOn_log_normSq W.isOpen (hG i) (hG0 i)).smul (a i)
  have hHv : LocallyIntegrableOn H W volume :=
    hH.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  have hsum : LocallyIntegrableOn (fun z => ∑ i, a i * Real.log (‖G i z‖ ^ 2)) W volume :=
    locallyIntegrableOn_finsetSum _ fun i _ => hlogc i
  have hFv : LocallyIntegrableOn (fun z => (∑ i, a i * Real.log (‖G i z‖ ^ 2)) + H z) W volume :=
    hsum.add hHv
  have hFc := locallyIntegrableOn_smul_measure c hFv
  have hae : ψ =ᵐ[(c • volume).restrict W] fun z => (∑ i, a i * Real.log (‖G i z‖ ^ 2)) + H z := by
    rw [Measure.restrict_smul]
    exact Measure.ae_smul_measure hψ c
  have hD : ∀ i, ddC (regularDistribution volume (fun z => a i * Real.log (‖G i z‖ ^ 2))
      (hlogc i)) = a i • divisorCurrent (hG i) (hG0 i) := by
    intro i
    rw [regularDistribution_const_mul (a i) (locallyIntegrableOn_log_normSq W.isOpen (hG i) (hG0 i))
      (hlogc i), ← ddCLM_apply, map_smul, ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]
  rw [regularDistribution_congr_ae_on hψloc hFc hae, regularDistribution_smul_measure c hFv hFc,
    regularDistribution_add' hsum hHv hFv, regularDistribution_sum _ hlogc hsum,
    regularDistribution_smul_measure c hHv]
  rw [← ddCLM_apply, map_smul, map_add, map_sum,
    ← ddCLM_apply ((c : ℝ) • regularDistribution volume H hHv), map_smul, smul_add]
  simp only [ddCLM_apply, hD]

end Flat

section Presentation

open HolomorphicIdealSheaves

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- One local presentation of a metered effective `ℚ`-divisor, as provided by its
`local_presentation` field: on the open set `U`, `ψ_E = Σ aᵢ log |gᵢ|² + h` and, in every chart,
`Θ_E = -ddᶜ h`. -/
structure LocalPresentation (D : MeteredEffectiveQDivisor n M) where
  /-- The domain. -/
  U : Set M
  isOpen : IsOpen U
  /-- The number of local equations. -/
  N : ℕ
  /-- The coefficients. -/
  a : Fin N → ℚ
  /-- The local equations. -/
  g : Fin N → M → ℂ
  /-- The smooth part of the weight. -/
  h : M → ℝ
  a_nonneg : ∀ i, 0 ≤ a i
  g_holo : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U
  g_ne : ∀ i, ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g i y ≠ 0
  h_smooth : ∀ e : ComplexChart n M,
    ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)
  weight_eq : ∀ y ∈ U, D.weight y =
    (∑ i, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y) + (h y : EReal)
  curvature_eq : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    e.val.symm z ∈ U → D.curvature.val.coeff e z = -smoothDDC (fun y => h (e.val.symm y)) z

theorem exists_localPresentation (D : MeteredEffectiveQDivisor n M) (x : M) :
    ∃ P : LocalPresentation D, x ∈ P.U := by
  obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, hg0, hh, hw, hc⟩ := D.local_presentation x
  exact ⟨⟨U, hU, N, a, g, h, ha, hg, hg0, hh, hw, hc⟩, hxU⟩

theorem coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

theorem generatorLog_one_of_ne_zero {X : Type*} {g : X → ℂ} {y : X} (hy : g y ≠ 0) :
    generatorLog (fun _ : Fin 1 => g) y = ((Real.log (‖g y‖ ^ 2) : ℝ) : EReal) := by
  rw [generatorLog_of_nonzero ⟨0, hy⟩]
  simp [generatorNormSq]

namespace LocalPresentation

variable {D : MeteredEffectiveQDivisor n M} (P : LocalPresentation D) (e : ComplexChart n M)

/-- The domain of the presentation in the chart `e`. -/
def chartDomain : Opens (ComplexModel n) :=
  ⟨e.val.target ∩ e.val.symm ⁻¹' P.U, e.val.isOpen_inter_preimage_symm P.isOpen⟩

theorem chartDomain_le : P.chartDomain e ≤ chartTarget e := fun _ hz => hz.1

/-- The local equations read in the chart `e`. -/
def chartG (i : Fin P.N) : ComplexModel n → ℂ := fun z => P.g i (e.val.symm z)

/-- The smooth part read in the chart `e`. -/
def chartH : ComplexModel n → ℝ := fun z => P.h (e.val.symm z)

theorem differentiableOn_chartG (i : Fin P.N) :
    DifferentiableOn ℂ (P.chartG e i) (P.chartDomain e) :=
  MeteredDivisorPositivity.differentiableOn_comp_chartSymm e (P.g_holo i)

theorem frequently_chartG_ne (i : Fin P.N) :
    ∀ y ∈ P.chartDomain e, ∃ᶠ z in 𝓝 y, P.chartG e i z ≠ 0 := by
  intro y hy
  rw [Filter.frequently_iff]
  intro s hs
  obtain ⟨V, hVs, hVo, hyV⟩ :=
    mem_nhds_iff.mp (inter_mem hs ((P.chartDomain e).isOpen.mem_nhds hy))
  have hVt : V ⊆ e.val.symm.source := fun z hz => (hVs hz).2.1
  have hVopen : IsOpen (e.val.symm '' V) := e.val.symm.isOpen_image_of_subset_source hVo hVt
  have hVU : e.val.symm '' V ⊆ P.U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hVs hz).2.2
  obtain ⟨_, ⟨z, hzV, rfl⟩, hm⟩ := P.g_ne i _ hVopen hVU ⟨_, mem_image_of_mem _ hyV⟩
  exact ⟨z, (hVs hzV).1, hm⟩

theorem contDiffOn_chartH : ContDiffOn ℝ ∞ (P.chartH e) (P.chartDomain e) := P.h_smooth e

/-- In the chart `e`, the weight is `Σ aᵢ log |Gᵢ|² + H` almost everywhere on the domain. -/
theorem ae_chartFunction_eq : ∀ᵐ z ∂(volume.restrict (P.chartDomain e : Set (ComplexModel n))),
    (chartFunction D.weight e z).toReal =
      ∑ i, (P.a i : ℝ) * Real.log (‖P.chartG e i z‖ ^ 2) + P.chartH e z := by
  have hall : ∀ᵐ z ∂(volume.restrict (P.chartDomain e : Set (ComplexModel n))),
      ∀ i, P.chartG e i z ≠ 0 :=
    ae_all_iff.mpr fun i => ae_ne_zero (P.chartDomain e).isOpen (P.differentiableOn_chartG e i)
      (P.frequently_chartG_ne e i)
  filter_upwards [hall, ae_restrict_mem (P.chartDomain e).isOpen.measurableSet] with z hz hzW
  have hcoe : ∀ f : Fin P.N → ℝ, ((∑ i, f i : ℝ) : EReal) = ∑ i, ((f i : ℝ) : EReal) := fun f =>
    coe_finsetSum _ f
  rw [chartFunction, P.weight_eq _ hzW.2]
  have hterm : ∀ i, ((P.a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => P.g i) (e.val.symm z) =
      (((P.a i : ℝ) * Real.log (‖P.chartG e i z‖ ^ 2) : ℝ) : EReal) := fun i => by
    rw [generatorLog_one_of_ne_zero (g := P.g i) (hz i), EReal.coe_mul]
    rfl
  simp only [hterm]
  rw [← hcoe, ← EReal.coe_add, EReal.toReal_coe]
  rfl

end LocalPresentation

end Presentation

section Global

open HolomorphicIdealSheaves GlobalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- The ratio of the Haar measure normalized by `b` to Lebesgue measure. -/
def haarFactor : ℝ≥0 := Measure.addHaarScalarFactor b.addHaar volume

theorem addHaar_eq_smul : b.addHaar = haarFactor b • volume :=
  Measure.isAddLeftInvariant_eq_smul b.addHaar volume

theorem haarFactor_pos : 0 < haarFactor b :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem chartDomain_cover (D : MeteredEffectiveQDivisor n M) (e : ComplexChart n M) :
    ∀ z ∈ chartTarget e, ∃ P : LocalPresentation D, z ∈ P.chartDomain e := by
  intro z hz
  obtain ⟨P, hP⟩ := exists_localPresentation D (e.val.symm z)
  exact ⟨P, hz, hP⟩

/-- **`ψ_E` is locally integrable** in every chart. -/
theorem chartLocallyIntegrable_weight (D : MeteredEffectiveQDivisor n M) :
    ChartLocallyIntegrable b D.weight := by
  intro e z hz
  obtain ⟨P, hzW⟩ := chartDomain_cover D e z hz
  have hF : LocallyIntegrableOn
      (fun z => ∑ i, (P.a i : ℝ) * Real.log (‖P.chartG e i z‖ ^ 2) + P.chartH e z)
      (P.chartDomain e) volume := by
    refine (locallyIntegrableOn_finsetSum _ fun i _ => ?_).add
      ((P.contDiffOn_chartH e).continuousOn.locallyIntegrableOn
        (P.chartDomain e).isOpen.measurableSet)
    simpa only [Pi.smul_def, smul_eq_mul] using
      (locallyIntegrableOn_log_normSq (P.chartDomain e).isOpen (P.differentiableOn_chartG e i)
        (P.frequently_chartG_ne e i)).smul (P.a i : ℝ)
  have hf : LocallyIntegrableOn (fun z => (chartFunction D.weight e z).toReal) (P.chartDomain e)
      b.addHaar := by
    rw [addHaar_eq_smul b]
    exact locallyIntegrableOn_smul_measure _
      (hF.congr ((P.ae_chartFunction_eq e).mono fun z hz => hz.symm))
  refine (hf z hzW).filter_mono ?_
  rw [(P.chartDomain e).isOpen.nhdsWithin_eq hzW]
  exact nhdsWithin_le_nhds

/-- `ddᶜ ψ_E` as a global current. -/
def ddCWeight (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    GlobalCurrent n M (degreeTwo hn) :=
  ⟨ddCCurrentFamily b hn D.weight (chartLocallyIntegrable_weight b D),
    fun e f η θ h => DDCOverlap.ddCCurrentFamily_overlap b hn D.weight
      (chartLocallyIntegrable_weight b D) e f η θ h⟩

/-- **The integration current `[E]` of a metered effective `ℚ`-divisor**:
the global current `ddᶜ ψ_E + Θ_E`. -/
def integrationCurrent (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    GlobalCurrent n M (degreeTwo hn) :=
  ddCWeight b hn D + smoothGlobalCurrent b (k := degreeTwo hn) D.curvature.val

/-- `ddᶜ ψ_E = [E] - Θ_E` as global currents. -/
theorem ddCWeight_eq (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    ddCWeight b hn D =
      integrationCurrent b hn D - smoothGlobalCurrent b (k := degreeTwo hn) D.curvature.val := by
  unfold integrationCurrent
  exact (add_sub_cancel_right (ddCWeight b hn D)
    (smoothGlobalCurrent b (k := degreeTwo hn) D.curvature.val)).symm

theorem coefficients_ddCWeight (hn : 0 < n) (D : MeteredEffectiveQDivisor n M)
    (e : ComplexChart n M) :
    (ddCWeight b hn D).coefficients b e =
      chartDDC b D.weight e (chartLocallyIntegrable_weight b D e) :=
  CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

theorem coefficients_smoothGlobalCurrent (hn : 0 < n) (a : SmoothRealForm n M 2)
    (e : ComplexChart n M) :
    (smoothGlobalCurrent b (k := degreeTwo hn) a).coefficients b e = smoothFormDistribution b a e :=
  CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

theorem coefficients_integrationCurrent (hn : 0 < n) (D : MeteredEffectiveQDivisor n M)
    (e : ComplexChart n M) :
    (integrationCurrent b hn D).coefficients b e =
      chartDDC b D.weight e (chartLocallyIntegrable_weight b D e) +
        smoothFormDistribution b D.curvature.val e := by
  rw [integrationCurrent, GlobalCurrent.coefficients_add, coefficients_ddCWeight,
    coefficients_smoothGlobalCurrent]

/-- On the domain of a presentation, the curvature current is `-ddᶜ h`. -/
theorem restrictForm_smoothFormDistribution_curvature {D : MeteredEffectiveQDivisor n M}
    (P : LocalPresentation D) (e : ComplexChart n M) :
    restrictForm (smoothFormDistribution b D.curvature.val e) (P.chartDomain_le e) =
      -ddC (regularDistribution b.addHaar (P.chartH e)
        ((P.contDiffOn_chartH e).continuousOn.locallyIntegrableOn
          (P.chartDomain e).isOpen.measurableSet)) := by
  ext v φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hint : Integrable (fun x => (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) x •
      D.curvature.val.coeff e x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b _ e) _
  rw [restrictForm_apply, AlternatingMap.neg_apply, neg_apply, hv,
    ddC_regularDistribution_apply_of_contDiffOn (P.contDiffOn_chartH e),
    smoothFormDistribution_apply, ← formEvaluationCLM_apply,
    ← (formEvaluationCLM _).integral_comp_comm hint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [formEvaluationCLM_apply]
  rw [congrFun (testFunction_inclusion_coe (P.chartDomain_le e) φ) x]
  by_cases hx : x ∈ P.chartDomain e
  · rw [P.curvature_eq e x hx.1 hx.2]
    change φ x * -(smoothDDC (P.chartH e) x ![v 0, v 1]) = _
    rw [mul_neg]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))]
    simp

/-- **Local description, `ddᶜ` form**: on the domain of a presentation, `[E] = ddᶜ (ψ_E - h)`. -/
theorem restrictForm_coefficients_eq_ddC (hn : 0 < n) {D : MeteredEffectiveQDivisor n M}
    (P : LocalPresentation D) (e : ComplexChart n M) :
    restrictForm ((integrationCurrent b hn D).coefficients b e) (P.chartDomain_le e) =
      ddC (restrictDistribution (regularDistribution b.addHaar
          (fun z => (chartFunction D.weight e z).toReal) (chartLocallyIntegrable_weight b D e))
          (P.chartDomain_le e) -
        regularDistribution b.addHaar (P.chartH e)
          ((P.contDiffOn_chartH e).continuousOn.locallyIntegrableOn
            (P.chartDomain e).isOpen.measurableSet)) := by
  rw [coefficients_integrationCurrent, restrictForm_add, chartDDC, restrictForm_ddC,
    restrictForm_smoothFormDistribution_curvature, ← ddCLM_apply (_ - _), map_sub, sub_eq_add_neg]
  rfl

/-- **Local description, divisor form**: on the domain of a presentation,
`[E] = c_b Σ aᵢ [div gᵢ]` (the factor `c_b` is the density of the Haar measure normalized by `b`
with respect to Lebesgue measure, which normalizes every chart coefficient). -/
theorem restrictForm_coefficients_eq_sum (hn : 0 < n) {D : MeteredEffectiveQDivisor n M}
    (P : LocalPresentation D) (e : ComplexChart n M) :
    restrictForm ((integrationCurrent b hn D).coefficients b e) (P.chartDomain_le e) =
      (haarFactor b : ℝ) • ∑ i, (P.a i : ℝ) •
        divisorCurrent (P.differentiableOn_chartG e i) (P.frequently_chartG_ne e i) := by
  rw [restrictForm_coefficients_eq_ddC, restrictDistribution_regularDistribution]
  have key : ∀ (μ : Measure (ComplexModel n)) (_ : μ = haarFactor b • volume)
      (hf : LocallyIntegrableOn (fun z => (chartFunction D.weight e z).toReal)
        (P.chartDomain e) μ)
      (hH : LocallyIntegrableOn (P.chartH e) (P.chartDomain e) μ),
      ddC (regularDistribution μ (fun z => (chartFunction D.weight e z).toReal) hf -
        regularDistribution μ (P.chartH e) hH) =
      (haarFactor b : ℝ) • ∑ i, (P.a i : ℝ) •
        divisorCurrent (P.differentiableOn_chartG e i) (P.frequently_chartG_ne e i) := by
    rintro μ rfl hf hH
    rw [← ddCLM_apply, map_sub, ddCLM_apply, ddCLM_apply,
      ddC_eq_sum_divisorCurrent_add (haarFactor b) (fun i => (P.a i : ℝ))
        (P.differentiableOn_chartG e) (P.frequently_chartG_ne e) (P.contDiffOn_chartH e)
        (P.ae_chartFunction_eq e) hf]
    abel
  exact key _ (addHaar_eq_smul b) _ _

end Global

section Properties

open HolomorphicIdealSheaves GlobalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

theorem distributionForm_sum_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} {k : ℕ} {ι : Type*} (s : Finset ι) (A : ι → DistributionForm Ω k)
    (v : Fin k → E) : (∑ i ∈ s, A i) v = ∑ i ∈ s, A i v := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, AlternatingMap.add_apply, ih]

/-- **`[E]` is closed.** -/
theorem isClosed_integrationCurrent (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    (integrationCurrent b hn D).IsClosed b := by
  intro e
  unfold LocalCurrents.IsClosed
  refine form_eq_of_forall_restrictForm_eq (fun P : LocalPresentation D => P.chartDomain e)
    (fun P => P.chartDomain_le e) (chartDomain_cover D e) fun P => ?_
  rw [restrictForm_exteriorDerivative, restrictForm_coefficients_eq_ddC]
  exact (Pending.LocalCurrents.ddC_isClosed _).trans (by ext v φ; rfl)

/-- **`[E]` is of type `(1,1)`.** -/
theorem isTypeOneOne_integrationCurrent (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    (integrationCurrent b hn D).IsTypeOneOne b hn := by
  intro e v w
  refine eq_of_forall_restrict_eq (fun P : LocalPresentation D => P.chartDomain e)
    (fun P => P.chartDomain_le e) (chartDomain_cover D e) fun P => ?_
  rw [← restrictForm_apply', ← restrictForm_apply', restrictForm_coefficients_eq_ddC]
  exact Pending.LocalCurrents.ddC_isOneOne _ v w

/-- `[E]` is positive on every constant complex line. -/
theorem constantDirectionPositive_integrationCurrent (hn : 0 < n)
    (D : MeteredEffectiveQDivisor n M) (e : ComplexChart n M) :
    ConstantDirectionPositive ((integrationCurrent b hn D).coefficients b e) := by
  intro v
  refine positiveDistribution_of_forall_restrict (fun P : LocalPresentation D => P.chartDomain e)
    (fun P => P.chartDomain_le e) (chartDomain_cover D e) fun P => ?_
  rw [← restrictForm_apply', restrictForm_coefficients_eq_sum, AlternatingMap.smul_apply,
    distributionForm_sum_apply]
  refine PositiveDistribution.smul (fun φ hφ => ?_) (haarFactor b).coe_nonneg
  rw [sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [AlternatingMap.smul_apply, smul_apply, smul_eq_mul, divisorCurrent_apply]
  exact mul_nonneg (by exact_mod_cast P.a_nonneg i)
    (integral_nonneg fun x => mul_nonneg (hφ x) (divisorDensity_apply_I_nonneg _ _))

/-- **`[E]` is positive** (on compactly supported vector squares). -/
theorem isSquarePositive_integrationCurrent (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    (integrationCurrent b hn D).IsSquarePositive b hn := fun e =>
  Pending.LocalCurrents.squarePositive_of_constantDirectionPositive _
    (isTypeOneOne_integrationCurrent b hn D e)
    (constantDirectionPositive_integrationCurrent b hn D e)

/-- **The Lelong--Poincaré equation for a metered effective `ℚ`-divisor** on a complex manifold.
`ψ_E` is locally integrable, and the global current `[E]` is closed, of type `(1,1)`, positive,
equal on the domain of every local presentation `ψ_E = Σ aᵢ log |gᵢ|² + h` to `Σ aᵢ [div gᵢ]`
(times the normalization `c_b` of chart coefficients), and

  `ddᶜ ψ_E = [E] - Θ_E`. -/
theorem lelongPoincare (hn : 0 < n) (D : MeteredEffectiveQDivisor n M) :
    ChartLocallyIntegrable b D.weight ∧
    ddCWeight b hn D =
      integrationCurrent b hn D - smoothGlobalCurrent b (k := degreeTwo hn) D.curvature.val ∧
    (integrationCurrent b hn D).IsClosed b ∧ (integrationCurrent b hn D).IsTypeOneOne b hn ∧
    (integrationCurrent b hn D).IsSquarePositive b hn ∧
    ∀ (P : LocalPresentation D) (e : ComplexChart n M),
      restrictForm ((integrationCurrent b hn D).coefficients b e) (P.chartDomain_le e) =
        (haarFactor b : ℝ) • ∑ i, (P.a i : ℝ) •
          divisorCurrent (P.differentiableOn_chartG e i) (P.frequently_chartG_ne e i) :=
  ⟨chartLocallyIntegrable_weight b D, ddCWeight_eq b hn D, isClosed_integrationCurrent b hn D,
    isTypeOneOne_integrationCurrent b hn D, isSquarePositive_integrationCurrent b hn D,
    fun P e => restrictForm_coefficients_eq_sum b hn P e⟩

end Properties

universe u

section Modification

open HolomorphicIdealSheaves GlobalCurrents PositiveClasses BlowupSequences ExceptionalMetric

variable {n : ℕ}
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- A global current is determined by its chart coefficients. -/
theorem globalCurrent_ext {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {k : CurrentDegree n} {T S : GlobalCurrent n M k}
    (h : ∀ e, T.coefficients b e = S.coefficients b e) : T = S := by
  apply Subtype.ext
  funext e
  have hT := CurrentPairing.toLocalCurrent_fromLocalCurrent b k (T.inChart e)
  have hS := CurrentPairing.toLocalCurrent_fromLocalCurrent b k (S.inChart e)
  change T.inChart e = S.inChart e
  rw [← hT, ← hS]
  exact congrArg _ (h e)

theorem coefficients_sub {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {k : CurrentDegree n} (T S : GlobalCurrent n M k)
    (e : ComplexChart n M) :
    (T - S).coefficients b e = T.coefficients b e - S.coefficients b e := by
  ext v φ
  rfl

theorem smoothFormDistribution_sub {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A B : ClosedRealOneOneForm n M) (e : ComplexChart n M) :
    smoothFormDistribution b (A - B).val e =
      smoothFormDistribution b A.val e - smoothFormDistribution b B.val e := by
  ext v φ
  have hA : Integrable (fun x => φ x • A.val.coeff e x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b _ e) _
  have hB : Integrable (fun x => φ x • B.val.coeff e x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b _ e) _
  have hcoeff : ∀ x, (A - B).val.coeff e x = A.val.coeff e x - B.val.coeff e x := fun x => by
    rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ← sub_eq_add_neg]
  rw [AlternatingMap.sub_apply, sub_apply, smoothFormDistribution_apply,
    smoothFormDistribution_apply, smoothFormDistribution_apply]
  simp only [hcoeff, smul_sub]
  rw [integral_sub hA hB]
  rfl

/-- **The exceptional correction and its class** (the last assertion of `bou:divisor-class`):
for a modification `π : Y → X` of a compact Kähler manifold there is an effective metered
`ℚ`-divisor `F`, supported in the exceptional locus, such that `ω̃ = π^* ω - Θ_F` is Kähler and,
as currents, `ω̃ = π^* ω - [F] + ddᶜ ψ_F`: the class of `ω̃` is `π^*{ω} - {F}`. -/
theorem exists_exceptional_correction_class {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace X]
    (omega : KahlerBackground n X) (π : Y → X) (hπ : IsBlowupSequence n X Y π) (hn : 0 < n) :
    ∃ F : MeteredEffectiveQDivisor n Y,
      F.support ⊆ exceptionalLocus n π ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - F.curvature).val.IsKahler ∧
      smoothGlobalCurrent b (k := degreeTwo hn)
          (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - F.curvature).val =
        smoothGlobalCurrent b (k := degreeTwo hn)
            (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form).val -
          integrationCurrent b hn F + ddCWeight b hn F := by
  obtain ⟨F, hsupp, hK, -⟩ := exists_exceptionalMetric omega π hπ
  refine ⟨F, hsupp, hK, ?_⟩
  rw [ddCWeight_eq b hn F]
  apply globalCurrent_ext b
  intro e
  rw [coefficients_smoothGlobalCurrent, smoothFormDistribution_sub, GlobalCurrent.coefficients_add,
    coefficients_sub, coefficients_sub, coefficients_smoothGlobalCurrent,
    coefficients_smoothGlobalCurrent]
  abel

end Modification

end SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
