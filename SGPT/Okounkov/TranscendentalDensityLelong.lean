import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Okounkov.PotentialFlagValuationIndependence
import SGPT.Foundations.Analysis.Pending.IdentityRegularDivisorialGeometry
import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

/-!
# Demailly's Lelong number estimate for the gentle approximations

Source: blueprint node `tok:sing-decrease`, part (c) (DRWNXZ Theorem 2.7; Demailly, *Regularization
of closed positive currents and intersection theory*, 1992, Proposition 3.1; Xia, *Foundations of
pluripotential theory*, `thm:quantitative-lower-bound-regularization`): the gentle approximations
`φ_j` of type `(2^{-j}, 𝓘(2^j φ))` of `tok:sing-decrease` (a) satisfy `ν(φ_j) ≤ ν(φ)` and
`ν(φ) - O(2^{-j}) ≤ ν(φ_j)`, so the generic Lelong numbers converge.

## Formal statement

The estimate is packaged **along smooth hypersurfaces** `E` (generic Lelong numbers
`ν(u, E) = inf_{x ∈ E} ν(u, x)`), which is the form its consumer uses (`tok:vol-integral`: the
generic Lelong numbers along `Y₁` of the gentle approximations converge). For any potential `v`
of type `(1/q, 𝓘(qφ))` with `φ ≤ v`:

* `divisorialLelongNumber_bounds_of_type` (TN normalization `ν(log ‖z‖, 0) = 1`):
  `ν(φ, E) - 2/q ≤ ν(v, E) ≤ ν(φ, E)`;
* `sourceGenericLelongNumber_bounds_of_type` (the book's normalization `ν(log |z|², 0) = 1`, used
  by the flag valuation): `ν(φ, E) - 1/q ≤ ν(v, E) ≤ ν(φ, E)`;
* `flagValuation_first_bounds_of_type`: the first coordinate of the flag valuation,
  `ν₁(φ) - 1/q ≤ ν₁(v) ≤ ν₁(φ)`;
* `exists_gentle_approximation_lelong`: the gentle approximations of a Kähler current of
  `tok:sing-decrease` (a) together with these bounds for `q = 2^{j+1}` and the convergence
  `ν₁(φ_j) → ν₁(φ)`.

The lower bound is TN's `DemaillyApproximantDivisorialLelong.divisorialLelongNumber_comp_sub_le`
(the valuative estimate for Demailly's approximants, with the identity map, whose log discrepancy
along a smooth hypersurface is `1`:
`IdentityRegularDivisorialGeometry.logDiscrepancyLE_id_of_regularAtDim`).

Deviation from the blueprint wording: the pointwise bound `ν(φ, x) - n 2^{-j} ≤ ν(φ_j, x)` at every
point `x` is not formalized; the hypersurface bound (with the better constant `2^{-j}` in the
book's normalization) is what the route consumes.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalDensity

open Set Filter
open scoped Topology ENNReal NNReal Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.Pending.IdentityRegularDivisorialGeometry
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH SGPT.Okounkov.TranscendentalCore

section Manifold

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **Demailly's estimate along a smooth hypersurface** (`tok:sing-decrease` (c), TN
normalization): if `v` has analytic singularities of type `(1/q, 𝓘(qφ))` and `φ ≤ v`, then
`ν(φ, E) - 2/q ≤ ν(v, E) ≤ ν(φ, E)` for every smooth hypersurface `E`. -/
theorem divisorialLelongNumber_bounds_of_type {θ : ClosedRealOneOneForm (m + 1) X}
    {φ v : X → EReal} (hφ : IsThetaPshPotential θ.val φ) {q : ℕ} (hq : 0 < q)
    (hv : HasAnalyticSingularitiesOfType (n := m + 1) v ((q : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) (q : ℝ) φ))
    (hle : ∀ x, φ x ≤ v x) {E : Set X} (hE : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m) :
    divisorialLelongNumber m φ E - ENNReal.ofReal (2 / q) ≤ divisorialLelongNumber m v E ∧
      divisorialLelongNumber m v E ≤ divisorialLelongNumber m φ E := by
  have hinj : IsInjectiveOffNull m (id : X → X) := by
    refine ⟨∅, fun y => ?_, Function.injective_id.injOn⟩
    simp
  have h := divisorialLelongNumber_comp_sub_le (π := (id : X → X)) contMDiff_id hinj hφ.1 hq hv
    (fun x hx => logDiscrepancyLE_id_of_regularAtDim (hE x hx))
  have h2 : (2 : ℝ) * ((1 : ℕ) : ℝ) / (q : ℝ) = 2 / q := by norm_num
  rw [h2] at h
  exact ⟨h, divisorialLelongNumber_comp_le_of_le (id : X → X) hle E⟩

omit [IsComplexManifold (m + 1) X] in
/-- `ν(u, E) = 2 ν_src(u, E)`: the divisorial Lelong number (TN normalization) is twice the
source generic Lelong number (book normalization). -/
theorem divisorialLelongNumber_eq_two_mul_source (u : X → EReal) (E : Set X) :
    divisorialLelongNumber m u E =
      2 * sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → X) u := by
  rw [← nativeGeneric_eq_two_mul_source (Nat.succ_ne_zero m), divisorialLelongNumber, iInf_subtype']

/-- **Demailly's estimate along a smooth hypersurface** (`tok:sing-decrease` (c), the book's
normalization `ν(log |z|², 0) = 1`): `ν(φ, E) - 1/q ≤ ν(v, E) ≤ ν(φ, E)`. -/
theorem sourceGenericLelongNumber_bounds_of_type {θ : ClosedRealOneOneForm (m + 1) X}
    {φ v : X → EReal} (hφ : IsThetaPshPotential θ.val φ) {q : ℕ} (hq : 0 < q)
    (hv : HasAnalyticSingularitiesOfType (n := m + 1) v ((q : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) (q : ℝ) φ))
    (hle : ∀ x, φ x ≤ v x) {E : Set X} (hE : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → X) φ - ENNReal.ofReal (1 / q) ≤
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → X) v ∧
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → X) v ≤
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → X) φ := by
  obtain ⟨hlo, hup⟩ := divisorialLelongNumber_bounds_of_type hφ hq hv hle hE
  rw [divisorialLelongNumber_eq_two_mul_source, divisorialLelongNumber_eq_two_mul_source] at hlo hup
  have h2 : ENNReal.ofReal (2 / q) = 2 * ENNReal.ofReal (1 / q) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [h2, ← ENNReal.mul_sub (fun _ _ => by simp)] at hlo
  exact ⟨(ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp hlo,
    (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp hup⟩

end Manifold

section Flag

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **The first coordinate of the valuation** (`tok:sing-decrease` (c) along `Y₁`): if `v` has
type `(1/q, 𝓘(qφ))`, `φ ≤ v` and both are quasi-psh, then `ν₁(φ) - 1/q ≤ ν₁(v) ≤ ν₁(φ)`. -/
theorem flagValuation_first_bounds_of_type {θ σ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ v : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hvpsh : IsThetaPshPotential σ.val v) {q : ℕ} (hq : 0 < q)
    (hv : HasAnalyticSingularitiesOfType (n := m + 1) v ((q : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) (q : ℝ) φ))
    (hle : ∀ x, φ x ≤ v x) :
    flagValuation F φ 0 - 1 / q ≤ flagValuation F v 0 ∧
      flagValuation F v 0 ≤ flagValuation F φ 0 := by
  obtain ⟨hlo, hup⟩ := sourceGenericLelongNumber_bounds_of_type hφ hq hv hle F.firstDivisor.2.2
  rw [← potentialFlagValuation_first F hφ, ← potentialFlagValuation_first F hvpsh] at hlo hup
  rw [flagValuation_eq hφ, flagValuation_eq hvpsh]
  set a := potentialFlagValuation F hφ 0
  set b := potentialFlagValuation F hvpsh 0
  refine ⟨?_, NNReal.coe_le_coe.mpr (ENNReal.coe_le_coe.mp hup)⟩
  have h1 : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) + ENNReal.ofReal (1 / q) := tsub_le_iff_right.mp hlo
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ENNReal.coe_toReal,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)] at h2
  show (a : ℝ) - 1 / q ≤ b
  linarith

/-- **`tok:sing-decrease` (a) and (c)**: if `θ + dd^c φ ≥ κ`, there are gentle approximations
`φ_j` of type `(2^{-(j+1)}, 𝓘(2^{j+1}φ))` decreasing to `φ`, with `θ + dd^c φ_j ≥ κ/4` for large
`j`, such that along every smooth hypersurface `E`
`ν(φ, E) - 2^{-(j+1)} ≤ ν(φ_j, E) ≤ ν(φ, E)` (book normalization), in particular
`ν₁(φ) - 2^{-(j+1)} ≤ ν₁(φ_j) ≤ ν₁(φ)` and `ν₁(φ_j) → ν₁(φ)` for the first coordinate of the
flag valuation. -/
theorem exists_gentle_approximation_lelong {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {κ : KahlerBackground (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential (θ - κ.form).val φ) :
    ∃ v : ℕ → F.carrier → EReal, DecreasesPointwiseTo v φ ∧
      (∀ j, SourceGentleAnalyticSingularities (v j) (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := m + 1) ((2 ^ (j + 1) : ℕ) : ℝ) φ)) ∧
      (∃ j₀ : ℕ, ∀ j, j₀ ≤ j → IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val (v j)) ∧
      (∀ (E : Set F.carrier), (∀ x ∈ E, RegularAtDim (n := m + 1) E x m) → ∀ j,
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → F.carrier) φ -
            ENNReal.ofReal (1 / ((2 ^ (j + 1) : ℕ) : ℝ)) ≤
          sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → F.carrier) (v j) ∧
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → F.carrier) (v j) ≤
          sourceGenericLelongNumber (n := m + 1) (Subtype.val : E → F.carrier) φ) ∧
      (∀ j, flagValuation F φ 0 - 1 / ((2 ^ (j + 1) : ℕ) : ℝ) ≤ flagValuation F (v j) 0 ∧
        flagValuation F (v j) 0 ≤ flagValuation F φ 0) ∧
      Tendsto (fun j => flagValuation F (v j) 0) atTop (𝓝 (flagValuation F φ 0)) := by
  obtain ⟨v, hdec, hgentle, hj₀⟩ :=
    TranscendentalBody.exists_gentle_approximation_of_kahlerCurrent hφ
  have hle : ∀ j x, φ x ≤ v j x := fun j x => (hdec.1 x).le_of_tendsto (hdec.2 x) j
  have hq : ∀ j : ℕ, 0 < 2 ^ (j + 1) := fun j => by positivity
  have hbounds : ∀ j, flagValuation F φ 0 - 1 / ((2 ^ (j + 1) : ℕ) : ℝ) ≤ flagValuation F (v j) 0 ∧
      flagValuation F (v j) 0 ≤ flagValuation F φ 0 := fun j =>
    flagValuation_first_bounds_of_type F hφ (hgentle j).1.choose_spec (hq j) (hgentle j).2.2.1
      (hle j)
  refine ⟨v, hdec, hgentle, hj₀,
    fun E hE j => sourceGenericLelongNumber_bounds_of_type hφ (hq j) (hgentle j).2.2.1 (hle j) hE,
    hbounds, ?_⟩
  have hlim : Tendsto (fun j : ℕ => flagValuation F φ 0 - 1 / ((2 ^ (j + 1) : ℕ) : ℝ)) atTop
      (𝓝 (flagValuation F φ 0)) := by
    have h : Tendsto (fun j : ℕ => 1 / ((2 ^ (j + 1) : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ => ((2 ^ (j + 1) : ℕ) : ℝ)) atTop atTop := by
        have := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
          (tendsto_add_atTop_nat 1)
        refine this.congr fun j => ?_
        simp
      have h2 := tendsto_inv_atTop_zero.comp h1
      simp only [Function.comp_def] at h2
      simpa only [one_div] using h2
    simpa using tendsto_const_nhds.sub h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun j => (hbounds j).1) (fun j => (hbounds j).2)

end Flag

end SGPT.Okounkov.TranscendentalDensity
