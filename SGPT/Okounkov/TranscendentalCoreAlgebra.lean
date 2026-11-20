import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Foundations.Analysis.Pending.IdealWeightPowers
import SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

/-!
# The algebra of analytic singularities

Source: blueprint node `tok:analytic-algebra`, i.e. DRWNXZ Remark 2.6 and the convexity
statement before Lemma 3.1: if `T ∈ 𝒜(ξ)`, `S ∈ 𝒜(ξ')` and `a, b ∈ ℚ_{≥ 0}`, then
`aT + bS ∈ 𝒜(aξ + bξ')`, and the same holds for `𝒜ᵍ`; if `π : Z → X` is a proper bimeromorphic
holomorphic map (an analytic modification), then `π^*T ∈ 𝒜(π^*ξ)` (and `π^*T ∈ 𝒜ᵍ(π^*ξ)` for
`T ∈ 𝒜ᵍ(ξ)`).

For global types: writing `c = p/N`, a potential of type `(c, 𝓘)` has type `(1/N, 𝓘^p)`
(`hasAnalyticSingularitiesOfType_rescale`), and potentials of types `(1/N, 𝓘)`, `(1/N, 𝓙)` add
to a potential of type `(1/N, 𝓘𝓙)` (TN's `hasAnalyticSingularitiesOfType_mul`).

## Main results

* `add_smul_mem_analyticCurrents`, `add_smul_mem_globalAnalyticCurrents`: `aT + bS`.
* `comp_mem_analyticCurrents`, `comp_mem_globalAnalyticCurrents`: pullbacks.
* `globalAnalyticCurrents_subset_analyticCurrents`: `𝒜ᵍ(ξ) ⊆ 𝒜(ξ)`.
* `hasAnalyticSingularities_add`, `hasAnalyticSingularities_nonneg_rat_smul` and the local
  versions `hasManifoldAnalyticSingularityType_add`,
  `hasManifoldAnalyticSingularityType_nonneg_rat_smul`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending.IdealWeightPowers

/-! ### Extended-real arithmetic -/

/-- `p • x = p x` in `EReal`, for natural `p`. -/
theorem ereal_nsmul_eq_mul (p : ℕ) (x : EReal) : p • x = ((p : ℝ) : EReal) * x := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [succ_nsmul, ih, Nat.cast_succ, EReal.coe_add, EReal.coe_one,
        EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr (Nat.cast_nonneg p)) zero_le_one,
        one_mul]

/-- Two positive rationals have a common denominator. -/
theorem exists_common_denominator {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q') :
    ∃ N p p' : ℕ, 0 < N ∧ 0 < p ∧ 0 < p' ∧ q = (p : ℚ) / N ∧ q' = (p' : ℚ) / N := by
  have hnum : ((q.num.toNat : ℕ) : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq.le)
  have hnum' : ((q'.num.toNat : ℕ) : ℚ) = q'.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq'.le)
  have hd : (q.den : ℚ) ≠ 0 := by positivity
  have hd' : (q'.den : ℚ) ≠ 0 := by positivity
  refine ⟨q.den * q'.den, q.num.toNat * q'.den, q'.num.toNat * q.den, by positivity,
    Nat.mul_pos (Int.lt_toNat.mpr (by exact_mod_cast Rat.num_pos.mpr hq)) q'.den_pos,
    Nat.mul_pos (Int.lt_toNat.mpr (by exact_mod_cast Rat.num_pos.mpr hq')) q.den_pos, ?_, ?_⟩
  · push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den q]
    field_simp
  · push_cast
    rw [hnum']
    conv_lhs => rw [← Rat.num_div_den q']
    field_simp

/-! ### Local analytic singularities -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The constant `0` has analytic singularity type (`0 = log |1|² + 0`). -/
theorem hasAnalyticSingularityTypeAt_zero (z : E) :
    HasAnalyticSingularityTypeAt (fun _ : E => (0 : EReal)) z := by
  refine ⟨1, 1, fun _ _ => 1, by norm_num,
    ⟨univ, isOpen_univ, mem_univ z, fun _ => differentiableOn_const 1⟩, fun _ => 0,
    ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩, Eventually.of_forall fun y => ?_⟩
  have hlog : generatorLog (fun _ : Fin 1 => fun _ : E => (1 : ℂ)) y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp
  simp [hlog]

/-- `aT` for `a ∈ ℚ_{≥ 0}`, locally. -/
theorem hasAnalyticSingularityTypeAt_nonneg_rat_smul {u : E → EReal} {z : E}
    (hu : HasAnalyticSingularityTypeAt u z) {r : ℚ} (hr : 0 ≤ r) :
    HasAnalyticSingularityTypeAt (fun y => ((r : ℝ) : EReal) * u y) z := by
  rcases hr.lt_or_eq with hr | rfl
  · exact Pending.QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul hu hr
  · simpa using hasAnalyticSingularityTypeAt_zero z

end Local

section Manifold

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Sums of potentials with analytic singularities have analytic singularities. -/
theorem hasManifoldAnalyticSingularityType_add {φ ψ : M → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := n) φ)
    (hψ : HasManifoldAnalyticSingularityType (n := n) ψ) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => φ x + ψ x) :=
  fun e z hz => Pending.RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add
    (hφ e z hz) (hψ e z hz)

omit [IsComplexManifold n M] in
/-- Nonnegative rational multiples of potentials with analytic singularities have analytic
singularities. -/
theorem hasManifoldAnalyticSingularityType_nonneg_rat_smul {φ : M → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := n) φ) {r : ℚ} (hr : 0 ≤ r) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => ((r : ℝ) : EReal) * φ x) :=
  fun e z hz => hasAnalyticSingularityTypeAt_nonneg_rat_smul (hφ e z hz) hr

/-- `aθ + bθ'`-psh: nonnegative real multiples of `θ`-psh potentials. -/
theorem isThetaPshPotential_nonneg_smul {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {c : ℝ} (hc : 0 ≤ c) :
    IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * φ x) := by
  rcases hc.lt_or_eq with hc | rfl
  · exact Pending.RestrictedApproximantComparison.isThetaPshPotential_smul hφ hc
  · have h0 : (0 : ℝ) • θ = 0 := zero_smul ℝ θ
    have hfun : (fun x => ((0 : ℝ) : EReal) * φ x) = fun _ => (0 : EReal) := by
      funext x
      simp
    rw [h0, hfun]
    exact (Pending.LocalPotentials.isThetaPshPotential_zero_iff 0).mpr (by intro e z hz w; simp)

/-- Source `tok:analytic-algebra` for `𝒜`: if `T ∈ 𝒜(ξ)`, `S ∈ 𝒜(ξ')` and `a, b ∈ ℚ_{≥ 0}`, then
`aT + bS ∈ 𝒜(aξ + bξ')`. -/
theorem add_smul_mem_analyticCurrents {θ θ' : ClosedRealOneOneForm n M} {φ ψ : M → EReal}
    (hφ : φ ∈ analyticCurrents θ) (hψ : ψ ∈ analyticCurrents θ') {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) ∈
      analyticCurrents ((a : ℝ) • θ + (b : ℝ) • θ') :=
  ⟨isThetaPshPotential_add_from_positive_sum
      (isThetaPshPotential_nonneg_smul hφ.1 (by exact_mod_cast ha))
      (isThetaPshPotential_nonneg_smul hψ.1 (by exact_mod_cast hb)),
    hasManifoldAnalyticSingularityType_add
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul hφ.2 ha)
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul hψ.2 hb)⟩

/-- Source `tok:analytic-algebra` for `𝒜`: `π^*T ∈ 𝒜(π^*ξ)` for an analytic modification
`π : Z → X` (a proper bimeromorphic holomorphic map). -/
theorem comp_mem_analyticCurrents {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → M}
    (hπ : Pending.AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {θ : ClosedRealOneOneForm n M} {φ : M → EReal} (hφ : φ ∈ analyticCurrents θ) :
    (fun y => φ (π y)) ∈ analyticCurrents (ClosedRealOneOneForm.pullback hπ.1 θ) :=
  ⟨Pending.AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ θ hφ.1,
    Pending.AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hπ.1 hφ.2⟩

/-! ### Global types -/

/-- `𝒜ᵍ(ξ) ⊆ 𝒜(ξ)`: a global type `(c, 𝓘)` gives the chartwise analytic type. -/
theorem globalAnalyticCurrents_subset_analyticCurrents (θ : ClosedRealOneOneForm n M) :
    globalAnalyticCurrents θ ⊆ analyticCurrents θ := by
  rintro φ ⟨hφ, c, 𝔞, htype⟩
  exact ⟨hφ, htype.hasManifoldAnalyticSingularityType⟩

/-- `𝒢(ξ) ⊆ 𝒜(ξ)`. -/
theorem gentleCurrents_subset_analyticCurrents (θ : ClosedRealOneOneForm n M) :
    gentleCurrents θ ⊆ analyticCurrents θ :=
  gentleCurrents_subset_globalAnalyticCurrents.trans
    (globalAnalyticCurrents_subset_analyticCurrents θ)

omit [IsComplexManifold n M] in
/-- A positive rational multiple of a potential of type `(c, 𝔞)` has type `(rc, 𝔞)`. -/
theorem hasAnalyticSingularitiesOfType_pos_rat_smul {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (h : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) {r : ℚ}
    (hr : 0 < r) :
    HasAnalyticSingularitiesOfType (n := n) (fun y => ((r : ℝ) : EReal) * φ y) (r * c) 𝔞 := by
  obtain ⟨hc, hcoh, hloc⟩ := h
  refine ⟨mul_pos hr hc, hcoh, fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hg, hspan, R, C, hRC, heq⟩ := hloc x
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨U, hU, hxU, N, g, hg, hspan, fun y => r * R y, r * C, fun y hy => ?_,
    fun y hy => ?_⟩
  · rw [abs_mul, abs_of_pos hrR]
    exact mul_le_mul_of_nonneg_left (hRC y hy) hrR.le
  · change ((r : ℝ) : EReal) * φ y = _
    rw [heq y hy, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hrR.le)
      (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, Rat.cast_mul, EReal.coe_mul r (R y)]

omit [IsComplexManifold n M] in
/-- **Rescaling a global type**: a potential of type `(p/N, 𝔞)` has type `(1/N, 𝔞^p)`. -/
theorem hasAnalyticSingularitiesOfType_rescale {φ : M → EReal} {p N : ℕ} (hp : 0 < p)
    (hN : 0 < N) {𝔞 : GermIdeal n M}
    (h : HasAnalyticSingularitiesOfType (n := n) φ ((p : ℚ) / N) 𝔞) :
    HasAnalyticSingularitiesOfType (n := n) φ ((N : ℚ)⁻¹) (idealPow 𝔞 p) := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hNQ : (N : ℚ) ≠ 0 := by positivity
  have h1 := hasAnalyticSingularitiesOfType_pos_rat_smul h (inv_pos.mpr hpQ)
  have hc : (p : ℚ)⁻¹ * ((p : ℚ) / N) = (N : ℚ)⁻¹ := by field_simp
  rw [hc] at h1
  have h2 := hasAnalyticSingularitiesOfType_pow h1 p
  have hfun : (fun y => p • (((((p : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * φ y)) = φ := by
    funext y
    rw [ereal_nsmul_eq_mul, ← mul_assoc, ← EReal.coe_mul]
    have : (p : ℝ) * (((p : ℚ)⁻¹ : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, EReal.coe_one, one_mul]
  rw [hfun] at h2
  exact h2

omit [IsComplexManifold n M] in
/-- Sums of potentials with analytic singularities of global types have analytic
singularities of a global type. -/
theorem hasAnalyticSingularities_add {φ ψ : M → EReal}
    (hφ : HasAnalyticSingularities (n := n) φ) (hψ : HasAnalyticSingularities (n := n) ψ) :
    HasAnalyticSingularities (n := n) (fun x => φ x + ψ x) := by
  obtain ⟨c, 𝔞, hc⟩ := hφ
  obtain ⟨c', 𝔟, hc'⟩ := hψ
  obtain ⟨N, p, p', hN, hp, hp', rfl, rfl⟩ := exists_common_denominator hc.1 hc'.1
  exact ⟨(N : ℚ)⁻¹, (idealPow 𝔞 p).mul (idealPow 𝔟 p'),
    hasAnalyticSingularitiesOfType_mul (hasAnalyticSingularitiesOfType_rescale hp hN hc)
      (hasAnalyticSingularitiesOfType_rescale hp' hN hc')⟩

omit [IsComplexManifold n M] in
/-- Nonnegative rational multiples of potentials with analytic singularities of a global type
have analytic singularities of a global type. -/
theorem hasAnalyticSingularities_nonneg_rat_smul {φ : M → EReal}
    (hφ : HasAnalyticSingularities (n := n) φ) {r : ℚ} (hr : 0 ≤ r) :
    HasAnalyticSingularities (n := n) (fun x => ((r : ℝ) : EReal) * φ x) := by
  obtain ⟨c, 𝔞, hc⟩ := hφ
  rcases hr.lt_or_eq with hr | rfl
  · exact ⟨r * c, 𝔞, hasAnalyticSingularitiesOfType_pos_rat_smul hc hr⟩
  · refine ⟨1, unitIdeal n M, ?_⟩
    have hfun : (fun x => (((0 : ℚ) : ℝ) : EReal) * φ x) = fun _ => (0 : EReal) := by
      funext x
      simp
    rw [hfun]
    exact hasAnalyticSingularitiesOfType_unitIdeal one_pos

/-- Source `tok:analytic-algebra` for `𝒜ᵍ`: if `T ∈ 𝒜ᵍ(ξ)`, `S ∈ 𝒜ᵍ(ξ')` and `a, b ∈ ℚ_{≥ 0}`,
then `aT + bS ∈ 𝒜ᵍ(aξ + bξ')`. -/
theorem add_smul_mem_globalAnalyticCurrents {θ θ' : ClosedRealOneOneForm n M}
    {φ ψ : M → EReal} (hφ : φ ∈ globalAnalyticCurrents θ) (hψ : ψ ∈ globalAnalyticCurrents θ')
    {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) ∈
      globalAnalyticCurrents ((a : ℝ) • θ + (b : ℝ) • θ') :=
  ⟨isThetaPshPotential_add_from_positive_sum
      (isThetaPshPotential_nonneg_smul hφ.1 (by exact_mod_cast ha))
      (isThetaPshPotential_nonneg_smul hψ.1 (by exact_mod_cast hb)),
    hasAnalyticSingularities_add (hasAnalyticSingularities_nonneg_rat_smul hφ.2 ha)
      (hasAnalyticSingularities_nonneg_rat_smul hψ.2 hb)⟩

/-- Source `tok:analytic-algebra` for `𝒜ᵍ`: `π^*T ∈ 𝒜ᵍ(π^*ξ)` for an analytic modification
`π : Z → X`; a potential of type `(c, 𝓘)` pulls back to one of type `(c, 𝓘 𝒪_Z)`. -/
theorem comp_mem_globalAnalyticCurrents {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → M}
    (hπ : Pending.AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {θ : ClosedRealOneOneForm n M} {φ : M → EReal} (hφ : φ ∈ globalAnalyticCurrents θ) :
    (fun y => φ (π y)) ∈ globalAnalyticCurrents (ClosedRealOneOneForm.pullback hπ.1 θ) := by
  obtain ⟨hpsh, c, 𝔞, htype⟩ := hφ
  exact ⟨Pending.AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ θ hpsh, c, GermIdeal.pullback (m := n) π 𝔞,
    Pending.AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hπ.1 htype⟩

end Manifold

end SGPT.Okounkov.TranscendentalCore
