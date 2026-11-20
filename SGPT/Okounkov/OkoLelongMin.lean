import SGPT.Okounkov.AlgebraicDXBody
import SGPT.Okounkov.ValuativeFirstCoordinate
import SGPT.Okounkov.AlgebraicBodyBound

/-!
# Lelong numbers from partial Okounkov bodies: first-coordinate minima

Source: chapter *The theory of Okounkov bodies*, subsection *Recover Lelong numbers from partial
Okounkov bodies*: `thm:nuOk` (`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁` for an admissible flag with
`Y₁ = E`) and `cor:numin` (`ν(V_θ, E) = lim_k k⁻¹ ord_E H⁰(X, L^k)`).

The source states both results for the *algebraic* partial Okounkov body
`Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` (`def:Okounkov:L687`), whose existence needs `thm:Gammaasg`
(not formalized: it needs the lower bound of `thm:DXmain1`). This file proves the parts that do
not depend on it.

## Transcendental form of `thm:nuOk`

For a smooth flag `Y•` on a connected compact Kähler manifold and `T = θ + dd^c φ` with
`φ ∈ PSH(X, θ)`, the partial Okounkov body `Δ_{Y•}(T)` of `def:generalPOB` satisfies

`min_{x ∈ Δ_{Y•}(T)} x₁ = ν(φ, Y₁)`

(`isLeast_firstCoordinate_generalPartialBody`), with `ν(φ, Y₁)` the generic Lelong number of `φ`
along `Y₁` (`sourceGenericLelongNumber`, finite: `sourceGenericLelongNumber_firstFlag_ne_top`).
This is the identity of `thm:nuOk` for the transcendental body, which the source identifies with
`Δ_{Y•}(L, h)` in `cor:transalgPOB`; it is a repackaging of
`SGPT.Okounkov.Valuative.isLeast_image_zero_generalPartialBody` with the first value of the
flag valuation read as a generic Lelong number.

As a consequence (`sourceGenericLelongNumber_le_of_generalPartialBody_subset`), an inclusion
`Δ_{Y•}(θ + dd^c φ) ⊆ Δ_{Y•}(σ + dd^c ψ)` gives `ν(ψ, Y₁) ≤ ν(φ, Y₁)`: the first step of the proof of
`cor:Deltacontimplyvarphi`, for transcendental bodies.

## The algebraic polytopes, lower bound of `thm:nuOk`

For an integral smooth projective complex scheme `X` with a smooth flag `Y•` of its analytic
manifold, a line bundle `L` with smooth metric `h₀` (`θ = c₁(L, h₀)`) and `φ ∈ PSH(X, θ)`:

* `eventually_lt_sectionVector_zero`: for every `η > 0` and all `k ≫ 0`, every nonzero
  `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` has `ord_{Y₁}(s) = ν(s)₁ > k (ν(φ, Y₁) - η)`;
* `eventually_lt_firstCoordinate_multiplierDegreePolytope`: for all `k ≫ 0`, every
  `x ∈ Δ_k(θ, φ)` (`def:Okounkov:L484`) has `x₁ > ν(φ, Y₁) - η`. Hence every Hausdorff limit of
  the polytopes `Δ_k(θ, φ)` has first-coordinate minimum `≥ ν(φ, Y₁)`; this is the inequality
  `≥` of `thm:nuOk` through the polytope description of `thm:HCP`.

## The asymptotic order of vanishing, `cor:numin`

For `E = Y₁` (the first member of a smooth flag), `firstFlagOrder k = ord_E H⁰(X, L^k)`, the
minimal first flag coordinate `ν(s)₁ = ord_E(s)` of the nonzero sections of `L^k`:

* `firstFlagOrder_add_le`: `ord_E H⁰(L^{k+l}) ≤ ord_E H⁰(L^k) + ord_E H⁰(L^l)`;
* `tendsto_firstFlagOrder_div` (`L` big): the limit `lim_k k⁻¹ ord_E H⁰(X, L^k)` exists and equals
  `min_{x ∈ Δ_{Y•}(L)} x₁` (the Okounkov body of `def:Okobd`);
* `mul_firstFlagLelong_le_firstFlagOrder`,
  `firstFlagLelong_le_firstCoordinate_lineBundleOkounkovBody`: `k ν(V_θ, E) ≤ ord_E H⁰(X, L^k)`
  for every `k > 0` with `H⁰(X, L^k) ≠ 0`, and `ν(V_θ, E) ≤ min_{x ∈ Δ_{Y•}(L)} x₁` (the
  inequality `≥` of `thm:nuOk` for `φ = V_θ`, where `Δ_{Y•}(θ, V_θ) = Δ_{Y•}(L)` in the source);
* `exists_tendsto_firstFlagOrder_div_ge`: hence `ν(V_θ, E) ≤ lim_k k⁻¹ ord_E H⁰(X, L^k)`, the
  inequality `≤` of `eq:nuVthetaE`.

The reverse inequality of `eq:nuVthetaE` (equivalently `min_{Δ_{Y•}(L)} x₁ ≤ ν(V_θ, E)`) needs
sections with small vanishing order along `E`, i.e. `Δ_{Y•}(L) = Δ_{Y•}(θ, V_θ)` (the
minimal-singularity case of `cor:transalgPOB`), which is open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.Okounkov.OkoLelong

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Okounkov SGPT.AlmostSemigroup
open scoped Topology ENNReal NNReal

/-! ### The transcendental form of `thm:nuOk` -/

section Transcendental

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The generic Lelong number `ν(φ, Y₁)` of a quasi-psh potential along the first member of the
flag is finite. -/
theorem sourceGenericLelongNumber_firstFlag_ne_top {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ ≠ ⊤ := by
  rw [← potentialFlagValuation_first F hφ]
  exact ENNReal.coe_ne_top

/-- The first value of the flag valuation is the generic Lelong number along `Y₁`:
`ν_{Y•}(θ + dd^c φ)₁ = ν(φ, Y₁)` (source `def:valcurr`). -/
theorem flagValuation_zero_eq_sourceGenericLelongNumber
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    TranscendentalCore.flagValuation F φ 0 =
      (sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toReal := by
  rw [TranscendentalCore.flagValuation_eq hφ, ← potentialFlagValuation_first F hφ]
  rfl

/-- **`thm:nuOk`, transcendental form**: for `T = θ + dd^c φ` with `φ ∈ PSH(X, θ)` and the
partial Okounkov body `Δ_{Y•}(T)` of `def:generalPOB`,
`min_{x ∈ Δ_{Y•}(T)} x₁ = ν(φ, Y₁)`. -/
theorem isLeast_firstCoordinate_generalPartialBody
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' PartialBody.generalPartialBody F θ φ)
      (sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toReal := by
  rw [← flagValuation_zero_eq_sourceGenericLelongNumber F hφ]
  exact Valuative.isLeast_image_zero_generalPartialBody hφ

/-- Lower bound of the transcendental `thm:nuOk`: `ν(φ, Y₁) ≤ x₁` on `Δ_{Y•}(θ + dd^c φ)`. -/
theorem sourceGenericLelongNumber_le_firstCoordinate
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ PartialBody.generalPartialBody F θ φ) :
    (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toReal ≤ x 0 :=
  (isLeast_firstCoordinate_generalPartialBody F hφ).2 ⟨x, hx, rfl⟩

/-- **First step of `cor:Deltacontimplyvarphi`, transcendental form**: an inclusion of partial
Okounkov bodies `Δ_{Y•}(θ + dd^c φ) ⊆ Δ_{Y•}(σ + dd^c ψ)` gives `ν(ψ, Y₁) ≤ ν(φ, Y₁)` (by
`thm:nuOk`). -/
theorem sourceGenericLelongNumber_le_of_generalPartialBody_subset
    {θ σ : ClosedRealOneOneForm (m + 1) F.carrier} {φ ψ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential σ.val ψ)
    (hsub : PartialBody.generalPartialBody F θ φ ⊆ PartialBody.generalPartialBody F σ ψ) :
    sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) ψ ≤
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ := by
  obtain ⟨⟨x, hx, hx0⟩, -⟩ := isLeast_firstCoordinate_generalPartialBody F hφ
  have h := sourceGenericLelongNumber_le_firstCoordinate F hψ (hsub hx)
  simp only at hx0
  rw [hx0] at h
  exact (ENNReal.toReal_le_toReal (sourceGenericLelongNumber_firstFlag_ne_top F hψ)
    (sourceGenericLelongNumber_firstFlag_ne_top F hφ)).mp h

end Transcendental

/-! ### The algebraic setting -/

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoLelongTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoLelongCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoLelongManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The generic Lelong number `ν(φ, Y₁)` (real-valued) of a function on the analytic manifold of
`X` along the first member `Y₁` of the flag. -/
def firstFlagLelong (φ : SchemeComplexPoint f → EReal) : ℝ :=
  (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : Y (1 : Fin (m + 2)) → SchemeComplexPoint f) φ).toReal

omit [IsIntegral X] in
/-- On the scheme, `ν(φ, Y₁)` is the transcendental generic Lelong number of the flag geometry of
`X`; hence the lower bound `ν(φ, Y₁) ≤ x₁` on `Δ_{Y•}(θ + dd^c φ)`. -/
theorem firstFlagLelong_le_of_mem_generalPartialBody {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {x : Fin (m + 1) → ℝ}
    (hx : letI := E.isSeparated; letI := E.quasiCompact;
      x ∈ PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) φ) :
    firstFlagLelong f Y φ ≤ x 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  exact sourceGenericLelongNumber_le_firstCoordinate
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hx

/-- The first coordinate is `1`-Lipschitz for the sup distance. -/
private theorem abs_sub_zero_le_dist (x z : Fin (m + 1) → ℝ) : |x 0 - z 0| ≤ dist x z := by
  rw [← Real.dist_eq]
  exact dist_le_pi_dist x z 0

/-- If `x` lies in the `η`-thickening of a set on which `c ≤ z₁`, then `c - η < x₁`. -/
private theorem lt_zero_of_mem_thickening {c η : ℝ} {K : Set (Fin (m + 1) → ℝ)}
    (hK : ∀ z ∈ K, c ≤ z 0) {x : Fin (m + 1) → ℝ} (hx : x ∈ thickening η K) : c - η < x 0 := by
  obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.mp hx
  have h1 := abs_sub_zero_le_dist x z
  have h2 := hK z hz
  have h3 : z 0 - x 0 ≤ |x 0 - z 0| := by rw [abs_sub_comm]; exact le_abs_self _
  linarith

/-- **`thm:nuOk`, lower bound on sections**: for every `η > 0` and all `k ≫ 0`, every nonzero
`s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` has `k (ν(φ, Y₁) - η) < ν(s)₁ = ord_{Y₁}(s)`. -/
theorem eventually_lt_sectionVector_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {η : ℝ} (hη : 0 < η) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      IsMultiplierSection f (m + 1) E φ k s →
        (k : ℝ) * (firstFlagLelong f Y φ - η) <
          (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨k₀, hk₀, h⟩ := AlgebraicDX.eventually_normalized_mem_thickening f E Y hY a H hφ hη
  refine ⟨k₀, hk₀, fun k hk s hs hm => ?_⟩
  have hmem := h k hk s hs hm
  have hlt := lt_zero_of_mem_thickening
    (fun z hz => firstFlagLelong_le_of_mem_generalPartialBody f E Y hY a H hφ hz) hmem
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₀.trans_le hk
  simp only [Pi.smul_apply, smul_eq_mul] at hlt
  rw [lt_inv_mul_iff₀ hkR] at hlt
  linarith

/-- **`thm:nuOk`, lower bound on the polytopes**: for every `η > 0` and all `k ≫ 0`, every point
`x ∈ Δ_k(θ, φ)` satisfies `ν(φ, Y₁) - η < x₁`. -/
theorem eventually_lt_firstCoordinate_multiplierDegreePolytope {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ multiplierDegreePolytope f (m + 1) E Y hY a φ k,
      firstFlagLelong f Y φ - η < x 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  filter_upwards [AlgebraicDX.eventually_multiplierDegreePolytope_subset_thickening f E Y hY a H
    hφ hη] with k hk x hx
  exact lt_zero_of_mem_thickening
    (fun z hz => firstFlagLelong_le_of_mem_generalPartialBody f E Y hY a H hφ hz) (hk hx)

/-! ### The asymptotic order of vanishing along `Y₁` -/

/-- `ord_{Y₁} H⁰(X, L^k)`: the minimal first flag coordinate `ν(s)₁ = ord_{Y₁}(s)` of the
nonzero sections `s ∈ H⁰(X, L^k)` (`0` by convention when `H⁰(X, L^k) = 0`). -/
def firstFlagOrder (k : ℕ) : ℕ :=
  sInf {j | ∃ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
    schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 = j}

/-- `ord_{Y₁} H⁰(X, L^k) ≤ ord_{Y₁}(s)` for every nonzero `s ∈ H⁰(X, L^k)`. -/
theorem firstFlagOrder_le {k : ℕ} (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    firstFlagOrder f E Y hY a k ≤ schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 :=
  Nat.sInf_le ⟨s, hs, rfl⟩

/-- `ord_{Y₁} H⁰(X, L^k)` is attained when `H⁰(X, L^k) ≠ 0`. -/
theorem exists_firstFlagOrder_eq {k : ℕ} (hne : ∃ s : bundlePowerGlobalSections L k, s ≠ 0) :
    ∃ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 = firstFlagOrder f E Y hY a k := by
  obtain ⟨s, hs⟩ := hne
  exact Nat.sInf_mem (s := {j | ∃ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
    schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 = j}) ⟨_, s, hs, rfl⟩

/-- **Subadditivity**: `ord_{Y₁} H⁰(L^{k+l}) ≤ ord_{Y₁} H⁰(L^k) + ord_{Y₁} H⁰(L^l)` when
`H⁰(L^k)` and `H⁰(L^l)` are nonzero (products of sections, `ν(st) = ν(s) + ν(t)`). -/
theorem firstFlagOrder_add_le {k l : ℕ} (hk : ∃ s : bundlePowerGlobalSections L k, s ≠ 0)
    (hl : ∃ s : bundlePowerGlobalSections L l, s ≠ 0) :
    firstFlagOrder f E Y hY a (k + l) ≤
      firstFlagOrder f E Y hY a k + firstFlagOrder f E Y hY a l := by
  obtain ⟨s, hs, hsv⟩ := exists_firstFlagOrder_eq f E Y hY a hk
  obtain ⟨t, ht, htv⟩ := exists_firstFlagOrder_eq f E Y hY a hl
  have hz := (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a).add_mem
    (⟨k, s, hs, rfl⟩ : ((fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℤ)),
      (k : ℤ)) ∈ schemeProjectiveSectionSemigroup f (m + 1) E Y hY a)
    (⟨l, t, ht, rfl⟩ : ((fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a l t ht i : ℤ)),
      (l : ℤ)) ∈ schemeProjectiveSectionSemigroup f (m + 1) E Y hY a)
  obtain ⟨d, u, hu, hdu⟩ := hz
  simp only [Prod.mk_add_mk] at hdu
  obtain ⟨hv, hd⟩ := Prod.mk.inj hdu
  have hdeg : d = k + l := by omega
  subst hdeg
  have hv0 : ((schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 : ℕ) : ℤ) +
      ((schemeFubiniStudySectionVector f (m + 1) E Y hY a l t ht 0 : ℕ) : ℤ) =
      ((schemeFubiniStudySectionVector f (m + 1) E Y hY a (k + l) u hu 0 : ℕ) : ℤ) := by
    simpa only [Pi.add_apply] using congrFun hv 0
  have hle := firstFlagOrder_le f E Y hY a u hu
  omega

/-- `ord_{Y₁} H⁰(L^{qm+r}) ≤ q ord_{Y₁} H⁰(L^m) + ord_{Y₁} H⁰(L^r)`, when all the degrees
`jm + r` (`j ≤ q`) and `m` carry nonzero sections. -/
theorem firstFlagOrder_mul_add_le {k r : ℕ} (hk : ∃ s : bundlePowerGlobalSections L k, s ≠ 0)
    (hr : ∀ j : ℕ, ∃ s : bundlePowerGlobalSections L (j * k + r), s ≠ 0) :
    ∀ q : ℕ, firstFlagOrder f E Y hY a (q * k + r) ≤
      q * firstFlagOrder f E Y hY a k + firstFlagOrder f E Y hY a r
  | 0 => by simp
  | q + 1 => by
      have ih := firstFlagOrder_mul_add_le hk hr q
      have hsplit : (q + 1) * k + r = k + (q * k + r) := by ring
      have h := firstFlagOrder_add_le f E Y hY a hk (hr q)
      rw [hsplit]
      calc firstFlagOrder f E Y hY a (k + (q * k + r))
          ≤ firstFlagOrder f E Y hY a k + firstFlagOrder f E Y hY a (q * k + r) := h
        _ ≤ firstFlagOrder f E Y hY a k +
              (q * firstFlagOrder f E Y hY a k + firstFlagOrder f E Y hY a r) := by omega
        _ = (q + 1) * firstFlagOrder f E Y hY a k + firstFlagOrder f E Y hY a r := by ring

/-- **Fekete bound**: if `H⁰(X, L^k) ≠ 0` for all `k ≥ K₀` and `H⁰(X, L^p) ≠ 0` with `p > 0`,
then `k⁻¹ ord_{Y₁} H⁰(L^k) ≤ p⁻¹ ord_{Y₁} H⁰(L^p) + ε` for all `k ≫ 0`. -/
theorem eventually_firstFlagOrder_div_le {K₀ : ℕ}
    (hK₀ : ∀ k, K₀ ≤ k → ∃ s : bundlePowerGlobalSections L k, s ≠ 0) {p : ℕ} (hp : 0 < p)
    (hsec : ∃ s : bundlePowerGlobalSections L p, s ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (firstFlagOrder f E Y hY a k : ℝ) / k ≤
      (firstFlagOrder f E Y hY a p : ℝ) / p + ε := by
  set B : ℕ := (Finset.range p).sup fun r => firstFlagOrder f E Y hY a (K₀ + r) with hB
  obtain ⟨N, hN⟩ := exists_nat_gt ((B : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (K₀ + p + N + 1)] with k hk
  -- write `k - K₀ = q p + r'`
  set q := (k - K₀) / p with hq
  set r' := (k - K₀) % p with hr'
  have hr'lt : r' < p := Nat.mod_lt _ hp
  have hdecomp : k = q * p + (K₀ + r') := by
    have := Nat.div_add_mod (k - K₀) p
    rw [← hq, ← hr'] at this
    have hk0 : K₀ ≤ k := by omega
    rw [mul_comm] at this
    omega
  have hsecs : ∀ j : ℕ, ∃ s : bundlePowerGlobalSections L (j * p + (K₀ + r')), s ≠ 0 :=
    fun j => hK₀ _ (by omega)
  have hbound := firstFlagOrder_mul_add_le f E Y hY a hsec hsecs q
  rw [← hdecomp] at hbound
  have hBr : firstFlagOrder f E Y hY a (K₀ + r') ≤ B :=
    Finset.le_sup (f := fun r => firstFlagOrder f E Y hY a (K₀ + r)) (Finset.mem_range.mpr hr'lt)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqp : (q : ℝ) * p ≤ k := by
    have : q * p ≤ k := by omega
    exact_mod_cast this
  have hbR : (firstFlagOrder f E Y hY a k : ℝ) ≤
      q * (firstFlagOrder f E Y hY a p : ℝ) + B := by
    have : firstFlagOrder f E Y hY a k ≤ q * firstFlagOrder f E Y hY a p + B := by omega
    exact_mod_cast this
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
  have hBk : (B : ℝ) / k ≤ ε := by
    rw [div_le_iff₀ hkpos]
    have h1 : (B : ℝ) < N * ε := by
      rw [div_lt_iff₀ hε] at hN
      linarith
    nlinarith
  have hap : (0 : ℝ) ≤ firstFlagOrder f E Y hY a p := Nat.cast_nonneg _
  have hfirst : (q : ℝ) * (firstFlagOrder f E Y hY a p : ℝ) / k ≤
      (firstFlagOrder f E Y hY a p : ℝ) / p := by
    rw [div_le_div_iff₀ hkpos hpR]
    nlinarith
  calc (firstFlagOrder f E Y hY a k : ℝ) / k
      ≤ (q * (firstFlagOrder f E Y hY a p : ℝ) + B) / k :=
        div_le_div_of_nonneg_right hbR hkpos.le
    _ = q * (firstFlagOrder f E Y hY a p : ℝ) / k + (B : ℝ) / k := add_div _ _ _
    _ ≤ (firstFlagOrder f E Y hY a p : ℝ) / p + ε := add_le_add hfirst hBk

/-- If `c ≤ k⁻¹ ord_{Y₁} H⁰(X, L^k)` for every `k > 0` with `H⁰(X, L^k) ≠ 0`, then `c ≤ x₁` on the
Okounkov body `Δ_{Y•}(L)` (`def:Okobd`). -/
theorem le_firstCoordinate_of_le_firstFlagOrder {c : ℝ}
    (hc : ∀ k : ℕ, 0 < k → (∃ s : bundlePowerGlobalSections L k, s ≠ 0) →
      c ≤ (firstFlagOrder f E Y hY a k : ℝ) / k)
    {x : Fin (m + 1) → ℝ} (hx : x ∈ lineBundleOkounkovBody f (m + 1) E Y hY a) : c ≤ x 0 := by
  have hK : IsClosed {y : Fin (m + 1) → ℝ | c ≤ y 0} := isClosed_le continuous_const
    (continuous_apply 0)
  have hKv : Convex ℝ {y : Fin (m + 1) → ℝ | c ≤ y 0} := by
    intro y hy z hz s t hs ht hst
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    have hc' : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hy hs, mul_le_mul_of_nonneg_left hz ht]
  refine AlgebraicDX.body_subset_of_normalized_mem _ hK hKv ?_ hx
  rintro z ⟨k, s, hs, rfl⟩
  refine ⟨by simp, fun h0 => ?_, fun hpos => ?_⟩
  · have hk0 : k = 0 := by
      change ((k : ℕ) : ℤ) = 0 at h0
      exact_mod_cast h0
    subst hk0
    rw [schemeFubiniStudySectionVector_degree_zero f m E Y hY a s hs]
    funext i
    simp
  · have hkpos : 0 < k := by
      change (0 : ℤ) < ((k : ℕ) : ℤ) at hpos
      exact_mod_cast hpos
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have h1 := hc k hkpos ⟨s, hs⟩
    have h2 : (firstFlagOrder f E Y hY a k : ℝ) ≤
        (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 : ℝ) := by
      exact_mod_cast firstFlagOrder_le f E Y hY a s hs
    simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, Counting.integerCast]
    push_cast
    rw [le_inv_mul_iff₀ (by exact_mod_cast hkR)]
    rw [le_div_iff₀ hkR] at h1
    linarith

/-- `min_{x ∈ Δ_{Y•}(L)} x₁ ≤ k⁻¹ ν(s)₁` for every nonzero `s ∈ H⁰(X, L^k)`, `k > 0`. -/
theorem firstCoordinate_le_of_section {ℓ : ℝ}
    (hℓ : IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) ℓ)
    {k : ℕ} (hk : 0 < k) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    ℓ ≤ (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 : ℝ) / k := by
  have hmem := normalized_mem_lineBundleOkounkovBody f (m + 1) E Y hY a hk s hs
  have h := hℓ.2 ⟨_, hmem, rfl⟩
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rwa [inv_mul_eq_div] at h

/-- `min_{x ∈ Δ_{Y•}(L)} x₁ ≤ k⁻¹ ord_{Y₁} H⁰(X, L^k)` whenever `H⁰(X, L^k) ≠ 0`, `k > 0`. -/
theorem firstCoordinate_le_firstFlagOrder {ℓ : ℝ}
    (hℓ : IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) ℓ)
    {k : ℕ} (hk : 0 < k) (hne : ∃ s : bundlePowerGlobalSections L k, s ≠ 0) :
    ℓ ≤ (firstFlagOrder f E Y hY a k : ℝ) / k := by
  obtain ⟨s, hs, hsv⟩ := exists_firstFlagOrder_eq f E Y hY a hne
  have := firstCoordinate_le_of_section f E Y hY a hℓ hk s hs
  rwa [hsv] at this

/-- For a big line bundle the first coordinate attains its minimum on `Δ_{Y•}(L)`. -/
theorem exists_isLeast_firstCoordinate_lineBundleOkounkovBody (hL : SGPT.LineBundle.IsBig f L (m + 1)) :
    ∃ ℓ : ℝ, IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) ℓ := by
  have hc : IsCompact ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) :=
    (isCompact_lineBundleOkounkovBody f (m + 1) E Y hY a).image (continuous_apply 0)
  have hne : ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a).Nonempty :=
    (nonempty_lineBundleOkounkovBody f (m + 1) E Y hY a hL).image _
  exact ⟨_, hc.isLeast_sInf hne⟩

/-- **`cor:numin`, existence of the limit**: for a big line bundle `L` and `E = Y₁`,
`lim_{k → ∞} k⁻¹ ord_E H⁰(X, L^k)` exists and equals `min_{x ∈ Δ_{Y•}(L)} x₁`. -/
theorem tendsto_firstFlagOrder_div (hL : SGPT.LineBundle.IsBig f L (m + 1)) {ℓ : ℝ}
    (hℓ : IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) ℓ) :
    Tendsto (fun k : ℕ => (firstFlagOrder f E Y hY a k : ℝ) / k) atTop (𝓝 ℓ) := by
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp hL.eventually_exists_ne_zero
  set K₀ := K₁ + 1 with hK₀def
  have hK₀ : ∀ k, K₀ ≤ k → ∃ s : bundlePowerGlobalSections L k, s ≠ 0 :=
    fun k hk => hK₁ k (by omega)
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [eventually_ge_atTop K₀] with k hk
    exact lt_of_lt_of_le hb (firstCoordinate_le_firstFlagOrder f E Y hY a hℓ (by omega) (hK₀ k hk))
  · intro b hb
    -- some degree `p` has `p⁻¹ ord_{Y₁} H⁰(L^p) < b`
    have hexists : ∃ p : ℕ, 0 < p ∧ (∃ s : bundlePowerGlobalSections L p, s ≠ 0) ∧
        (firstFlagOrder f E Y hY a p : ℝ) / p < b := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨x, hx, rfl⟩, -⟩ := hℓ
      have := le_firstCoordinate_of_le_firstFlagOrder f E Y hY a (c := b)
        (fun k hk hne => hcon k hk hne) hx
      linarith
    obtain ⟨p, hp, hsec, hpb⟩ := hexists
    have hε : 0 < (b - (firstFlagOrder f E Y hY a p : ℝ) / p) / 2 := by linarith
    filter_upwards [eventually_firstFlagOrder_div_le f E Y hY a hK₀ hp hsec hε] with k hk
    linarith

/-- **`cor:numin`, the inequality `≤` on each degree**: `k ν(V_θ, Y₁) ≤ ord_{Y₁}(s)` for every
nonzero `s ∈ H⁰(X, L^k)`, `k > 0`, where `V_θ` is the minimal-singularity potential of
`θ = c₁(L, h₀)`. -/
theorem mul_firstFlagLelong_le_sectionVector {k : ℕ} (hk : 0 < k)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (k : ℝ) * firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val) ≤
      (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs 0 : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
  set θ := H.curvature a with hθ
  have hu := H.isThetaPshPotential_normalized_sectionLogNormSq a k hk s hs
  have hpsef : ∃ u : SchemeComplexPoint f → EReal, IsThetaPshPotential θ.val u := ⟨_, hu⟩
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hpsef
  have hmem := AlgebraicDX.lineBundleOkounkovBody_subset_generalPartialBody f E Y hY a H hpsef
    (normalized_mem_lineBundleOkounkovBody f (m + 1) E Y hY a hk s hs)
  have h := firstFlagLelong_le_of_mem_generalPartialBody f E Y hY a H hV hmem
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [le_inv_mul_iff₀ hkR] at h
  linarith

/-- `k ν(V_θ, Y₁) ≤ ord_{Y₁} H⁰(X, L^k)` whenever `H⁰(X, L^k) ≠ 0`, `k > 0`. -/
theorem mul_firstFlagLelong_le_firstFlagOrder {k : ℕ} (hk : 0 < k)
    (hne : ∃ s : bundlePowerGlobalSections L k, s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (k : ℝ) * firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val) ≤
      (firstFlagOrder f E Y hY a k : ℝ) := by
  obtain ⟨s, hs, hsv⟩ := exists_firstFlagOrder_eq f E Y hY a hne
  have := mul_firstFlagLelong_le_sectionVector f E Y hY a H hk s hs
  rwa [hsv] at this

/-- `ν(V_θ, Y₁) ≤ x₁` for every `x ∈ Δ_{Y•}(L)`, i.e. `ν(V_θ, Y₁) ≤ min_{x ∈ Δ_{Y•}(L)} x₁`. -/
theorem firstFlagLelong_le_firstCoordinate_lineBundleOkounkovBody
    {x : Fin (m + 1) → ℝ} (hx : x ∈ lineBundleOkounkovBody f (m + 1) E Y hY a) :
    letI := E.isSeparated
    letI := E.quasiCompact
    firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val) ≤ x 0 := by
  refine le_firstCoordinate_of_le_firstFlagOrder f E Y hY a (fun k hk hne => ?_) hx
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hkR, mul_comm]
  exact mul_firstFlagLelong_le_firstFlagOrder f E Y hY a H hk hne

/-- **`cor:numin`, existence of the limit and the inequality `≤`**: for a big line bundle `L` and
`E = Y₁` the first member of a smooth flag, the limit `lim_k k⁻¹ ord_E H⁰(X, L^k)` exists and
`ν(V_θ, E) ≤ lim_k k⁻¹ ord_E H⁰(X, L^k)`. -/
theorem exists_tendsto_firstFlagOrder_div_ge (hL : SGPT.LineBundle.IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ ℓ : ℝ, Tendsto (fun k : ℕ => (firstFlagOrder f E Y hY a k : ℝ) / k) atTop (𝓝 ℓ) ∧
      IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) '' lineBundleOkounkovBody f (m + 1) E Y hY a) ℓ ∧
      firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val) ≤ ℓ := by
  obtain ⟨ℓ, hℓ⟩ := exists_isLeast_firstCoordinate_lineBundleOkounkovBody f E Y hY a hL
  refine ⟨ℓ, tendsto_firstFlagOrder_div f E Y hY a hL hℓ, hℓ, ?_⟩
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hℓ
  exact firstFlagLelong_le_firstCoordinate_lineBundleOkounkovBody f E Y hY a H hx

end SGPT.Okounkov.OkoLelong
