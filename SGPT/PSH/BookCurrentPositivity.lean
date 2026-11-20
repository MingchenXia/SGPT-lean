import SGPT.PSH.BookCurrentProducts
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation

/-!
# Positive currents on a complex manifold (`def:pos_curr`)

Source: `chapter_pshfunctions.tex`, `def:pos_curr`: an `(m,m)`-current `T` on a complex manifold
`Y` of dimension `N` is *positive* if `m > N` or, for all smooth `(1,0)`-forms
`β₁, …, β_{N-m}`, the measure `T ∧ i β₁ ∧ β̄₁ ∧ ⋯ ∧ i β_{N-m} ∧ β̄_{N-m}` is positive.
Proofs follow Xia, *Foundations of pluripotential theory*, `q01` (positive currents) and the
local `dd^c`-lemma for closed positive `(1,1)`-currents.

## Formalization

Currents are the project's geometric currents `GlobalCurrent N Y k` (SGPT.Foundations.Analysis):
compatible families of continuous functionals on compactly supported smooth real test forms of
complementary degree `2N - k` in all holomorphic charts; an `(m,m)`-current has real degree
`k = 2m` (so `m ≤ N` is built into the degree and the clause `m > N` is vacuous but kept).
The measure `T ∧ ψ` of a smooth form `ψ` of degree `2(N - m)` is, in a chart `e`, the
distribution `φ ↦ T(φ ψ)`; it is positive iff it is nonnegative on nonnegative test functions in
every chart (positivity of a measure is local).  Hence `IsPositiveCurrent m hk T`: in every chart,
for all smooth `(1,0)`-forms `β_j` on the chart domain (smooth maps into `(ℂ^N)^*`), all test
functions `φ ≥ 0` and the test form `α = φ · ∏ i β_j ∧ β̄_j`, one has `T(α) ≥ 0`.  The forms
`β_j` are tested on the chart domains; a global smooth `(1,0)`-form restricts to such local
forms, and conversely the local test only involves `β_j` near the compact support of `φ`.

The currents are real (they act on real test forms); the book recalls that positive currents are
real, so this is the class of currents the book's definition singles out.

## Main results

* `IsPositiveCurrent` — the source definition.
* `isPositiveCurrent_of_isFullPositive` — TN's full positivity (nonnegativity on all test forms
  that are strongly positive at every point) implies weak positivity (`(1,1)`-currents).
* `hasNonnegativeDistributionalLevi_of_isPositiveCurrent` — local potentials of a weakly positive
  `(1,1)`-current are plurisubharmonic in the distributional sense.
* `exists_theta_representation_of_isPositiveCurrent` — on a compact complex manifold every closed
  weakly positive `(1,1)`-current is `θ + dd^c u` with `u` `θ`-psh (`dd^c`-lemma).
* `isPositiveCurrent_iff_isFullPositive` — for closed `(1,1)`-currents on compact manifolds the
  source positivity is TN's full positivity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.PSH.BookCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
open SGPT.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
open SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity
open SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
open SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
open SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
open SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
open SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
open SGPT.Foundations.Analysis.Pending.XiaoCompatibleGlobalPotential
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
open SGPT.Foundations.Analysis.Pending.ClosedCurrentSmoothBottChernRepresentative
open SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation
open _root_.SGPT.Foundations.Analysis.LocalCurrents

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-! ### The definition -/

section Definition

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The complementary test degree of an `(m,m)`-current is `2 (N - m)`. -/
theorem testDegree_eq {k : CurrentDegree N} {m : ℕ} (hk : k.val = 2 * m) :
    2 * (N - m) = Module.finrank ℝ (ComplexModel N) - k.val := by
  have h1 := k.isLt
  rw [hk] at h1 ⊢
  rw [complexModel_real_finrank] at h1 ⊢
  omega

/-- **Positive `(m,m)`-currents** (`def:pos_curr`, weak positivity).  `T` is a current of real
degree `k = 2m` on the `N`-dimensional complex manifold `Y`.  It is positive if `m > N` or, in
every holomorphic chart, `T(φ · i β₁ ∧ β̄₁ ∧ ⋯ ∧ i β_{N-m} ∧ β̄_{N-m}) ≥ 0` for all smooth
`(1,0)`-forms `β_j` and all test functions `φ ≥ 0`, i.e. the measures
`T ∧ i β₁ ∧ β̄₁ ∧ ⋯ ∧ i β_{N-m} ∧ β̄_{N-m}` are positive. -/
def IsPositiveCurrent (m : ℕ) {k : CurrentDegree N} (hk : k.val = 2 * m)
    (T : GlobalCurrent N Y k) : Prop :=
  N < m ∨ ∀ (e : ComplexChart N Y) (β : Fin (N - m) → ComplexModel N → ComplexModel N →L[ℂ] ℂ),
    (∀ j, ContDiffOn ℝ ∞ (β j) (chartTarget e : Set (ComplexModel N))) →
    ∀ φ : 𝓓(chartTarget e, ℝ), (∀ z, 0 ≤ φ z) →
    ∀ α : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel N) - k.val),
      (∀ z, α z = φ z • castForm (testDegree_eq hk) (betaProduct fun j => β j z)) →
        0 ≤ T.inChart e α

theorem IsPositiveCurrent.add {m : ℕ} {k : CurrentDegree N} {hk : k.val = 2 * m}
    {S T : GlobalCurrent N Y k} (hS : IsPositiveCurrent m hk S)
    (hT : IsPositiveCurrent m hk T) : IsPositiveCurrent m hk (S + T) := by
  rcases hS with hS | hS
  · exact Or.inl hS
  rcases hT with hT | hT
  · exact Or.inl hT
  exact Or.inr fun e β hβ φ hφ α hα => by
    show 0 ≤ S.inChart e α + T.inChart e α
    exact add_nonneg (hS e β hβ φ hφ α hα) (hT e β hβ φ hφ α hα)

theorem IsPositiveCurrent.smul {m : ℕ} {k : CurrentDegree N} {hk : k.val = 2 * m}
    {T : GlobalCurrent N Y k} (hT : IsPositiveCurrent m hk T) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveCurrent m hk (c • T) := by
  rcases hT with hT | hT
  · exact Or.inl hT
  exact Or.inr fun e β hβ φ hφ α hα => by
    show 0 ≤ c * T.inChart e α
    exact mul_nonneg hc (hT e β hβ φ hφ α hα)

theorem isPositiveCurrent_zero (m : ℕ) {k : CurrentDegree N} (hk : k.val = 2 * m) :
    IsPositiveCurrent m hk (0 : GlobalCurrent N Y k) :=
  Or.inr fun e _ _ _ _ α _ => by simp

end Definition

/-! ### Degree transport of test forms -/

section Cast

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem castTestDegree_apply' {a b : ℕ} (h : a = b) (α : TestForm U a) (x : ComplexModel n) :
    castTestDegree h α x = castForm h (α x) := by
  subst b
  rfl

theorem castTestDegree_castTestDegree {a b : ℕ} (h : a = b) (h' : b = a) (α : TestForm U a) :
    castTestDegree h' (castTestDegree h α) = α := by
  subst b
  rfl

theorem eqRec_id_apply {a b : ℕ} (h : a = b) (α : TestForm U a) :
    (h ▸ ContinuousLinearMap.id ℝ (TestForm U a) : TestForm U a →L[ℝ] TestForm U b) α =
      castTestDegree h α := by
  subst b
  rfl

end Cast

/-! ### Full positivity implies weak positivity -/

section FullPositive

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

theorem castForm_mem_spCone {a b : ℕ} (h : 2 * a = 2 * b) {P : RealForm (m + 1) (2 * a)}
    (hP : P ∈ spCone a) : castForm h P ∈ spCone b := by
  have hab : a = b := by omega
  subst hab
  have hc : castForm h P = P := by
    ext v
    rw [castForm_apply]
    rfl
  rwa [hc]

/-- The degree hypothesis of a `(1,1)`-current. -/
theorem degreeTwo_val_eq (m : ℕ) : (degreeTwo (Nat.succ_pos m)).val = 2 * 1 := rfl

/-- **Strongly positive testing implies the source positivity**: a `(1,1)`-current that is
nonnegative on all test forms that are strongly positive at every point (TN `IsFullPositive`) is
positive in the sense of `def:pos_curr`, since `φ ∏ i β_j ∧ β̄_j` is strongly positive. -/
theorem isPositiveCurrent_of_isFullPositive
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (hT : IsFullPositive T) :
    IsPositiveCurrent 1 (degreeTwo_val_eq m) T := by
  refine Or.inr fun e β _hβ φ hφ α hα => ?_
  have hdeg : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]; omega
  let α' : TestForm (chartTarget e) (2 * m) := castTestDegree hdeg.symm α
  have hα' : ∀ x, α' x ∈ spCone m := by
    intro x
    change castTestDegree hdeg.symm α x ∈ spCone m
    rw [castTestDegree_apply', hα x, map_smul, castForm_castForm]
    exact smul_mem_spCone (castForm_mem_spCone _ (betaProduct_mem_spCone _)) (hφ x)
  have h := hT e α' hα'
  rwa [castTestDegree_castTestDegree] at h

end FullPositive

/-! ### Weak positivity gives plurisubharmonic local potentials -/

section Levi

variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}

private theorem reader_restrict' (hVU : V ≤ U) (A : DistributionForm U 2) :
    complementaryRead (restrictForm A hVU) = restrict hVU (complementaryRead A) := by
  ext γ φ
  have hφ : (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) = extTest hVU φ := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hVU φ) y, extTest_apply]
  simp only [complementaryRead, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    restrictForm_apply, LocalBedfordTaylorLocality.restrict_apply, smul_eq_mul, hφ]

/-- Pairing a current of bidimension `(m,m)` with the coefficients of a constant-form test. -/
theorem sum_formBasis_coeffTest {q : ℕ} (S : LocalProductCurrent (m + 1) U q)
    (γ : formSpan (m + 1) q) (α : 𝓓(U, RealForm (m + 1) (2 * q))) (φ : 𝓓(U, ℝ))
    (hα : ∀ z, α z = φ z • (γ : RealForm (m + 1) (2 * q))) :
    ∑ i, S (formBasis (m + 1) q i) (coeffTest α i) = S γ φ := by
  have hc : ∀ i, coeffTest α i = (formBasis (m + 1) q).repr γ i • φ := by
    intro i
    ext z
    change coeffCLM (m + 1) q i (α z) = _
    rw [hα z, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    congr 1
    change ((formBasis (m + 1) q).coord i) (formProj (m + 1) q (γ : RealForm (m + 1) (2 * q))) = _
    rw [formProj_coe]
    rfl
  simp_rw [hc, map_smul]
  conv_rhs => rw [← (formBasis (m + 1) q).sum_repr γ]
  rw [map_sum]
  simp only [map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Weak positivity, read on a constant product `γ = ∏ i b_j ∧ b̄_j` through TN's chart span
current: `T(γ)(φ) ≥ 0` for `φ ≥ 0`. -/
theorem chartSpanCurrent_betaProduct_nonneg
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsPositiveCurrent 1 (degreeTwo_val_eq m) T) (e : ComplexChart (m + 1) M)
    (b : Fin m → ComplexModel (m + 1) →L[ℂ] ℂ) (φ : 𝓓(chartTarget e, ℝ)) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ chartSpanCurrent T e ⟨betaProduct b, betaProduct_mem_formSpan b⟩ φ := by
  rcases hT with hT | hT
  · omega
  have hdeg : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]; omega
  let τ : TestForm (chartTarget e) (2 * m) :=
    TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (betaProduct b : RealForm (m + 1) (2 * m))) φ
  have hkey : chartSpanCurrent T e ⟨betaProduct b, betaProduct_mem_formSpan b⟩ φ =
      T.inChart e ((hdeg ▸ ContinuousLinearMap.id ℝ (TestForm (chartTarget e) (2 * m)) :
        TestForm (chartTarget e) (2 * m) →L[ℝ] TestForm (chartTarget e)
          (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) τ) := rfl
  rw [hkey, eqRec_id_apply]
  apply hT e (fun j _ => b j) (fun _ => contDiffOn_const) φ hφ
  intro z
  rw [castTestDegree_apply']
  change castForm hdeg (φ z • betaProduct b) = _
  rw [map_smul]

/-- **Local potentials of a weakly positive `(1,1)`-current are psh** (distributionally): if
`dd^c R = T` on an open subset of a chart, then `R` has nonnegative distributional Levi form. -/
theorem hasNonnegativeDistributionalLevi_of_isPositiveCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsPositiveCurrent 1 (degreeTwo_val_eq m) T) (e : ComplexChart (m + 1) M)
    (hU : U ≤ chartTarget e) (R : 𝓓'(U, ℝ))
    (hR : ddC R = restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hU) :
    HasNonnegativeDistributionalLevi R := by
  have hfull : ddc (ScalarLeviPositiveCurrent.scalarTopCurrent R) =
      restrict hU (chartSpanCurrent T e) := by
    rw [← complementaryRead_ddC, hR, reader_restrict',
      complementaryRead_coefficients_eq_chartSpanCurrent]
  apply BookCurrent.hasNonnegativeDistributionalLevi_of_betaProduct_pairings R
  intro β α φ hφ hα
  rw [sum_formBasis_coeffTest _ ⟨betaProduct β, betaProduct_mem_formSpan β⟩ α φ hα, hfull,
    LocalBedfordTaylorLocality.restrict_apply]
  exact chartSpanCurrent_betaProduct_nonneg T hT e β (extTest hU φ)
    (fun z => by rw [extTest_apply]; exact hφ z)

private theorem ddC_add' {W : Opens (ComplexModel (m + 1))}
    (R Q : 𝓓'(W, ℝ)) : ddC (R + Q) = ddC R + ddC Q :=
  map_add ddCLM R Q

private theorem restrictForm_add' {Ω W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ Ω) (A B : DistributionForm Ω 2) :
    restrictForm (A + B) hW = restrictForm A hW + restrictForm B hW := by
  ext v φ
  rfl

/-- A weakly positive current with a smooth-background scalar reading is locally `θ`-psh. -/
theorem isLocallyThetaPshDistribution_of_isPositiveCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsPositiveCurrent 1 (degreeTwo_val_eq m) T) (σ : ClosedRealOneOneForm (m + 1) M)
    (S : (e : ComplexChart (m + 1) M) → 𝓓'(chartTarget e, ℝ))
    (hread : ∀ e, T.coefficients (canonicalBasis (m + 1)) e =
      smoothFormDistribution (canonicalBasis (m + 1)) σ.val e + ddC (S e)) :
    ∀ e, IsLocallyThetaPshDistribution (canonicalBasis (m + 1)).addHaar σ.val e (S e) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials σ e z hz
  let U : Opens (ComplexModel (m + 1)) := ⟨W, hpot.1⟩
  have hU : U ≤ chartTarget e := hpot.2.1
  have hρ : LocallyIntegrableOn ρ U (canonicalBasis (m + 1)).addHaar :=
    hpot.2.2.1.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hσ : restrictForm
      (smoothFormDistribution (canonicalBasis (m + 1)) σ.val e) hU =
      ddC (regularDistribution (canonicalBasis (m + 1)).addHaar ρ hρ) := by
    have h := restrictForm_smoothFormDistribution_eq_ddC σ.val e hU ρ hpot
    rw [coefficients_smoothGlobalCurrent] at h
    exact h
  let R := restrictDistribution (S e) hU +
    regularDistribution (canonicalBasis (m + 1)).addHaar ρ hρ
  have hR : ddC R = restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hU := by
    have h := congrArg (fun A => restrictForm A hU) (hread e)
    rw [restrictForm_add', hσ, restrictForm_ddC] at h
    dsimp only [R]
    rw [ddC_add']
    exact (add_comm _ _).trans h.symm
  exact ⟨U, hU, ρ, hρ, hzW, hpot,
    hasNonnegativeDistributionalLevi_of_isPositiveCurrent T hT e hU R hR⟩

end Levi

/-! ### The `dd^c`-lemma and the comparison of positivities on compact manifolds -/

section Compact

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]

/-- **`dd^c`-lemma for closed positive `(1,1)`-currents** (FPT `q07`): on a compact complex
manifold every closed weakly positive `(1,1)`-current is `θ + dd^c u` for a closed smooth real
`(1,1)`-form `θ` and a `θ`-psh function `u`, as an equality of currents. -/
theorem exists_theta_representation_of_isPositiveCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsPositiveCurrent 1 (degreeTwo_val_eq m) T) :
    ∃ (σ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
      (hu : IsThetaPshPotential σ.val u), T = thetaPotentialCurrent σ.val u hu := by
  obtain ⟨k, g, P, hP, R, χ, hχ, hc, hs, Q, σ,
      _hnon, _hsP, _hsum, _hR, _hT, hread, _hQ⟩ :=
    exists_smooth_native_bott_chern_representative (canonicalBasis (m + 1))
      (Nat.succ_pos m) T hclosed h11
  let S := finiteScalarFamily g χ hχ hc hs R
  have hS : ScalarFamilyCompatible S := finiteScalarFamily_compatible g χ hχ hc hs R
  have hlocal := isLocallyThetaPshDistribution_of_isPositiveCurrent T hT σ S hread
  obtain ⟨u, hu, hchart⟩ := exists_isThetaPshPotential_of_isCoordinateCompatible
    (canonicalBasis (m + 1)).addHaar S
    (isCoordinateCompatible_of_scalarFamilyCompatible S hS) hlocal
  refine ⟨σ, u, hu, ?_⟩
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  rw [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    coefficients_smoothGlobalCurrent, globalDDC_coefficients, hread e]
  obtain ⟨_hfin, hL, heq⟩ := hchart e
  change smoothFormDistribution (canonicalBasis (m + 1)) σ.val e + ddC (S e) =
    smoothFormDistribution (canonicalBasis (m + 1)) σ.val e +
      ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal) _)
  rw [heq]

/-- Weak positivity implies TN's full positivity for closed `(1,1)`-currents on compact
manifolds. -/
theorem isFullPositive_of_isPositiveCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsPositiveCurrent 1 (degreeTwo_val_eq m) T) : IsFullPositive T := by
  obtain ⟨σ, u, hu, rfl⟩ := exists_theta_representation_of_isPositiveCurrent T hclosed h11 hT
  exact thetaPotentialCurrent_full_positive σ.val u hu

/-- **The source positivity of closed `(1,1)`-currents is TN's full positivity.** -/
theorem isPositiveCurrent_iff_isFullPositive
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    IsPositiveCurrent 1 (degreeTwo_val_eq m) T ↔ IsFullPositive T :=
  ⟨isFullPositive_of_isPositiveCurrent T hclosed h11, isPositiveCurrent_of_isFullPositive T⟩

end Compact

end SGPT.PSH.BookCurrent
