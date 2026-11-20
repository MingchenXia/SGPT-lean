import SGPT.BDivisor.BDBlowupProjective
import SGPT.BDivisor.ClassPushforward
import SGPT.Projective.BDivNov16PrimeSpan
import SGPT.Projective.NumEqNSCurveInjectivity
import SGPT.Projective.ActualCurveDegreeLinearity
import SGPT.Projective.NativeNefCurveDegree

/-!
# Numerical classes of real divisors and the cycle class map

Lane BD, blueprint `bd.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef
b-divisors are introduced by Dang--Favre [DF20] [...] our transcendental intersection theory
coincides with theirs in the algebraic setting."

Dang--Favre's b-divisor classes have incarnations in the real numerical spaces `N¹(Y)_ℝ` of the
models `Y`: real divisors modulo numerical equivalence, compatible under the push-forward of
divisors. This file builds `N¹(Y)_ℝ` of a compact complex manifold `Y` and identifies it, for
`Y` connected and projective, with the Néron--Severi space `NS(Y)_ℝ ⊆ H^{1,1}(Y, ℝ)`
(`SGPT.BDivisor.DFAlg.neronSeveri`) through the cycle class map, compatibly with the
push-forward of divisors along modifications.

* `RealDivisor m Y` — real (Weil = Cartier, `Y` smooth) divisors `∑ a_P P`, `P` prime divisors.
* `divisorClass` — the cycle class map `D ↦ {[D]} = ∑ a_P {[P]}`; its range is `NS(Y)_ℝ`
  (`range_divisorClass`), and every effective divisor has a real Weil divisor with the same
  class (`exists_realDivisor_divisorClass_eq_cycleClass`).
* `classDegreeAlong` — the degree `α · C = ∫_C g^*θ` of a class along a holomorphic map
  `g : C → Y` from a compact Riemann surface (any smooth representative `θ`); for
  `α = {[D]}` it is `D · C = deg g^*𝒪(D)`. `numericallyTrivialDivisors`: the divisors with
  `D · C = 0` for every curve; `NumericalClasses m Y = Div(Y)_ℝ / ≡` is `N¹(Y)_ℝ`.
* `numericallyTrivialDivisors_eq_ker` and `numericalClassEquiv`: for `Y` compact connected
  projective, **numerically trivial ⇔ cohomologically trivial**, and the cycle class map induces
  a linear isomorphism `N¹(Y)_ℝ ≃ NS(Y)_ℝ` (the curve half is the complete-intersection-curve
  argument of `NumEqNSCurveInjectivity.lean` with the Hodge index theorem).
* `primePushforward`, `divisorPushforward` — the push-forward of divisors along a modification
  `π : Y → X`: `π_* P = π(P)` if `P ⊄ Exc(π)` (then `π(P)` is a prime divisor,
  `primeImage_val`, and `π` is injective on `P ∖ Exc(π)`, so `π|_P` has degree one), and
  `π_* P = 0` if `P ⊆ Exc(π)` (then `π(P)` contains no prime divisor,
  `not_prime_subset_image_of_subset_exceptionalLocus`).
* `divisorClass_divisorPushforward`: **`cl(π_* D) = π_* cl(D)`**, the compatibility of the cycle
  class map with push-forward; `numericalPushforward` and
  `numericalClassEquiv_numericalPushforward`: the push-forward descends to numerical classes and
  corresponds to the push-forward of classes under `N¹ ≃ NS`.
* `IsCurveNef`, `isCurveNef_of_classNef`: Dang--Favre's nef classes are the curve-nef ones
  (`α · C ≥ 0` for every curve); a nef class (`def:nef`, `ClassNefWithRespectTo`) is curve-nef.
  The converse on `NS(Y)_ℝ` of a projective manifold is Kleiman's criterion (not formalized).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.DFAlg

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Projective.NumEq

/-! ### Real divisors and the cycle class map -/

section CycleClass

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]

variable (m Y) in
/-- **Real divisors** `Div(Y)_ℝ`: finite real combinations `∑ a_P P` of prime divisors `P` of `Y`.
On a complex manifold every prime divisor is Cartier, so these are the real Weil and the real
Cartier divisors. -/
abbrev RealDivisor := SGPT.PSH.GeometricPrimeCarrier (m + 1) Y →₀ ℝ

/-- **The cycle class map** `Div(Y)_ℝ → H^{1,1}(Y, ℝ)`, `∑ a_P P ↦ ∑ a_P {[P]}`. -/
def divisorClass : RealDivisor m Y →ₗ[ℝ] RealBottChern (m + 1) Y :=
  Finsupp.linearCombination ℝ fun P => cycleClass (SGPT.Siu.primeEffectiveDivisor P)

theorem divisorClass_single (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y) (a : ℝ) :
    divisorClass (Finsupp.single P a) = a • cycleClass (SGPT.Siu.primeEffectiveDivisor P) :=
  Finsupp.linearCombination_single ℝ a P

/-- **The image of the cycle class map is the Néron--Severi space.** -/
theorem range_divisorClass :
    LinearMap.range (divisorClass (m := m) (Y := Y)) = neronSeveri (m + 1) Y := by
  rw [divisorClass, Finsupp.range_linearCombination,
    SGPT.Projective.BDivNov16.neronSeveri_eq_span_primeCycleClass]

theorem divisorClass_mem_neronSeveri (D : RealDivisor m Y) :
    divisorClass D ∈ neronSeveri (m + 1) Y := by
  rw [← range_divisorClass]
  exact LinearMap.mem_range_self _ D

/-- Every effective divisor `D` has a real Weil divisor `∑ ν_P P` (`ν_P ≥ 0`, its prime
decomposition `[D] = ∑ ν_P [P]`) with the same cycle class. -/
theorem exists_realDivisor_divisorClass_eq_cycleClass (D : EffectiveDivisor (m + 1) Y) :
    ∃ W : RealDivisor m Y, (∀ P, 0 ≤ W P) ∧ divisorClass W = cycleClass D := by
  classical
  obtain ⟨F, c, hc, h⟩ := SGPT.Projective.BDivNov16.cycleClass_eq_finite_prime_sum D
  refine ⟨∑ P ∈ F, Finsupp.single P (c P), fun P => ?_, ?_⟩
  · rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun Q hQ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact (hc Q hQ).2
    · exact le_rfl
  · rw [map_sum, h]
    exact Finset.sum_congr rfl fun P _ => divisorClass_single P (c P)

end CycleClass

/-! ### Degrees along curves and numerical equivalence -/

section Numerical

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- **The degree of a class along a curve**: `α · C = ∫_C g^*θ` for `g : C → Y` holomorphic from
a compact Riemann surface and `θ` any smooth representative of `α` (`degreeAlong`, which only
depends on the class). For `α = c₁(L)` and `g` the normalization of an irreducible curve `Γ` this
is `L · Γ = deg g^*L`. -/
def classDegreeAlong {C : Type} [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
    [IsComplexManifold 1 C] [CompactSpace C] (κ : KahlerBackground 1 C) {g : C → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g) :
    RealBottChern (m + 1) Y →ₗ[ℝ] ℝ where
  toFun α := Quotient.liftOn α (fun θ => degreeAlong κ hg θ)
    (fun _ _ h => degreeAlong_eq_of_bottChernRel κ hg h)
  map_add' α β := by
    induction α using Quotient.inductionOn with
    | h θ =>
    induction β using Quotient.inductionOn with
    | h θ' =>
    exact CompleteIntersections.AlgebraicNativeCI.degreeAlong_add_actual κ hg θ θ'
  map_smul' c α := by
    induction α using Quotient.inductionOn with
    | h θ =>
    exact CompleteIntersections.AlgebraicNativeCI.degreeAlong_smul_actual κ hg c θ

@[simp] theorem classDegreeAlong_ofRepresentative {C : Type} [TopologicalSpace C]
    [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C] [CompactSpace C]
    (κ : KahlerBackground 1 C) {g : C → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    (θ : ClosedRealOneOneForm (m + 1) Y) :
    classDegreeAlong κ hg (RealBottChern.ofRepresentative θ) = degreeAlong κ hg θ := rfl

/-- **Numerically trivial classes**: degree `0` along every holomorphic map from a compact
connected Riemann surface (equivalently `α · Γ = 0` for every irreducible curve `Γ ⊆ Y`). -/
def numericallyTrivialClasses : Submodule ℝ (RealBottChern (m + 1) Y) where
  carrier := {α | ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
    [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C)
    (g : C → Y) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
    classDegreeAlong κ hg α = 0}
  zero_mem' := by
    intro C _ _ _ _ _ κ g hg
    exact map_zero _
  add_mem' := by
    intro α β hα hβ C _ _ _ _ _ κ g hg
    rw [map_add, hα C κ g hg, hβ C κ g hg, add_zero]
  smul_mem' := by
    intro c α hα C _ _ _ _ _ κ g hg
    rw [map_smul, hα C κ g hg, smul_zero]

theorem ofRepresentative_mem_numericallyTrivialClasses_iff (θ : ClosedRealOneOneForm (m + 1) Y) :
    RealBottChern.ofRepresentative θ ∈ numericallyTrivialClasses ↔ IsNumericallyTrivial θ :=
  Iff.rfl

/-- **Cohomologically trivial classes are numerically trivial.** -/
theorem zero_mem_numericallyTrivialClasses_of_eq {α : RealBottChern (m + 1) Y} (h : α = 0) :
    α ∈ numericallyTrivialClasses := by
  rw [h]
  exact Submodule.zero_mem _

/-- **Injectivity of the cycle class map on numerical classes** (the curve half): on a compact
connected projective manifold, a class of `NS(Y)_ℝ` of degree `0` on every curve vanishes. -/
theorem eq_zero_of_mem_numericallyTrivialClasses [CompactSpace Y] [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) {α : RealBottChern (m + 1) Y}
    (hNS : α ∈ neronSeveri (m + 1) Y) (hnum : α ∈ numericallyTrivialClasses) : α = 0 := by
  induction α using Quotient.inductionOn with
  | h θ =>
  exact ofRepresentative_eq_zero_of_numericallyTrivial_of_isProjectiveManifold hY θ hNS
    ((ofRepresentative_mem_numericallyTrivialClasses_iff θ).mp hnum)

variable [CompactSpace Y]

/-- **Numerically trivial real divisors**: `D · C = 0` for every curve `C`. -/
def numericallyTrivialDivisors : Submodule ℝ (RealDivisor m Y) :=
  numericallyTrivialClasses.comap divisorClass

variable (m Y) in
/-- **The numerical space `N¹(Y)_ℝ`**: real divisors modulo numerical equivalence. -/
abbrev NumericalClasses := RealDivisor m Y ⧸ (numericallyTrivialDivisors (m := m) (Y := Y))

/-- **Numerically trivial ⇔ cohomologically trivial** for real divisors on a compact connected
projective manifold: the numerically trivial divisors are the kernel of the cycle class map. -/
theorem numericallyTrivialDivisors_eq_ker [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) :
    numericallyTrivialDivisors (m := m) (Y := Y) = LinearMap.ker divisorClass := by
  ext D
  rw [LinearMap.mem_ker]
  constructor
  · intro hD
    exact eq_zero_of_mem_numericallyTrivialClasses hY (divisorClass_mem_neronSeveri D)
      (Submodule.mem_comap.mp hD)
  · intro hD
    exact Submodule.mem_comap.mpr (zero_mem_numericallyTrivialClasses_of_eq hD)

/-- **`N¹(Y)_ℝ ≃ NS(Y)_ℝ`**: on a compact connected projective manifold the cycle class map
induces a linear isomorphism from the numerical classes of real divisors onto the Néron--Severi
space. -/
def numericalClassEquiv [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) :
    NumericalClasses m Y ≃ₗ[ℝ] neronSeveri (m + 1) Y :=
  (Submodule.quotEquivOfEq _ _ (numericallyTrivialDivisors_eq_ker hY)).trans
    ((LinearMap.quotKerEquivRange divisorClass).trans (LinearEquiv.ofEq _ _ range_divisorClass))

@[simp] theorem numericalClassEquiv_mk [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) (D : RealDivisor m Y) :
    (numericalClassEquiv hY (Submodule.Quotient.mk D) : RealBottChern (m + 1) Y) =
      divisorClass D := rfl

end Numerical

/-! ### Push-forward of divisors along modifications -/

section Pushforward

variable {m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y] {π : Y → X}

local notation "PrimeX" => SGPT.PSH.GeometricPrimeCarrier (m + 1) X
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- **The image prime divisor** `π(P)` of a prime divisor `P ⊄ Exc(π)`: the prime divisor of `X`
whose strict transform is `P`. -/
def primeImage (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeY)
    (hP : ¬ P.val ⊆ exceptionalLocus (m + 1) π) : PrimeX :=
  Classical.choose (PrimePushforward.exists_eq_strictTransformPrime hπ P hP)

omit [CompactSpace X] in
theorem strictTransformPrime_primeImage (hπ : IsAnalyticModification (n := m + 1) π)
    (P : PrimeY) (hP : ¬ P.val ⊆ exceptionalLocus (m + 1) π) :
    SGPT.Siu.strictTransformPrime hπ (primeImage hπ P hP) = P :=
  Classical.choose_spec (PrimePushforward.exists_eq_strictTransformPrime hπ P hP)

omit [CompactSpace X] in
/-- The carrier of `π(P)` is the image `π(P)`. -/
theorem primeImage_val (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeY)
    (hP : ¬ P.val ⊆ exceptionalLocus (m + 1) π) : (primeImage hπ P hP).val = π '' P.val := by
  conv_rhs => rw [← strictTransformPrime_primeImage hπ P hP]
  exact (SGPT.Siu.image_strictTransformPrime hπ _).symm

omit [CompactSpace X] [CompactSpace Y] in
/-- `π` is injective off its exceptional locus; in particular `π|_P : P → π(P)` is bimeromorphic
(of degree one) for a prime divisor `P ⊄ Exc(π)`. -/
theorem injOn_compl_exceptionalLocus (hπ : IsAnalyticModification (n := m + 1) π) :
    InjOn π (exceptionalLocus (m + 1) π)ᶜ := by
  obtain ⟨s, -, -, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hpre := AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hπ
  have hnot : ∀ z, z ∉ exceptionalLocus (m + 1) π →
      π z ∉ π '' exceptionalLocus (m + 1) π := fun z hz h => by
    have : z ∈ π ⁻¹' (π '' exceptionalLocus (m + 1) π) := h
    rw [hpre] at this
    exact hz this
  intro u hu v hv huv
  have h1 := hleft u (hnot u hu)
  have h2 := hleft v (hnot v hv)
  rw [← h1, ← h2, huv]

omit [CompactSpace X] [CompactSpace Y] in
/-- For a prime divisor `P ⊆ Exc(π)`, the image `π(P)` contains no prime divisor of `X` (it has
codimension at least two), so `π_* P = 0`. -/
theorem not_prime_subset_image_of_subset_exceptionalLocus
    (hπ : IsAnalyticModification (n := m + 1) π) {P : PrimeY}
    (hP : P.val ⊆ exceptionalLocus (m + 1) π) (Q : PrimeX) : ¬ Q.val ⊆ π '' P.val :=
  fun hQ => Modification4.not_prime_subset_image_exceptionalLocus hπ Q
    (hQ.trans (image_mono hP))

open Classical in
/-- **Push-forward of a prime divisor along a modification**: `π_* P = π(P)` if `P ⊄ Exc(π)`, and
`π_* P = 0` if `P ⊆ Exc(π)`. -/
def primePushforward (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeY) :
    RealDivisor m X :=
  if hP : P.val ⊆ exceptionalLocus (m + 1) π then 0 else Finsupp.single (primeImage hπ P hP) 1

/-- **Push-forward of real divisors** `π_* : Div(Y)_ℝ → Div(X)_ℝ` along a modification. -/
def divisorPushforward (hπ : IsAnalyticModification (n := m + 1) π) :
    RealDivisor m Y →ₗ[ℝ] RealDivisor m X :=
  Finsupp.linearCombination ℝ (primePushforward hπ)

/-- `π_* {[P]} = 0` for a prime divisor `P ⊆ Exc(π)`. -/
theorem classPushforward_cycleClass_of_subset (hπ : IsAnalyticModification (n := m + 1) π)
    {P : PrimeY} (hP : P.val ⊆ exceptionalLocus (m + 1) π) :
    classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (cycleClass (SGPT.Siu.primeEffectiveDivisor P)) = 0 := by
  rw [cycleClass, ← bottChernClass_closedCurrentPushforward]
  have hzero : closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (divisorCurrent (SGPT.Siu.primeEffectiveDivisor P)) = 0 := by
    apply Subtype.ext
    simp only [closedCurrentPushforward_val,
      SGPT.Projective.BDivNov16.divisorCurrent_prime_val, ZeroMemClass.coe_zero]
    exact PrimePushforward.currentPushforward_primeDivisorCurrent_eq_zero hπ P hP
  rw [hzero]
  exact (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_zero

/-- `π_* {[D̃]} = {[D]}` for the strict transform `D̃` of a prime divisor `D` of `X`. -/
theorem classPushforward_cycleClass_strictTransformPrime
    (hπ : IsAnalyticModification (n := m + 1) π) (Q : PrimeX) :
    classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (cycleClass (SGPT.Siu.primeEffectiveDivisor (SGPT.Siu.strictTransformPrime hπ Q))) =
      cycleClass (SGPT.Siu.primeEffectiveDivisor Q) := by
  rw [cycleClass, ← bottChernClass_closedCurrentPushforward]
  have hcurrent : closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (divisorCurrent (SGPT.Siu.primeEffectiveDivisor (SGPT.Siu.strictTransformPrime hπ Q))) =
        divisorCurrent (SGPT.Siu.primeEffectiveDivisor Q) := by
    apply Subtype.ext
    simp only [closedCurrentPushforward_val, SGPT.Projective.BDivNov16.divisorCurrent_prime_val]
    exact PrimePushforward.currentPushforward_primeDivisorCurrent_strictTransformPrime hπ Q
  rw [hcurrent]
  rfl

/-- `π_* {[P]} = cl(π_* P)` for every prime divisor `P` of `Y`. -/
theorem classPushforward_cycleClass_prime (hπ : IsAnalyticModification (n := m + 1) π)
    (P : PrimeY) :
    classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (cycleClass (SGPT.Siu.primeEffectiveDivisor P)) =
      divisorClass (primePushforward hπ P) := by
  classical
  by_cases hP : P.val ⊆ exceptionalLocus (m + 1) π
  · rw [classPushforward_cycleClass_of_subset hπ hP, primePushforward, dif_pos hP, map_zero]
  · rw [primePushforward, dif_neg hP, divisorClass_single, one_smul]
    conv_lhs => rw [← strictTransformPrime_primeImage hπ P hP]
    exact classPushforward_cycleClass_strictTransformPrime hπ _

/-- **Compatibility of the cycle class map with push-forward**: `cl(π_* D) = π_* cl(D)` for every
real divisor `D` on `Y` and every modification `π : Y → X`. -/
theorem divisorClass_divisorPushforward (hπ : IsAnalyticModification (n := m + 1) π)
    (D : RealDivisor m Y) :
    divisorClass (divisorPushforward hπ D) =
      classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) (divisorClass D) := by
  have h : (divisorClass (m := m) (Y := X)).comp (divisorPushforward hπ) =
      (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)).comp
        (divisorClass (m := m) (Y := Y)) := by
    apply Finsupp.lhom_ext
    intro P a
    simp only [LinearMap.comp_apply, divisorPushforward, Finsupp.linearCombination_single,
      map_smul, divisorClass_single, classPushforward_cycleClass_prime hπ P]
  exact LinearMap.congr_fun h D

/-- **Push-forward preserves numerical triviality** of real divisors on a compact connected
projective manifold `Y`. -/
theorem divisorPushforward_mem_numericallyTrivialDivisors [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (hπ : IsAnalyticModification (n := m + 1) π) {D : RealDivisor m Y}
    (hD : D ∈ numericallyTrivialDivisors) :
    divisorPushforward hπ D ∈ numericallyTrivialDivisors := by
  rw [numericallyTrivialDivisors_eq_ker hY] at hD
  refine Submodule.mem_comap.mpr ?_
  rw [divisorClass_divisorPushforward, LinearMap.mem_ker.mp hD, map_zero]
  exact Submodule.zero_mem _

/-- **The push-forward `π_* : N¹(Y)_ℝ → N¹(X)_ℝ` of numerical classes** along a modification,
`Y` compact connected projective. -/
def numericalPushforward [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (hπ : IsAnalyticModification (n := m + 1) π) :
    NumericalClasses m Y →ₗ[ℝ] NumericalClasses m X :=
  Submodule.mapQ _ _ (divisorPushforward hπ)
    fun _ hD => divisorPushforward_mem_numericallyTrivialDivisors hY hπ hD

@[simp] theorem numericalPushforward_mk [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (hπ : IsAnalyticModification (n := m + 1) π) (D : RealDivisor m Y) :
    numericalPushforward hY hπ (Submodule.Quotient.mk D) =
      Submodule.Quotient.mk (divisorPushforward hπ D) := rfl

/-- **Under `N¹ ≃ NS`, the push-forward of numerical classes is the push-forward of classes.** -/
theorem numericalClassEquiv_numericalPushforward [ConnectedSpace X] [ConnectedSpace Y]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (hπ : IsAnalyticModification (n := m + 1) π) (d : NumericalClasses m Y) :
    (numericalClassEquiv hX (numericalPushforward hY hπ d) : RealBottChern (m + 1) X) =
      classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (numericalClassEquiv hY d) := by
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  rw [numericalPushforward_mk, numericalClassEquiv_mk, numericalClassEquiv_mk,
    divisorClass_divisorPushforward]

/-- **Push-forward preserves the Néron--Severi spaces**: `π_* NS(Y)_ℝ ⊆ NS(X)_ℝ`. -/
theorem classPushforward_mem_neronSeveri_of_isAnalyticModification
    (hπ : IsAnalyticModification (n := m + 1) π)
    {α : RealBottChern (m + 1) Y} (hα : α ∈ neronSeveri (m + 1) Y) :
    classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) α ∈
      neronSeveri (m + 1) X := by
  rw [← range_divisorClass] at hα
  obtain ⟨D, rfl⟩ := hα
  rw [← divisorClass_divisorPushforward hπ]
  exact divisorClass_mem_neronSeveri _

end Pushforward

/-! ### Curve-nef classes -/

section Nef

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- **Curve-nef classes** (Dang--Favre's nef classes of `N¹(Y)_ℝ`, read through the cycle class
map): `α · C ≥ 0` for every holomorphic map from a compact connected Riemann surface. -/
def IsCurveNef (α : RealBottChern (m + 1) Y) : Prop :=
  ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C]
    [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C) (g : C → Y)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
    0 ≤ classDegreeAlong κ hg α

/-- **Nef classes are curve-nef**: if `α` is nef (`α + ε{ω}` has smooth semipositive
representatives for every `ε > 0`), then `α · C ≥ 0` for every curve. -/
theorem isCurveNef_of_classNef (omega : KahlerBackground (m + 1) Y) {α : RealBottChern (m + 1) Y}
    (hα : ClassNefWithRespectTo omega α) : IsCurveNef α := by
  induction α using Quotient.inductionOn with
  | h θ =>
  intro C _ _ _ _ _ κ g hg
  exact CompleteIntersections.AlgebraicNativeCI.degreeAlong_nonneg_of_nativeNef omega κ hg θ hα

/-- Curve-nef classes form a convex cone. -/
theorem IsCurveNef.add {α β : RealBottChern (m + 1) Y} (hα : IsCurveNef α) (hβ : IsCurveNef β) :
    IsCurveNef (α + β) := by
  intro C _ _ _ _ _ κ g hg
  rw [map_add]
  exact add_nonneg (hα C κ g hg) (hβ C κ g hg)

theorem IsCurveNef.smul {α : RealBottChern (m + 1) Y} (hα : IsCurveNef α) {c : ℝ} (hc : 0 ≤ c) :
    IsCurveNef (c • α) := by
  intro C _ _ _ _ _ κ g hg
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg hc (hα C κ g hg)

end Nef

end SGPT.BDivisor.DFAlg
