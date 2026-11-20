import SGPT.Hodge.ExceptionalIndependence
import SGPT.BDivisor.BlowupModel2Order
import SGPT.Foundations.Analysis.Pending.FiniteConnectedSmoothPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Okounkov.ThetaPotentialCurrentCombinations

/-!
# Exceptional classes and b-divisors of currents

Consequences of the independence of exceptional classes
(`SGPT.Hodge.Exceptional.exceptional_independence`) for the b-divisors `𝔻(T)` of chapter
*The theory of b-divisors*.

* `genericLelong_pull_eq_zero_of_not_subset`, `siuDivisorialPart_pull_eq_sum`,
  `divPullClass_eq_sum`: for a non-divisorial closed positive current `T` on `X` and a modification
  `π : Y → X`, the divisorial part of `π^*T` is the finite sum `∑_E ν(π^*T, E)[E]` over the
  `π`-exceptional prime divisors (`eq:RegpistarT`: `Reg π^*T = π^*T - ∑ ν(T, E)[E]`).
* `regPullClass_sub_eq_sum`: for non-divisorial `T, T'` with `{T} = {T'}`,
  `𝔻(T')_Y - 𝔻(T)_Y = ∑_E (ν(π^*T, E) - ν(π^*T', E)) {E}`.
* `genericLelong_pull_eq_of_regPullClass_eq`: if moreover `𝔻(T)_Y = 𝔻(T')_Y`, then
  `ν(π^*T, D) = ν(π^*T', D)` for every prime divisor `D` of `Y`.
* `sourceCurrentIOrder_of_forall_blowupModel`: the generic-Lelong-number criterion of the
  `𝓘`-order (`prop:Iequivchar2`) over the book's blow-up models.
* `currentBDivisor_injective` (**`thm:bdiv_current_corr`, injectivity**): for non-divisorial
  `T, T'` in the same class, `𝔻(T) = 𝔻(T')` implies `T ∼_𝓘 T'`.
* `currentPushforward_sourceCurrentIOrder` (**`lma:pushIpo`**): for a modification `π : Y → X` of
  compact manifolds, `Y` Kähler, and non-divisorial closed positive `T, S` on `Y` in the same class,
  `T ≼_𝓘 S` implies `π_*T ≼_𝓘 π_*S`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  SGPT.BDivisor SGPT.Currents.AnalyticSupport

section Pull

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))
local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- The finite set of `π`-exceptional prime divisors (the prime divisors contained in `Exc π`). -/
def excPrimes {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) : Finset PrimeY :=
  (finite_setOf_prime_subset
    (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1)
    (Modification4.interior_exceptionalLocus_eq_empty hπ)).toFinset

omit [CompactSpace X] in
theorem mem_excPrimes {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) {D : PrimeY} :
    D ∈ excPrimes hπ ↔ D.val ⊆ exceptionalLocus (m + 1) π := by
  rw [excPrimes, Set.Finite.mem_toFinset]
  rfl

/-- For a non-divisorial `T`, `ν(π^*T, D) = 0` along every non-exceptional prime divisor `D`
(`D` is a strict transform, and `ν(π^*T, D̃) = ν(T, D) = 0`). -/
theorem genericLelong_pull_eq_zero_of_not_subset {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurX} (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (hnd : SGPT.Siu.IsNonDivisorial T hT) (D : PrimeY)
    (hD : ¬ D.val ⊆ exceptionalLocus (m + 1) π) :
    SGPT.Siu.currentGenericLelong (Modification4.pull hπ T hT)
      (Modification4.isClosedPositiveCurrent_pull hπ hT) D = 0 := by
  obtain ⟨D₀, rfl⟩ := PrimePushforward.exists_eq_strictTransformPrime hπ D hD
  rw [currentGenericLelong_pull_strictTransformPrime hπ hT D₀]
  exact (SGPT.Siu.isNonDivisorial_iff hT).mp hnd D₀

/-- **`eq:RegpistarT`**: for a non-divisorial `T`, the divisorial part of `π^*T` is the finite sum
`∑_{E exceptional} ν(π^*T, E)[E]`. -/
theorem siuDivisorialPart_pull_eq_sum {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {T : CurX} (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hnd : SGPT.Siu.IsNonDivisorial T hT) :
    SGPT.Siu.siuDivisorialPart (Modification4.pull hπ T hT)
        (Modification4.isClosedPositiveCurrent_pull hπ hT) =
      ∑ D ∈ excPrimes hπ, (SGPT.Siu.currentGenericLelong (Modification4.pull hπ T hT)
        (Modification4.isClosedPositiveCurrent_pull hπ hT) D).toReal •
          SGPT.Siu.primeDivisorCurrent D := by
  classical
  set P := Modification4.pull hπ T hT
  have hP := Modification4.isClosedPositiveCurrent_pull hπ hT
  ext e η
  have h1 := SGPT.Siu.hasSum_siuDivisorialPart hP e η
  have h2 : HasSum (fun D : PrimeY =>
      ((SGPT.Siu.currentGenericLelong P hP D).toReal • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      (∑ D ∈ excPrimes hπ, ((SGPT.Siu.currentGenericLelong P hP D).toReal •
        SGPT.Siu.primeDivisorCurrent D).inChart e η) := by
    apply hasSum_sum_of_ne_finset_zero
    intro D hD
    rw [mem_excPrimes] at hD
    rw [genericLelong_pull_eq_zero_of_not_subset hπ hT hnd D hD, ENNReal.toReal_zero, zero_smul]
    rfl
  rw [h1.unique h2, SGPT.Siu.inChart_finsetSum]

theorem primeDivisorClass_eq (D : PrimeY) :
    primeDivisorClass D = bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨SGPT.Siu.primeDivisorCurrent D, (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).1,
        (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).2.1⟩ := rfl

/-- The class of a finite combination of currents of integration. -/
theorem bottChernClass_sum_primeDivisorCurrent (F : Finset PrimeY) (c : PrimeY → ℝ)
    (h1 : (∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D).IsClosed (canonicalBasis (m + 1)))
    (h2 : (∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D).IsTypeOneOne (canonicalBasis (m + 1))
      (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D, h1, h2⟩ =
      ∑ D ∈ F, c D • primeDivisorClass D := by
  have heq : (⟨∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D, h1, h2⟩ :
      ClosedOneOneCurrent (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
      ∑ D ∈ F, c D • ⟨SGPT.Siu.primeDivisorCurrent D,
        (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).1,
        (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).2.1⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    rfl
  rw [heq]
  change bottChernClassLinearMap (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_smul]
  rfl

end Pull

section Model

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- `{Div π^*T} = ∑_{E exceptional} ν(π^*T, E) {E}` for non-divisorial `T`. -/
theorem divPullClass_eq_sum (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hnd : SGPT.Siu.IsNonDivisorial T hT) :
    π.divPullClass T hT = ∑ D ∈ excPrimes π.isAnalyticModification,
      (SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T hT)
        (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT) D).toReal •
          primeDivisorClass D := by
  have h := siuDivisorialPart_pull_eq_sum π.isAnalyticModification hT hnd
  unfold Modification.divPullClass
  have hcl := (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT))
  rw [← bottChernClass_sum_primeDivisorCurrent _ _ (h ▸ hcl.1) (h ▸ hcl.2.1)]
  congr 1
  exact Subtype.ext h

/-- **`𝔻(T')_Y - 𝔻(T)_Y = ∑_E (ν(π^*T, E) - ν(π^*T', E)){E}`** for non-divisorial `T, T'` with
`{T} = {T'}` (the sum over the `π`-exceptional prime divisors). -/
theorem regPullClass_sub_eq_sum (π : Modification (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hnd : SGPT.Siu.IsNonDivisorial T hT) (hnd' : SGPT.Siu.IsNonDivisorial T' hT')
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T', hT'.1, hT'.2.1⟩) :
    π.regPullClass T' hT' - π.regPullClass T hT =
      ∑ D ∈ excPrimes π.isAnalyticModification,
        ((SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T hT)
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT) D).toReal -
        (SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T' hT')
          (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT') D).toReal) •
          primeDivisorClass D := by
  rw [π.regPullClass_eq hT, π.regPullClass_eq hT', hclass, divPullClass_eq_sum π hT hnd,
    divPullClass_eq_sum π hT' hnd']
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- **Equal b-divisor classes on a model give equal generic Lelong numbers**: for non-divisorial
`T, T'` in the same class with `𝔻(T)_Y = 𝔻(T')_Y`, `ν(π^*T, D) = ν(π^*T', D)` for every prime
divisor `D` of `Y` (by the independence of exceptional classes). -/
theorem genericLelong_pull_eq_of_regPullClass_eq (π : Modification (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hnd : SGPT.Siu.IsNonDivisorial T hT) (hnd' : SGPT.Siu.IsNonDivisorial T' hT')
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T', hT'.1, hT'.2.1⟩)
    (heq : π.regPullClass T hT = π.regPullClass T' hT')
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.carrier) :
    SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T hT)
        (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT) D =
      SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T' hT')
        (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT') D := by
  by_cases hD : D ∈ excPrimes π.isAnalyticModification
  · have h0 := regPullClass_sub_eq_sum π hT hT' hnd hnd' hclass
    rw [heq, sub_self] at h0
    have hc := exceptional_coeff_eq_zero π.isAnalyticModification _
      (fun E hE => (mem_excPrimes _).mp hE) _ h0.symm D hD
    rw [sub_eq_zero] at hc
    exact (ENNReal.toReal_eq_toReal_iff' (SGPT.Siu.currentGenericLelong_ne_top _ D)
      (SGPT.Siu.currentGenericLelong_ne_top _ D)).mp hc
  · rw [mem_excPrimes] at hD
    rw [genericLelong_pull_eq_zero_of_not_subset _ hT hnd D hD,
      genericLelong_pull_eq_zero_of_not_subset _ hT' hnd' D hD]

/-- **The generic-Lelong-number criterion of the `𝓘`-order over blow-up models**
(`prop:Iequivchar2`): if `ν(π^*T', D) ≤ ν(π^*T, D)` for every blow-up model `π : Y → X` (finite
composition of blow-ups with smooth centres) and every prime divisor `D` of `Y`, then
`T ≼_𝓘 T'`. -/
theorem sourceCurrentIOrder_of_forall_blowupModel {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hle : ∀ π : Modification (m + 1) X, π.IsBlowupModel →
      ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.carrier,
        SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T' hT')
            (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT') D ≤
          SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T hT)
            (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT) D) :
    SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T T' := by
  obtain ⟨θ, u, hu, hTeq⟩ := hT.exists_thetaPotential
  obtain ⟨σ, v, hv, hT'eq⟩ := hT'.exists_thetaPotential
  refine ⟨θ, σ, u, v, hu, hv, hTeq, hT'eq, ?_⟩
  apply (FiniteConnectedSmoothPrimeIdealOrder.iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right
    hu.1.quasiPlurisubharmonic hv.quasiPshPotential).mpr
  intro Y _ _ _ π hπ hseq E hcl hconn hhyper
  obtain ⟨k, hk, hreg⟩ := hhyper
  obtain ⟨V, hVE, hVdim⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
      (show IsClosedConnectedSubmanifold (m + 1) E k from ⟨hcl, hconn, hreg⟩)
  let ρ : Modification (m + 1) X := Modification.ofIsBlowupSequence hseq
  let Ep : SGPT.PSH.GeometricPrimeCarrier (m + 1) ρ.carrier := ⟨E, V, hVE, by omega⟩
  have h := hle ρ hseq Ep
  have hT1 := SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent
    (Modification4.isClosedPositiveCurrent_pull ρ.isAnalyticModification hT)
    (PrimePushforward.pull_eq_thetaPotentialCurrent ρ.isAnalyticModification hT hu hTeq)
  have hT2 := SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent
    (Modification4.isClosedPositiveCurrent_pull ρ.isAnalyticModification hT')
    (PrimePushforward.pull_eq_thetaPotentialCurrent ρ.isAnalyticModification hT' hv hT'eq)
  unfold SGPT.Siu.currentGenericLelong at h
  rw [hT1, hT2] at h
  exact (iInf_lelongNumber_le_iff_squaredLog (Nat.succ_ne_zero m) (fun w => u (π w))
    (fun w => v (π w)) E).mpr h

/-- **`thm:bdiv_current_corr`, injectivity**: for non-divisorial closed positive `(1,1)`-currents
`T, T'` on `X` with `{T} = {T'}`, if `𝔻(T) = 𝔻(T')` (over the book's blow-up models), then
`T ∼_𝓘 T'`. -/
theorem currentBDivisor_injective {T T' : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X}
    (hnd : SGPT.Siu.IsNonDivisorial T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
    (hnd' : SGPT.Siu.IsNonDivisorial T'.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T'))
    (hclass : SGPT.PSH.BookCurrent.currentClass T = SGPT.PSH.BookCurrent.currentClass T')
    (heq : currentBDivisor T = currentBDivisor T') :
    SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T.current T'.current ∧
      SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T'.current T.current := by
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  have hT' := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T'
  have hν : ∀ π : Modification (m + 1) X, π.IsBlowupModel →
      ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.carrier,
        SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T.current hT)
            (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT) D =
          SGPT.Siu.currentGenericLelong (Modification4.pull π.isAnalyticModification T'.current hT')
            (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT') D := by
    intro π hπ D
    have hmod : π.regPullClass T.current hT = π.regPullClass T'.current hT' := by
      have := congrArg (fun B => WeilBDivisorOn.onModel B ⟨π, hπ⟩) heq
      exact this
    exact genericLelong_pull_eq_of_regPullClass_eq π hT hT' hnd hnd' hclass hmod D
  exact ⟨sourceCurrentIOrder_of_forall_blowupModel hT hT' fun π hπ D => (hν π hπ D).ge,
    sourceCurrentIOrder_of_forall_blowupModel hT' hT fun π hπ D => (hν π hπ D).le⟩

end Model

section PushIpo

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

omit [CompactSpace X] in
theorem isClosedPositiveCurrent_sum (F : Finset PrimeY) (c : PrimeY → ℝ)
    (hc : ∀ D ∈ F, 0 ≤ c D) :
    SGPT.Siu.IsClosedPositiveCurrent (∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using SGPT.Siu.isClosedPositiveCurrent_zero
  | insert D F hD ih =>
    rw [Finset.sum_insert hD]
    exact ((SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).smul
      (hc D (Finset.mem_insert_self _ _))).add
      (ih fun E hE => hc E (Finset.mem_insert_of_mem hE))

omit [CompactSpace X] in
/-- A finite combination over `F ⊆ excPrimes` rewritten over all exceptional primes. -/
theorem sum_eq_sum_excPrimes {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    [DecidableEq PrimeY] (F : Finset PrimeY) (hF : ∀ D ∈ F, D.val ⊆ exceptionalLocus (m + 1) π)
    (c : PrimeY → ℝ) {V : Type*} [AddCommMonoid V] [Module ℝ V] (g : PrimeY → V) :
    ∑ D ∈ F, c D • g D =
      ∑ D ∈ excPrimes hπ, (if D ∈ F then c D else 0) • g D := by
  rw [← Finset.sum_subset (s₁ := F) (fun D hD => (mem_excPrimes hπ).mpr (hF D hD))]
  · exact Finset.sum_congr rfl fun D hD => by rw [if_pos hD]
  · intro D _ hD
    rw [if_neg hD, zero_smul]

/-- `{π^*π_*R} = π^*π_*{R}`. -/
theorem bottChernClass_pullPush {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {R : CurY} (hR : SGPT.Siu.IsClosedPositiveCurrent R) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨Modification4.pullPush hπ R hR, (Modification4.isClosedPositiveCurrent_pullPush hπ hR).1,
          (Modification4.isClosedPositiveCurrent_pullPush hπ hR).2.1⟩ =
      classPullback hπ.1 (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨R, hR.1, hR.2.1⟩)) := by
  rw [← bottChernClass_closedCurrentPushforward]
  exact PrimePushforward.bottChernClass_pull hπ
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hR)

/-- **`lma:pushIpo`**: let `π : Y → X` be a modification of compact complex manifolds with `Y`
connected Kähler, and `T, S` non-divisorial closed positive `(1,1)`-currents on `Y` in the same cohomology
class. If `T ≼_𝓘 S`, then `π_*T ≼_𝓘 π_*S`. -/
theorem currentPushforward_sourceCurrentIOrder [ConnectedSpace Y] (ωY : KahlerBackground (m + 1) Y)
    {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T S : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hS : SGPT.Siu.IsClosedPositiveCurrent S)
    (hTnd : SGPT.Siu.IsNonDivisorial T hT) (hSnd : SGPT.Siu.IsNonDivisorial S hS)
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩)
    (hI : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T S) :
    SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder (currentPushforward hπ.1 T)
      (currentPushforward hπ.1 S) := by
  classical
  let _ : MeasurableSpace Y := borel Y
  have _ : BorelSpace Y := ⟨rfl⟩
  -- Siu's pull–push: `π^*π_*T = T + F_T`, `π^*π_*S = S + F_S`
  obtain ⟨FT, cT, hFT, hPT⟩ := Modification4.pullback_pushforward_eq_add hπ hT hTnd
  obtain ⟨FS, cS, hFS, hPS⟩ := Modification4.pullback_pushforward_eq_add hπ hS hSnd
  set aT : PrimeY → ℝ := fun D => if D ∈ FT then cT D else 0 with haT
  set aS : PrimeY → ℝ := fun D => if D ∈ FS then cS D else 0 with haS
  have hsT := sum_eq_sum_excPrimes hπ FT (fun D hD => (hFT D hD).1) cT
    SGPT.Siu.primeDivisorCurrent
  have hsS := sum_eq_sum_excPrimes hπ FS (fun D hD => (hFS D hD).1) cS
    SGPT.Siu.primeDivisorCurrent
  have haT0 : ∀ D ∈ excPrimes hπ, 0 ≤ aT D := fun D _ => by
    simp only [haT]; split_ifs with h
    · exact (hFT D h).2.le
    · exact le_rfl
  have haS0 : ∀ D ∈ excPrimes hπ, 0 ≤ aS D := fun D _ => by
    simp only [haS]; split_ifs with h
    · exact (hFS D h).2.le
    · exact le_rfl
  have hPT' : Modification4.pullPush hπ T hT =
      T + ∑ D ∈ excPrimes hπ, aT D • SGPT.Siu.primeDivisorCurrent D := hPT.trans (by rw [hsT])
  have hPS' : Modification4.pullPush hπ S hS =
      S + ∑ D ∈ excPrimes hπ, aS D • SGPT.Siu.primeDivisorCurrent D := hPS.trans (by rw [hsS])
  -- classes: `{T} + ∑ aT {E} = {S} + ∑ aS {E}`
  have hDT := isClosedPositiveCurrent_sum (excPrimes hπ) aT haT0
  have hDS := isClosedPositiveCurrent_sum (excPrimes hπ) aS haS0
  have hcls : ∀ (R : CurY) (hR : SGPT.Siu.IsClosedPositiveCurrent R) (a : PrimeY → ℝ)
      (ha : SGPT.Siu.IsClosedPositiveCurrent
        (∑ D ∈ excPrimes hπ, a D • SGPT.Siu.primeDivisorCurrent D))
      (h : Modification4.pullPush hπ R hR =
        R + ∑ D ∈ excPrimes hπ, a D • SGPT.Siu.primeDivisorCurrent D),
      classPullback hπ.1 (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨R, hR.1, hR.2.1⟩)) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨R, hR.1, hR.2.1⟩ +
        ∑ D ∈ excPrimes hπ, a D • primeDivisorClass D := by
    intro R hR a ha h
    rw [← bottChernClass_pullPush hπ hR,
      ← bottChernClass_sum_primeDivisorCurrent _ _ ha.1 ha.2.1, ← bottChernClass_add']
    congr 1
    exact Subtype.ext h
  have hEq := (hcls T hT aT hDT hPT').symm.trans
    ((congrArg (fun α => classPullback hπ.1 (classPushforward hπ.1 (canonicalBasis (m + 1))
      (Nat.succ_pos m) α)) hclass).trans (hcls S hS aS hDS hPS'))
  rw [hclass, add_right_inj] at hEq
  have hdiff : ∑ D ∈ excPrimes hπ, (aT D - aS D) • primeDivisorClass D = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hEq, sub_self]
  have hcoef := exceptional_coeff_eq_zero hπ _ (fun E hE => (mem_excPrimes hπ).mp hE) _ hdiff
  have hDv : ∑ D ∈ excPrimes hπ, aT D • SGPT.Siu.primeDivisorCurrent D =
      ∑ D ∈ excPrimes hπ, aS D • SGPT.Siu.primeDivisorCurrent D :=
    Finset.sum_congr rfl fun D hD => by rw [sub_eq_zero.mp (hcoef D hD)]
  -- presentations upstairs with a common form
  obtain ⟨θ, u, hu, hTeq⟩ := hT.exists_thetaPotential
  have hSθ : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩ =
      RealBottChern.ofRepresentative θ := by
    rw [← hclass]
    have : (⟨T, hT.1, hT.2.1⟩ : ClosedOneOneCurrent (M := Y) (canonicalBasis (m + 1))
        (Nat.succ_pos m)) = thetaClosedCurrent θ u hu := Subtype.ext hTeq
    rw [this, bottChernClass_thetaClosedCurrent]
  obtain ⟨w, hw, hSeq, -⟩ := PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
    ⟨S, hS.1, hS.2.1⟩ θ hS.2.2 hSθ
  have huw := (SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder_iff_of_representation ωY hu hw
    hTeq hSeq).mp hI
  obtain ⟨Θ, ψ, hψ, hDeq⟩ := hDT.exists_thetaPotential
  obtain ⟨huψ, hcurT⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hψ
  obtain ⟨hwψ, hcurS⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hw hψ
  have hIup : IOrderOnManifold (n := m + 1) (fun x => u x + ψ x) (fun x => w x + ψ x) :=
    ActualMultiplierOrderAddition.iOrderOnManifold_add hu hψ hw hψ huw
      (IEnvelope.iOrderOnManifold_refl ψ)
  -- presentations downstairs
  have hTX := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT
  have hSX := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hS
  obtain ⟨θX, uX, huX, hTXeq⟩ := hTX.exists_thetaPotential
  obtain ⟨σX, vX, hvX, hSXeq⟩ := hSX.exists_thetaPotential
  have hpT : Modification4.pullPush hπ T hT = thetaPotentialCurrent
      (ClosedRealOneOneForm.pullback hπ.1 θX).val (fun y => uX (π y))
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ θX huX) :=
    PrimePushforward.pull_eq_thetaPotentialCurrent hπ hTX huX hTXeq
  have hpS : Modification4.pullPush hπ S hS = thetaPotentialCurrent
      (ClosedRealOneOneForm.pullback hπ.1 σX).val (fun y => vX (π y))
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ σX hvX) :=
    PrimePushforward.pull_eq_thetaPotentialCurrent hπ hSX hvX hSXeq
  have hpT2 : Modification4.pullPush hπ T hT =
      thetaPotentialCurrent (θ + Θ).val (fun x => u x + ψ x) huψ := by
    rw [hcurT, hPT', ← hTeq, ← hDeq]
  have hpS2 : Modification4.pullPush hπ S hS =
      thetaPotentialCurrent (θ + Θ).val (fun x => w x + ψ x) hwψ := by
    rw [hcurS, hPS', ← hSeq, ← hDv, ← hDeq]
  have hIpull : IOrderOnManifold (n := m + 1) (fun y => uX (π y)) (fun y => vX (π y)) :=
    (SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder_iff_of_representation ωY _ _ hpT hpS).mp
      ((SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder_iff_of_representation ωY huψ hwψ hpT2
        hpS2).mpr hIup)
  exact ⟨θX, σX, uX, vX, huX, hvX, hTXeq, hSXeq,
    (GenuineModificationIdealOrderInvariance.iOrder_iff_comp hπ huX.1.quasiPlurisubharmonic
      hvX.quasiPshPotential).mpr hIpull⟩

end PushIpo

end SGPT.Hodge.Exceptional
