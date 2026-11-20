import SGPT.BDivisor.BDDangFavreWeil

/-!
# Pull-back of divisors and Dang--Favre's Cartier classes

Lane BD, blueprint `bd.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef
b-divisors are introduced by Dang--Favre [DF20] [...] our transcendental intersection theory
coincides with theirs in the algebraic setting."

Dang--Favre's Cartier b-divisor classes are the Weil classes *determined* on some model `Y` by a
numerical class `c ∈ N¹(Y)_ℝ`: their incarnation on every model `Y'` dominating `Y` is the
pull-back `g^* c` of `c` (pull-back of Cartier divisors, i.e. total transform). Their nef Cartier
classes are those with `c` nef (in Dang--Favre's sense: `c · C ≥ 0` for every curve).

* `primePullback`, `divisorPullback` (with `pullbackExceptionalPrimes`,
  `pullbackExceptionalCoeff`, `pull_primeDivisorCurrent_eq_exceptional`): the total transform
  `g^*P = P̃ + ∑_E c_E E` of a prime
  divisor along a modification (`P̃` the strict transform, `E` exceptional, `c_E ≥ 0` the
  generic Lelong number of `g^*[P]` along `E`, i.e. the vanishing order of `g^* s_P`).
* `divisorClass_divisorPullback`: **`cl(g^* D) = g^* cl(D)`**.
* `numericalPullback`, `numericalClassEquiv_numericalPullback`: the pull-back of numerical
  classes, corresponding to the pull-back of classes under `N¹ ≃ NS`.
* `isDeterminedOn_iff_isRealizationAny`: a Dang--Favre Weil class is determined on the model `π`
  by `c` iff its image under `dangFavreWeilEquiv` is realized on `π` by `cl(c)`
  (`IsRealizationAny`): **Dang--Favre's Cartier classes are the algebraic Cartier
  b-divisors**.
* `isAlgebraicAny_of_isRealizationAny`, `IsAlgNefCartierAny.isAlgebraicAny`: a b-divisor realized
  on a model by a class of `NS(Y)_ℝ` is algebraic.
* `exists_dangFavreNefCartier_of_isAlgNefCartierAny`: every algebraic nef Cartier b-divisor
  (`IsAlgNefCartierAny`) is the image of a Dang--Favre nef Cartier class. The converse is
  Kleiman's criterion (curve-nef classes of `NS(Y)_ℝ` are nef), not formalized here.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.DFAlg

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Hodge.BDivChain.NativeDraft

/-! ### Pull-back of divisors along a modification -/

section Pullback

variable {m : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y] {π : Y → X}

local notation "PrimeX" => SGPT.PSH.GeometricPrimeCarrier (m + 1) X
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- The finitely many exceptional prime divisors `E` occurring in the total transform `π^* P`. -/
def pullbackExceptionalPrimes (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeX) :
    Finset PrimeY :=
  (PrimePushforward.pull_primeDivisorCurrent_eq hπ P).choose

/-- The coefficients `c_E = ν(π^*[P], E)` of the exceptional part of `π^* P`. -/
def pullbackExceptionalCoeff (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeX) :
    PrimeY → ℝ :=
  (PrimePushforward.pull_primeDivisorCurrent_eq hπ P).choose_spec.choose

/-- The exceptional coefficients are nonnegative and supported on exceptional prime divisors. -/
theorem pullbackExceptional_spec (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeX) :
    ∀ E ∈ pullbackExceptionalPrimes hπ P,
      E.val ⊆ exceptionalLocus (m + 1) π ∧ 0 ≤ pullbackExceptionalCoeff hπ P E :=
  (PrimePushforward.pull_primeDivisorCurrent_eq hπ P).choose_spec.choose_spec.1

/-- `π^*[P] = [P̃] + ∑_E c_E [E]`. -/
theorem pull_primeDivisorCurrent_eq_exceptional (hπ : IsAnalyticModification (n := m + 1) π)
    (P : PrimeX) :
    Modification4.pull hπ (SGPT.Siu.primeDivisorCurrent P)
        (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent P) =
      SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ P) +
        ∑ E ∈ pullbackExceptionalPrimes hπ P,
          pullbackExceptionalCoeff hπ P E • SGPT.Siu.primeDivisorCurrent E :=
  (PrimePushforward.pull_primeDivisorCurrent_eq hπ P).choose_spec.choose_spec.2

/-- **The total transform** `π^* P = P̃ + ∑_E c_E E` of a prime divisor `P` of `X` along a
modification `π : Y → X`: `P̃` is the strict transform, the `E` are finitely many prime divisors
contained in the exceptional locus, `c_E = ν(π^*[P], E) ≥ 0` (the vanishing order of `π^* s_P`
along `E`). -/
def primePullback (hπ : IsAnalyticModification (n := m + 1) π) (P : PrimeX) : RealDivisor m Y :=
  Finsupp.single (SGPT.Siu.strictTransformPrime hπ P) 1 +
    ∑ E ∈ pullbackExceptionalPrimes hπ P, Finsupp.single E (pullbackExceptionalCoeff hπ P E)

/-- **`π^* {[P]} = cl(π^* P)`** for a prime divisor `P` of `X`. -/
theorem classPullback_cycleClass_prime (hπ : IsAnalyticModification (n := m + 1) π)
    (P : PrimeX) :
    SGPT.BDivisor.classPullback hπ.1 (cycleClass (SGPT.Siu.primeEffectiveDivisor P)) =
      divisorClass (primePullback hπ P) := by
  classical
  have hE := (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor P)).choose_spec.2
  have hG : IsThetaPshPotential
      (MeteredDivisorOperations.pullback hπ.1 (Modification4.interior_exceptionalLocus_eq_empty hπ)
        (PrimePushforward.primeMetric P)).curvature.val
      (MeteredDivisorOperations.pullback hπ.1 (Modification4.interior_exceptionalLocus_eq_empty hπ)
        (PrimePushforward.primeMetric P)).weight :=
    SGPT.Okounkov.TranscendentalLifting.isThetaPshPotential_weight _
  -- the class of the pulled-back metric
  have h1 : SGPT.BDivisor.classPullback hπ.1 (cycleClass (SGPT.Siu.primeEffectiveDivisor P)) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (thetaClosedCurrent _ _ hG) := by
    rw [bottChernClass_thetaClosedCurrent, cycleClass_eq_of_isDivisorMetric _ _ hE,
      SGPT.BDivisor.classPullback_ofRepresentative]
    rfl
  -- the current of the pulled-back metric is `π^*[P] = [P̃] + ∑ c_E [E]`
  have h2 : thetaClosedCurrent _ _ hG =
      divisorCurrent (SGPT.Siu.primeEffectiveDivisor (SGPT.Siu.strictTransformPrime hπ P)) +
        ∑ E ∈ pullbackExceptionalPrimes hπ P,
          pullbackExceptionalCoeff hπ P E • divisorCurrent (SGPT.Siu.primeEffectiveDivisor E) := by
    apply Subtype.ext
    change thetaPotentialCurrent _ _ hG = _
    rw [PrimePushforward.thetaPotentialCurrent_eq_integrationCurrent _ hG,
      ← PrimePushforward.pull_primeDivisorCurrent hπ P, pull_primeDivisorCurrent_eq_exceptional]
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      SGPT.Projective.BDivNov16.divisorCurrent_prime_val]
  rw [h1, h2, primePullback, map_add, map_sum, divisorClass_single, one_smul]
  change bottChernClassLinearMap (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m) _ = _
  rw [map_add, map_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun E _ => ?_)
  rw [map_smul, divisorClass_single]
  rfl

/-- **Pull-back of real divisors** `π^* : Div(X)_ℝ → Div(Y)_ℝ` (total transform). -/
def divisorPullback (hπ : IsAnalyticModification (n := m + 1) π) :
    RealDivisor m X →ₗ[ℝ] RealDivisor m Y :=
  Finsupp.linearCombination ℝ (primePullback hπ)

/-- **Compatibility of the cycle class map with pull-back**: `cl(π^* D) = π^* cl(D)`. -/
theorem divisorClass_divisorPullback (hπ : IsAnalyticModification (n := m + 1) π)
    (D : RealDivisor m X) :
    divisorClass (divisorPullback hπ D) = SGPT.BDivisor.classPullback hπ.1 (divisorClass D) := by
  have h : (divisorClass (m := m) (Y := Y)).comp (divisorPullback hπ) =
      (SGPT.BDivisor.classPullback hπ.1).comp (divisorClass (m := m) (Y := X)) := by
    apply Finsupp.lhom_ext
    intro P a
    simp only [LinearMap.comp_apply, divisorPullback, Finsupp.linearCombination_single,
      map_smul, divisorClass_single, classPullback_cycleClass_prime hπ P]
  exact LinearMap.congr_fun h D

/-- **Pull-back preserves numerical triviality** of real divisors on a compact connected projective
manifold `X`. -/
theorem divisorPullback_mem_numericallyTrivialDivisors [ConnectedSpace X]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (hπ : IsAnalyticModification (n := m + 1) π) {D : RealDivisor m X}
    (hD : D ∈ numericallyTrivialDivisors) :
    divisorPullback hπ D ∈ numericallyTrivialDivisors := by
  rw [numericallyTrivialDivisors_eq_ker hX] at hD
  refine Submodule.mem_comap.mpr ?_
  rw [divisorClass_divisorPullback, LinearMap.mem_ker.mp hD, map_zero]
  exact Submodule.zero_mem _

/-- **The pull-back `π^* : N¹(X)_ℝ → N¹(Y)_ℝ` of numerical classes** along a modification, `X`
compact connected projective. -/
def numericalPullback [ConnectedSpace X]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (hπ : IsAnalyticModification (n := m + 1) π) :
    NumericalClasses m X →ₗ[ℝ] NumericalClasses m Y :=
  Submodule.mapQ _ _ (divisorPullback hπ)
    fun _ hD => divisorPullback_mem_numericallyTrivialDivisors hX hπ hD

@[simp] theorem numericalPullback_mk [ConnectedSpace X]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (hπ : IsAnalyticModification (n := m + 1) π) (D : RealDivisor m X) :
    numericalPullback hX hπ (Submodule.Quotient.mk D) =
      Submodule.Quotient.mk (divisorPullback hπ D) := rfl

/-- **Under `N¹ ≃ NS`, the pull-back of numerical classes is the pull-back of classes.** -/
theorem numericalClassEquiv_numericalPullback [ConnectedSpace X] [ConnectedSpace Y]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (hπ : IsAnalyticModification (n := m + 1) π) (d : NumericalClasses m X) :
    (numericalClassEquiv hY (numericalPullback hX hπ d) : RealBottChern (m + 1) Y) =
      SGPT.BDivisor.classPullback hπ.1 (numericalClassEquiv hX d) := by
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  rw [numericalPullback_mk, numericalClassEquiv_mk, numericalClassEquiv_mk,
    divisorClass_divisorPullback]

end Pullback

/-! ### Dang--Favre's Cartier classes -/

section Cartier

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **Dang--Favre Cartier classes**: the Weil class `d` is determined on the model `π` by the
numerical class `c ∈ N¹(Y_π)_ℝ`, i.e. `d_{π'} = g^* c` for every model `π'` dominating `π`
(`g : Y_{π'} → Y_π` the dominating morphism). -/
def IsDeterminedOn (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model)
    (c : NumericalClasses m π.1.carrier) : Prop :=
  ∀ (π' : (ModelSystem.blowup (m + 1) X).Model) (h : π ≤ π'),
    d.1 π' = numericalPullback (blowup_model_isProjective hX π)
      (Modification.Dominates.isAnalyticModification (show π.1 ≤ π'.1 from h)) c

/-- **Dang--Favre's Cartier classes are the algebraic Cartier b-divisors**: `d` is determined on
`π` by `c` iff its image `dangFavreWeilEquiv hX d` is realized on `π` by the class `cl(c)`. -/
theorem isDeterminedOn_iff_isRealizationAny
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model)
    (c : NumericalClasses m π.1.carrier) :
    IsDeterminedOn hX d π c ↔
      IsRealizationAny (dangFavreWeilEquiv hX d).1 π
        (numericalClassEquiv (blowup_model_isProjective hX π) c) := by
  unfold IsDeterminedOn IsRealizationAny
  refine forall₂_congr fun π' h => ⟨fun hd => ?_, fun hr => ?_⟩
  · show (numericalClassEquiv (blowup_model_isProjective hX π') (d.1 π') :
      RealBottChern (m + 1) π'.1.carrier) = _
    rw [hd, numericalClassEquiv_numericalPullback (blowup_model_isProjective hX π)
      (blowup_model_isProjective hX π')]
    rfl
  · apply (numericalClassEquiv (blowup_model_isProjective hX π')).injective
    apply Subtype.ext
    rw [numericalClassEquiv_numericalPullback (blowup_model_isProjective hX π)
      (blowup_model_isProjective hX π')]
    exact hr

omit [ConnectedSpace X] in
/-- A b-divisor realized on a model by a class of the Néron--Severi space is algebraic: its
incarnations above the model are pull-backs, and the others push-forwards of those. -/
theorem isAlgebraicAny_of_isRealizationAny
    {C : WeilFamilyAny (ModelSystem.blowup (m + 1) X)} {π : (ModelSystem.blowup (m + 1) X).Model}
    {α : RealBottChern (m + 1) π.1.carrier} (hα : α ∈ neronSeveri (m + 1) π.1.carrier)
    (hC : IsRealizationAny C π α) : IsAlgebraicAny C := by
  intro π''
  obtain ⟨ρ, hπρ, hπ''ρ⟩ := ModelSystem.Model.exists_le_le π π''
  have hρ : C.1 ρ ∈ neronSeveri (m + 1) ρ.1.carrier := by
    rw [hC ρ hπρ]
    exact classPullbackOfLE_mem_neronSeveri _ hα
  rw [← C.2 π'' ρ hπ''ρ, classPushforwardAny_eq π'' ρ hπ''ρ]
  exact classPushforward_mem_neronSeveri_of_isAnalyticModification
    (Modification.Dominates.isAnalyticModification (show π''.1 ≤ ρ.1 from hπ''ρ)) hρ

omit [ConnectedSpace X] in
/-- Algebraic nef Cartier b-divisors are algebraic. -/
theorem IsAlgNefCartierAny.isAlgebraicAny {C : WeilFamilyAny (ModelSystem.blowup (m + 1) X)}
    (hC : IsAlgNefCartierAny C) : IsAlgebraicAny C := by
  obtain ⟨π, α, hα, hr, -⟩ := hC
  exact isAlgebraicAny_of_isRealizationAny hα hr

/-- **Algebraic nef Cartier b-divisors come from Dang--Favre nef Cartier classes**: if
`IsAlgNefCartierAny C`, then `C` is the image under `dangFavreWeilEquiv` of a Dang--Favre Weil
class determined on some model `π` by a numerical class `c` which is nef in Dang--Favre's sense
(`cl(c) · Γ ≥ 0` for every curve `Γ`), and even nef in the sense of `def:nef`. -/
theorem exists_dangFavreNefCartier_of_isAlgNefCartierAny
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    {C : WeilFamilyAny (ModelSystem.blowup (m + 1) X)} (hC : IsAlgNefCartierAny C) :
    ∃ (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model)
      (c : NumericalClasses m π.1.carrier),
      (dangFavreWeilEquiv hX d).1 = C ∧ IsDeterminedOn hX d π c ∧
        IsCurveNef (numericalClassEquiv (blowup_model_isProjective hX π) c :
          RealBottChern (m + 1) π.1.carrier) ∧
        ∃ κ : KahlerBackground (m + 1) π.1.carrier,
          ClassNefWithRespectTo κ (numericalClassEquiv (blowup_model_isProjective hX π) c :
            RealBottChern (m + 1) π.1.carrier) := by
  have hA : IsAlgebraicAny C := hC.isAlgebraicAny
  obtain ⟨π, α, hα, hr, κ, hnef⟩ := hC
  set d := (dangFavreWeilEquiv hX).symm ⟨C, hA⟩
  set c := (numericalClassEquiv (blowup_model_isProjective hX π)).symm ⟨α, hα⟩
  have hdC : (dangFavreWeilEquiv hX d).1 = C := by
    rw [LinearEquiv.apply_symm_apply]
  have hcα : (numericalClassEquiv (blowup_model_isProjective hX π) c :
      RealBottChern (m + 1) π.1.carrier) = α := by
    rw [LinearEquiv.apply_symm_apply]
  refine ⟨d, π, c, hdC, ?_, ?_, κ, ?_⟩
  · rw [isDeterminedOn_iff_isRealizationAny, hdC, hcα]
    exact hr
  · rw [hcα]
    exact isCurveNef_of_classNef κ hnef
  · rw [hcα]
    exact hnef

end Cartier

end SGPT.BDivisor.DFAlg
