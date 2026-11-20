import SGPT.BDivisor.DFAlgNeronSeveri
import SGPT.BDivisor.BlowupModelSystem
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Bergman.SiuNativeProjectiveEquivalence
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.Pending.BlowupSequenceTotalTransform

/-!
# Blow-up models of a projective manifold are projective

Lane BD, blueprint `bd.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef
b-divisors are introduced by Dang--Favre [DF20] [...] our transcendental intersection theory
coincides with theirs in the algebraic setting."

Dang--Favre index b-divisor classes by the (projective) birational models of a projective
variety `X`. The book indexes b-divisors by the blow-up models of `X` (`def:modif`,
`SGPT.BDivisor.ModelSystem.blowup`). For the two theories to be compared model by model, every
blow-up model of a projective manifold must itself be projective, so that the numerical space
`N¹(Y)_ℝ` of each model is available and is identified with the Néron--Severi space
`NS(Y)_ℝ ⊆ H^{1,1}(Y, ℝ)` (`BDNumericalClasses.lean`). This file proves that projectivity.

* `meteredCurvature_mem_neronSeveri`: the curvature class `{Θ_E}` of **every** metered effective
  `ℚ`-divisor `E` on a compact manifold lies in `NS(Y)_ℝ` (an integral multiple `q E` metrizes an
  effective divisor, `exists_integralModel`).
* `exists_kahler_mem_neronSeveri_of_isBlowupSequence`: if `ω` is a Kähler form with
  `{ω} ∈ NS(X)_ℝ` and `π : Y → X` is a finite composition of blow-ups with smooth centres, then
  `Y` is compact and carries a Kähler form `π^*ω - Θ_E` (`E` an exceptional metered
  `ℚ`-divisor, `exists_exceptionalMetric`) whose class `π^*{ω} - {Θ_E}` lies in `NS(Y)_ℝ`.
* `isProjectiveManifold_of_isBlowupSequence`: **blow-ups of projective manifolds along smooth
  centres are projective** (through the projectivity criterion
  `isProjectiveManifold_iff_exists_kahler_mem_neronSeveri`).
* `blowup_model_isProjectiveManifold`: every model of the book's model system of a compact
  projective manifold is a compact projective manifold (connected if `X` is).
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
  SGPT.Foundations.Analysis.Pending

section Metered

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **The curvature class of every metered effective `ℚ`-divisor is algebraic**: for `E` a metered
effective `ℚ`-divisor on a compact complex manifold, `{Θ_E} ∈ NS(M)_ℝ`. Indeed some integral
multiple `q E` (`q > 0`) is a smooth metric on `𝒪(D)` for an effective divisor `D`, so
`q {Θ_E} = {Θ_{qE}} = cl(D)`. -/
theorem meteredCurvature_mem_neronSeveri (E : MeteredEffectiveQDivisor n M) :
    RealBottChern.ofRepresentative E.curvature ∈ neronSeveri n M := by
  obtain ⟨q, hq, D, hD⟩ := SGPT.Okounkov.TranscendentalLifting.exists_integralModel E
  have h := curvature_mem_neronSeveri hD
  rw [MeteredDivisorScaling.curvature_smul, RealBottChern.ofRepresentative_smul] at h
  have hq' : (((q : ℚ) : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < ((q : ℚ) : ℝ) := by exact_mod_cast hq
    exact this.ne'
  have h' := (neronSeveri n M).smul_mem (((q : ℚ) : ℝ))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hq', one_smul] at h'

end Metered

section Blowup

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **A Kähler class in the Néron--Severi space lifts to every blow-up model.** If `ω` is a
Kähler form on the compact manifold `X` with `{ω} ∈ NS(X)_ℝ` and `π : Y → X` is a finite
composition of blow-ups with smooth centres, then `Y` is compact and has a Kähler form whose class
lies in `NS(Y)_ℝ`, namely `π^*ω - Θ_E` for an exceptional metered `ℚ`-divisor `E`; its class is
`π^*{ω} - {Θ_E}`. -/
theorem exists_kahler_mem_neronSeveri_of_isBlowupSequence [CompactSpace X]
    (omega : ClosedRealOneOneForm n X) (hK : omega.val.IsKahler)
    (hNS : RealBottChern.ofRepresentative omega ∈ neronSeveri n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    CompactSpace Y ∧ ∃ omega' : ClosedRealOneOneForm n Y, omega'.val.IsKahler ∧
      RealBottChern.ofRepresentative omega' ∈ neronSeveri n Y := by
  obtain ⟨hY, E, -, hKE⟩ :=
    ExceptionalMetricProof.exists_exceptionalMetric_aux ⟨omega, hK⟩ hπ
  have := hY
  refine ⟨hY, _, hKE, ?_⟩
  have hpb : RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega) ∈ neronSeveri n Y := by
    rw [← SGPT.BDivisor.classPullback_ofRepresentative]
    exact classPullback_mem_neronSeveri hπ.contMDiff
      (BlowupSequenceTotalTransform.interior_exceptionalLocus_eq_empty_of_isBlowupSequence hπ) hNS
  have hE : RealBottChern.ofRepresentative E.curvature ∈ neronSeveri n Y :=
    meteredCurvature_mem_neronSeveri E
  change RealBottChern.ofRepresentative
    (ClosedRealOneOneForm.pullback hπ.contMDiff omega - E.curvature) ∈ neronSeveri n Y
  rw [sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg]
  exact (neronSeveri n Y).add_mem hpb ((neronSeveri n Y).neg_mem hE)

/-- **Blow-ups of projective manifolds along smooth centres are projective.** If `X` is a compact
projective manifold and `π : Y → X` is a finite composition of blow-ups with smooth centres, then
`Y` is a compact projective manifold. -/
theorem isProjectiveManifold_of_isBlowupSequence [CompactSpace X]
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    CompactSpace Y ∧ SGPT.Trace.Bertini.IsProjectiveManifold n Y := by
  obtain ⟨omega, hK, hNS⟩ :=
    SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hX
  obtain ⟨hY, omega', hK', hNS'⟩ :=
    exists_kahler_mem_neronSeveri_of_isBlowupSequence omega hK hNS hπ
  have := hY
  refine ⟨hY, ?_⟩
  exact SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mpr
    ⟨omega', hK', hNS'⟩

end Blowup

section Models

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **Every model of the book's model system of a projective manifold is a compact projective
manifold.** -/
theorem blowup_model_isProjectiveManifold (hX : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    (π : (ModelSystem.blowup n X).Model) :
    CompactSpace π.1.carrier ∧ SGPT.Trace.Bertini.IsProjectiveManifold n π.1.carrier :=
  isProjectiveManifold_of_isBlowupSequence (π := π.1.map) hX π.2

/-- The models of the book's model system of a connected projective manifold are connected. -/
theorem blowup_model_connectedSpace [ConnectedSpace X] (π : (ModelSystem.blowup n X).Model) :
    ConnectedSpace π.1.carrier :=
  Modification.IsBlowupModel.connectedSpace π.2

end Models

end SGPT.BDivisor.DFAlg
