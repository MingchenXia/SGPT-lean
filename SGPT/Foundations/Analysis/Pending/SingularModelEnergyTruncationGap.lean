import SGPT.Foundations.Analysis.Pending.SingularModelEnergyEndpointBounds

set_option autoImplicit false

/-!
# Actual full-mass transfer of singular truncation-gap integrals

Xia SGPT PDF0121--0122, Proposition 3.1.17. Genuine same-type truncations
have actual reference mass and actual plurifine max locality. The resulting
equal tail masses transfer their actual canonical gap integral to the fixed
diagonal measure of a full-mass endpoint. Genuine pole nullity handles the
singular reference without a boundedness assumption.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncationGap

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativeEnergyIntegrability SingularModelEnergyTruncation GlobalNonPluripolar
  GlobalDiagonalScaling DiagonalMass MongeAmpereEnergyDecreasing

noncomputable section

/-- Off the reference pole, the actual canonical truncation-tail gap is the level. -/
theorem canonicalDiff_truncation_tail {a b : EReal} (hat : a ≠ ⊤) (hab : a ≠ ⊥)
    (j : ℕ) (hba : b ≤ a - ((j : ℝ) : EReal)) :
    canonicalERealDiffToReal a (max b (a - ((j : ℝ) : EReal))) = j := by
  rw [max_eq_right hba, ← EReal.coe_toReal hat hab, ← EReal.coe_sub,
    canonicalERealDiffToReal_coe_coe]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Produced genuine same-type truncations have the actual reference diagonal mass. -/
theorem diagonalPotentialMeasure_truncation_univ (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) (j : ℕ) :
    diagonalPotentialMeasure θ (truncation φ u j)
      (relativeEInfinity_truncation hφ hu huφ j).1 univ = diagonalPotentialMass θ φ hφ :=
  FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega
    (fun _ => (relativeEInfinity_truncation hφ hu huφ j).1)
    (fun _ => hφ) (fun _ => (relativeEInfinity_truncation hφ hu huφ j).2)

/-- Under the source full-mass hypothesis, the actual truncation gap integral
equals its integral against the actual fixed endpoint measure. -/
theorem integral_canonicalDiff_truncation_eq (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hfull : RelativeFullMass θ φ u hφ) (j : ℕ) :
    (∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
      ∂diagonalPotentialMeasure θ (truncation φ u j)
        (relativeEInfinity_truncation hφ.plurisubharmonic hfull.plurisubharmonic
          (MoreSingularOn.of_le fun x _ => hfull.le_reference x) j).1) =
    ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
      ∂diagonalPotentialMeasure θ u hfull.plurisubharmonic := by
  obtain ⟨hu, hule, hmass⟩ := hfull
  let huφ : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let htj := relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j
  let μ := diagonalPotentialMeasure θ u hu
  let μj := diagonalPotentialMeasure θ (truncation φ u j) htj.1
  let A := {x | φ x - ((j : ℝ) : EReal) < u x}
  let g := fun x => canonicalERealDiffToReal (φ x) (truncation φ u j x)
  change (∫ x, g x ∂μj) = ∫ x, g x ∂μ
  let : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure omega (fun _ => hu.1)
  let : IsFiniteMeasure μj := globalMixedMeasure_isFiniteMeasure omega (fun _ => htj.1.1)
  have hAm : MeasurableSet A :=
    FiniteEnergyCharacterization.measurableSet_lt_truncation hφ.plurisubharmonic.1 hu.1 j
  have hloc : μj.restrict A = μ.restrict A :=
    FiniteEnergyCharacterization.diagonalPotentialMeasure_truncation_restrict
      θ hφ.plurisubharmonic hu j htj.1
  have htotal : μj univ = μ univ :=
    (diagonalPotentialMeasure_truncation_univ omega θ hφ.plurisubharmonic hu huφ j).trans hmass.symm
  have hAeq : μj A = μ A := by
    rw [← Measure.restrict_apply_self, hloc, Measure.restrict_apply_self]
  have hcompl : μj.real Aᶜ = μ.real Aᶜ := by
    have ht : μj.real univ = μ.real univ := congrArg ENNReal.toReal htotal
    have ha : μj.real A = μ.real A := congrArg ENNReal.toReal hAeq
    linarith [measureReal_add_measureReal_compl (μ := μj) hAm,
      measureReal_add_measureReal_compl (μ := μ) hAm]
  have hint : Integrable g μ :=
    integrable_canonicalDiff_globalMixedMeasure omega hφ.plurisubharmonic.1 htj.1.1
      htj.2.symm (fun _ => hu.1)
  have hintj : Integrable g μj :=
    integrable_canonicalDiff_globalMixedMeasure omega hφ.plurisubharmonic.1 htj.1.1
      htj.2.symm (fun _ => htj.1.1)
  have hnonnull (ρ : Measure M) (hn : ρ {x | φ x = ⊥} = 0) :
      ∀ᵐ x ∂ρ, φ x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using hn
  have htail (ρ : Measure M) (hn : ∀ᵐ x ∂ρ, φ x ≠ ⊥) :
      (∫ x in Aᶜ, g x ∂ρ) = (j : ℝ) * ρ.real Aᶜ := by
    have heq : g =ᵐ[ρ.restrict Aᶜ] fun _ => (j : ℝ) := by
      filter_upwards [ae_restrict_of_ae hn, ae_restrict_mem hAm.compl] with x hx hxA
      exact canonicalDiff_truncation_tail (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
        hx j (not_lt.mp hxA)
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_comm]
  have htailj := htail μj (hnonnull μj
    (globalMixedMeasure_pole_null_of_nondegenerate (fun _ => htj.1.1) hφ.plurisubharmonic))
  have htailu := htail μ (hnonnull μ
    (globalMixedMeasure_pole_null_of_nondegenerate (fun _ => hu.1) hφ.plurisubharmonic))
  have hIA : (∫ x in A, g x ∂μj) = ∫ x in A, g x ∂μ := by rw [hloc]
  rw [← integral_add_compl hAm hintj, ← integral_add_compl hAm hint, hIA,
    htailj, htailu, hcompl]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncationGap
