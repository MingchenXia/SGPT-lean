import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
import SGPT.Foundations.Analysis.Pending.SingularPEnvelopeMixedMassPreservation
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial

set_option autoImplicit false

/-! # Actual independent mixed mass equality from source P-equivalence -/

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

open FirstPass FirstPass.PositiveClasses FirstPass.POrder GlobalNonPluripolar
  GlobalDiagonalScaling MixedMass SingularGlobalPOrder SingularPositiveCommonBackgroundExistence
  SingularPEnvelopeMixedMassPreservation SingularPBackgroundMassPolynomial
  CanonicalBackgroundPolynomial

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Natural source P-equivalence internally produces all positive natural-tail mixed mass identities; genuine envelope preservation and actual polynomial recovery then produce the original mixed mass equality, including originally zero masses. -/
theorem globalMixedMass_eq_of_sourcePEquivalent (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, SourcePEquivalent (n := n) (u i) (v i)) :
    globalMixedMass θ u (fun i => (hu i).1) =
      globalMixedMass θ v (fun i => (hv i).1) := by
  apply globalMixedMass_eq_of_add_background_nat_eq omega hu hv 1 zero_lt_one
  intro N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  let θN : Fin n → ClosedRealOneOneForm n M := fun i => θ i + (N : ℝ) • omega.form
  have huN : ∀ i, IsThetaPshPotential (θN i).val (u i) :=
    isThetaPshPotential_add_background omega hu (Nat.cast_nonneg N)
  have hvN : ∀ i, IsThetaPshPotential (θN i).val (v i) :=
    isThetaPshPotential_add_background omega hv (Nat.cast_nonneg N)
  have hupN (i : Fin n) : DiagonalMass.HasPositivePotentialMass (θN i) (u i) (huN i) :=
    hasPositivePotentialMass_add_smul omega (hu i) hNp
  have hvpN (i : Fin n) : DiagonalMass.HasPositivePotentialMass (θN i) (v i) (hvN i) :=
    hasPositivePotentialMass_add_smul omega (hv i) hNp
  have henv : (fun i => singularityEnvelope (θN i).val (u i)) =
      (fun i => singularityEnvelope (θN i).val (v i)) := by
    funext i
    exact pEquivalentWith_iff_envelope_eq.mp
      ((sourcePEquivalent_iff_pEquivalentWith omega (θN i) (huN i) (hvN i)
        (hupN i) (hvpN i)).mp (huv i))
  have hPu : ∀ i, IsThetaPshPotential (θN i).val (singularityEnvelope (θN i).val (u i)) :=
    fun i => singularityEnvelope_isThetaPshPotential (θN i).val (θN i).property.1
      (θN i).property.2 (huN i).1.hasSmoothLocalPotentials (u i) (huN i)
  have hPv : ∀ i, IsThetaPshPotential (θN i).val (singularityEnvelope (θN i).val (v i)) :=
    fun i => singularityEnvelope_isThetaPshPotential (θN i).val (θN i).property.1
      (θN i).property.2 (hvN i).1.hasSmoothLocalPotentials (v i) (hvN i)
  calc
    globalMixedMass θN u (fun i => (huN i).1) =
        globalMixedMass θN (fun i => singularityEnvelope (θN i).val (u i))
          (fun i => (hPu i).1) := (globalMixedMass_singularityEnvelope_eq omega huN).symm
    _ = globalMixedMass θN (fun i => singularityEnvelope (θN i).val (v i))
          (fun i => (hPv i).1) := by
      unfold globalMixedMass
      rw [globalMixedMeasure_congr rfl henv (fun i => (hPu i).1) (fun i => (hPv i).1)]
    _ = globalMixedMass θN v (fun i => (hvN i).1) :=
      globalMixedMass_singularityEnvelope_eq omega hvN

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality
