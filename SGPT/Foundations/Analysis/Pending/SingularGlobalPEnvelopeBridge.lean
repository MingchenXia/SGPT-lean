import SGPT.Foundations.Analysis.Pending.SingularPEnvelopeMixedMassPreservation
import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

set_option autoImplicit false

/-! # Original-background envelopes, perturbed masses and genuine global P-order -/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge

open FirstPass FirstPass.PositiveClasses FirstPass.POrder GlobalNonPluripolar
  GlobalDiagonalScaling MixedMass MixedMassBoundedDifference CanonicalBackgroundPolynomial
  SingularPEnvelopeMixedMassPreservation SingularPBackgroundMassPolynomial
  SingularGlobalPOrder SingularPositiveCommonBackgroundExistence
  PluripolarCapacityDichotomy DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem singularityEnvelope_zero_kahler (omega : KahlerBackground n M) :
    singularityEnvelope omega.form.val (fun _ : M => (0 : EReal)) = (fun _ => 0) :=
  le_antisymm (singularityEnvelope_le_zero omega.form.val _)
    (self_le_singularityEnvelope (isThetaPshPotential_zero omega) le_rfl)

/-- Independent mixed envelope preservation applied to every actual selector
coefficient internally gives preservation after a positive background perturbation,
while the envelopes themselves are taken in the original backgrounds. -/
theorem globalMixedMass_add_background_original_envelopes_eq
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    {a : ℝ} (ha : 0 < a) :
    globalMixedMass (fun i => θ i + a • omega.form)
      (fun i => singularityEnvelope (θ i).val (u i))
      (fun i => (LocalPotentials.isThetaPshPotential_add_of_semipositive
        (singularityEnvelope_isThetaPshPotential (θ i).val (θ i).property.1
          (θ i).property.2 (hu i).1.hasSmoothLocalPotentials (u i) (hu i))
        (KahlerDomination.isSemipositive_smul omega.isSemipositive ha.le)).1) =
    globalMixedMass (fun i => θ i + a • omega.form) u
      (fun i => (isThetaPshPotential_add_background omega hu ha.le i).1) := by
  classical
  let P : Fin n → M → EReal := fun i => singularityEnvelope (θ i).val (u i)
  have hP : ∀ i, IsThetaPshPotential (θ i).val (P i) := fun i =>
    singularityEnvelope_isThetaPshPotential (θ i).val (θ i).property.1
      (θ i).property.2 (hu i).1.hasSmoothLocalPotentials (u i) (hu i)
  apply (ENNReal.toReal_eq_toReal_iff'
    (globalMixedMass_lt_top omega _).ne (globalMixedMass_lt_top omega _).ne).mp
  rw [globalMixedMass_add_background_toReal_eq_sum omega hP ha,
    globalMixedMass_add_background_toReal_eq_sum omega hu ha]
  apply Finset.sum_congr rfl
  intro g _
  have hUopt : ∀ i, IsThetaPshPotential
      (optForm omega θ (g i)).val (optPot u (g i)) := by
    intro i
    cases g i with
    | none => exact isThetaPshPotential_zero omega
    | some j => exact hu j
  have hPopt : ∀ i, IsThetaPshPotential
      (optForm omega θ (g i)).val (optPot P (g i)) := by
    intro i
    cases g i with
    | none => exact isThetaPshPotential_zero omega
    | some j => exact hP j
  have henv : (fun i => singularityEnvelope (optForm omega θ (g i)).val
      (optPot u (g i))) = (fun i => optPot P (g i)) := by
    funext i
    cases g i with
    | none => exact singularityEnvelope_zero_kahler omega
    | some j => rfl
  have hcoeff : globalMixedMass (fun i => optForm omega θ (g i))
      (fun i => optPot P (g i)) (fun i => (hPopt i).1) =
      globalMixedMass (fun i => optForm omega θ (g i))
        (fun i => optPot u (g i)) (fun i => (hUopt i).1) := by
    have hpres := globalMixedMass_singularityEnvelope_eq omega hUopt
    unfold globalMixedMass at hpres ⊢
    rw [globalMixedMeasure_congr rfl henv _ (fun i => (hPopt i).1)] at hpres
    exact hpres
  rw [hcoeff]

/-- The natural positive background, the produced perturbed mass identity and
the proved positive ordered criterion give global source equivalence even when
the original diagonal mass is zero. No original-background idempotence is used. -/
theorem sourcePEquivalent_singularityEnvelope (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    SourcePEquivalent (n := n) u (singularityEnvelope θ.val u) := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hu.1.hasSmoothLocalPotentials u hu
  have horder := sourcePOrder_of_moreSingularOn omega θ θ hu hP
    (moreSingularOn_singularityEnvelope hu)
  have huΘ : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  have hPΘ : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val
      (singularityEnvelope θ.val u) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hP
      (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  apply (sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder omega
    (θ + (1 : ℝ) • omega.form) huΘ hPΘ
    (hasPositivePotentialMass_add_smul omega hu zero_lt_one)
    (hasPositivePotentialMass_add_smul omega hP zero_lt_one) horder).mpr
  exact (globalMixedMass_add_background_original_envelopes_eq omega
    (fun _ : Fin n => hu) zero_lt_one).symm

/-- A comparison of the actual envelopes in the given background transports
to the actual existential positive-background source order, including zero
original masses, through the internally produced two envelope equivalences. -/
theorem sourcePOrder_of_pOrderWith (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (huv : POrderWith θ u v) : SourcePOrder (n := n) u v := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hu.1.hasSmoothLocalPotentials u hu
  have hQ := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hv.1.hasSmoothLocalPotentials v hv
  have henv := sourcePOrder_of_moreSingularOn omega θ θ hP hQ
    (MoreSingularOn.of_le fun x _ => huv x)
  exact ((sourcePEquivalent_singularityEnvelope omega θ hu).1.trans omega henv).trans
    omega (sourcePEquivalent_singularityEnvelope omega θ hv).2

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
