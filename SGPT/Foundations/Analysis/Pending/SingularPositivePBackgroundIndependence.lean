import SGPT.Foundations.Analysis.Pending.SingularPositiveMassPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundTransport
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial

set_option autoImplicit false

/-! # Actual positive-mass P-order independence under Kähler enlargement -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularPositiveMassPEquivalence SingularPositivePBackgroundTransport
  SingularPBackgroundMassPolynomial CanonicalBackgroundPolynomial

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem pOrderWith_of_add_kahler (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hvpos : HasPositivePotentialMass θ v hv)
    (hnew : POrderWith (θ + omega.form) u v) : POrderWith θ u v := by
  let p := singularityEnvelope θ.val u
  let q := singularityEnvelope θ.val v
  let w : M → EReal := fun x => max (p x) (q x)
  have hp : IsThetaPshPotential θ.val p :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hq : IsThetaPshPotential θ.val q :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials v hv
  have hw : IsThetaPshPotential θ.val w := IsThetaPshPotential.max hp hq
  have hqpos : HasPositivePotentialMass θ q hq := by
    change 0 < diagonalPotentialMass θ q hq
    rw [singularityEnvelopeMassPreserving omega θ v hv hq]
    exact hvpos
  have hwpos : HasPositivePotentialMass θ w hw :=
    lt_of_lt_of_le hqpos (diagonalPotentialMass_mono_of_kahler omega hq hw
      (MoreSingularOn.of_le fun x _ => le_max_right _ _))
  have hb (f : M → EReal) :
      singularityEnvelope θ.val f ≤ singularityEnvelope (θ + omega.form).val f := by
    apply uscRegularization_mono
    apply sSup_le_sSup
    intro z hz
    exact ⟨⟨LocalPotentials.isThetaPshPotential_add_of_semipositive hz.1.1
      omega.isSemipositive, hz.1.2⟩, hz.2⟩
  have hwle : w ≤ singularityEnvelope (θ + omega.form).val v :=
    fun x => max_le ((hb u x).trans (hnew x)) (hb v x)
  have hw' := LocalPotentials.isThetaPshPotential_add_of_semipositive hw omega.isSemipositive
  have hq' := LocalPotentials.isThetaPshPotential_add_of_semipositive hq omega.isSemipositive
  have hv' := LocalPotentials.isThetaPshPotential_add_of_semipositive hv omega.isSemipositive
  have hwm : diagonalPotentialMass θ w hw ≤
      diagonalPotentialMass (θ + omega.form) w hw' := by
    have hs : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val w := by
      simpa only [one_smul] using hw'
    simpa only [one_smul] using
      AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
        omega.isSemipositive zero_lt_one hw hs
  have hqm : diagonalPotentialMass θ q hq ≤
      diagonalPotentialMass (θ + omega.form) q hq' := by
    have hs : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val q := by
      simpa only [one_smul] using hq'
    simpa only [one_smul] using
      AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
        omega.isSemipositive zero_lt_one hq hs
  have hvm : diagonalPotentialMass θ v hv ≤
      diagonalPotentialMass (θ + omega.form) v hv' := by
    have hs : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val v := by
      simpa only [one_smul] using hv'
    simpa only [one_smul] using
      AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
        omega.isSemipositive zero_lt_one hv hs
  have hwpos' : HasPositivePotentialMass (θ + omega.form) w hw' := lt_of_lt_of_le hwpos hwm
  have hqpos' : HasPositivePotentialMass (θ + omega.form) q hq' := lt_of_lt_of_le hqpos hqm
  have hvpos' : HasPositivePotentialMass (θ + omega.form) v hv' := lt_of_lt_of_le hvpos hvm
  have hbase : PEquivalentWith (θ + omega.form) w q := by
    constructor
    · change singularityEnvelope (θ + omega.form).val w ≤
        singularityEnvelope (θ + omega.form).val (singularityEnvelope θ.val v)
      rw [singularityEnvelope_comp_add_semipositive omega θ omega.form
        omega.isSemipositive hv hvpos]
      exact (singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hwle x)).trans_eq
        (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
          omega (θ + omega.form) v hv' hvpos')
    · exact singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => le_max_right _ _)
  have hmass : diagonalPotentialMass θ w hw = diagonalPotentialMass θ q hq := by
    apply globalMixedMass_eq_of_add_background_nat_eq omega
      (fun _ : Fin n => hw) (fun _ : Fin n => hq) 1 zero_lt_one
    intro N hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    let η := ((N : ℝ) - 1) • omega.form
    have hη : η.val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hNr)
    have hlarge : PEquivalentWith ((θ + omega.form) + η) w q :=
      ⟨pOrderWith_add_semipositive omega (θ + omega.form) η hη hw' hq' hwpos' hqpos' hbase.1,
        pOrderWith_add_semipositive omega (θ + omega.form) η hη hq' hw' hqpos' hwpos' hbase.2⟩
    have he := diagonalPotentialMass_eq_of_pEquivalentWith omega ((θ + omega.form) + η)
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hw' hη)
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hq' hη) hlarge
    have hθN : (θ + omega.form) + η = θ + (N : ℝ) • omega.form := by
      dsimp only [η]
      module
    simpa only [hθN, diagonalPotentialMass, diagonalPotentialMeasure,
      MixedMass.globalMixedMass] using he
  have hw0 : w ≤ 0 := fun x => max_le (singularityEnvelope_le_zero θ.val u x)
    (singularityEnvelope_le_zero θ.val v x)
  have hwq : w ≤ q :=
    (equalMassLeSingularityEnvelope omega θ q w hq hw hqpos hw0
      (MoreSingularOn.of_le fun x _ => le_max_right _ _) hmass.symm).trans_eq
        (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
          omega θ v hv hvpos)
  exact fun x => (le_max_left _ _).trans (hwq x)

/-- The genuine positive-mass forward composition and internally produced natural-tail mass identities, actual polynomial recovery and equal-mass domination give both directions of source Kähler-background independence. -/
theorem pOrderWith_add_kahler_iff (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv) :
    POrderWith (θ + omega.form) u v ↔ POrderWith θ u v :=
  ⟨pOrderWith_of_add_kahler omega θ hu hv hvpos,
    pOrderWith_add_semipositive omega θ omega.form omega.isSemipositive hu hv hupos hvpos⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundIndependence
