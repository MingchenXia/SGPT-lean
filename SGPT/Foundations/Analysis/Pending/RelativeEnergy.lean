import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.Pending.MixedMass

set_option autoImplicit false

/-!
# Relative Monge--Ampere energy

This module begins the faithful construction of Xia's relative energy
`E_theta^phi` (SGPT, Definition 3.1.6, pages 0117--0118).  The first layer is
the actual endpoint mixed measure

`theta_u^j wedge theta_phi^(n-j)`.

It is assembled from the project's global mixed non-pluripolar measure; it is
not an abstract mass field.  The index `j : Fin (n + 1)` records the number of
copies of `u`.  Later definitions integrate the common-pole-corrected signed
difference `u - phi` against these measures and then extend the energy from
relatively minimal potentials to all relative potentials by an infimum over
relatively minimal majorants.

No geodesic or `d_S` object is introduced here: both depend on this energy.
-/

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.RelativeEnergy

open FirstPass
open FirstPass.PositiveClasses
open GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The tuple with `j` copies of `u` followed by `n-j` copies of `phi`.
This is the potential tuple underlying
`theta_u^j wedge theta_phi^(n-j)`. -/
def endpointMixedPotential (j : Fin (n + 1))
    (u phi : M → EReal) : Fin n → M → EReal :=
  fun i => if i.val < j.val then u else phi

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every component of the endpoint tuple is theta-plurisubharmonic. -/
theorem endpointMixedPotential_thetaPlurisubharmonic
    (theta : ClosedRealOneOneForm n M) (j : Fin (n + 1))
    (u phi : M → EReal) (hu : IsThetaPshPotential theta.val u)
    (hphi : IsThetaPshPotential theta.val phi) :
    ∀ i, ThetaPlurisubharmonic theta.val (endpointMixedPotential j u phi i) := by
  intro i
  by_cases h : i.val < j.val
  · simpa [endpointMixedPotential, h] using hu.1
  · simpa [endpointMixedPotential, h] using hphi.1

/-- The actual global mixed non-pluripolar measure
`theta_u^j wedge theta_phi^(n-j)`. -/
def endpointMixedMeasure (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) : Measure M :=
  globalMixedMeasure (fun _ : Fin n => theta)
    (endpointMixedPotential j u phi)
    (endpointMixedPotential_thetaPlurisubharmonic theta j u phi hu hphi)

omit [BorelSpace M] in
/-- The endpoint mixed measure is independent of the proof witnesses for the
two genuine theta-PSH potentials. -/
theorem endpointMixedMeasure_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi hphi' : IsThetaPshPotential theta.val phi)
    (hu hu' : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) :
    endpointMixedMeasure theta phi u hphi hu j =
      endpointMixedMeasure theta phi u hphi' hu' j := by
  unfold endpointMixedMeasure
  exact globalMixedMeasure_proof_independent
    (endpointMixedPotential_thetaPlurisubharmonic theta j u phi hu hphi)
    (endpointMixedPotential_thetaPlurisubharmonic theta j u phi hu' hphi')

/-- The whole-space mass of the actual endpoint mixed measure. -/
def endpointMixedMass (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) : ENNReal :=
  endpointMixedMeasure theta phi u hphi hu j Set.univ

omit [BorelSpace M] in
theorem endpointMixedMass_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi hphi' : IsThetaPshPotential theta.val phi)
    (hu hu' : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) :
    endpointMixedMass theta phi u hphi hu j =
      endpointMixedMass theta phi u hphi' hu' j := by
  exact congrArg (fun μ : Measure M => μ Set.univ)
    (endpointMixedMeasure_proof_independent theta phi u hphi hphi' hu hu' j)

/-- The `j`-th signed endpoint term in Xia's relative energy formula.  The
integrand is the ordinary real difference `u - phi` away from the common pole
locus and is zero on that locus. -/
def relativeEnergyTerm (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) : ℝ :=
  ∫ x, canonicalERealDiffToReal (u x) (phi x)
    ∂ endpointMixedMeasure theta phi u hphi hu j

omit [BorelSpace M] in
/-- The signed endpoint term is independent of theta-PSH proof witnesses. -/
theorem relativeEnergyTerm_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi hphi' : IsThetaPshPotential theta.val phi)
    (hu hu' : IsThetaPshPotential theta.val u) (j : Fin (n + 1)) :
    relativeEnergyTerm theta phi u hphi hu j =
      relativeEnergyTerm theta phi u hphi' hu' j := by
  unfold relativeEnergyTerm
  rw [endpointMixedMeasure_proof_independent theta phi u hphi hphi' hu hu' j]

/-- The finite-type relative Monge--Ampere energy

`E_theta^phi(u) = (1/(n+1)) sum_j integral (u-phi)
  theta_u^j wedge theta_phi^(n-j)`.

The source applies this formula to `RelativeEInfinity`; the definition itself
only needs the two genuine theta-PSH witnesses. -/
def relativeEnergyOfMinimalType (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u) : ℝ :=
  (∑ j : Fin (n + 1), relativeEnergyTerm theta phi u hphi hu j) /
    (n + 1 : ℝ)

omit [BorelSpace M] in
theorem relativeEnergyOfMinimalType_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi hphi' : IsThetaPshPotential theta.val phi)
    (hu hu' : IsThetaPshPotential theta.val u) :
    relativeEnergyOfMinimalType theta phi u hphi hu =
      relativeEnergyOfMinimalType theta phi u hphi' hu' := by
  unfold relativeEnergyOfMinimalType
  congr 1

omit [BorelSpace M] in
/-- The relative energy of the reference potential is zero. -/
@[simp] theorem relativeEnergyOfMinimalType_self
    (theta : ClosedRealOneOneForm n M) (phi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi) :
    relativeEnergyOfMinimalType theta phi phi hphi hphi = 0 := by
  simp [relativeEnergyOfMinimalType, relativeEnergyTerm]

/-- The set of finite-type majorant energies used to extend the relative
energy to `PSH(X, theta; phi)`.  Membership records an actual relatively
minimal majorant, rather than an abstract energy value. -/
def relativeEnergyMajorantValues (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsModelPotential theta phi) : Set EReal :=
  {e | ∃ (v : M → EReal) (hv : RelativeEInfinity theta phi v),
    u ≤ v ∧ e =
      (relativeEnergyOfMinimalType theta phi v hphi.plurisubharmonic
        hv.plurisubharmonic : EReal)}

/-- Xia's extended relative Monge--Ampere energy: the infimum of the actual
finite-type energies of all relatively minimal majorants. -/
def relativeMongeAmpereEnergy (theta : ClosedRealOneOneForm n M)
    (phi u : M → EReal) (hphi : IsModelPotential theta phi)
    (_hu : RelativePSH theta phi u) : EReal :=
  sInf (relativeEnergyMajorantValues theta phi u hphi)

omit [BorelSpace M] in
/-- Every relative potential has at least the reference potential as a
relatively minimal majorant, so the defining infimum is never over an empty
set. -/
theorem relativeEnergyMajorantValues_nonempty
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi : IsModelPotential theta phi) (hu : RelativePSH theta phi u) :
    (relativeEnergyMajorantValues theta phi u hphi).Nonempty := by
  refine ⟨(0 : ℝ), phi, ?_, hu.le_reference, ?_⟩
  · exact ⟨hphi.plurisubharmonic, SameSingularityTypeOn.refl phi Set.univ⟩
  · simp

omit [BorelSpace M] in
/-- The extended energy lies below the energy of every displayed relatively
minimal majorant. -/
theorem relativeMongeAmpereEnergy_le_of_majorant
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi) (hu : RelativePSH theta phi u)
    (hv : RelativeEInfinity theta phi v) (huv : u ≤ v) :
    relativeMongeAmpereEnergy theta phi u hphi hu ≤
      (relativeEnergyOfMinimalType theta phi v hphi.plurisubharmonic
        hv.plurisubharmonic : EReal) := by
  apply sInf_le
  exact ⟨v, hv, huv, rfl⟩

omit [BorelSpace M] in
/-- The extended energy is independent of the proof witnessing membership in
the relative PSH class. -/
theorem relativeMongeAmpereEnergy_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi u : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu hu' : RelativePSH theta phi u) :
    relativeMongeAmpereEnergy theta phi u hphi hu =
      relativeMongeAmpereEnergy theta phi u hphi hu' := by
  rfl

end

end SGPT.Foundations.Analysis.Pending.RelativeEnergy
