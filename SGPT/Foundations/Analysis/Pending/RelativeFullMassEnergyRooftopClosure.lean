import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

set_option autoImplicit false

/-!
# The rooftop minimum of two finite-energy potentials has finite energy

Xia, SGPT, Proposition 3.1.21, `E¹` case (`xia-sgpt:page-0132`--`page-0134`):
if `u, v ∈ E¹(X, theta; phi)` then `P_theta(min(u, v)) ∈ E¹(X, theta; phi)`.

Xia's proof solves the relative Monge--Ampère equations of his Lemma 3.1.7 and
uses the relative energy `E_theta^phi`; neither exists in this project.  We use
instead the classical route through the contact sets (Darvas, *The Mabuchi
geometry of finite energy classes*, the proof that `E_p` is stable under
rooftop envelopes), whose two inputs are both already proved here:

* **concentration** (Xia, Theorem 2.4.4 for the minimum obstacle):
  `theta^n_w` puts no mass off `{w = u} ∪ {w = v}`, `w = P_theta(min(u, v))`
  (`RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero`);
* **contact comparison** (Xia, Lemma 2.4.2): since `w ≤ u`,
  `1_{w = u} theta^n_w ≤ 1_{w = u} theta^n_u`
  (`MaxMassDecomposition.contact_measure_le`).

On `{w = u}` the integrand `|phi - w|` is `|phi - u|`, so

  `∫ |phi - w| theta^n_w ≤ ∫_{w = u} |phi - u| theta^n_u + ∫_{w = v} |phi - v| theta^n_v`

(`relativeFiniteEnergyIntegral_rooftop_le`), which is finite.  The full-mass
half is `RelativeFullMass.relativeFullMass_rooftop` (it needs `0 < n`, the
Kähler background and the envelope lattice mass reduction, exactly as its
consumer `FiniteGeodesics.relativeFiniteEnergyIntegral_finite_finiteGeodesic`
supplies them).

The interface `RelativeFiniteEnergyOrderClosure.RelativeFiniteEnergy.rooftop`
states the same closure with none of these three hypotheses; it is NOT
discharged here and its statement is not touched.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending

open FirstPass
open FirstPass.PositiveClasses
open DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **The relative energy integral of a rooftop minimum is at most the sum of
those of the obstacles.**  `w = P_theta(min(u, v))`, assumed `theta`-PSH and
below both obstacles: `theta^n_w` lives on the contact sets, where it is
dominated by `theta^n_u`, resp. `theta^n_v`, and where `|phi - w|` is
`|phi - u|`, resp. `|phi - v|`. -/
theorem relativeFiniteEnergyIntegral_rooftop_le [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))))
    (hwu : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u)
    (hwv : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v) :
    relativeFiniteEnergyIntegral theta phi
        (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hw ≤
      relativeFiniteEnergyIntegral theta phi u hu +
        relativeFiniteEnergyIntegral theta phi v hv := by
  set w : M → EReal := rooftopEnvelope theta.val (fun x => min (u x) (v x)) with hwdef
  set μw := diagonalPotentialMeasure theta w hw with hμw
  set A : Set M := {x | w x = u x} with hAdef
  set B : Set M := {x | w x = v x} with hBdef
  have hwm : Measurable w := hw.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum : Measurable u := hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hA : MeasurableSet A := measurableSet_eq_fun hwm hum
  have hB : MeasurableSet B := measurableSet_eq_fun hwm hvm
  -- `theta^n_w` lives on `A ∪ B`
  have hN : μw {x | w x ≠ u x ∧ w x ≠ v x} = 0 :=
    RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero
      omega theta hu hv hw
  have hrestr : μw.restrict (A ∪ B) = μw := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null (fun x hx => ?_) hN
    have hx' : ¬ (x ∈ A ∪ B) := hx
    simp only [hAdef, hBdef, mem_union, mem_ofPred_eq, not_or] at hx'
    exact hx'
  -- contact comparison, as measures
  have hcmpA : μw.restrict A ≤ (diagonalPotentialMeasure theta u hu).restrict A := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact MaxMassDecomposition.contact_measure_le omega hw hu hwu hs
  have hcmpB : μw.restrict B ≤ (diagonalPotentialMeasure theta v hv).restrict B := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact MaxMassDecomposition.contact_measure_le omega hw hv hwv hs
  have hpieceA : ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw ≤
      relativeFiniteEnergyIntegral theta phi u hu := by
    calc ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw
        = ∫⁻ x in A, canonicalERealAbsDiff (phi x) (u x) ∂μw :=
          setLIntegral_congr_fun hA fun x hx => by
            simp only [hAdef, mem_ofPred_eq] at hx
            rw [hx]
      _ ≤ ∫⁻ x in A, canonicalERealAbsDiff (phi x) (u x)
            ∂(diagonalPotentialMeasure theta u hu) := lintegral_mono' hcmpA le_rfl
      _ ≤ relativeFiniteEnergyIntegral theta phi u hu := setLIntegral_le_lintegral _ _
  have hpieceB : ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw ≤
      relativeFiniteEnergyIntegral theta phi v hv := by
    calc ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw
        = ∫⁻ x in B, canonicalERealAbsDiff (phi x) (v x) ∂μw :=
          setLIntegral_congr_fun hB fun x hx => by
            simp only [hBdef, mem_ofPred_eq] at hx
            rw [hx]
      _ ≤ ∫⁻ x in B, canonicalERealAbsDiff (phi x) (v x)
            ∂(diagonalPotentialMeasure theta v hv) := lintegral_mono' hcmpB le_rfl
      _ ≤ relativeFiniteEnergyIntegral theta phi v hv := setLIntegral_le_lintegral _ _
  calc relativeFiniteEnergyIntegral theta phi w hw
      = ∫⁻ x, canonicalERealAbsDiff (phi x) (w x) ∂μw := rfl
    _ = ∫⁻ x in A ∪ B, canonicalERealAbsDiff (phi x) (w x) ∂μw := by rw [hrestr]
    _ ≤ ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw +
          ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add hpieceA hpieceB

/-- **Xia, Proposition 3.1.21, `E¹` case, in the Kähler form available here.**
The rooftop minimum of two relative finite-energy potentials is relative finite
energy.  The full-mass half is `relativeFullMass_rooftop` (hence the hypotheses
`hn`, `omega`, `hprojection`); the energy half is
`relativeFiniteEnergyIntegral_rooftop_le`. -/
theorem RelativeFiniteEnergy.rooftop_of_kahler [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : RelativeFiniteEnergy theta phi v hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    RelativeFiniteEnergy theta phi
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hphi := by
  obtain ⟨hwfull, hwu, hwv⟩ := relativeFullMass_rooftop hn omega theta phi u v hphi
    hu.fullMass hv.fullMass hprojection
  obtain ⟨hu', hufin⟩ := hu.2
  obtain ⟨hv', hvfin⟩ := hv.2
  refine ⟨hwfull, hwfull.plurisubharmonic, ?_⟩
  exact (relativeFiniteEnergyIntegral_rooftop_le omega theta hu' hv'
    hwfull.plurisubharmonic hwu hwv).trans_lt (ENNReal.add_lt_top.mpr ⟨hufin, hvfin⟩)

end

end SGPT.Foundations.Analysis.Pending
