import SGPT.Foundations.Analysis.Pending.MaximalPshVanishingMass
import SGPT.Foundations.Analysis.Pending.PolydiskSecondDifference

set_option autoImplicit false

/-!
# The Perron--Bremermann envelope solves the homogeneous Monge--Ampere equation

Putting `Pending.PolydiskPerronEnvelope` (the envelope is plurisubharmonic and
maximal) together with `Pending.MaximalPshVanishingMass` (a maximal semiconcave
potential carries no Bedford--Taylor mass): the Perron--Bremermann envelope of
continuous boundary data on the unit polydisk has vanishing Monge--Ampere
measure, once it is known to be semiconcave.

This is the *balayage* statement, in the local form Xia's Lemma 2.4.3 uses: the
solution of the Dirichlet problem on a ball has no Monge--Ampere mass inside.

The semiconcavity hypothesis is the one remaining input, Blocki's `C^{1,1}`
estimate (Theorem 2.3.2).  Its pluripotential half is proved in
`Pending.PolydiskSecondDifference.IsPerronData.secondDifference_perronEnvelope_le`;
what is missing is the Taylor estimate on the explicit Mobius family
`(a, h, zeta) ↦ T_{a,h} zeta`, which involves no pluripotential theory.

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Theorems 2.3.1 and 2.3.2; Bedford--Taylor, Invent.
Math. 37 (1976).
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- The open unit polydisk as an object of `Opens`. -/
def unitPolydiskOpens (n : ℕ) : Opens (ComplexModel n) :=
  ⟨unitPolydisk n, isOpen_unitPolydisk⟩

/-- The Perron--Bremermann envelope of continuous boundary data is a locally
bounded plurisubharmonic function on the polydisk: it is squeezed between the
data and any upper bound for the data. -/
theorem IsPerronData.isLocallyBoundedPshOn_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) :
    IsLocallyBoundedPshOn (unitPolydiskOpens n) (perronEnvelope v) := by
  obtain ⟨M, hM⟩ := hv.exists_bound
  refine ⟨hv.plurisubharmonicOn_perronEnvelope, fun z hz => ?_⟩
  refine ⟨unitPolydiskOpens n, hz, le_rfl, M, fun w hw => ?_⟩
  have hwc : w ∈ closedUnitPolydisk n := unitPolydisk_subset_closedUnitPolydisk hw
  have hup : perronEnvelope v w ≤ M :=
    hv.perronEnvelope_le_of_forall_le
      (fun x hx => le_trans (le_abs_self _) (hM x hx)) hw
  have hlow : -M ≤ perronEnvelope v w := by
    have h1 : -M ≤ v w := neg_le_of_abs_le (hM w hwc)
    exact le_trans h1 (hv.self_le_perronEnvelope hw)
  exact abs_le.mpr ⟨hlow, hup⟩

/-- **Balayage on the polydisk.**  A semiconcave Perron--Bremermann envelope
has no Bedford--Taylor mass: it solves the homogeneous Monge--Ampere equation. -/
theorem IsPerronData.eq_zero_of_isBTLimit_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v)
    (hsc : IsLocallySemiconcaveOn (unitPolydiskOpens n) (perronEnvelope v))
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (unitPolydiskOpens n) (fun _ => perronEnvelope v) μ) :
    μ = 0 :=
  eq_zero_of_isBTLimit_of_isMaximalPshOn hv.isLocallyBoundedPshOn_perronEnvelope
    hv.isMaximalPshOn_perronEnvelope hsc hμ

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
