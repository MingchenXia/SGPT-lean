import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

set_option autoImplicit false

/-!
# Two elementary comparisons of potentials, below the rooftop layer

Re-layering for Boucksom 4.8 (TN.4 #1; TN-CLASSICAL run 0159 r2).  Boucksom's proof of 4.8
(`BoucksomResolutionAssembly`, `UniformNefCore`, proved in `UniformAmbientVolumeBignessInterface`)
used two elementary lemmas from modules that sit above the rooftop / envelope layer, and through them
its import closure contained `BoucksomNonBigSupremumMass`, whose named input is a CONSEQUENCE of
Boucksom 4.8 (I-0902 item 1).  To prove that input from Boucksom 4.8 without an import cycle, the two
lemmas are restated here on top of their (low) ingredients, with the same statements and proofs:

* `isThetaPshPotential_smul` (= `RestrictedApproximantComparison.isThetaPshPotential_smul`): a positive
  multiple of a `θ`-psh potential is a `(c θ)`-psh potential;
* `diagonalPotentialMass_le_of_le_add_smul` (= `DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul`,
  Copy-4 `eq:dom-mass`, one term): `v ∈ PSH(θ)`, `w ∈ PSH(θ + εω)`, `v ≤ w` give
  `∫θ_v^k ≤ ∫(θ + εω)_w^k`.

Neither module that states them originally is changed.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.PotentialMassComparison

noncomputable section

open FirstPass FirstPass.PositiveClasses DiagonalMass

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- A positive multiple of a `θ`-psh potential is an `(c • θ)`-psh potential (the statement and
proof of `RestrictedApproximantComparison.isThetaPshPotential_smul`). -/
theorem isThetaPshPotential_smul {θ : ClosedRealOneOneForm k Z} {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 < c) :
    IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x) := by
  refine ⟨GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hc hu.1, fun x U hU hxU => ?_⟩
  obtain ⟨y, hyU, hy⟩ := hu.2 x U hU hxU
  refine ⟨y, hyU, ?_⟩
  show (c : EReal) * u y ≠ ⊥
  induction h : u y using EReal.rec with
  | bot => exact absurd h hy
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

variable [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- **`eq:dom-mass`, one term** (the statement and proof of
`DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul`).  If `v ∈ PSH(Z, θ)`,
`w ∈ PSH(Z, θ + εω)`, `ε > 0` and `v ≤ w`, then `∫θ_v^k ≤ ∫(θ + εω)_w^k`. -/
theorem diagonalPotentialMass_le_of_le_add_smul (omegaZ : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {ε : ℝ} (hε : 0 < ε) {v w : Z → EReal}
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential (θ + ε • omegaZ.form).val w)
    (hvw : v ≤ w) :
    diagonalPotentialMass θ v hv ≤ diagonalPotentialMass (θ + ε • omegaZ.form) w hw := by
  have hsemi : (ε • omegaZ.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omegaZ.isSemipositive hε.le
  have hv' : IsThetaPshPotential (θ + ε • omegaZ.form).val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  calc diagonalPotentialMass θ v hv
      ≤ diagonalPotentialMass (θ + ε • omegaZ.form) v hv' :=
        AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul omegaZ.isSemipositive
          hε hv hv'
    _ ≤ diagonalPotentialMass (θ + ε • omegaZ.form) w hw :=
        diagonalPotentialMass_mono_of_kahler omegaZ hv' hw
          (MoreSingularOn.of_le fun x _ => hvw x)

end

end SGPT.Foundations.Analysis.Pending.PotentialMassComparison
