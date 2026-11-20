import SGPT.IGood.Misc2VolBigL
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

/-! Actual semipositive original Chern representatives have the original
zero minimal envelope and the actual smooth top intersection as mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual normalized envelope is literally zero for a semipositive
original form; it is not a substituted minimal-singularity certificate. -/
theorem thetaPshSupremum_eq_zero_of_semipositive (θ : ClosedRealOneOneForm n M)
    (hθ : θ.val.IsSemipositive) : thetaPshSupremum θ.val = fun _ => 0 := by
  apply le_antisymm
  · exact thetaPshSupremum_le_zero θ.val
  · exact le_thetaPshSupremum ((LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hθ) le_rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual non-pluripolar mass of the original minimal envelope has
exactly the original smooth repeated-slot Chern integral as its real value. -/
theorem minimal_mass_toReal_eq_slotIntegral_of_semipositive (hn : 0 < n)
    (κ : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hθ : θ.val.IsSemipositive)
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val)) :
    (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV).toReal =
      slotIntegral κ (fun _ : Fin n => θ) := by
  have h0 : IsThetaPshPotential θ.val (fun _ : M => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hθ
  rw [SGPT.IGood.Misc2VolBigL.diagonalPotentialMass_congr θ
    (thetaPshSupremum_eq_zero_of_semipositive θ hθ) hV h0]
  change (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun _ _ => (0 : EReal))
    (fun _ => h0.1)).toReal = _
  exact globalMixedMass_toReal_eq_slotIntegral hn κ
    (fun _ => NefMixedMass.nefWithRespectTo_of_isSemipositive hθ) (fun _ => h0)
    (fun _ => ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩)

end SGPT.LineBundle.AmpleChern
