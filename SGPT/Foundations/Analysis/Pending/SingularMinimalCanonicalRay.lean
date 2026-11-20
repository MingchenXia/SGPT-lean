import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffConstantInvariance
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass

set_option autoImplicit false

/-! # The literal minimal-reference canonical ray for arbitrary genuine PSH inputs -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularCanonicalCutoffSlices
  SingularCanonicalCutoffRay SingularCanonicalCutoffRayEnergy
  SingularCanonicalCutoffConstantInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual arbitrary-input canonical ray uses the literal minimal potential and the actual global supremum normalization. -/
def canonicalRay (θ : ClosedRealOneOneForm n M) (u : M → EReal) : ℝ → M → EReal :=
  cutoffSlice θ (thetaPshSupremum θ.val)
    (fun x => u x - ((⨆ y, u y).toReal : EReal))

variable [CompactSpace M]

private theorem normalized_input_properties [Nonempty M]
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsThetaPshPotential θ.val (fun x => u x - ((⨆ y, u y).toReal : EReal)) ∧
      (fun x => u x - ((⨆ y, u y).toReal : EReal)) ≤ thetaPshSupremum θ.val := by
  have hfin := ModelRaySupremum.iSup_ne_top_ne_bot hu
  have hS : (((⨆ y, u y).toReal : ℝ) : EReal) = ⨆ y, u y :=
    EReal.coe_toReal hfin.1 hfin.2
  have hp := hu.sub_const (⨆ y, u y).toReal
  have h0 := sub_const_nonpositive_of_le (fun x => hS.symm ▸ le_iSup u x)
  exact ⟨hp, le_thetaPshSupremum hp h0⟩

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- Actual big-class PSH regularity, elementary actual envelope order and genuine positive volume internally produce all minimal-reference model fields without idempotence. -/
theorem isModelPotential_thetaPshSupremum (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    IsModelPotential θ (thetaPshSupremum θ.val) := by
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hfix : thetaPshSupremum θ.val =
      singularityEnvelope θ.val (thetaPshSupremum θ.val) := by
    apply le_antisymm
    · exact self_le_singularityEnvelope hV (thetaPshSupremum_le_zero θ.val)
    · exact uscRegularization_le hV.quasiPshPotential.1.upperSemicontinuous
        (singularitySupremum_le_thetaPshSupremum θ.val (thetaPshSupremum θ.val))
  exact ⟨hV, hfix,
    RestrictedApproximantMass.diagonalPotentialMass_thetaPshSupremum_pos_of_isBigClass
      omega θ hbig hV⟩

/-- The actual finite supremum normalization and produced minimal model internally give the genuine bounded source ray for every strong PSH input. -/
theorem isBoundedRayFromModel_canonicalRay (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsBoundedRayFromModel θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) (canonicalRay θ u) := by
  have hnorm := normalized_input_properties hu
  exact isBoundedRayFromModel_cutoffSlice omega
    (isModelPotential_thetaPshSupremum omega θ hbig) hnorm.1 hnorm.2

/-- Genuine cutoff-ray constant invariance identifies the arbitrary-input definition with the literal original cutoff construction for every nonpositive strong PSH input. -/
theorem canonicalRay_eq_cutoffSlice_of_nonpositive (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (hu0 : u ≤ 0) :
    canonicalRay θ u = cutoffSlice θ (thetaPshSupremum θ.val) u := by
  exact cutoffSlice_sub_const_eq omega (isModelPotential_thetaPshSupremum omega θ hbig)
    hu (le_thetaPshSupremum hu hu0) (⨆ y, u y).toReal (normalized_input_properties hu).2

omit [MeasurableSpace M] [BorelSpace M] in
/-- Genuine finite-constant supremum translation makes the actual normalized input identical, producing whole-function canonical-ray constant invariance for all genuine PSH inputs. -/
theorem canonicalRay_sub_const_eq (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (c : ℝ) :
    canonicalRay θ (fun x => u x - (c : EReal)) = canonicalRay θ u := by
  let S : ℝ := (⨆ y, u y).toReal
  have hfin := ModelRaySupremum.iSup_ne_top_ne_bot hu
  have hS : (S : EReal) = ⨆ y, u y := EReal.coe_toReal hfin.1 hfin.2
  have hsup : (⨆ x, u x - (c : EReal)) = ((S - c : ℝ) : EReal) := by
    simp only [sub_eq_add_neg, ← EReal.coe_neg]
    rw [iSup_add_coe, ← hS, ← EReal.coe_add]
  have hreal : (⨆ x, u x - (c : EReal)).toReal = S - c := by
    rw [hsup, EReal.toReal_coe]
  have heq : (fun x => (u x - (c : EReal)) -
      ((⨆ y, u y - (c : EReal)).toReal : EReal)) =
        fun x => u x - ((⨆ y, u y).toReal : EReal) := by
    funext x
    rw [hreal]
    change (u x - (c : EReal)) - ((S - c : ℝ) : EReal) = u x - (S : EReal)
    simp only [sub_eq_add_neg, ← EReal.coe_neg]
    rw [add_assoc, ← EReal.coe_add]
    exact congrArg (fun r : ℝ => u x + (r : EReal)) (by ring)
  exact congrArg (fun w : M → EReal => cutoffSlice θ (thetaPshSupremum θ.val) w) heq

/-- The actual minimal model and genuine supremum normalization internally yield the literal original radial mixed mass formula with the unnormalized input masses. -/
theorem radialEnergy_canonicalRay_eq_mixed_mass_deficit (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    RelativeGeodesicRays.radialEnergy θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) (canonicalRay θ u) =
      (((∑ k : Fin (n + 1),
        ((endpointMixedMass θ (thetaPshSupremum θ.val) u
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu k).toReal -
            (DiagonalMass.diagonalPotentialMass θ (thetaPshSupremum θ.val)
              (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic).toReal)) /
                (n + 1 : ℝ) : ℝ) : EReal) := by
  have hnorm := normalized_input_properties hu
  rw [canonicalRay, radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega
    (isModelPotential_thetaPshSupremum omega θ hbig) hnorm.1 hnorm.2]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rw [endpointMixedMass_sub_const
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu (⨆ y, u y).toReal k]

end

end SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay
