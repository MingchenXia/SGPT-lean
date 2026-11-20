import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

set_option autoImplicit false

/-! # Genuine all-quasi-PSH potentials supply their positive P-background -/

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  GlobalQuasiPshKahlerBackground SingularPositiveCommonBackgroundExistence
  SingularGlobalPOrder

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Two genuine local quasi-PSH potentials internally supply a positive
common Kähler multiple, with both actual strong PSH and mass witnesses. -/
theorem exists_pos_common_kahler_background (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    ∃ C : ℝ, 0 < C ∧
      ∃ huC : IsThetaPshPotential (C • omega.form).val u,
      ∃ hvC : IsThetaPshPotential (C • omega.form).val v,
        HasPositivePotentialMass (C • omega.form) u huC ∧
        HasPositivePotentialMass (C • omega.form) v hvC := by
  obtain ⟨A, hA, huA⟩ := exists_pos_isThetaPshPotential_smul omega hu
  obtain ⟨B, hB, hvB⟩ := exists_pos_isThetaPshPotential_smul omega hv
  have hB1 : 0 < B + 1 := by linarith
  have hA1 : 0 < A + 1 := by linarith
  have hformu : A • omega.form + (B + 1) • omega.form =
      (A + B + 1) • omega.form := by module
  have hformv : B • omega.form + (A + 1) • omega.form =
      (A + B + 1) • omega.form := by module
  have huC : IsThetaPshPotential ((A + B + 1) • omega.form).val u := by
    simpa only [hformu] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive huA
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hB1.le)
  have hvC : IsThetaPshPotential ((A + B + 1) • omega.form).val v := by
    simpa only [hformv] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hvB
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hA1.le)
  refine ⟨A + B + 1, by linarith, huC, hvC, ?_, ?_⟩
  · simpa only [hformu] using hasPositivePotentialMass_add_smul omega huA hB1
  · simpa only [hformv] using hasPositivePotentialMass_add_smul omega hvB hA1

/-- The defining source relation is reflexive precisely on the entire
genuine local quasi-PSH domain. -/
theorem sourcePOrder_self_iff_globalQuasiPsh (omega : KahlerBackground n M)
    (u : M → EReal) :
    SourcePOrder (n := n) u u ↔ IsGlobalQuasiPshPotential (n := n) u := by
  constructor
  · rintro ⟨θ, hu, _, _, _, _⟩
    exact hu.quasiPshPotential
  · intro hu
    obtain ⟨C, _, huC, _, hup, _⟩ := exists_pos_common_kahler_background omega hu hu
    exact ⟨C • omega.form, huC, huC, hup, hup, le_rfl⟩

/-- Additive singularity comparison supplies actual source P-order without
assuming any smooth closed background or positive original mass. -/
theorem sourcePOrder_of_moreSingularOn_globalQuasiPsh
    (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v)
    (hmore : MoreSingularOn u v Set.univ) : SourcePOrder (n := n) u v := by
  obtain ⟨C, _, huC, hvC, hup, hvp⟩ := exists_pos_common_kahler_background omega hu hv
  exact ⟨C • omega.form, huC, hvC, hup, hvp, pOrderWith_of_moreSingular hmore⟩

end

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
