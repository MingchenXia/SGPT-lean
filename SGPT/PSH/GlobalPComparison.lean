import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalPComparison

open Set
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.POrder
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Literal original existential positive-background source relation, without a new definition. -/
abbrev sourcePOrder (u v : M → EReal) : Prop :=
  SingularGlobalPOrder.SourcePOrder (n := n) u v

/-- Original source P type is precisely comparison in both directions. -/
abbrev sourcePEquivalent (u v : M → EReal) : Prop :=
  SingularGlobalPOrder.SourcePEquivalent (n := n) u v

/-- Raw genuine quasi-PSH data internally produce a TRUE positive common background. -/
theorem exists_positive_common_background_of_quasiPsh (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    ∃ θ : ClosedRealOneOneForm n M,
      ∃ huθ : IsThetaPshPotential θ.val u,
      ∃ hvθ : IsThetaPshPotential θ.val v,
        HasPositivePotentialMass θ u huθ ∧ HasPositivePotentialMass θ v hvθ := by
  obtain ⟨θ, huθ⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background omega u).mp hu
  obtain ⟨σ, hvσ⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background omega v).mp hv
  exact SingularPositiveCommonBackgroundExistence.exists_positive_common_background omega θ σ huθ hvσ

/-- The printed existential relation is the original envelope order in ANY true positive background. -/
theorem sourcePOrder_iff_positive_background (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv) :
    sourcePOrder (n := n) u v ↔ POrderWith θ u v :=
  SingularGlobalPOrder.sourcePOrder_iff_pOrderWith omega θ hu hv hupos hvpos

/-- Original "some, equivalently every" is genuine: reverse uses an internally produced witness. -/
theorem sourcePOrder_iff_every_positive_background (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    sourcePOrder (n := n) u v ↔
      ∀ (θ : ClosedRealOneOneForm n M) (huθ : IsThetaPshPotential θ.val u)
        (hvθ : IsThetaPshPotential θ.val v),
        HasPositivePotentialMass θ u huθ → HasPositivePotentialMass θ v hvθ → POrderWith θ u v := by
  constructor
  · intro h θ huθ hvθ hup hvp
    exact (sourcePOrder_iff_positive_background omega θ huθ hvθ hup hvp).mp h
  · intro h
    obtain ⟨θ, huθ, hvθ, hup, hvp⟩ := exists_positive_common_background_of_quasiPsh omega hu hv
    exact (sourcePOrder_iff_positive_background omega θ huθ hvθ hup hvp).mpr
      (h θ huθ hvθ hup hvp)

theorem sourcePOrder_refl (omega : KahlerBackground n M) {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) : sourcePOrder (n := n) u u := by
  obtain ⟨θ, huθ⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background omega u).mp hu
  exact SingularGlobalPOrder.sourcePOrder_refl_of_isThetaPshPotential omega huθ

theorem sourcePOrder_trans (omega : KahlerBackground n M) {u v w : M → EReal}
    (huv : sourcePOrder (n := n) u v) (hvw : sourcePOrder (n := n) v w) :
    sourcePOrder (n := n) u w := SingularGlobalPOrder.SourcePOrder.trans omega huv hvw

/-- The actual source preorder is coarser than original finite-constant singularity order. -/
theorem sourcePOrder_of_moreSingular (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) (hv : IsGlobalQuasiPshPotential (n := n) v)
    (hmore : MoreSingularOn u v univ) : sourcePOrder (n := n) u v := by
  obtain ⟨θ, huθ⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background omega u).mp hu
  obtain ⟨σ, hvσ⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background omega v).mp hv
  exact SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega θ σ huθ hvσ hmore

/-- Whole original background-addition lemma: true added memberships and masses are internal. -/
theorem pOrderWith_add_kahler_iff (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv) :
    POrderWith θ u v ↔ POrderWith (θ + omega.form) u v := by
  have hu' : IsThetaPshPotential (θ + omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu omega.isSemipositive
  have hv' : IsThetaPshPotential (θ + omega.form).val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv omega.isSemipositive
  have hup' : HasPositivePotentialMass (θ + omega.form) u hu' := by
    simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hu zero_lt_one
  have hvp' : HasPositivePotentialMass (θ + omega.form) v hv' := by
    simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hv zero_lt_one
  exact (sourcePOrder_iff_positive_background omega θ hu hv hupos hvpos).symm.trans
    (sourcePOrder_iff_positive_background omega (θ + omega.form) hu' hv' hup' hvp')

/-- Complete printed positive-mass example, retaining the original envelope and global relation. -/
theorem sourcePEquivalent_singularityEnvelope (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (_hpos : HasPositivePotentialMass θ u hu) :
    sourcePEquivalent (n := n) u (singularityEnvelope θ.val u) :=
  SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega θ hu

end SGPT.PSH.GlobalPComparison
