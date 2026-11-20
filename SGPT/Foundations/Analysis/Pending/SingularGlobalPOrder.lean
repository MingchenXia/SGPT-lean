import SGPT.Foundations.Analysis.Pending.SingularPositivePCommonBackground
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence

set_option autoImplicit false

/-! # The actual source P-relation using positive common backgrounds -/

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularPositivePCommonBackground SingularPositiveCommonBackgroundExistence
  SingularPositiveMassPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Xia's source relation: a genuine positive common background witnesses actual P-envelope comparison. -/
def SourcePOrder (u v : M → EReal) : Prop :=
  ∃ θ : ClosedRealOneOneForm n M,
    ∃ hu : IsThetaPshPotential θ.val u,
    ∃ hv : IsThetaPshPotential θ.val v,
      HasPositivePotentialMass θ u hu ∧ HasPositivePotentialMass θ v hv ∧ POrderWith θ u v

/-- Mutual comparison in the source's actual existential positive-background relation. -/
def SourcePEquivalent (u v : M → EReal) : Prop :=
  SourcePOrder (n := n) u v ∧ SourcePOrder (n := n) v u

theorem sourcePOrder_iff_pOrderWith (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv) :
    SourcePOrder (n := n) u v ↔ POrderWith θ u v := by
  constructor
  · rintro ⟨σ, huσ, hvσ, hupσ, hvpσ, huv⟩
    exact (pOrderWith_iff_of_positive_backgrounds omega σ θ huσ hvσ hu hv
      hupσ hvpσ hupos hvpos).mp huv
  · exact fun huv => ⟨θ, hu, hv, hupos, hvpos, huv⟩

theorem sourcePEquivalent_iff_pEquivalentWith (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv) :
    SourcePEquivalent (n := n) u v ↔ PEquivalentWith θ u v := by
  exact and_congr (sourcePOrder_iff_pOrderWith omega θ hu hv hupos hvpos)
    (sourcePOrder_iff_pOrderWith omega θ hv hu hvpos hupos)

theorem sourcePOrder_refl_of_isThetaPshPotential (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) : SourcePOrder (n := n) u u := by
  obtain ⟨τ, huτ, _, hupτ, _⟩ := exists_positive_common_background omega θ θ hu hu
  exact ⟨τ, huτ, huτ, hupτ, hupτ, le_rfl⟩

theorem SourcePOrder.trans (omega : KahlerBackground n M) {u v w : M → EReal}
    (huv : SourcePOrder (n := n) u v) (hvw : SourcePOrder (n := n) v w) :
    SourcePOrder (n := n) u w := by
  obtain ⟨θ, huθ, hvθ, hupθ, hvpθ, hθ⟩ := huv
  obtain ⟨σ, hvσ, hwσ, hvpσ, hwpσ, hσ⟩ := hvw
  obtain ⟨C, hC, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (θ - σ)
  let η := θ - σ + C • omega.form
  have hη : η.val.IsSemipositive := hsemi
  have hC1 : 0 < C + 1 := by linarith
  let τ := θ + (C + 1) • omega.form
  have huτ : IsThetaPshPotential τ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive huθ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hC1.le)
  have hvτ : IsThetaPshPotential τ.val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hvθ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hC1.le)
  have hwη : IsThetaPshPotential (σ + η).val w :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hwσ hη
  have hforms : (σ + η) + (1 : ℝ) • omega.form = τ := by
    dsimp only [η, τ]
    module
  have hwτ : IsThetaPshPotential τ.val w := by
    simpa only [hforms] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hwη
        (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  have hupτ : HasPositivePotentialMass τ u huτ :=
    hasPositivePotentialMass_add_smul omega huθ hC1
  have hvpτ : HasPositivePotentialMass τ v hvτ :=
    hasPositivePotentialMass_add_smul omega hvθ hC1
  have hwpτ : HasPositivePotentialMass τ w hwτ := by
    simpa only [hforms] using hasPositivePotentialMass_add_smul omega hwη zero_lt_one
  have hθτ := (pOrderWith_iff_of_positive_backgrounds omega θ τ huθ hvθ huτ hvτ
    hupθ hvpθ hupτ hvpτ).mp hθ
  have hστ := (pOrderWith_iff_of_positive_backgrounds omega σ τ hvσ hwσ hvτ hwτ
    hvpσ hwpσ hvpτ hwpτ).mp hσ
  exact ⟨τ, huτ, hwτ, hupτ, hwpτ, hθτ.trans hστ⟩

theorem sourcePOrder_of_moreSingularOn (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hmore : MoreSingularOn u v Set.univ) : SourcePOrder (n := n) u v := by
  obtain ⟨τ, huτ, hvτ, hupτ, hvpτ⟩ := exists_positive_common_background omega θ σ hu hv
  exact ⟨τ, huτ, hvτ, hupτ, hvpτ, pOrderWith_of_moreSingular hmore⟩

theorem sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hupos : HasPositivePotentialMass θ u hu) (hvpos : HasPositivePotentialMass θ v hv)
    (huv : SourcePOrder (n := n) u v) :
    SourcePEquivalent (n := n) u v ↔
      diagonalPotentialMass θ u hu = diagonalPotentialMass θ v hv := by
  have hfixed := (sourcePOrder_iff_pOrderWith omega θ hu hv hupos hvpos).mp huv
  exact (sourcePEquivalent_iff_pEquivalentWith omega θ hu hv hupos hvpos).trans
    (pEquivalentWith_iff_diagonalPotentialMass_eq_of_pOrderWith omega θ hu hv hupos hfixed)

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
