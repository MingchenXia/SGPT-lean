import SGPT.Foundations.Analysis.Pending.SingularCutoffSubgeodesicBarrier
import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStages

set_option autoImplicit false

/-! # Actual closed canonical cutoff Perron stages -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStages

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  SingularModelNormalizedMixedCutoff SingularCutoffSubgeodesicBarrier

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine closed Perron stage from the model to its actual real cutoff. -/
def cutoffStage (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    (C s : ℝ) : M → EReal :=
  closedSubgeodesicSlice (finiteGeodesic θ.val φ (realCutoff φ u C))
    φ (realCutoff φ u C) (s / C)

/-- The genuine closed stage starts exactly at the reference. -/
theorem cutoffStage_zero (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    (C : ℝ) : cutoffStage θ φ u C 0 = φ := by
  simp only [cutoffStage, zero_div, closedSubgeodesicSlice_zero]

/-- The genuine positive-length stage ends exactly at the actual cutoff. -/
theorem cutoffStage_terminal (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    {C : ℝ} (hC : 0 < C) : cutoffStage θ φ u C C = realCutoff φ u C := by
  rw [cutoffStage, div_self hC.ne', closedSubgeodesicSlice_one]

/-- The internally constructed joint cutoff competitor yields the exact actual closed-stage lower barrier. -/
theorem realCutoff_le_cutoffStage {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hup : u ≤ φ) {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    realCutoff φ u s ≤ cutoffStage θ φ u C s := by
  by_cases hs0 : s = 0
  · subst s
    rw [cutoffStage_zero]
    intro x
    simp only [realCutoff, EReal.coe_zero, sub_zero, max_eq_right (hup x)]
    exact le_rfl
  by_cases hsC : s = C
  · subst s
    rw [cutoffStage_terminal θ φ u hC]
  have hr : s / C ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hC,
      (div_lt_one hC).mpr (lt_of_le_of_ne hs.2 hsC)⟩
  have h := realCutoff_time_le_finiteGeodesic hp hu hup C (s / C)
  have hmul : C * (s / C) = s := by field_simp
  rw [hmul] at h
  simpa only [cutoffStage, closedSubgeodesicSlice_eq_curve hr] using h

private theorem sub_coe_le_self {p : EReal} (hp : p ≠ ⊤) {s : ℝ} (hs : 0 ≤ s) :
    p - (s : EReal) ≤ p := by
  by_cases hb : p = ⊥
  · simp [hb]
  rw [← EReal.coe_toReal hp hb, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Actual Perron chord control and the produced cutoff barrier give the full closed-stage bounds, retaining all poles. -/
theorem cutoffStage_bounds {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hup : u ≤ φ) {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    (fun x => φ x - (s : EReal)) ≤ cutoffStage θ φ u C s ∧
      cutoffStage θ φ u C s ≤ φ := by
  have hbar := realCutoff_le_cutoffStage hp hu hup hC hs
  have hterm : realCutoff φ u C ≤ φ := by
    intro x
    exact max_le (hup x) (sub_coe_le_self (hp.1.quasiPlurisubharmonic.ne_top x) hC.le)
  refine ⟨fun x => (le_max_right _ _).trans (hbar x), ?_⟩
  by_cases hs0 : s = 0
  · subst s
    rw [cutoffStage_zero]
  by_cases hsC : s = C
  · subst s
    rw [cutoffStage_terminal θ φ u hC]
    exact hterm
  have hr : s / C ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hC,
      (div_lt_one hC).mpr (lt_of_le_of_ne hs.2 hsC)⟩
  intro x
  rw [cutoffStage, closedSubgeodesicSlice_eq_curve hr]
  exact (finiteGeodesic_le_eRealChord hp (IsThetaPshPotential.max hu (hp.sub_const C)) hr x).trans
    ((eRealChord_mono (le_refl (φ x)) (hterm x) hr.1.le hr.2.le).trans_eq
      (FiniteGeodesicEnergyAffineE1.eRealChord_self (φ x) hr))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Genuine cutoff finite type and full-mass Perron joint PSH are produced internally before applying the actual closed-segment finite-type theorem. -/
theorem relativeEInfinity_cutoffStage (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    RelativeEInfinity θ φ (cutoffStage θ φ u C s) := by
  have h0 : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeEInfinity θ φ (realCutoff φ u C) :=
    relativeEInfinity_realCutoff hφ.plurisubharmonic hu (MoreSingularOn.of_le fun x _ => hup x) C
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (realCutoff φ u C) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h1
  have hsub := finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hf0.1 hf1.1
  exact relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
    θ φ φ (realCutoff φ u C) hφ h0 h1 hsub.2.2.1
      ⟨div_nonneg hs.1 hC.le, (div_le_one hC).mpr hs.2⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStages
