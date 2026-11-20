import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStageOrder
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure

set_option autoImplicit false

/-! # Genuine USC-regularized canonical cutoff slices -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffSlices

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages
  SingularCanonicalCutoffStageOrder

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual cutoff slice is the genuine USC-regularized supremum over all real horizons above its clipped time. -/
def cutoffSlice (θ : ClosedRealOneOneForm n M) (φ u : M → EReal) (s : ℝ) : M → EReal :=
  uscRegularization (⨆ C : {C : ℝ // max s 0 < C},
    cutoffStage θ φ u C.val (max s 0))

/-- Genuine actual stage endpoints and the reference USC fixed point give the exact initial slice. -/
theorem cutoffSlice_zero {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hp : IsThetaPshPotential θ.val φ) : cutoffSlice θ φ u 0 = φ := by
  let : Nonempty {C : ℝ // (0 : ℝ) < C} := ⟨⟨1, zero_lt_one⟩⟩
  simp only [cutoffSlice, max_self, cutoffStage_zero, iSup_const]
  exact uscRegularization_eq hp.quasiPshPotential.1.upperSemicontinuous

/-- Actual cutoff barriers and genuine USC upper control produce the full pole-safe slice bounds without a limit-class premise. -/
theorem cutoffSlice_bounds {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hup : u ≤ φ) {s : ℝ} (hs : 0 ≤ s) :
    realCutoff φ u s ≤ cutoffSlice θ φ u s ∧
      (fun x => φ x - (s : EReal)) ≤ cutoffSlice θ φ u s ∧
        cutoffSlice θ φ u s ≤ φ := by
  let C : {C : ℝ // max s 0 < C} := ⟨s + 1, by rw [max_eq_left hs]; linarith⟩
  have hC : 0 < C.val := by change 0 < s + 1; linarith
  have hsc : s ∈ Icc (0 : ℝ) C.val := ⟨hs, by change s ≤ s + 1; linarith⟩
  have hbar := realCutoff_le_cutoffStage hp hu hup hC hsc
  have hmid := (le_iSup (fun D : {C : ℝ // max s 0 < C} =>
      cutoffStage θ φ u D.val (max s 0)) C).trans (le_uscRegularization _)
  have heq := congrArg (fun t : ℝ => cutoffStage θ φ u C.val t) (max_eq_left hs)
  have hlow : realCutoff φ u s ≤ cutoffSlice θ φ u s :=
    hbar.trans (heq.symm.le.trans hmid)
  refine ⟨hlow, fun x => (le_max_right _ _).trans (hlow x), ?_⟩
  have hraw : (⨆ D : {C : ℝ // max s 0 < C},
      cutoffStage θ φ u D.val (max s 0)) ≤ φ := by
    apply iSup_le
    intro D
    exact (cutoffStage_bounds hp hu hup
      (lt_of_le_of_lt (le_max_right s 0) D.property)
      ⟨le_max_right s 0, D.property.le⟩).2
  exact uscRegularization_le hp.quasiPshPotential.1.upperSemicontinuous hraw

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Internally produced stage finite type and true model normalization yield the actual slice finite type via genuine bounded USC-supremum closure. -/
theorem relativeEInfinity_cutoffSlice (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) (s : ℝ) :
    RelativeEInfinity θ φ (cutoffSlice θ φ u s) := by
  let : Nonempty {C : ℝ // max s 0 < C} := ⟨⟨max s 0 + 1, by linarith⟩⟩
  have hC (C : {C : ℝ // max s 0 < C}) : 0 < C.val :=
    lt_of_le_of_lt (le_max_right s 0) C.property
  have hs (C : {C : ℝ // max s 0 < C}) : max s 0 ∈ Icc (0 : ℝ) C.val :=
    ⟨le_max_right s 0, C.property.le⟩
  have hφ0 : φ ≤ 0 := hφ.envelope_eq ▸ singularityEnvelope_le_zero θ.val φ
  have hscalar (C : {C : ℝ // max s 0 < C}) (x : M) :
      cutoffStage θ φ u C.val (max s 0) x ≤ ((0 : ℝ) : EReal) :=
    ((cutoffStage_bounds hφ.plurisubharmonic hu hup (hC C) (hs C)).2 x).trans (hφ0 x)
  exact SingularModelBoundedSupremumEnergyClosure.relativeEInfinity_uscRegularization_iSup
    (hφ := hφ) (fun C => relativeEInfinity_cutoffStage omega hφ hu hup (hC C) (hs C))
    hscalar

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffSlices
