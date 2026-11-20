import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRay
import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinRay
import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffConstantInvariance

set_option autoImplicit false

/-! # Actual canonical cutoff maxima and the least upper ray, SGPT (6.8)

The actual cutoff barriers and genuine finite Perron order first bound
the canonical maximum below any natural full-mass source upper ray.
No ray-join equality or distance comparison is a premise.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffJoin

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  RelativePreceqRays SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages
  SingularCanonicalCutoffSlices SingularCanonicalCutoffRay SingularBoundedRayJoinSlices
  SingularBoundedRayJoinRay SingularCanonicalCutoffConstantInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
  {hφ : IsModelPotential θ φ} {L : ℝ → M → EReal}

/-- The true canonical maximum lies below every genuine full-mass Perron
upper ray, with no finite-energy or bounded-type premise on that upper ray. -/
theorem cutoffSlice_max_le_upperRay
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hup : u ≤ φ) (hvp : v ≤ φ) (hL : IsRayFromModel θ φ hφ L)
    (hle : ∀ t, 0 ≤ t → cutoffSlice θ φ u t ≤ L t)
    (hle' : ∀ t, 0 ≤ t → cutoffSlice θ φ v t ≤ L t)
    {s : ℝ} (hs : 0 ≤ s) :
    cutoffSlice θ φ (fun x => max (u x) (v x)) s ≤ L s := by
  have hraw : (⨆ T : {T : ℝ // max s 0 < T},
      cutoffStage θ φ (fun x => max (u x) (v x)) T.val (max s 0)) ≤ L s := by
    apply iSup_le
    intro T
    have hT : 0 < T.val := lt_of_le_of_lt (le_max_right s 0) T.property
    have hsT : s < T.val := (le_max_left s 0).trans_lt T.property
    have hcu : realCutoff φ u T.val ≤ L T.val :=
      (cutoffSlice_bounds hφ.plurisubharmonic hu hup hT.le).1.trans (hle T.val hT.le)
    have hcv : realCutoff φ v T.val ≤ L T.val :=
      (cutoffSlice_bounds hφ.plurisubharmonic hv hvp hT.le).1.trans (hle' T.val hT.le)
    have hcut : realCutoff φ (fun x => max (u x) (v x)) T.val ≤ L T.val := by
      intro x
      exact max_le
        (max_le ((le_max_left _ _).trans (hcu x)) ((le_max_left _ _).trans (hcv x)))
        ((le_max_right _ _).trans (hcu x))
    have hstage := SingularBoundedRayJoinStageOrder.joinStage_le_upperRay
      (ℓ := fun t => realCutoff φ (fun x => max (u x) (v x)) t)
      (ℓ' := fun t => realCutoff φ (fun x => max (u x) (v x)) t)
      hL hT ⟨hs, hsT.le⟩ hcut hcut
    have heq := congrArg (fun r : ℝ =>
      cutoffStage θ φ (fun x => max (u x) (v x)) T.val r) (max_eq_left hs)
    apply heq.le.trans
    simpa only [SingularBoundedRayJoinStages.joinStage, cutoffStage, max_self] using hstage
  exact uscRegularization_le
    (hL.1.1 s hs).plurisubharmonic.quasiPshPotential.1.upperSemicontinuous hraw

variable [BorelSpace M] [ConnectedSpace M]

/-- Genuine input order, internally produced bounded rays and the actual
least-upper property identify the actual maximum cutoff ray with the
actually constructed bounded join at every nonnegative time, SGPT (6.8). -/
theorem cutoffSlice_max_eq_joinSlice (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hup : u ≤ φ) (hvp : v ≤ φ) {s : ℝ} (hs : 0 ≤ s) :
    cutoffSlice θ φ (fun x => max (u x) (v x)) s =
      joinSlice θ φ (cutoffSlice θ φ u) (cutoffSlice θ φ v) s := by
  have hRu := isBoundedRayFromModel_cutoffSlice omega hφ hu hup
  have hRv := isBoundedRayFromModel_cutoffSlice omega hφ hv hvp
  have hmaxp : (fun x => max (u x) (v x)) ≤ φ :=
    fun x => max_le (hup x) (hvp x)
  have hRm := isBoundedRayFromModel_cutoffSlice omega hφ
    (IsThetaPshPotential.max hu hv) hmaxp
  have hJ := isBoundedRayFromModel_joinSlice omega hRu hRv
  apply le_antisymm
  · apply cutoffSlice_max_le_upperRay hu hv hup hvp ⟨hJ.1.1, hJ.2⟩
    · intro t ht x
      exact (le_max_left _ _).trans (max_le_joinSlice hRu hRv ht x)
    · intro t ht x
      exact (le_max_right _ _).trans (max_le_joinSlice hRu hRv ht x)
    · exact hs
  · exact joinSlice_le_upperRay ⟨hRm.1.1, hRm.2⟩
      (fun t _ => cutoffSlice_mono_input (fun x => le_max_left (u x) (v x)) t)
      (fun t _ => cutoffSlice_mono_input (fun x => le_max_right (u x) (v x)) t) hs

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffJoin
