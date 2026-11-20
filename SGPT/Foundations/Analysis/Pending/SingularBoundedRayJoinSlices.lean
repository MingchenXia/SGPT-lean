import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageBounds
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure

set_option autoImplicit false

/-! # Actual bounded join slices and their least upper order property -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinSlices

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages
  SingularBoundedRayJoinStageOrder SingularBoundedRayJoinStageBounds

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine regularized supremum of actual terminal-maximum stages uses all real terminal times greater than the clipped actual slice time. -/
def joinSlice (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (ℓ ℓ' : ℝ → M → EReal) (s : ℝ) : M → EReal :=
  uscRegularization (⨆ T : {T : ℝ // max s 0 < T},
    joinStage θ φ ℓ ℓ' T.val (max s 0))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {ℓ ℓ' L : ℝ → M → EReal}

/-- The actual stage finite-type and produced fixed-time scalar bound internally produce genuine bounded-type join slices at every real time, with no limit-class input. -/
theorem relativeEInfinity_joinSlice (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') (s : ℝ) :
    RelativeEInfinity θ φ (joinSlice θ φ ℓ ℓ' s) := by
  let : Nonempty {T : ℝ // max s 0 < T} := ⟨⟨max s 0 + 1, by linarith⟩⟩
  have hT (T : {T : ℝ // max s 0 < T}) : 0 < T.val :=
    lt_of_le_of_lt (le_max_right s 0) T.property
  have hs (T : {T : ℝ // max s 0 < T}) : max s 0 ∈ Icc (0 : ℝ) T.val :=
    ⟨le_max_right s 0, T.property.le⟩
  exact SingularModelBoundedSupremumEnergyClosure.relativeEInfinity_uscRegularization_iSup
    (hφ := hφ) (fun T => relativeEInfinity_joinStage omega hℓ hℓ' (hT T) (hs T))
    (fun T x => joinStage_le_linear omega hℓ hℓ' (hT T) (hs T) x)

include hφ in
omit [BorelSpace M] [ConnectedSpace M] in
/-- The genuine stage endpoint and actual USC fixed-point property produce exactly the model as the initial join slice. -/
theorem joinSlice_zero : joinSlice θ φ ℓ ℓ' 0 = φ := by
  let : Nonempty {T : ℝ // (0 : ℝ) < T} := ⟨⟨1, zero_lt_one⟩⟩
  simp only [joinSlice, max_self, joinStage_zero, iSup_const]
  exact uscRegularization_eq hφ.plurisubharmonic.quasiPshPotential.1.upperSemicontinuous

omit [BorelSpace M] [ConnectedSpace M] in
/-- Both actual bounded source ray slices lie below the actual regularized join slice at every nonnegative time. -/
theorem max_le_joinSlice (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') {s : ℝ} (hs : 0 ≤ s) :
    (fun x => max (ℓ s x) (ℓ' s x)) ≤ joinSlice θ φ ℓ ℓ' s := by
  let T : {T : ℝ // max s 0 < T} := ⟨s + 1, by rw [max_eq_left hs]; linarith⟩
  have hT : 0 < T.val := by change 0 < s + 1; linarith
  have hst : s ∈ Icc (0 : ℝ) T.val := ⟨hs, by change s ≤ s + 1; linarith⟩
  have hle := max_le_joinStage hℓ hℓ' hT hst
  have hmid := (le_iSup (fun S : {T : ℝ // max s 0 < T} =>
      joinStage θ φ ℓ ℓ' S.val (max s 0)) T).trans (le_uscRegularization _)
  have heq := congrArg (fun r : ℝ => joinStage θ φ ℓ ℓ' T.val r) (max_eq_left hs)
  exact hle.trans (heq.symm.le.trans hmid)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Genuine full-mass source upper-ray geometry and natural pointwise domination internally bound the actual regularized join slices, without a target least-ray premise. -/
theorem joinSlice_le_upperRay (hL : IsRayFromModel θ φ hφ L)
    (hle : ∀ t, 0 ≤ t → ℓ t ≤ L t) (hle' : ∀ t, 0 ≤ t → ℓ' t ≤ L t)
    {s : ℝ} (hs : 0 ≤ s) : joinSlice θ φ ℓ ℓ' s ≤ L s := by
  have hraw : (⨆ T : {T : ℝ // max s 0 < T},
      joinStage θ φ ℓ ℓ' T.val (max s 0)) ≤ L s := by
    apply iSup_le
    intro T
    have hT : 0 < T.val := lt_of_le_of_lt (le_max_right s 0) T.property
    have hst : s ∈ Icc (0 : ℝ) T.val :=
      ⟨hs, (le_max_left s 0).trans T.property.le⟩
    have heq := congrArg (fun r : ℝ => joinStage θ φ ℓ ℓ' T.val r) (max_eq_left hs)
    exact heq.le.trans
      (joinStage_le_upperRay hL hT hst (hle T.val hT.le) (hle' T.val hT.le))
  exact uscRegularization_le
    (hL.1.1 s hs).plurisubharmonic.quasiPshPotential.1.upperSemicontinuous hraw

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinSlices
