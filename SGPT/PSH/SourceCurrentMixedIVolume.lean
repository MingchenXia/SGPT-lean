import SGPT.PSH.SourceMixedIVolumeCurrentPresentation
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation

/-! # The actual mixed I-volume of arbitrary original full positive currents

All representations are produced from the original currents. The universal
reader covers every genuine presentation, and no preferred representation is
an input to existence. Native degree-two currents here have dimension m+1;
the original dimension-zero empty tuple was handled in the preceding module.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem fromNativePSH {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    (ofFixedModel (m + 1) M).IsThetaPSH (nativeClosedFormToAtlas θ) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hu

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem exists_nativeTupleRepresentation
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    ∃ (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
      (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i) := by
  choose θ u hu hread hchart using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  exact ⟨θ, u, hu, hread⟩

/-- Arbitrary ORIGINAL full currents internally produce ONE unique value with
EVERY genuine representation readback. Only natural closed/type/full positivity
are inputs; no class, potential, representation or finite-mass certificate. -/
theorem exists_unique_sourceCurrentMixedIVolume (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    ∃! V : ENNReal, ∀ (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
      (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      (∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i)) →
      V = sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (θ i)) u
        (fun i => fromNativePSH (hu i)) := by
  obtain ⟨σ, w, hw, hread⟩ := exists_nativeTupleRepresentation T hc h11 hp
  refine ⟨sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (σ i)) w
    (fun i => fromNativePSH (hw i)), ?_, ?_⟩
  · intro θ u hu hT
    apply sourceGeneralMixedIVolume_eq_of_thetaPotentialCurrent_eq ω
      (fun i => nativeClosedFormToAtlas (σ i)) (fun i => nativeClosedFormToAtlas (θ i))
      w u (fun i => fromNativePSH (hw i)) (fun i => fromNativePSH (hu i))
    intro i
    simpa only [sourceNativeAtlasForm_roundTrip] using (hread i).symm.trans (hT i)
  · intro V hV
    exact hV σ w hw hread

/-- The unique actual original-current value. Original GlobalCurrent inputs
are retained; no new current/proxy/certificate category is introduced. -/
def sourceCurrentMixedIVolume (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) : ENNReal :=
  Classical.choose (exists_unique_sourceCurrentMixedIVolume ω T hc h11 hp)

/-- EVERY actual native closed-form/genuine-potential presentation reads back
as the same represented general volume; no chosen-only representation cut. -/
theorem sourceCurrentMixedIVolume_eq_representation (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i))
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hread : ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i)) :
    sourceCurrentMixedIVolume ω T hc h11 hp =
      sourceGeneralMixedIVolume ω (fun i => nativeClosedFormToAtlas (θ i)) u
        (fun i => fromNativePSH (hu i)) :=
  (Classical.choose_spec (exists_unique_sourceCurrentMixedIVolume ω T hc h11 hp)).1 θ u hu hread

/-- Actual finiteness is an OUTPUT for arbitrary original currents; an actual
representation is produced internally before applying genuine mixed finiteness. -/
theorem sourceCurrentMixedIVolume_lt_top (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    sourceCurrentMixedIVolume ω T hc h11 hp < ⊤ := by
  obtain ⟨θ, u, hu, hread⟩ := exists_nativeTupleRepresentation T hc h11 hp
  rw [sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  exact sourceGeneralMixedIVolume_lt_top ω _ u (fun i => fromNativePSH (hu i))

/-- The actual original-current quantity is independent of every genuine
Kahler background; the same actual representation is produced inside. -/
theorem sourceCurrentMixedIVolume_kahler_independent (ω Ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    sourceCurrentMixedIVolume ω T hc h11 hp = sourceCurrentMixedIVolume Ω T hc h11 hp := by
  obtain ⟨θ, u, hu, hread⟩ := exists_nativeTupleRepresentation T hc h11 hp
  rw [sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread,
    sourceCurrentMixedIVolume_eq_representation Ω T hc h11 hp θ u hu hread]
  exact sourceGeneralMixedIVolume_kahler_independent ω Ω _ u (fun i => fromNativePSH (hu i))

/-- Every actual positive-I-volume presentation gives EXACTLY the original
mixed I-envelope formula, without requiring positive NP masses of the inputs. -/
theorem sourceCurrentMixedIVolume_eq_positive_representation (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i))
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hread : ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i))
    (hpos : ∀ i, 0 < sourceIVolume (nativeClosedFormToAtlas (θ i)) (u i)
      (fromNativePSH (hu i))) :
    sourceCurrentMixedIVolume ω T hc h11 hp =
      sourceEnvelopeMixedIVolume (fun i => nativeClosedFormToAtlas (θ i)) u
        (fun i => fromNativePSH (hu i)) := by
  rw [sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  exact sourceGeneralMixedIVolume_eq_positive ω _ u (fun i => fromNativePSH (hu i)) hpos

end SGPT.PSH.VariableComplexAtlas
