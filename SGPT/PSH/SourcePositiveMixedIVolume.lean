import SGPT.Envelopes.SourceIEnvelopeRepresentativeChange
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-! # The original positive mixed I-volume formula

The quantity is the actual mixed non-pluripolar mass of the actual I-envelopes.
Its positive-volume restriction is the printed original definition. Smooth
representative invariance is proved without identifying this direct formula
with the later all-current Kahler-perturbation extension at zero volume.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The literal actual I-envelope mixed mass. Its positive-I-volume restriction
is original `def:mix_vol2`; the general perturbed extension is a separate object. -/
def sourceEnvelopeMixedIVolume
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) : ℝ≥0∞ :=
  sourceMixedNonPluripolarMass θ (fun i => sourceIEnvelope (θ i) (u i))
    (fun i => isThetaPSH_sourceIEnvelope (hu i))

omit [BorelSpace M] in
/-- Exact actual native readback, retaining the same independent forms and
same original source I-envelopes rather than a replacement product. -/
theorem sourceEnvelopeMixedIVolume_eq_native
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceEnvelopeMixedIVolume θ u hu = MixedMass.globalMixedMass
      (fun i => atlasClosedFormToNative (θ i))
      (fun i => sourceIEnvelope (θ i) (u i))
      (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) _).mp
        (isThetaPSH_sourceIEnvelope (hu i))).1) := rfl

/-- Actual compact Kahler finiteness is an output for every genuine tuple. -/
theorem sourceEnvelopeMixedIVolume_lt_top (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceEnvelopeMixedIVolume θ u hu < ⊤ :=
  sourceMixedNonPluripolarMass_lt_top ω θ _ (fun i => isThetaPSH_sourceIEnvelope (hu i))

omit [BorelSpace M] in
/-- Constant tuples recover the existing actual original I-volume, including n=0. -/
theorem sourceEnvelopeMixedIVolume_diagonal
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceEnvelopeMixedIVolume (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu) =
      sourceIVolume θ u hu :=
  sourceMixedNonPluripolarMass_diagonal θ _ (isThetaPSH_sourceIEnvelope hu)

/-- Simultaneous permutation of actual independent forms and potentials
preserves the actual envelope mixed volume. -/
theorem sourceEnvelopeMixedIVolume_perm
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (σ : Equiv.Perm (Fin n)) :
    sourceEnvelopeMixedIVolume (fun i => θ (σ i)) (fun i => u (σ i)) (fun i => hu (σ i)) =
      sourceEnvelopeMixedIVolume θ u hu := by
  simp only [sourceEnvelopeMixedIVolume, sourceMixedNonPluripolarMass_eq_native]
  exact congrArg (fun μ : Measure M => μ univ)
    (GlobalSlotPerm.globalMixedMeasure_perm
      (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) _).mp
        (isThetaPSH_sourceIEnvelope (hu i))).1) σ)

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem sameSingularity_sub_chartSmooth
    {g : M → ℝ} (hg : ChartSmooth (n := n) g) (u : M → EReal) :
    SGPT.PSH.SingularityEquiv u (fun x => u x - (g x : EReal)) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  refine ⟨⟨B, fun x _ => ?_⟩, ⟨B, fun x _ => ?_⟩⟩
  · have hh := add_le_add (le_refl (u x - (g x : EReal)))
      (EReal.coe_le_coe_iff.mpr (abs_le.mp (hbound x)).2)
    have heq : u x - (g x : EReal) + (g x : EReal) = u x := by
      simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
        neg_add_cancel, EReal.coe_zero, add_zero]
    rwa [heq] at hh
  · change u x + -(g x : EReal) ≤ u x + (B : EReal)
    have hb : -g x ≤ B := by linarith [(abs_le.mp (hbound x)).1]
    have hc : -(g x : EReal) ≤ (B : EReal) := by
      rw [← EReal.coe_neg]
      exact EReal.coe_le_coe_iff.mpr hb
    exact add_le_add le_rfl hc

/-- Every actual independent smooth representative change preserves the same
formula; genuine compensated PSH and mixed-mass comparisons are manufactured. -/
theorem sourceEnvelopeMixedIVolume_changeRepresentative (ω : KahlerBackground n M)
    (θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : Fin n → M → EReal) (g : Fin n → M → ℝ)
    (hchange : ∀ i, SourceSmoothBackgroundChange (θ i) (η i) (g i))
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceEnvelopeMixedIVolume η (fun i x => u i x - (g i x : EReal))
      (fun i => sourceThetaPSH_sub_smooth (hchange i) (hu i)) =
      sourceEnvelopeMixedIVolume θ u hu := by
  let U : Fin n → M → EReal := fun i => sourceIEnvelope (θ i) (u i)
  let V : Fin n → M → EReal := fun i x => U i x - (g i x : EReal)
  let W : Fin n → M → EReal := fun i =>
    sourceIEnvelope (η i) (fun x => u i x - (g i x : EReal))
  have hU i : (ofFixedModel n M).IsThetaPSH (θ i) (U i) :=
    isThetaPSH_sourceIEnvelope (hu i)
  have hV i : (ofFixedModel n M).IsThetaPSH (η i) (V i) :=
    sourceThetaPSH_sub_smooth (hchange i) (hU i)
  have hW i : (ofFixedModel n M).IsThetaPSH (η i) (W i) :=
    isThetaPSH_sourceIEnvelope (sourceThetaPSH_sub_smooth (hchange i) (hu i))
  have hWV i : SGPT.PSH.SingularityEquiv (W i) (V i) :=
    SGPT.PSH.singularityEquiv_trans
      (SGPT.PSH.singularityEquiv_symm
        (sourceIEnvelope_changeRepresentative (hchange i) (hu i)).2)
      (sameSingularity_sub_chartSmooth
        ((sourceSmoothBackgroundChange_iff_native _ _ _).mp (hchange i)).1 (U i))
  change sourceMixedNonPluripolarMass η W hW = sourceMixedNonPluripolarMass θ U hU
  calc
    sourceMixedNonPluripolarMass η W hW = sourceMixedNonPluripolarMass η V hV :=
      le_antisymm
        (sourceMixedNonPluripolarMass_mono ω hW hV (fun i => (hWV i).1))
        (sourceMixedNonPluripolarMass_mono ω hV hW (fun i => (hWV i).2))
    _ = sourceMixedNonPluripolarMass θ U hU := by
      simp only [sourceMixedNonPluripolarMass_eq_native]
      exact congrArg (fun μ : Measure M => μ univ)
        (GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
          (θ := fun i => atlasClosedFormToNative (θ i))
          (η := fun i => atlasClosedFormToNative (η i)) (u := U) (f := g)
          (fun i => ((sourceSmoothBackgroundChange_iff_native _ _ _).mp (hchange i)).1)
          (fun i => ((sourceSmoothBackgroundChange_iff_native _ _ _).mp (hchange i)).2)
          (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) _).mp (hU i)).1))

/-- Actual I-order gives monotonicity of the envelope formula in any common
original background, even when the original I-volumes vanish. -/
theorem sourceEnvelopeMixedIVolume_mono_of_sourceIOrder (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (hI : ∀ i, sourceIOrder (ofFixedModel n M) (u i) (v i)) :
    sourceEnvelopeMixedIVolume θ u hu ≤ sourceEnvelopeMixedIVolume θ v hv :=
  sourceMixedNonPluripolarMass_mono ω
    (fun i => isThetaPSH_sourceIEnvelope (hu i))
    (fun i => isThetaPSH_sourceIEnvelope (hv i))
    (fun i => MoreSingularOn.of_le fun x _ =>
      (sourceIOrder_iff_sourceIEnvelope_le (hu i) (hv i)).mp (hI i) x)

/-- DIFFERENT actual representatives are retained: equality of the original
Bott--Chern classes internally produces every smooth gauge and genuine domain. -/
theorem sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder
    (ω : KahlerBackground n M)
    (θ η : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u v : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (η i) (v i))
    (hclass : ∀ i, RealBottChern.ofRepresentative (atlasClosedFormToNative (θ i)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (η i)))
    (hI : ∀ i, sourceIOrder (ofFixedModel n M) (u i) (v i)) :
    sourceEnvelopeMixedIVolume θ u hu ≤ sourceEnvelopeMixedIVolume η v hv := by
  classical
  have hrel i : ClosedRealOneOneForm.BottChernRel
      (atlasClosedFormToNative (η i)) (atlasClosedFormToNative (θ i)) :=
    ((RealBottChern.ofRepresentative_eq_iff _ _).mp (hclass i)).symm
  choose g hg hηθ using hrel
  have hchange i : SourceSmoothBackgroundChange (η i) (θ i) (g i) :=
    (sourceSmoothBackgroundChange_iff_native _ _ _).mpr ⟨hg i, hηθ i⟩
  let v' : Fin n → M → EReal := fun i x => v i x - (g i x : EReal)
  have hv' i : (ofFixedModel n M).IsThetaPSH (θ i) (v' i) :=
    sourceThetaPSH_sub_smooth (hchange i) (hv i)
  have hI' i : sourceIOrder (ofFixedModel n M) (u i) (v' i) := by
    have ht := (sameSingularity_sub_chartSmooth (hg i) (v i)).1
    obtain ⟨B, hB⟩ := ht
    apply (sourceIOrder_iff_native ⟨θ i, hu i⟩ ⟨θ i, hv' i⟩).mpr
    exact ((sourceIOrder_iff_native ⟨θ i, hu i⟩ ⟨η i, hv i⟩).mp (hI i)).trans
      (iOrderOnManifold_of_le_add
        ((isThetaPSH_iff_nativeThetaPotential (θ i) _).mp (hv' i)).1.quasiPlurisubharmonic
        (fun x => hB x (mem_univ x)))
  exact (sourceEnvelopeMixedIVolume_mono_of_sourceIOrder ω hu hv' hI').trans_eq
    (sourceEnvelopeMixedIVolume_changeRepresentative ω η θ v g hchange hv)

end SGPT.PSH.VariableComplexAtlas
