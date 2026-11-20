import SGPT.PSH.SourceGeneralMixedIVolume
import SGPT.Okounkov.ThetaPotentialCurrentSingularity
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

/-! # Mixed I-volume presentation independence for actual whole currents

The positive-dimensional statements compare the original native degree-two
currents. The original dimension-zero mixed tuple is handled separately by
uniqueness of every Fin0 function, without a surrogate current degree.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame

section PositiveDimension
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Equality of ENTIRE actual currents internally gives equality in the actual
smooth Bott--Chern quotient, with no incoming class or smooth-gauge witness. -/
theorem sourceThetaPotentialCurrent_class_eq
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)} {u v : M → EReal}
    (hu : (ofFixedModel (m + 1) M).IsThetaPSH θ u)
    (hv : (ofFixedModel (m + 1) M).IsThetaPSH η v)
    (heq : thetaPotentialCurrent (atlasClosedFormToNative θ).val u
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) =
      thetaPotentialCurrent (atlasClosedFormToNative η).val v
        ((isThetaPSH_iff_nativeThetaPotential η v).mp hv)) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η) := by
  have ht : ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (atlasClosedFormToNative θ)
        u ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) =
      ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (atlasClosedFormToNative η)
        v ((isThetaPSH_iff_nativeThetaPotential η v).mp hv) := Subtype.ext heq
  have hc := congrArg (CurrentBottChernClass.bottChernClass
    (canonicalBasis (m + 1)) (Nat.succ_pos m)) ht
  simpa only [ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent] using hc

/-- The SAME entire-current equality gives all actual source multiplier ideals
at every positive real level; no ideal or P-equivalence output is a premise. -/
theorem sourceThetaPotentialCurrent_iEquivalent (ω : KahlerBackground (m + 1) M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)} {u v : M → EReal}
    (hu : (ofFixedModel (m + 1) M).IsThetaPSH θ u)
    (hv : (ofFixedModel (m + 1) M).IsThetaPSH η v)
    (heq : thetaPotentialCurrent (atlasClosedFormToNative θ).val u
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) =
      thetaPotentialCurrent (atlasClosedFormToNative η).val v
        ((isThetaPSH_iff_nativeThetaPotential η v).mp hv)) :
    sourceIEquivalent (ofFixedModel (m + 1) M) u v :=
  (sourceIEquivalent_iff_native ⟨θ, hu⟩ ⟨η, hv⟩).mpr
    (SGPT.Okounkov.iEquivalent_of_thetaPotentialCurrent_eq ω
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential η v).mp hv) heq)

/-- Actual whole-current equality in every independent slot preserves the direct
formula, even at zero I-volume. Both smooth classes and I-orders are produced. -/
theorem sourceEnvelopeMixedIVolume_eq_of_thetaPotentialCurrent_eq
    (ω : KahlerBackground (m + 1) M)
    (θ η : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M))
    (u v : Fin (m + 1) → M → EReal)
    (hu : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (η i) (v i))
    (heq : ∀ i, thetaPotentialCurrent (atlasClosedFormToNative (θ i)).val (u i)
        ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) =
      thetaPotentialCurrent (atlasClosedFormToNative (η i)).val (v i)
        ((isThetaPSH_iff_nativeThetaPotential (η i) (v i)).mp (hv i))) :
    sourceEnvelopeMixedIVolume θ u hu = sourceEnvelopeMixedIVolume η v hv := by
  have hclass i := sourceThetaPotentialCurrent_class_eq (hu i) (hv i) (heq i)
  have hI i := sourceThetaPotentialCurrent_iEquivalent ω (hu i) (hv i) (heq i)
  exact le_antisymm
    (sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω θ η u v hu hv
      hclass (fun i => (hI i).1))
    (sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω η θ v u hv hu
      (fun i => (hclass i).symm) (fun i => (hI i).2))

/-- The original SINGLE I-volume, and hence its positivity, is intrinsic to the
same actual whole current, including its possible zero value. -/
theorem sourceIVolume_eq_of_thetaPotentialCurrent_eq (ω : KahlerBackground (m + 1) M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)} {u v : M → EReal}
    (hu : (ofFixedModel (m + 1) M).IsThetaPSH θ u)
    (hv : (ofFixedModel (m + 1) M).IsThetaPSH η v)
    (heq : thetaPotentialCurrent (atlasClosedFormToNative θ).val u
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) =
      thetaPotentialCurrent (atlasClosedFormToNative η).val v
        ((isThetaPSH_iff_nativeThetaPotential η v).mp hv)) :
    sourceIVolume θ u hu = sourceIVolume η v hv := by
  have hm := sourceEnvelopeMixedIVolume_eq_of_thetaPotentialCurrent_eq ω
    (fun _ => θ) (fun _ => η) (fun _ => u) (fun _ => v) (fun _ => hu) (fun _ => hv)
    (fun _ => heq)
  simpa only [sourceEnvelopeMixedIVolume_diagonal] using hm

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem perturbedPSH (ω : KahlerBackground (m + 1) M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)} {u : M → EReal}
    (hu : (ofFixedModel (m + 1) M).IsThetaPSH θ u) (ε : NNReal) :
    (ofFixedModel (m + 1) M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ε.property)

/-- The actual general infimum is invariant under EVERY genuine presentation
of the same native current tuple; all original zero I-volumes remain admitted. -/
theorem sourceGeneralMixedIVolume_eq_of_thetaPotentialCurrent_eq
    (ω : KahlerBackground (m + 1) M)
    (θ η : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M))
    (u v : Fin (m + 1) → M → EReal)
    (hu : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (η i) (v i))
    (heq : ∀ i, thetaPotentialCurrent (atlasClosedFormToNative (θ i)).val (u i)
        ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) =
      thetaPotentialCurrent (atlasClosedFormToNative (η i)).val (v i)
        ((isThetaPSH_iff_nativeThetaPotential (η i) (v i)).mp (hv i))) :
    sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume ω η v hv := by
  have hclass i := sourceThetaPotentialCurrent_class_eq (hu i) (hv i) (heq i)
  have hI i := sourceThetaPotentialCurrent_iEquivalent ω (hu i) (hv i) (heq i)
  unfold sourceGeneralMixedIVolume
  apply iInf_congr
  intro ε
  let Θ : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M) := fun i =>
    nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε.val : ℝ) • ω.form)
  let Η : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M) := fun i =>
    nativeClosedFormToAtlas (atlasClosedFormToNative (η i) + (ε.val : ℝ) • ω.form)
  have hΘ i : (ofFixedModel (m + 1) M).IsThetaPSH (Θ i) (u i) := perturbedPSH ω (hu i) ε
  have hΗ i : (ofFixedModel (m + 1) M).IsThetaPSH (Η i) (v i) := perturbedPSH ω (hv i) ε
  have hc i : RealBottChern.ofRepresentative (atlasClosedFormToNative (Θ i)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (Η i)) := by
    simp only [Θ, Η, sourceNativeAtlasForm_roundTrip, RealBottChern.ofRepresentative_add,
      hclass i]
  exact le_antisymm
    (sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω Θ Η u v hΘ hΗ
      hc (fun i => (hI i).1))
    (sourceEnvelopeMixedIVolume_mono_of_class_eq_of_sourceIOrder ω Η Θ v u hΗ hΘ
      (fun i => (hc i).symm) (fun i => (hI i).2))
end PositiveDimension

section ZeroDimension
variable {M0 : Type*} [TopologicalSpace M0]
  [ChartedSpace (ComplexModel 0) M0] [IsComplexManifold 0 M0]
  [MeasurableSpace M0] [BorelSpace M0] [CompactSpace M0] [ConnectedSpace M0]

/-- Original dimension0 presentation independence uses only the UNIQUE Fin0
form/potential tuples; no invented degree-two current or numerical massvalue. -/
theorem sourceMixedIVolume_presentation_independent_zero (ω Ω : KahlerBackground 0 M0)
    (θ η : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 M0))
    (u v : Fin 0 → M0 → EReal)
    (hu : ∀ i, (ofFixedModel 0 M0).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel 0 M0).IsThetaPSH (η i) (v i)) :
    sourceEnvelopeMixedIVolume θ u hu = sourceEnvelopeMixedIVolume η v hv ∧
      sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume Ω η v hv := by
  have eθ : θ = η := Subsingleton.elim θ η
  have eu : u = v := Subsingleton.elim u v
  subst η
  subst v
  exact ⟨rfl, sourceGeneralMixedIVolume_kahler_independent ω Ω θ u hu⟩
end ZeroDimension

end SGPT.PSH.VariableComplexAtlas
