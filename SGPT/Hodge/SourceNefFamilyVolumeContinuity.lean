import SGPT.Hodge.SourceModelModifiedNef
import SGPT.Hodge.SourceNefProjectiveFamilies
import SGPT.Hodge.SourceCartierFamilySequenceAlgebra
import SGPT.Hodge.BDivVolumeNetRealDraft

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open Set Filter
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
  SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

local notation "Sys" => ModelSystem.blowup n X

omit [ConnectedSpace X] in
/-- Finite sums retain the actual classes on every original model. -/
theorem family_sum_onModel {I : Type*} (s : Finset I)
    (D : I → WeilFamilyAny Sys) (π : (ModelSystem.blowup n X).Model) :
    (∑ i ∈ s, D i).val π=∑ i ∈ s, (D i).val π := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    change (D a).val π+(∑ i ∈ s,D i).val π= _
    rw [ih]

/-- The original nef predicate supplies actual modelwise pseudo-effectivity. -/
theorem isPseudoeffectiveAny_of_isNef (ω : KahlerBackground n X)
    (D : WeilFamilyAny Sys) (hD : IsNefAny D) : IsPseudoeffectiveAny D := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero D
  | succ m =>
    intro π
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    exact classPseudoeffective_of_modifiedNef κ
      ((WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup ⟨ω⟩
        ((isNefAny_iff_existing (Nat.succ_pos m) D).mp hD) π).2 κ)

omit [ConnectedSpace X] in
/-- Actual zero potentials prove pseudo-effectivity of the zero family. -/
theorem isPseudoeffectiveAny_zero (ω : KahlerBackground n X) :
    IsPseudoeffectiveAny (0 : WeilFamilyAny Sys) := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero 0
  | succ m =>
    intro π
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    change ClassPseudoeffectiveViaPotentials (0 : RealBottChern (m+1) π.1.carrier)
    rw [←RealBottChern.ofRepresentative_zero]
    apply (classPseudoeffectiveViaPotentials_ofRepresentative _).mpr
    refine ⟨fun _ => (0 : EReal),(LocalPotentials.isThetaPshPotential_zero_iff _).mpr ?_⟩
    simpa only [zero_smul] using
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (show (0 : ℝ)≤0 by norm_num))

omit [ConnectedSpace X] in
/-- Sums of actual positive source class witnesses remain pseudo-effective. -/
theorem isPseudoeffectiveAny_add {D E : WeilFamilyAny Sys}
    (hD : IsPseudoeffectiveAny D) (hE : IsPseudoeffectiveAny E) :
    IsPseudoeffectiveAny (D+E) := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero (D+E)
  | succ m =>
    intro π
    exact SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_add (hD π) (hE π)

omit [ConnectedSpace X] in
theorem isPseudoeffectiveAny_smul {D : WeilFamilyAny Sys}
    (hD : IsPseudoeffectiveAny D) {c : ℝ} (hc : 0≤c) :
    IsPseudoeffectiveAny (c • D) := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero (c • D)
  | succ m =>
    intro π
    exact SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul (hD π) hc

omit [ConnectedSpace X] in
/-- Every actual finite subset sum has genuine modelwise positivity. -/
theorem isPseudoeffectiveAny_sum (ω : KahlerBackground n X) {I : Type*}
    (s : Finset I) (D : I → WeilFamilyAny Sys)
    (hD : ∀ i ∈ s,IsPseudoeffectiveAny (D i)) : IsPseudoeffectiveAny (∑ i ∈ s,D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isPseudoeffectiveAny_zero ω
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPseudoeffectiveAny_add (hD a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hD i (Finset.mem_insert_of_mem hi)))

omit [ConnectedSpace X] in
/-- Original finite subset sums preserve the ORIGINAL pseudo-effective family order. -/
theorem leAny_sum (ω : KahlerBackground n X) {I : Type*}
    (s : Finset I) (D E : I → WeilFamilyAny Sys)
    (hDE : ∀ i ∈ s,LEAny (D i) (E i)) : LEAny (∑ i ∈ s,D i) (∑ i ∈ s,E i) := by
  have hp := isPseudoeffectiveAny_sum ω s (fun i => E i-D i) hDE
  intro π
  have he : (∑ i ∈ s,E i)-(∑ i ∈ s,D i)=∑ i ∈ s,(E i-D i) :=
    (Finset.sum_sub_distrib E D).symm
  change ClassPseudoeffectiveViaPotentials (((∑ i ∈ s,E i)-(∑ i ∈ s,D i)).val π)
  rw [he]
  exact hp π

omit [ConnectedSpace X] in
/-- No countability/cofinality assumption: finite addition is continuous
in every actual model's original Euclidean topology. -/
theorem convergesAny_sum {I J : Type*} {l : Filter J}
    (s : Finset I) (D : I → J → WeilFamilyAny Sys) (E : I → WeilFamilyAny Sys)
    (hc : ∀ i ∈ s,ConvergesAny l (D i) (E i)) :
    ConvergesAny l (fun j => ∑ i ∈ s,D i j) (∑ i ∈ s,E i) := by
  intro π
  rw [tendsto_euclideanTopology_iff]
  intro f
  simp_rw [family_sum_onModel,map_sum]
  exact tendsto_finsetSum s (fun i hi => (tendsto_euclideanTopology_iff.mp (hc i hi π)) f)

/-- Genuine original pure-volume order, on the full actual model family. -/
theorem volumeAny_mono_of_pseudoeffective (ω : KahlerBackground n X)
    {D E : WeilFamilyAny Sys} (hD : IsPseudoeffectiveAny D)
    (hE : IsPseudoeffectiveAny E) (hDE : LEAny D E) : volumeAny D≤volumeAny E := by
  classical
  unfold volumeAny
  rw [if_pos hD,if_pos hE]
  apply iInf_mono
  intro π
  cases n with
  | zero => simp only [SGPT.Hodge.BDivChain.modelClassVolume_eq_one_of_dim_zero,le_refl]
  | succ m =>
    let : MeasurableSpace π.1.carrier := borel π.1.carrier
    have : BorelSpace π.1.carrier := ⟨rfl⟩
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground ⟨ω⟩ π
    change SGPT.PSH.VariableComplexAtlas.sourceClassVolume (D.val π)≤
      SGPT.PSH.VariableComplexAtlas.sourceClassVolume (E.val π)
    have h := SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_le_add_of_pseudoeffective
      κ (hD π) (hDE π)
    simpa only [add_sub_cancel] using h

/-- Smooth/pseudo-effective scalar perturbations converge in the actual
pure volume for EVERY scalar filter, without a monotonicity-output premise. -/
theorem volumeAny_add_smul_tendsto (ω : KahlerBackground n X)
    {I : Type*} {l : Filter I} [l.NeBot]
    (D C : WeilFamilyAny Sys) (hD : IsPseudoeffectiveAny D) (hC : IsPseudoeffectiveAny C)
    (c : I → ℝ) (hc : ∀ i,0≤c i) (hc0 : Tendsto c l (𝓝 0)) :
    Tendsto (fun i => volumeAny (D+c i • C)) l (𝓝 (volumeAny D)) := by
  have hp i : IsPseudoeffectiveAny (D+c i • C) :=
    isPseudoeffectiveAny_add hD (isPseudoeffectiveAny_smul hC (hc i))
  have hconv : ConvergesAny l (fun i => D+c i • C) D :=
    convergesAny_add_smul_zero (by
      intro π
      rw [tendsto_euclideanTopology_iff]
      intro f
      exact tendsto_const_nhds) C hc0
  have hle i : volumeAny D≤volumeAny (D+c i • C) := by
    apply volumeAny_mono_of_pseudoeffective ω hD (hp i)
    intro π
    change ClassPseudoeffectiveViaPotentials ((D.val π+c i • C.val π)-D.val π)
    have hh := isPseudoeffectiveAny_smul hC (hc i) π
    change ClassPseudoeffectiveViaPotentials (c i • C.val π) at hh
    simpa only [add_sub_cancel_left] using hh
  exact tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le (h := Eventually.of_forall hle))
    (limsup_volumeAny_le_blowup ⟨ω⟩ hp hconv)

/-- Every subset sum in an arbitrary actual decreasing net has the genuine
finite real-volume limit needed for signed finite polarization. -/
theorem volumeRealAny_sum_tendsto_of_antitone (ω : KahlerBackground n X)
    {I J : Type*} [Preorder J] [IsDirected J (·≤·)] [Nonempty J]
    (s : Finset I) (D : I → J → WeilFamilyAny Sys) (E : I → WeilFamilyAny Sys)
    (hp : ∀ i ∈ s,∀ j,IsPseudoeffectiveAny (D i j))
    (ha : ∀ i ∈ s,∀ j k,j≤k → LEAny (D i k) (D i j))
    (hc : ∀ i ∈ s,ConvergesAny atTop (D i) (E i)) :
    Tendsto (fun j => volumeRealAny (∑ i ∈ s,D i j)) atTop
      (𝓝 (volumeRealAny (∑ i ∈ s,E i))) := by
  apply tendsto_volumeRealAny_of_antitone_blowup ⟨ω⟩
  · intro j
    exact isPseudoeffectiveAny_sum ω s _ (fun i hi => hp i hi j)
  · intro j k hjk
    exact leAny_sum ω s _ _ (fun i hi => ha i hi j k hjk)
  · exact convergesAny_sum s D E hc

end SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
