import SGPT.Hodge.SourceCartierKahlerRows
import SGPT.Hodge.SourceCartierDiagonalIndex

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
open scoped Topology

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Subtracting the same ACTUAL family preserves the literal modelwise order. -/
theorem leAny_sub_const {S : ModelSystem n X} {D E : WeilFamilyAny S}
    (h : LEAny D E) (C : WeilFamilyAny S) : LEAny (D-C) (E-C) := by
  intro π
  change ClassPseudoeffectiveViaPotentials ((E.val π-C.val π)-(D.val π-C.val π))
  have he : (E.val π-C.val π)-(D.val π-C.val π)=E.val π-D.val π := by abel
  rw [he]
  exact h π

/-- Subtraction is continuous in the ORIGINAL topology on every actual model. -/
theorem convergesAny_sub_const {S : ModelSystem n X} {I : Type*} {l : Filter I}
    {A : I → WeilFamilyAny S} {A₀ : WeilFamilyAny S}
    (h : ConvergesAny l A A₀) (C : WeilFamilyAny S) :
    ConvergesAny l (fun i => A i-C) (A₀-C) := by
  intro π
  rw [tendsto_euclideanTopology_iff]
  intro f
  have hf := (tendsto_euclideanTopology_iff.mp (h π)) f
  change Tendsto (fun i => f ((A i).val π-C.val π)) l (𝓝 (f (A₀.val π-C.val π)))
  simpa only [map_sub] using hf.sub_const (f (C.val π))

theorem convergesAny_comp {S : ModelSystem n X} {I J : Type*} {l : Filter I} {k : Filter J}
    {A : I → WeilFamilyAny S} {A₀ : WeilFamilyAny S}
    (h : ConvergesAny l A A₀) {j : J → I} (hj : Tendsto j k l) :
    ConvergesAny k (fun i => A (j i)) A₀ := fun π => (h π).comp hj

/-- A vanishing real multiple of one ACTUAL fixed family does not alter
the original modelwise topology limit. -/
theorem convergesAny_add_smul_zero {S : ModelSystem n X} {I : Type*} {l : Filter I}
    {A : I → WeilFamilyAny S} {A₀ : WeilFamilyAny S}
    (h : ConvergesAny l A A₀) (C : WeilFamilyAny S) {c : I → ℝ}
    (hc : Tendsto c l (𝓝 0)) : ConvergesAny l (fun i => A i+c i • C) A₀ := by
  intro π
  rw [tendsto_euclideanTopology_iff]
  intro f
  have hf := (tendsto_euclideanTopology_iff.mp (h π)) f
  change Tendsto (fun i => f ((A i).val π+c i • C.val π)) l (𝓝 (f (A₀.val π)))
  simpa only [map_add,map_smul,smul_eq_mul,zero_mul,add_zero] using hf.add (hc.mul_const (f (C.val π)))

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X] [CompactSpace X]

/-- Genuine nonnegative smooth pullback gives pseudo-effectivity on EVERY
actual original model, with its actual zero potential as witness. -/
theorem rootKahler_isPseudoeffectiveAny (ω : KahlerBackground (m+1) X) :
    IsPseudoeffectiveAny (rootCartierAny (RealBottChern.ofRepresentative ω.form)) := by
  intro π
  change ClassPseudoeffectiveViaPotentials
    ((rootCartier (RealBottChern.ofRepresentative ω.form)).onModel π)
  rw [rootCartier_onModel,classPullback_ofRepresentative]
  exact ⟨fun _ => 0,(LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (ClosedRealOneOneForm.pullback_isSemipositive π.1.contMDiff_map ω.isSemipositive)⟩

/-- Original class order is compatible with adding a larger nonnegative
multiple of a genuinely pseudo-effective fixed family. -/
theorem leAny_add_smul {S : ModelSystem (m+1) X} {D E : WeilFamilyAny S}
    (hDE : LEAny D E) {C : WeilFamilyAny S} (hC : IsPseudoeffectiveAny C)
    {a b : ℝ} (hab : a ≤ b) : LEAny (D+a • C) (E+b • C) := by
  intro π
  have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_add
    (hDE π) (SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul
      (hC π) (sub_nonneg.mpr hab))
  change ClassPseudoeffectiveViaPotentials ((E.val π+b • C.val π)-(D.val π+a • C.val π))
  convert hp using 1
  module

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
