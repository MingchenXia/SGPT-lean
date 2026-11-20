import SGPT.Hodge.SourceCompactClassUpper
import SGPT.Hodge.SourceMixedLinearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceIntersection SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- Compact ORIGINAL root classes produce an actual GLOBAL original modelwise
Cartier upper for every nef family; no root or family bound is supplied. -/
theorem exists_uniform_family_upper_of_compact_root_pos (ω : KahlerBackground (m+1) X)
    (K : Set (RealBottChern (m+1) X))
    (hK : @IsCompact _ (SGPT.BDivisor.euclideanTopology _) K) :
    ∃ R : ℝ,1≤R ∧ ∀ D : WeilFamilyAny Sys,IsNefAny D → rootClassLinear D∈K →
      LEAny D (R • rootCartierAny (RealBottChern.ofRepresentative ω.form)) := by
  obtain ⟨R,hR,hupper⟩ := exists_uniform_semipositive_upper_of_isCompact ω K hK
  refine ⟨R+1,by linarith,?_⟩
  intro D hD hDK
  let C := rootCartierAny (RealBottChern.ofRepresentative ω.form)
  have hC : IsPseudoeffectiveAny C := rootKahler_pseudoeffective ω
  let B := kahlerPerturbedBigNef ω ω D hD 1 zero_lt_one
  have hDB : LEAny D B.val := by
    intro π
    have hp := hC π
    change ClassPseudoeffectiveViaPotentials ((D.val π+(1 : ℝ) • C.val π)-D.val π)
    convert hp using 1; module
  have hroot (α : RealBottChern (m+1) X) :
      modelCartier ModelSystem.Model.root α=rootCartierAny α := rfl
  have hB : LEAny B.val (rootCartierAny (rootClassLinear B.val)) := by
    have h := bigNefFamily_le_modelCartier ω B ModelSystem.Model.root
    rw [hroot] at h
    exact h
  obtain ⟨θ,hθ,hsemi⟩ := hupper (rootClassLinear D) hDK
  have hp : ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) :=
    ⟨fun _ => 0,(LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hsemi⟩
  have hBc : rootClassLinear B.val=rootClassLinear D+RealBottChern.ofRepresentative ω.form := by
    change rootClassLinear (D+(1 : ℝ) • rootCartierAny (RealBottChern.ofRepresentative ω.form))=_
    rw [map_add,map_smul,rootClassLinear_rootCartier,one_smul]
  have htrace : ClassPseudoeffectiveViaPotentials
      ((R+1) • RealBottChern.ofRepresentative ω.form-rootClassLinear B.val) := by
    convert hp using 1
    rw [hBc,hθ]
    module
  have hcart : LEAny (rootCartierAny (rootClassLinear B.val))
      (rootCartierAny ((R+1) • RealBottChern.ofRepresentative ω.form)) := by
    rw [←hroot,←hroot]
    exact modelCartier_mono htrace
  have h := leAny_trans hDB (leAny_trans hB hcart)
  rw [rootCartierAny_smul] at h
  exact h

end SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
