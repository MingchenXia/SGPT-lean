import SGPT.Foundations.Analysis.Pending.RawUnramifiedLelongCovariance
import SGPT.Foundations.Analysis.Pending.QuasiPshLelongUpperSemicontinuity
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

set_option autoImplicit false

/-! # Whole raw Lelong readers on actual strict transforms under proper maps

Actual Remmert mapping and irreducibility produce the whole image.
Literal unramified covariance and two closed superlevels then produce reader invariance.
No finite factorization, center-pole implication or Lelong compatibility is assumed.
-/

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawProperStrictTransformLelongReader

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences

noncomputable section

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Proper image analyticity and a genuinely unramified seed internally
produce the whole image of the given actual strict transform. -/
theorem image_eq_of_strictTransform {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hproper : IsProperMap π) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (Vt : ClosedIrreducibleAnalyticSubvariety n Y)
    (hstrict : Vt.carrier = strictTransform n π V.carrier) :
    π '' Vt.carrier = V.carrier := by
  have hnon : (π ⁻¹' V.carrier \ exceptionalLocus n π).Nonempty := by
    apply closure_nonempty_iff.mp
    change (strictTransform n π V.carrier).Nonempty
    rw [← hstrict]
    exact Vt.nonempty
  obtain ⟨y, hyV, hyE⟩ := hnon
  have hO := StrictTransformComposition.isOpen_compl_exceptionalLocus hπ
  have himgnbhd : π '' (exceptionalLocus n π)ᶜ ∈ 𝓝 (π y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hπ hyE]
    exact image_mem_map (hO.mem_nhds hyE)
  obtain ⟨U, hUsub, hU, hyU⟩ := _root_.mem_nhds_iff.mp himgnbhd
  have himga : IsComplexAnalyticSubset (n := n) (π '' Vt.carrier) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hπ Vt.analytic fun K hK =>
      (hproper.isCompact_preimage hK).inter_left Vt.isClosed_carrier
  have hVsub : V.carrier ⊆ π '' Vt.carrier := by
    apply StrictTransformLocus.subset_of_inter_isOpen_subset V himga hU ⟨π y, hyV, hyU⟩
    rintro x ⟨hxV, hxU⟩
    obtain ⟨z, hzE, hzx⟩ := hUsub hxU
    refine ⟨z, ?_, hzx⟩
    rw [hstrict]
    apply subset_closure
    exact ⟨by change π z ∈ V.carrier; rwa [hzx], hzE⟩
  have htsub : Vt.carrier ⊆ π ⁻¹' V.carrier := by
    rw [hstrict]
    exact closure_minimal sdiff_subset (V.isClosed_carrier.preimage hπ.continuous)
  exact subset_antisymm (by rintro x ⟨y, hy, rfl⟩; exact htsub hy) hVsub

/-- Literal unramified covariance extends along the two actual dense sets
to the whole raw reader, including infinite values and identically bot weights. -/
theorem iInf_lelongNumber_comp_eq_of_strictTransform {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hproper : IsProperMap π) {u : X → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (Vt : ClosedIrreducibleAnalyticSubvariety n Y)
    (hstrict : Vt.carrier = strictTransform n π V.carrier) :
    (⨅ y ∈ Vt.carrier, lelongNumber (n := n) (fun y => u (π y)) y) =
      ⨅ x ∈ V.carrier, lelongNumber (n := n) u x := by
  let S : Set Y := π ⁻¹' V.carrier \ exceptionalLocus n π
  have hclosure : Vt.carrier = closure S := hstrict
  have himage := image_eq_of_strictTransform hπ hproper V Vt hstrict
  have huP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ hu
  let L : ℝ≥0∞ := ⨅ x ∈ V.carrier, lelongNumber (n := n) u x
  let K : ℝ≥0∞ := ⨅ y ∈ Vt.carrier, lelongNumber (n := n) (fun y => u (π y)) y
  have hcS : IsClosed ((fun y => lelongNumber (n := n) (fun y => u (π y)) y) ⁻¹' Ici L) :=
    (QuasiPshLelongUpperSemicontinuity.upperSemicontinuous_lelongNumber huP).isClosed_preimage L
  have hsubS : S ⊆ (fun y => lelongNumber (n := n) (fun y => u (π y)) y) ⁻¹' Ici L := by
    intro y hy
    change L ≤ lelongNumber (n := n) (fun y => u (π y)) y
    rw [RawUnramifiedLelongCovariance.lelongNumber_comp_eq_of_not_exceptional hπ hy.2]
    exact iInf₂_le (π y) hy.1
  have hLK : L ≤ K := by
    apply le_iInf₂
    intro y hy
    exact closure_minimal hsubS hcS (hclosure ▸ hy)
  have hcT : IsClosed ((fun x => lelongNumber (n := n) u x) ⁻¹' Ici K) :=
    (QuasiPshLelongUpperSemicontinuity.upperSemicontinuous_lelongNumber hu).isClosed_preimage K
  have hsubT : π '' S ⊆ (fun x => lelongNumber (n := n) u x) ⁻¹' Ici K := by
    rintro x ⟨y, hy, rfl⟩
    change K ≤ lelongNumber (n := n) u (π y)
    rw [← RawUnramifiedLelongCovariance.lelongNumber_comp_eq_of_not_exceptional hπ hy.2]
    exact iInf₂_le y (hclosure.symm ▸ subset_closure hy)
  have hVcl : V.carrier ⊆ closure (π '' S) := by
    rw [← himage, hclosure]
    exact image_closure_subset_closure_image hπ.continuous
  have hKL : K ≤ L := by
    apply le_iInf₂
    intro x hx
    exact closure_minimal hsubT hcT (hVcl hx)
  exact le_antisymm hKL hLK

end
end SGPT.Foundations.Analysis.Pending.RawProperStrictTransformLelongReader
