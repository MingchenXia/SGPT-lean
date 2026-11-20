import SGPT.Projective.NativeRegularSectionMultiplicity
import SGPT.Projective.NativeSubmanifoldArea

/-! Actual original ambient/member windows for full current comparison.
Blueprint: `native-regular-member-window.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open DivisorRegularLocus

variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hl : IsSmoothHypersurfaceMember (m + 1)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- A genuine original ambient neighborhood reads the SAME entire native
member in ONE native chart and the SAME original coefficient's regular
zero locus. All chart/frame/presentation domains are produced. -/
theorem exists_native_member_window :
    let p := sourceNativeFiniteSectionProjectiveMap L s hgen
    let hp := sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen
    let W := member p l
    let hW := fun x (hx : x ∈ W) => regularAtDim_member p hp hl hx
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hW
    ∀ x ∈ W,
      ∃ (E : AtlasFrame L) (c : ComplexChart (m + 1) X)
        (P : RegularPresentation
          (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm) (c.val x))
        (e : ComplexChart m W) (O : Set X),
        P.m = 1 ∧ IsOpen O ∧ x ∈ O ∧ O ⊆ E.val.baseSet ∩ c.val.source ∧
        (∀ y : W, y.1 ∈ O → y ∈ e.val.source ∧ c.val y.1 ∈ P.U) ∧
        regularLocus
            (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm) ∩
              (c.val '' O) = c.val '' (W ∩ O) := by
  let p := sourceNativeFiniteSectionProjectiveMap L s hgen
  let hp := sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen
  let W := member p l
  let hW := fun x (hx : x ∈ W) => regularAtDim_member p hp hl hx
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hW
  dsimp only
  intro x hx
  let E : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  have hxE : x ∈ E.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  obtain ⟨c, hxc, P, hPm, _⟩ :=
    exists_regularPresentation_linearSection L s hgen l hl E x hxE hx
  let e : ComplexChart m W := complexChartAt ⟨x, hx⟩
  have hxe : (⟨x, hx⟩ : W) ∈ e.val.source := mem_complexChartAt_source _
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp e.val.open_source
  have hxV : x ∈ V := by
    have h := hxe
    rw [← hVe] at h
    exact h
  let O := (V ∩ E.val.baseSet) ∩ (c.val.source ∩ c.val ⁻¹' P.U)
  have hO : IsOpen O :=
    (hV.inter E.val.open_baseSet).inter (c.val.isOpen_inter_preimage P.isOpen)
  have hxO : x ∈ O := ⟨⟨hxV, hxE⟩, hxc, P.mem⟩
  have hOsub : O ⊆ E.val.baseSet ∩ c.val.source := fun _ hy => ⟨hy.1.2, hy.2.1⟩
  have hmem : ∀ y : W, y.1 ∈ O → y ∈ e.val.source ∧ c.val y.1 ∈ P.U := by
    intro y hy
    refine ⟨?_, hy.2.2⟩
    rw [← hVe]
    exact hy.1.1
  refine ⟨E, c, P, e, O, hPm, hO, hxO, hOsub, hmem, ?_⟩
  ext ζ
  constructor
  · rintro ⟨hζ, y, hyO, rfl⟩
    have hyE := (hOsub hyO).1
    have hyc := (hOsub hyO).2
    have hg0 := eq_zero_of_mem_regularLocus hζ
    have hcoef : sectionCoefficient L.Fiber E.val (linearSection L s l) y = 0 := by
      simpa only [Function.comp_apply, c.val.left_inv hyc] using hg0
    have hs0 : linearSection L s l y = 0 := by
      let := E.property
      apply (E.val.linearEquivAt ℂ y hyE).injective
      exact hcoef.trans (map_zero _).symm
    exact ⟨y, ⟨(linearSection_zero_iff L s hgen l y).mp hs0, hyO⟩, rfl⟩
  · rintro ⟨y, ⟨hyW, hyO⟩, rfl⟩
    have hyE := (hOsub hyO).1
    have hyc := (hOsub hyO).2
    have hyP := (hmem ⟨y, hyW⟩ hyO).2
    have hg0 : (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm)
        (c.val y) = 0 := by
      let := E.property
      rw [Function.comp_apply, c.val.left_inv hyc]
      change (E.val.linearEquivAt ℂ y hyE) (linearSection L s l y) = 0
      rw [(linearSection_zero_iff L s hgen l y).mpr hyW, map_zero]
    exact ⟨P.mem_regularLocus_of_mem hyP hg0, y, hyO, rfl⟩

end SGPT.Projective.NumEq.CompleteIntersections
