import SGPT.PSH.AtlasCohomologyPullback
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! GENUINE disjoint-union variable atlas: exact native overlaps within one
component and PROVED empty overlaps across distinct components. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {I : Type u} {C : I → Type u} [∀ c,TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c,ChartedSpace (ComplexModel (n c)) (C c)] [∀ c,IsComplexManifold (n c) (C c)]

/-- One genuine native chart extended along its actual OPEN sigma embedding. -/
def sigmaNativeChart (t : (c : I) × ComplexChart (n c) (C c)) :
    OpenPartialHomeomorph ((c : I) × C c) (ComplexModel (n t.1)) :=
  t.2.val.lift_openEmbedding (f := Sigma.mk t.1) Topology.IsOpenEmbedding.sigmaMk

omit [∀ c,IsComplexManifold (n c) (C c)] in
/-- Distinct actual components have no chart overlap; no compatibility
certificate is supplied to the disjoint-union construction. -/
theorem sigmaNativeChart_transition_empty {c d : I} (hcd : c≠d)
    (e : ComplexChart (n c) (C c)) (f : ComplexChart (n d) (C d)) :
    ((sigmaNativeChart ⟨c,e⟩).symm.trans (sigmaNativeChart ⟨d,f⟩)).source=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  change z∈e.val.target ∧ Sigma.mk c (e.val.symm z)∈Sigma.mk d '' f.val.source at hz
  obtain ⟨p,_hp,heq⟩ := hz.2
  exact hcd (congrArg Sigma.fst heq).symm

/-- The genuine varying-dimension atlas of the ACTUAL disjoint union of
native complex manifolds, including arbitrary empty index families. -/
def sigmaNativeAtlas : VariableComplexAtlas ((c : I) × C c) where
  Index := (c : I) × ComplexChart (n c) (C c)
  dimension := fun t => n t.1
  chart := sigmaNativeChart
  cover := by
    rintro ⟨c,p⟩
    obtain ⟨e,he⟩ := (ofFixedModel (n c) (C c)).cover p
    exact ⟨⟨c,e⟩,p,he,rfl⟩
  holomorphic := by
    rintro ⟨c,e⟩ ⟨d,f⟩
    by_cases hcd : c=d
    · subst d
      change DifferentiableOn ℂ
        ((e.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk).symm.trans
          (f.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk))
        ((e.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk).symm.trans
          (f.val.lift_openEmbedding (f := Sigma.mk c) Topology.IsOpenEmbedding.sigmaMk)).source
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (ofFixedModel (n c) (C c)).holomorphic e f
    · rw [sigmaNativeChart_transition_empty hcd e f]
      exact differentiableOn_empty

/-- SAME-component transitions are LITERALLY the native original transition. -/
theorem sigmaNativeAtlas_transition (c : I)
    (e f : ComplexChart (n c) (C c)) :
    (((sigmaNativeAtlas (n := n) (C := C)).chart ⟨c,e⟩).symm.trans
      ((sigmaNativeAtlas (n := n) (C := C)).chart ⟨c,f⟩))=e.val.symm.trans f.val :=
  OpenPartialHomeomorph.lift_openEmbedding_trans e.val f.val Topology.IsOpenEmbedding.sigmaMk

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
