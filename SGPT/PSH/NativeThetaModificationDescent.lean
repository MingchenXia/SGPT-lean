import SGPT.PSH.NativeQPSHPullback
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent

/-! # Literal original theta-PSH descent from a compact modification source

The atlas is the entire native holomorphic atlas. The pulled background is the
literal whole tensor constructed in `NativeQPSHPullback`. The source may be
empty, disconnected, or zero-dimensional. No Kähler background is required.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Surjectivity of the actual modification makes its whole target compact
from the original compact source, with no nonemptiness or Kähler hypothesis. -/
theorem compactSpace_of_compact_nativeModification_source [CompactSpace Y]
    {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    CompactSpace X := by
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  refine ⟨?_⟩
  have he : π '' (univ : Set Y) = univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨y, rfl⟩ := hs x
      exact mem_image_of_mem π (mem_univ y)
  simpa only [he] using (isCompact_univ.image hπ.1.continuous)

/-- The original universal theta predicate descends with literal values on
every fibre. The compact target, descent and uniqueness are all produced. -/
theorem existsUnique_nativeThetaPSH_descent [CompactSpace Y]
    {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {w : Y → EReal}
    (hw : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w) :
    ∃! u : X → EReal, (ofFixedModel n X).IsThetaPSH θ u ∧ u ∘ π = w := by
  let : CompactSpace X := compactSpace_of_compact_nativeModification_source hπ
  have hn := (isThetaPSH_iff_nativeThetaPotential (θ.nativeHolomorphicPullback hπ.1) w).mp hw
  obtain ⟨u, hu, he⟩ :=
    AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hπ
      (atlasClosedFormToNative θ) hn
  refine ⟨u, ⟨(isThetaPSH_iff_nativeThetaPotential θ u).mpr hu, funext he⟩, ?_⟩
  intro v hv
  funext x
  obtain ⟨y, rfl⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ x
  exact (congrFun hv.2 y).trans (he y).symm

/-- Literal pullback between the original all-chart theta-PSH carriers is an
order isomorphism. Its inverse is genuine whole-fibre descent, not a class map. -/
def nativeThetaPSHPullbackOrderIso [CompactSpace Y]
    {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    {u : X → EReal // (ofFixedModel n X).IsThetaPSH θ u} ≃o
      {w : Y → EReal // (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w} := by
  let f : {u : X → EReal // (ofFixedModel n X).IsThetaPSH θ u} →
      {w : Y → EReal // (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w} :=
    fun u => ⟨u.val ∘ π, u.property.comp_native_analyticModification hπ⟩
  have hi : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ x
    exact congrFun (congrArg Subtype.val he) y
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨u, hu, _⟩ := existsUnique_nativeThetaPSH_descent hπ θ w.property
    refine ⟨⟨u, hu.1⟩, ?_⟩
    exact Subtype.ext hu.2
  refine { Equiv.ofBijective f ⟨hi, hs⟩ with map_rel_iff' := ?_ }
  intro u v
  change (∀ y, u.val (π y) ≤ v.val (π y)) ↔ ∀ x, u.val x ≤ v.val x
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ x
    exact h y
  · intro h y
    exact h (π y)

/-- The exported order isomorphism applies as the same original composition,
including every exceptional fibre and every infinite pole value. -/
theorem nativeThetaPSHPullbackOrderIso_apply [CompactSpace Y]
    {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : {u : X → EReal // (ofFixedModel n X).IsThetaPSH θ u}) :
    (nativeThetaPSHPullbackOrderIso hπ θ u).val = u.val ∘ π := rfl

end SGPT.PSH.VariableComplexAtlas
