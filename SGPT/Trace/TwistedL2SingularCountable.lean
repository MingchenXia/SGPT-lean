import SGPT.Trace.TwistedL2SingularLocalBound

/-!
# Countable chart-frame cover for the section limit

The original complex-manifold assumption already includes second countability.
Its Lindelöf property supplies a countable cover by actual preferred chart and
line-bundle frame neighborhoods.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The actual preferred chart and preferred bundle frame at a point. -/
def preferredChartFrameDomain (L : HermitianHolomorphicLineBundle.{0, 0} n X) (y : X) : Set X :=
  (complexChartAt (n := n) y).val.source ∩ (trivializationAt ℂ L.Fiber y).baseSet

/-- A countable family of actual preferred chart-frame neighborhoods covers
all of the original complex manifold, without compactness of the manifold. -/
theorem exists_countable_preferredChartFrame_cover
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) :
    ∃ D : Set X, D.Countable ∧ ∀ x : X, ∃ y ∈ D, x ∈ preferredChartFrameDomain L y := by
  let W : X → Set X := preferredChartFrameDomain L
  have hWo : ∀ y, IsOpen (W y) := fun y =>
    ((complexChartAt (n := n) y).val.open_source).inter
      (trivializationAt ℂ L.Fiber y).open_baseSet
  have hcover : (univ : Set X) ⊆ ⋃ y, W y := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_complexChartAt_source x,
      mem_baseSet_trivializationAt ℂ L.Fiber x⟩
  obtain ⟨D, hD, hDcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof (univ : Set X)).elim_countable_subcover W hWo hcover
  refine ⟨D, hD, fun x => ?_⟩
  obtain ⟨y, hyD, hxW⟩ := mem_iUnion₂.mp (hDcov (mem_univ x))
  exact ⟨y, hyD, hxW⟩


/-- The preferred actual holomorphic frame, bundled with its atlas membership. -/
def preferredAtlasFrame (L : HermitianHolomorphicLineBundle.{0, 0} n X) (y : X) : AtlasFrame L :=
  ⟨trivializationAt ℂ L.Fiber y, inferInstance⟩

/-- Choose countably many actual chart-frame domains covering `X` and, in
each corresponding Euclidean domain, a countable dense set. These are the
actual indices on which one diagonal subsequence will be selected. -/
theorem exists_countable_frame_dense_sets
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) :
    ∃ D : Set X, D.Countable ∧
      (∀ x : X, ∃ y ∈ D, x ∈ preferredChartFrameDomain L y) ∧
      ∃ Q : D → Set (ComplexModel n), ∀ y : D,
        Q y ⊆ chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val) ∧
        (Q y).Countable ∧
        chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val) ⊆
          closure (Q y) := by
  obtain ⟨D, hD, hcover⟩ := exists_countable_preferredChartFrame_cover L
  choose Q hQsub hQc hQdense using fun y : D =>
    (TopologicalSpace.IsSeparable.of_separableSpace
      (chartFrameDomain L (complexChartAt (n := n) y.val)
        (preferredAtlasFrame L y.val))).exists_countable_dense_subset
  exact ⟨D, hD, hcover, Q, fun y => ⟨hQsub y, hQc y, hQdense y⟩⟩

end SGPT.Trace.TwistedL2
