import SGPT.Trace.NativeCanonicalPhysicalHodgeIntegral

/-! Produced finite native chart partition with exact prescribed first
piece; intrinsic physical Hodge energy dominates every actual chart subset. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem exists_nativeCanonicalChartPartition_leading_piece
    (c : ComplexChart n X) (W : Set X) (hW : MeasurableSet W) (hsub : W ⊆ c.val.source) :
    ∃ (P : NativeCanonicalChartPartition n X) (i : Fin P.size), P.chart i = c ∧ P.piece i = W := by
  classical
  let P := Classical.choice (exists_nativeCanonicalChartPartition (n := n) (X := X))
  let V : Fin (P.size + 1) → Set X := Fin.cases W P.piece
  let e : Fin (P.size + 1) → ComplexChart n X := Fin.cases c P.chart
  have hV : ∀ i, MeasurableSet (V i) := Fin.cases hW P.measurable_piece
  have hVe : ∀ i, V i ⊆ (e i).val.source := Fin.cases hsub P.piece_subset
  have hcover : ⋃ i, V i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp (show x ∈ ⋃ i, P.piece i by rw [P.cover]; exact mem_univ x)
    exact mem_iUnion.mpr ⟨i.succ,hi⟩
  let Q : NativeCanonicalChartPartition n X := {
    size := P.size + 1
    chart := e
    piece := disjointed V
    measurable_piece := fun i => disjointedRec (fun {t j} ht => ht.diff (hV j)) (hV i)
    piece_subset := fun i => (disjointed_subset V i).trans (hVe i)
    disjoint_piece := disjoint_disjointed V
    cover := by rw [iUnion_disjointed,hcover] }
  refine ⟨Q,0,rfl,?_⟩
  change disjointed V (⊥ : Fin (P.size + 1)) = W
  exact (disjointed_bot V).trans rfl

variable [IsComplexManifold n X] (L : HermitianHolomorphicLineBundle n X)
  (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)

theorem nativePhysicalHodgeEnergy_ge_chartSubset
    (c : ComplexChart n X) (W : Set X) (hW : MeasurableSet W) (hsub : W ⊆ c.val.source) :
    (∫⁻ z in c.val '' W, nativeCanonicalPhysicalCoordinateDensity L S w c z) ≤
      nativePhysicalHodgeEnergy L S w := by
  classical
  obtain ⟨P,i,hc,hpiece⟩ := exists_nativeCanonicalChartPartition_leading_piece c W hW hsub
  rw [nativePhysicalHodgeEnergy_eq_partition L S w P]
  change (∫⁻ z in c.val '' W, nativeCanonicalPhysicalCoordinateDensity L S w c z) ≤
    ∑ j : Fin P.size, ∫⁻ z in (P.chart j).val '' P.piece j,
      nativeCanonicalPhysicalCoordinateDensity L S w (P.chart j) z
  have h := Finset.single_le_sum (f := fun j : Fin P.size =>
    ∫⁻ z in (P.chart j).val '' P.piece j, nativeCanonicalPhysicalCoordinateDensity L S w (P.chart j) z)
    (fun _ _ => zero_le) (Finset.mem_univ i)
  simpa only [hc,hpiece] using h

end SGPT.Trace.Bertini
