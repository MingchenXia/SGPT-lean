import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
import SGPT.Foundations.Analysis.Pending.ProductTestForms

set_option autoImplicit false

/-!
# The actual base partition times an actual curve cutoff

Independent product-localization producer supporting Xia SGPT PDF0171.
Holomorphic product projections supply chart smoothness; genuine compact
factor supports supply compactness. Actual chart readers agree at every
ambient coordinate, including points outside either chart target.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyProductPartition

open FirstPass

/-- The actual global product cutoff function, not a supplied partition or chart-reading certificate. -/
def productWeight {M T : Type*} (f : M → ℝ) (ζ : T → ℝ) : M × T → ℝ :=
  fun q => f q.1 * ζ q.2

/-- Every actual nonzero product has both factors nonzero, so its topological support lies in the closed product of the factor supports. -/
theorem tsupport_productWeight_subset {M T : Type*} [TopologicalSpace M] [TopologicalSpace T]
    (f : M → ℝ) (ζ : T → ℝ) :
    tsupport (productWeight f ζ) ⊆ tsupport f ×ˢ tsupport ζ := by
  apply closure_minimal ?_ ((isClosed_tsupport f).prod (isClosed_tsupport ζ))
  intro q hq
  exact ⟨subset_tsupport f (left_ne_zero_of_mul hq),
    subset_tsupport ζ (right_ne_zero_of_mul hq)⟩

/-- Actual compact factor supports give an actual compact support on the product. -/
theorem hasCompactSupport_productWeight {M T : Type*} [TopologicalSpace M] [TopologicalSpace T]
    {f : M → ℝ} {ζ : T → ℝ} (hf : HasCompactSupport f) (hζ : HasCompactSupport ζ) :
    HasCompactSupport (productWeight f ζ) :=
  (hf.prod hζ).of_isClosed_subset (isClosed_tsupport _) (tsupport_productWeight_subset f ζ)

/-- The actual finite product family sums to the actual curve cutoff. -/
theorem sum_productWeight_eq {M T : Type*} {m : ℕ} (f : Fin m → M → ℝ)
    (ζ : T → ℝ) (hf : ∀ x, ∑ a, f a x = 1) (q : M × T) :
    (∑ a, productWeight (f a) ζ q) = ζ q.2 := by
  simp only [productWeight, ← Finset.sum_mul, hf, one_mul]

open scoped ProductComplexManifold
open GlobalSlotStokes ProductComplexManifold CompactAffineCurveCharts
  FiniteGeodesicMaximality BedfordTaylorStripCovariance FiniteGeodesicStripCharts
  SingularModelEnergyCoreChartData

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]

/-- The actual holomorphic product projections and global smooth pullback produce chart smoothness of the actual product cutoff. -/
theorem chartSmooth_productWeight {f : M → ℝ} {ζ : T → ℝ}
    (hf : ChartSmooth (n := n) f) (hζ : ChartSmooth (n := 1) ζ) :
    ChartSmooth (n := n + 1) (productWeight f ζ) := by
  have hfst := ProductTestForms.chartSmooth_comp (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) hf
  have hsnd := ProductTestForms.chartSmooth_comp (contMDiff_snd (n := n) (m := 1) (X := M) (Y := T)) hζ
  exact fun e => (hfst e).mul (hsnd e)

private theorem strip_product_model (z : ComplexModel n) (s : ComplexModel 1) :
    stripModelEquiv n (prodModelEquiv n 1 (z, s)) = (z, curveModelEquiv s) := by
  simp [stripModelEquiv, curveModelEquiv]

omit [IsComplexManifold n M] [IsComplexManifold 1 T] in
/-- Actual product chart readers factor into the actual base chart reader and the raw complex curve reader at every ambient coordinate, including unfitted points. -/
theorem chartRead_productWeight_eq (d : ComplexChart n M) (e : ComplexChart 1 T)
    (f : M → ℝ) (ζ : T → ℝ) (q : ComplexModel (n + 1)) :
    chartRead (productComplexChart d e) (productWeight f ζ) q =
      stripCutoff (chartRead d f) (fun σ => chartRead e ζ (curveModelEquiv.symm σ)) q := by
  classical
  have hfst : stripFst n q = ((prodModelEquiv n 1).symm q).1 := rfl
  have hsnd : curveModelEquiv.symm (q (Fin.last n)) = ((prodModelEquiv n 1).symm q).2 := by
    rw [← stripModelEquiv_snd]
    change curveModelEquiv.symm (curveModelEquiv (((prodModelEquiv n 1).symm q).2)) = _
    exact curveModelEquiv.symm_apply_apply _
  have htarget : q ∈ (productComplexChart d e).val.target ↔
      stripFst n q ∈ d.val.target ∧ curveModelEquiv.symm (q (Fin.last n)) ∈ e.val.target := by
    change q ∈ (prodChart d.val e.val).target ↔ _
    rw [prodChart_target, hfst, hsnd]
    rfl
  by_cases hd : stripFst n q ∈ d.val.target
  · by_cases he : curveModelEquiv.symm (q (Fin.last n)) ∈ e.val.target
    · rw [chartRead_of_mem (htarget.mpr ⟨hd, he⟩)]
      dsimp only [stripCutoff]
      rw [chartRead_of_mem hd, chartRead_of_mem he]
      change f (((prodChart d.val e.val).symm q).1) * ζ (((prodChart d.val e.val).symm q).2) = _
      rw [prodChart_symm_apply, hfst, hsnd]
    · rw [chartRead_of_notMem (fun ht => he (htarget.mp ht).2)]
      dsimp only [stripCutoff]
      rw [chartRead_of_notMem he, mul_zero]
  · rw [chartRead_of_notMem (fun ht => hd (htarget.mp ht).1)]
    dsimp only [stripCutoff]
    rw [chartRead_of_notMem hd, zero_mul]

omit [IsComplexManifold 1 T] in
/-- Natural factor supports put the actual product cutoff in the actual product chart source and its coordinates in the true product core domain, precisely the source conditions of the compact slot charts. -/
theorem tsupport_productWeight_subset_core_chart {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    {f : M → ℝ} {ζ : T → ℝ} (hfJ : tsupport f ⊆ (J.source : Set M))
    (hζe : tsupport ζ ⊆ e.val.source) (hζN : tsupport ζ ⊆ (N : Set T)) :
    ∀ q ∈ tsupport (productWeight f ζ),
      q ∈ (productComplexChart J.chart e).val.source ∧
      (productComplexChart J.chart e).val q ∈
        stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen := by
  intro q hq
  have hfactor := tsupport_productWeight_subset f ζ hq
  have hx := hfJ hfactor.1
  have hy := hζe hfactor.2
  refine ⟨?_, ?_⟩
  · change q ∈ (prodChart J.chart.val e.val).source
    rw [prodChart_source]
    exact ⟨hx.1, hy⟩
  · change stripModelEquiv n (prodModelEquiv n 1 (J.chart.val q.1, e.val q.2)) ∈
      (J.domain : Set (ComplexModel n)) ×ˢ (coreTimeDomain e N : Set ℂ)
    rw [strip_product_model]
    refine ⟨hx.2, ?_⟩
    change curveModelEquiv.symm (curveModelEquiv (e.val q.2)) ∈ e.val.target ∧
      e.val.symm (curveModelEquiv.symm (curveModelEquiv (e.val q.2))) ∈ N
    rw [curveModelEquiv.symm_apply_apply, e.val.left_inv hy]
    exact ⟨e.val.map_source hy, hζN hfactor.2⟩

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyProductPartition
