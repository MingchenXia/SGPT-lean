import SGPT.NAPotential.PointwiseEnvelope
import SGPT.Foundations.Analysis.Pending.QuasiPshAlmostEverywhereComparison

/-! Actual original-chart a.e. recovery of the source spatial usc regularization.
Analytic support for revised rmk:pwlinhull; no LP or raw-envelope definition changes. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA.HullAnalytic
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A genuine original quasi-psh function lies below an usc function everywhere
when the comparison holds Lebesgue-a.e. in every original chart. All n, including 0. -/
theorem le_of_manifoldQuasiPSH_of_ae_chart_le_usc {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (hv : UpperSemicontinuous v)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
        u (e.val.symm z) ≤ v (e.val.symm z)) : u ≤ v := by
  intro x
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have htgt : e.val x ∈ e.val.target := e.val.map_source hsrc
  have hvchart : UpperSemicontinuousOn (chartFunction v e) e.val.target := by
    intro z hz
    have hc : ContinuousAt e.val.symm z :=
      (e.val.continuousOn_symm z hz).continuousAt (e.val.open_target.mem_nhds hz)
    exact UpperSemicontinuousAt.upperSemicontinuousWithinAt e.val.target
      (UpperSemicontinuousAt.comp (hv (e.val.symm z)) hc)
  have hle := QuasiPshAlmostEverywhereComparison.le_of_ae_le
    (hu e) e.val.open_target hvchart volume (hae e) (e.val x) htgt
  simpa only [chartFunction, e.val.left_inv hsrc] using hle

/-- Exact source/native spatial regularization from actual source θ-psh,
pointwise domination and genuine original chartwise a.e. equality.
No regularization equality or capacity-null certificate is an incoming premise. -/
theorem uscRegularization_eq_of_sourceThetaPSH_of_ae_chart_eq
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u f : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hfu : f ≤ u)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
        f (e.val.symm z) = u (e.val.symm z)) : uscRegularization f = u := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  apply le_antisymm
  · exact uscRegularization_le hn.1.quasiPlurisubharmonic.upperSemicontinuous hfu
  · apply le_of_manifoldQuasiPSH_of_ae_chart_le_usc hn.1.quasiPlurisubharmonic
      (upperSemicontinuous_uscRegularization f)
    intro e
    filter_upwards [hae e] with z hz
    rw [← hz]
    exact le_uscRegularization f (e.val.symm z)
end SGPT.PSH.VariableComplexAtlas.WholeClosureNA.HullAnalytic
