import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- Original local quasi-PSH functions give genuine global raw quasi-PSH
functions on the actual open-submanifold subtype, through its original charts. -/
theorem manifoldQuasiPlurisubharmonic_opens_restrict {u : ComplexModel n → EReal}
    (hu : QuasiPlurisubharmonicOn u Ω) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun x : Ω => u x) := by
  intro e z hz
  obtain ⟨x, he⟩ := Opens.chart_eq ⟨e.val.symm z⟩ e.property
  have hc (y : Ω) : e.val y = (y : ComplexModel n) := by
    rw [he, chartAt_self_eq]
    rfl
  have hmem : z ∈ Ω := by
    have hi := e.val.right_inv hz
    rw [hc] at hi
    exact hi ▸ (e.val.symm z).property
  apply (hu z hmem).congr
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy
  change u y = u ((e.val.symm y : Ω) : ComplexModel n)
  rw [← hc (e.val.symm y), e.val.right_inv hy]

/-- Actual open-submanifold charts preserve the native reader for every
original function, even before any analytic regularity is imposed. -/
theorem lelongNumber_opens_restrict (u : ComplexModel n → EReal) (x : Ω) :
    lelongNumber (n := n) (fun y : Ω => u y) x = lelongNumber (n := n) u x := by
  let e := complexChartAt (n := n) x
  have hc (y : Ω) : e.val y = (y : ComplexModel n) := rfl
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have ht : (x : ComplexModel n) ∈ e.val.target := by
    simpa only [hc] using e.val.map_source hx
  have hgerm : chartFunction (fun y : Ω => u y) e =ᶠ[𝓝 (x : ComplexModel n)] u := by
    filter_upwards [e.val.open_target.mem_nhds ht] with z hz
    change u ((e.val.symm z : Ω) : ComplexModel n) = u z
    rw [← hc (e.val.symm z), e.val.right_inv hz]
  calc
    _ = lelongNumber (n := n) (chartFunction (fun y : Ω => u y) e) x := by
      simpa only [hc] using
        (LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hx).symm
    _ = _ := LelongNumberComparison.lelongNumber_congr hgerm

end SGPT.Okounkov
