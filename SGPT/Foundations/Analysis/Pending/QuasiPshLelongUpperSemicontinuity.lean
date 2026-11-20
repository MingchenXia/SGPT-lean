import SGPT.Foundations.Analysis.Pending.PshLelongUpperSemicontinuity
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance

set_option autoImplicit false

/-! # Actual upper semicontinuity of Lelong readers for raw quasi-PSH germs and manifolds -/

open Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiPshLelongUpperSemicontinuity

open FirstPass FirstPass.NonKahlerLocus LelongNumberComparison
  LelongChartReaderInvariance PshLelongUpperSemicontinuity

noncomputable section

variable {n : ℕ}

/-- One genuine quasi-PSH germ internally supplies a fixed PSH model and
continuous correction on a neighborhood, hence actual point-Lelong USC. -/
theorem upperSemicontinuousAt_lelongNumber_of_quasiPlurisubharmonicAt
    {u : ComplexModel n → EReal} {x : ComplexModel n}
    (hu : QuasiPlurisubharmonicAt u x) :
    UpperSemicontinuousAt (fun y => lelongNumber (n := n) u y) x := by
  obtain ⟨P, h, ⟨W, hW, hxW, hP⟩, hsmooth, heq⟩ := hu
  have hnbhd : {y | u y = P y + (h y : EReal) ∧ ContDiffAt ℝ ∞ h y} ∈ 𝓝 x :=
    heq.and hsmooth
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hnbhd
  have hνeq (y : ComplexModel n) (hy : y ∈ V) :
      lelongNumber (n := n) u y = lelongNumber (n := n) P y := by
    have hgerm : u =ᶠ[𝓝 y] fun z => P z + (h z : EReal) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact (hVsub hz).1
    rw [lelongNumber_congr hgerm,
      lelongNumber_add_continuous_eq (hVsub hy).2.continuousAt]
  intro b hb
  change lelongNumber (n := n) u x < b at hb
  have hxP : lelongNumber (n := n) P x < b := by rwa [hνeq x hxV] at hb
  obtain ⟨a, ha, hab⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hxP
  have hnear := eventually_lelongNumber_lt_of_lt (hP.plurisubharmonicOn hW) hW hxW
    (a := (a : ℝ)) (by simpa only [ENNReal.ofReal_coe_nnreal] using ha)
  filter_upwards [hnear, hV.mem_nhds hxV] with y hy hyV
  rw [hνeq y hyV]
  exact hy.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hab)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Raw global quasi-PSH functions have an actual upper-semicontinuous Lelong
map on the original manifold, with no nondegeneracy or mass premise. -/
theorem upperSemicontinuous_lelongNumber {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    UpperSemicontinuous (fun x => lelongNumber (n := n) u x) := by
  intro x b hb
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have ht : e.val x ∈ e.val.target := e.val.map_source hx
  have hmodel := upperSemicontinuousAt_lelongNumber_of_quasiPlurisubharmonicAt (hu e (e.val x) ht)
  have hνchart : lelongNumber (n := n) (chartFunction u e) (e.val x) < b := by
    rwa [lelongNumber_chartFunction_eq e hx]
  have hnear := (e.val.continuousAt hx).eventually (hmodel b hνchart)
  filter_upwards [hnear, e.val.open_source.mem_nhds hx] with y hy hyS
  rwa [lelongNumber_chartFunction_eq e hyS] at hy

end
end SGPT.Foundations.Analysis.Pending.QuasiPshLelongUpperSemicontinuity
