import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-! # Actual preferred germ inclusion implies all-chart inclusion -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.QuasiEquisingularApproximation
  DemaillyApproximationAnalyticType QuasiEquisingularApproximationDemailly

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Preferred germ-ideal inclusion gives actual weighted inclusion in every atlas chart. -/
theorem multiplierIdealIncluded_of_multiplierIdeal_le
    {α β : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hφ : ThetaPlurisubharmonic α φ) (hψ : ThetaPlurisubharmonic β ψ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hle : (multiplierIdeal (n := n) c φ).Le (multiplierIdeal (n := n) d ψ)) :
    MultiplierIdealIncluded (n := n) φ c ψ d := by
  intro e z hz f _hf hsource
  let x : M := e.val.symm z
  have hx : x ∈ e.val.source := e.val.map_target hz
  have hex : e.val x = z := e.val.right_inv hz
  have hsource' : MultiplierIntegrableAt (chartFunction φ e) c f (e.val x) volume := by
    rw [hex]
    exact (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mpr hsource
  have hcorrect : MultiplierIntegrableAt
      (fun w => chartFunction φ e w + ((0 : ℝ) : EReal)) c f (e.val x) volume := by
    simpa only [EReal.coe_zero, add_zero] using hsource'
  have hmem : (multiplierIdeal (n := n) c φ).mem x (fun p => f (e.val p)) :=
    mem_multiplierIdeal_of_chart hφ hc e e.val.open_target
      (ρ := fun _ => 0) continuousOn_const hx (e.val.map_source hx) hcorrect
  obtain ⟨_, htarget⟩ := hle x _ hmem
  have husc : UpperSemicontinuousOn (chartFunction ψ e)
      (ChartWeightedL2.overlapDomain e (complexChartAt (n := n) x)) :=
    (hψ.quasiPlurisubharmonic e).upperSemicontinuousOn.mono fun _ hw => hw.1
  have htrans : MultiplierIntegrableAt (chartFunction ψ e) d
      (fun w => f (e.val (e.val.symm w))) (e.val x) volume :=
    ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      (g := fun p => f (e.val p)) e (complexChartAt (n := n) x) hx
      (mem_complexChartAt_source x) husc hd.ne' htarget
  have hfinal : MultiplierIntegrableAt (chartFunction ψ e) d f z volume := by
    rw [hex] at htrans
    refine htrans.congr (EventuallyEq.refl _ _) ?_
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    exact congrArg f (e.val.right_inv hw)
  exact (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mp hfinal

end
end SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
