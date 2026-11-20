import SGPT.Foundations.Analysis.Pending.FlatComplexTorus
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials

set_option autoImplicit false

/-!
# Actual flat compact-curve and product-core regularizer potentials

The actual flat torus has constant fundamental-form coefficients in every
atlas chart. The normalized quadratic potential and the genuine two
projection pullbacks construct the full regularizer potential on the same
actual core domain used by the signed energy chart data. No regularizer
local-potential certificate is supplied as an input.
-/

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FlatCurveRegularizerPotential

open scoped ProductComplexManifold
open FirstPass FirstPass.HolomorphicMaps FirstPass.LocalPotentialPullback
  ProductComplexManifold FlatComplexTorus SingularModelEnergyCoreChartData
  CompactAffineCurveCharts GlobalSlotStokes FiniteGeodesicMaximality
  BedfordTaylorStripCovariance

noncomputable section

/-- The normalized quadratic potential produces the full actual flat form
on every genuine atlas chart, including dimension zero. -/
theorem isSmoothLocalPotential_flat {d : ℕ} (e : ComplexChart d (Torus d)) :
    IsSmoothLocalPotential (flatKahlerBackground d).form.val e e.val.target
      (fun z => Real.pi * ‖z‖ ^ 2) := by
  have hnorm : ContDiffOn ℝ ∞ (fun z : ComplexModel d => ‖z‖ ^ 2) e.val.target :=
    (contDiff_norm_sq ℝ).contDiffOn
  have hsmooth : ContDiffOn ℝ ∞ (fun z : ComplexModel d => Real.pi * ‖z‖ ^ 2)
      e.val.target := by
    simpa only [smul_eq_mul] using hnorm.const_smul Real.pi
  refine ⟨e.val.open_target, Subset.rfl, hsmooth, ?_⟩
  intro z hz
  have hscaled : smoothDDC (fun y : ComplexModel d => Real.pi * ‖y‖ ^ 2) z =
      Real.pi • smoothDDC (fun y : ComplexModel d => ‖y‖ ^ 2) z := by
    simpa only [smul_eq_mul] using smoothDDC_smul e.val.open_target hnorm Real.pi hz
  have hquad : smoothDDC (fun y : ComplexModel d => ‖y‖ ^ 2) z =
      Real.pi⁻¹ • LocalProductCurrents.kahlerForm d := by
    simpa only [sub_zero] using LocalBedfordTaylorCollar.smoothDDC_norm_sub_sq 0 z
  rw [hscaled, hquad, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  rfl

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Two actual projection potentials, on their true common core domain,
produce the full scalar product regularizer without a supplied Gamma
potential. The additional spatial background may be any closed form. -/
theorem isSmoothLocalPotential_product_core {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 (Torus 1))
    (N : Opens (Torus 1)) (β : ClosedRealOneOneForm n M)
    (ρM : ComplexModel n → ℝ)
    (hρM : IsSmoothLocalPotential β.val J.chart J.domain ρM) (A : ℝ) :
    IsSmoothLocalPotential (A • prodForm β (flatKahlerBackground 1).form).val
      (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)
      (fun q => A *
        (ρM (coordinateMap (Prod.fst : M × Torus 1 → M)
          (productComplexChart J.chart e) J.chart q) +
        Real.pi * ‖coordinateMap (Prod.snd : M × Torus 1 → Torus 1)
          (productComplexChart J.chart e) e q‖ ^ 2)) := by
  let Ω := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  let P := productComplexChart J.chart e
  have hcurve (q : ComplexModel (n + 1)) :
      curveModelEquiv.symm ((stripModelEquiv n q).2) =
        ((prodModelEquiv n 1).symm q).2 := by
    change curveModelEquiv.symm (curveModelEquiv (((prodModelEquiv n 1).symm q).2)) = _
    exact curveModelEquiv.symm_apply_apply _
  have htarget : (Ω : Set (ComplexModel (n + 1))) ⊆ P.val.target := by
    intro q hq
    change q ∈ (prodChart J.chart.val e.val).target
    rw [prodChart_target]
    exact ⟨J.domain_le_target hq.1, hcurve q ▸ hq.2.1⟩
  have hfst : (Ω : Set (ComplexModel (n + 1))) ⊆
      potentialDomain (Prod.fst : M × Torus 1 → M) P J.chart J.domain := by
    intro q hq
    refine ⟨⟨htarget hq, ?_⟩, ?_⟩
    · change J.chart.val.symm (((prodModelEquiv n 1).symm q).1) ∈ J.chart.val.source
      exact J.chart.val.map_target (J.domain_le_target hq.1)
    · change J.chart.val (J.chart.val.symm (((prodModelEquiv n 1).symm q).1)) ∈ J.domain
      rw [J.chart.val.right_inv
        (show ((prodModelEquiv n 1).symm q).1 ∈ J.chart.val.target
          from J.domain_le_target hq.1)]
      exact hq.1
  have hsnd : (Ω : Set (ComplexModel (n + 1))) ⊆
      potentialDomain (Prod.snd : M × Torus 1 → Torus 1) P e e.val.target := by
    intro q hq
    have hcoord : q ∈ coordinateDomain (Prod.snd : M × Torus 1 → Torus 1) P e := by
      refine ⟨htarget hq, ?_⟩
      change e.val.symm (((prodModelEquiv n 1).symm q).2) ∈ e.val.source
      exact e.val.map_target (hcurve q ▸ hq.2.1)
    exact ⟨hcoord, coordinateMap_mem_target hcoord⟩
  have hpullM := (isSmoothLocalPotential_pullback contMDiff_fst P hρM).mono Ω.isOpen hfst
  have hpullT := (isSmoothLocalPotential_pullback contMDiff_snd P
    (isSmoothLocalPotential_flat e)).mono Ω.isOpen hsnd
  exact FirstPass.LocalPotentials.localPotential_smul
    (FirstPass.LocalPotentials.localPotential_add
      (a := ClosedRealOneOneForm.pullback contMDiff_fst β)
      (b := ClosedRealOneOneForm.pullback contMDiff_snd (flatKahlerBackground 1).form)
      hpullM hpullT) A

end

end SGPT.Foundations.Analysis.Pending.FlatCurveRegularizerPotential
