import SGPT.BDivisor.StrictVolume.PencilZeroVolume
import SGPT.Toric.PointBlowupHyperplane
import SGPT.Toric.SameDivisorChernClass
import SGPT.Toric.MetricFiniteSums

/-! SAME physical pencil Chern class is the actual hyperplane-minus-exceptional class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff BigOperators

private def metricDifference {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    {gamma : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth gamma}
    {D E : ToricDivisor gamma hs} (h : BigToricMetric D) (g : BigToricMetric E) :
    BigToricMetric (D - E) where
  form := h.form - g.form
  weight v z := h.weight v z - g.weight v z
  smooth v := (h.smooth v).sub (g.smooth v)
  coeff v z := by
    rw [sub_eq_add_neg h.form g.form, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg]
    rw [h.coeff v z, g.coeff v z]
    simpa only [sub_eq_add_neg] using (smoothDDC_sub isOpen_univ (h.smooth v).contDiffOn
      (g.smooth v).contDiffOn (mem_univ z)).symm
  invariant v a ha z := by rw [h.invariant v a ha z, g.invariant v a ha z]
  transition v w a := by
    have hlf (p q : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
        latticeFunctional (p - q) x = latticeFunctional p x - latticeFunctional q x := by
      simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul,
        Finset.sum_sub_distrib]
    rw [toricCartierDatum_sub, toricCartierDatum_sub, hlf, hlf]
    linarith [h.transition v w a, g.transition v w a]

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def originalPencilDifferenceMetric : BigToricMetric (blowupDirectionDivisor hs) :=
  BigToricMetric.castMetric (originalPencilDivisor_eq_H_sub_E hs).symm
    (metricDifference (nativeSourceHyperplaneMetric hs) (originalExceptionalMetric hs))

theorem originalPencilDifferenceMetric_form :
    (originalPencilDifferenceMetric hs).form =
      (nativeSourceHyperplaneMetric hs).form - (originalExceptionalMetric hs).form := by
  unfold originalPencilDifferenceMetric
  rw [BigToricMetric.castMetric_form]
  rfl

theorem originalPencilFsClass_eq_H_sub_E :
    RealBottChern.ofRepresentative (originalPencilFsMetric hs).form =
      RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form -
        RealBottChern.ofRepresentative (originalExceptionalMetric hs).form := by
  calc
    _ = RealBottChern.ofRepresentative (originalPencilDifferenceMetric hs).form :=
      toricSameDivisor_firstChernClass _ _
    _ = RealBottChern.ofRepresentative
        ((nativeSourceHyperplaneMetric hs).form - (originalExceptionalMetric hs).form) := by
      rw [originalPencilDifferenceMetric_form]
    _ = _ := (RealBottChern.ofRepresentativeLinearMap
      (n := 2) (M := PolytopeToricVariety blowupGenerator hs)).map_sub _ _

theorem originalPencil_H_sub_E_sourceVolume_zero :
    sourceClassVolume
      (RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form -
        RealBottChern.ofRepresentative (originalExceptionalMetric hs).form) = 0 := by
  rw [← originalPencilFsClass_eq_H_sub_E hs]
  exact originalPencil_sourceClassVolume_zero hs

end SGPT.BDivisor.StrictPencilNext
