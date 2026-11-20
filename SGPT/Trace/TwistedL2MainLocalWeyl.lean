import SGPT.Trace.TwistedL2MainLocalCoefficient
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl

/-!
# Local regularization after the distributional equation

This draft isolates the Weyl step used for a smooth input minus an L² weak
solution. Its weighted L² and weak-equation hypotheses still have to be
produced for the actual chart coefficient in the twisted estimate.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff ComplexConjugate ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.OTChen

/-- A weighted L² weak solution of the `∂̄` equation for a smooth local
function can be subtracted from it to produce a holomorphic representative.
This does not establish the weighted L² or weak-equation hypotheses. -/
theorem exists_holomorphic_local_representative {n : ℕ}
    {D : Set (ComplexModel n)} (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {a u : ComplexModel n → ℂ}
    (ha : ContDiffOn ℝ 1 a D) (hu : MemLp u 2 (weightedVolume D w))
    (heq : WeakDbarEq D u (fun j => dbarDir (coordVec j) a)) :
    ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F D ∧
      ∀ᵐ z ∂(volume.restrict D), a z - u z = F z := by
  have huloc : LocallyIntegrableOn u D :=
    locallyIntegrableOn_of_memLp_weightedVolume hD hw hu
  have haloc : LocallyIntegrableOn a D := ha.continuousOn.locallyIntegrableOn hD.measurableSet
  have hFloc : LocallyIntegrableOn (fun z => a z - u z) D := haloc.sub huloc
  have hcoord : ∀ h, IsTestFunctionOn D h → ∀ j,
      ∫ x, (a x - u x) * dbarDir (coordVec j) h x = 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn huloc hdc hdcs hdts
    simp only [sub_mul]
    rw [integral_sub i1 i2, weakDbarEq_of_contDiffOn hD ha h hh j, heq h hh j]
    ring
  exact exists_differentiableOn_ae_eq_of_weak_dbar hD hFloc
    (integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)

end SGPT.Trace.TwistedL2
