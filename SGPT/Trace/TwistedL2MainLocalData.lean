import SGPT.Trace.TwistedL2MainLocalIntegration

/-!
# Coordinate expression for the actual data pairing

This draft reads the genuine `∂̄G` functional as the Euclidean weighted
coordinate pairings needed by the local weak-equation theorem.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Complex
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

set_option linter.unusedSectionVars false in
/-- The original data pairing of a packed scalar test family agrees with the
finite sum of Euclidean weighted coordinate pairings. -/
theorem localDataPairing_vectorTest
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    (α : Fin n → ComplexModel n → ℂ)
    (hα : ∀ j, IsTestFunctionOn (T.pieceDomain c e) (α j)) :
    T.localDataPairing c e ρ (vectorTest α) =
      ∑ j, ∫ z, conj (α j z) * dbarDir (coordVec j) (chartCoeff T.L c e T.G) z
        ∂(weightedVolume (T.pieceDomain c e) (localWeight T.L c e ρ T.φ)) := by
  let D := T.pieceDomain c e
  let p := localWeight T.L c e ρ T.φ
  let a := chartCoeff T.L c e T.G
  have hD : IsOpen D := T.isOpen_pieceDomain c e
  have hp : ContinuousOn p D := (T.contDiffOn_localWeight e hρ).continuousOn
  have ha : ContDiffOn ℝ 1 a D := (T.G_smooth c e).of_le (by norm_num)
  have hint : ∀ j, Integrable (fun z => conj (α j z) * dbarDir (coordVec j) a z * cweight p z) := by
    intro j
    have hsub : tsupport (fun z => conj (α j z)) ⊆ tsupport (α j) := by
      refine tsupport_subset_of_eq_zero fun z hz => ?_
      simp [image_eq_zero_of_notMem_tsupport hz]
    have hcomp : HasCompactSupport (fun z => conj (α j z)) :=
      (hα j).2.1.of_isClosed_subset (isClosed_tsupport _) hsub
    have hfac : ContinuousOn (fun z => dbarDir (coordVec j) a z * cweight p z) D := by
      have hp' : ContinuousOn (cweight p) D :=
        Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hp.neg)
      exact (continuousOn_dbarDir_of_contDiffOn hD ha _).mul hp'
    have hcont : Continuous (fun z =>
        (dbarDir (coordVec j) a z * cweight p z) * conj (α j z)) :=
      continuous_mul_of_tsupport_subset hD hfac (continuous_conj.comp (hα j).1.continuous)
        (hsub.trans (hα j).2.2)
    have hc := hcont.integrable_of_hasCompactSupport (μ := (volume : Measure (ComplexModel n))) hcomp.mul_left
    refine hc.congr (Eventually.of_forall fun z => ?_)
    ring
  change (∫ z, dbarPairing a z (vectorTest α z) * cweight p z) = _
  simp_rw [dbarPairing_vectorTest, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_weightedVolume hD hp]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) (f :=
    fun z => conj (α j z) * dbarDir (coordVec j) a z * cweight p z) (fun z hz => by
      have hz' : z ∉ tsupport (α j) := fun hz' => hz ((hα j).2.2 hz')
      simp [image_eq_zero_of_notMem_tsupport hz'])]
  refine setIntegral_congr_fun hD.measurableSet fun z _ => ?_
  simp only [cweight, Complex.real_smul]
  ring

end TwistedDatum
end SGPT.Trace.TwistedL2
