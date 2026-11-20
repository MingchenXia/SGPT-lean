import SGPT.Trace.TwistedL2MainLocalData
import SGPT.Foundations.Analysis.Pending.HormanderTestPairing

/-!
# The local distributional equation for the actual correction

This draft combines the actual H₁ test-pairing equation with the chart and
frame identities, then invokes the existing Euclidean weak-∂bar theorem.
It still depends on the conditional Riesz solution's test equations.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The actual frame coefficient of the Hilbert correction satisfies the
local distributional `∂̄` equation of the original smooth section, provided
its genuine local adjoint-test equations hold. -/
theorem weakDbarEq_chartCorrectionCoeff
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (htest : ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing)
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    WeakDbarEq (T.pieceDomain c e)
      (fun z => T.correctionFrameCoeff u e (c.val.symm z))
      (fun j => dbarDir (coordVec j) (chartCoeff T.L c e T.G)) := by
  let D := T.pieceDomain c e
  let p := localWeight T.L c e ρ T.φ
  let w := T.localH1Weight c e ρ
  let ψ := T.localTwist c
  have hD : IsOpen D := T.isOpen_pieceDomain c e
  have hp : ContDiffOn ℝ ∞ p D := T.contDiffOn_localWeight e hρ
  have hw : ContinuousOn w D := T.continuousOn_localH1Weight c e hρ
  apply weakDbarEq_of_adjoint_pairing hD hw hp
    (fun z _ => T.localWeight_eq_H1_add_twist c e ρ z)
  intro α hα
  have hh : IsLocalTestField T.L T.U c e (vectorTest α) :=
    T.isLocalTestField_vectorTest c e α hα
  let q : T.LocalTestPiece := ⟨c, e, ρ, vectorTest α, hρ, hh⟩
  have hpair := htest q
  change ⟪T.tstarL2 hρ hh, u⟫_ℂ = T.localDataPairing c e ρ (vectorTest α) at hpair
  rw [T.inner_tstar_eq_chart_integral u c e hρ hh,
    T.localDataPairing_vectorTest c e hρ α hα] at hpair
  have hleft :
      (∫ z, conj (tstarForm p ψ α z) * T.correctionFrameCoeff u e (c.val.symm z)
          ∂(weightedVolume D w)) =
        ∫ z in D, conj (T.pieceTheta c e ρ (vectorTest α) z) *
          T.correctionFrameCoeff u e (c.val.symm z) * (Real.exp (-w z) : ℂ) := by
    rw [integral_weightedVolume hD hw]
    refine setIntegral_congr_fun hD.measurableSet fun z hz => ?_
    rw [T.tstarForm_vectorTest_eq_pieceTheta c e ρ α hz]
    simp only [Complex.real_smul]
    ring
  rw [hleft]
  exact hpair

end TwistedDatum
end SGPT.Trace.TwistedL2
