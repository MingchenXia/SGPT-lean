import SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPositiveLocalPsh
import SGPT.Foundations.Analysis.Pending.DistributionLocalDdcPotential
import SGPT.Foundations.Analysis.Pending.PshRepresentative

set_option autoImplicit false

/-! Every original fully positive closed (1,1) current internally has genuine
local PSH potentials. Arbitrary scalar LF potentials acquire their actual
PSH representatives, rather than being assumed to have QPsh/L1 readers.
Full mathematical statements and ENTIRE proofs precede this source. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.FullPositiveCurrentLocalPshPotential

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  LocalProductCurrents LocalBedfordTaylorLocality LocalBedfordTaylorProducts
  GlobalCurrentPotentials CanonicalCurrentFrame
  ActualAnalyticCurrentLocalDensity ActualCanonicalComplementaryCurrentCalibration
  GlobalPositiveCurrentACRestriction ActualDistributionTwoFormReading
  ActualDistributionTwoFormDdc LelongPoincareDivisor

variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}

private theorem reader_restrict (hVU : V ≤ U) (A : DistributionForm U 2) :
    complementaryRead (restrictForm A hVU) = restrict hVU (complementaryRead A) := by
  ext γ φ
  have hφ : (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) = extTest hVU φ := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hVU φ) y, extTest_apply]
  simp only [complementaryRead, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    restrictForm_apply, LocalBedfordTaylorLocality.restrict_apply, smul_eq_mul, hφ]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Original full positivity internally supplies all Levi inequalities and
a genuine PSH representative for an arbitrary actual scalar LF potential. -/
theorem exists_pshRepresentative_of_original_full_positive
    (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M)
    (hU : U ≤ chartTarget e) (R : 𝓓'(U, ℝ))
    (hR : ddC R = restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hU) :
    ∃ u : ComplexModel (m + 1) → EReal, IsPshRepresentative μ R u := by
  have hfull : ddc (ScalarLeviPositiveCurrent.scalarTopCurrent R) =
      restrict hU (chartSpanCurrent T e) := by
    rw [← complementaryRead_ddC, hR, reader_restrict,
      complementaryRead_coefficients_eq_chartSpanCurrent]
  have hp : IsPositive (ddc (ScalarLeviPositiveCurrent.scalarTopCurrent R)) := by
    rw [hfull]
    exact isPositive_restrict
      (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent T hT e) hU
  exact Pending.exists_pshRepresentative μ
    (FullPositiveScalarCurrentLeviConverse.hasNonnegativeDistributionalLevi_of_isPositive_ddc R hp)

/-- Natural original closedness, type and full positivity supply the actual
neighborhood, arbitrary scalar potential, PSH representative and full equation.
No local reader, QPsh, integrability or class certificate is an input. -/
theorem exists_local_psh_potential_of_full_positive
    (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M)
    (x : ComplexModel (m + 1)) (hx : x ∈ e.val.target) :
    ∃ (W : Opens (ComplexModel (m + 1))) (hW : W ≤ chartTarget e)
      (u : ComplexModel (m + 1) → EReal), x ∈ W ∧ PlurisubharmonicOn u W ∧
        (∀ᵐ z ∂μ.restrict W, u z ≠ ⊤ ∧ u z ≠ ⊥) ∧
        ∃ hL : LocallyIntegrableOn (fun z => (u z).toReal) W μ,
          ddC (regularDistribution μ (fun z => (u z).toReal) hL) =
            restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hW := by
  obtain ⟨W, hW, R, hxW, hR⟩ :=
    DistributionLocalDdcPotential.exists_local_scalar_potential
      (T.coefficients (canonicalBasis (m + 1)) e) (hclosed e) (h11 e) x hx
  obtain ⟨u, hu, hfin, hL, heq⟩ :=
    exists_pshRepresentative_of_original_full_positive μ T hT e hW R hR
  refine ⟨W, hW, u, hxW, hu, hfin, hL, ?_⟩
  rw [← heq]
  exact hR

end SGPT.Foundations.Analysis.Pending.FullPositiveCurrentLocalPshPotential
