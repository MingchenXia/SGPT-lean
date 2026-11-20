import SGPT.Foundations.Analysis.Pending.ActualOneOneComplementaryReadingInjectivity
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
/-! Complete mathematical statements and ENTIRE proofs precede first baseline. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualLocallyIntegrableFormDensityUniqueness
open FirstPass StronglyPositiveForms ActualDistributionTwoFormReading
  _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Full actual distribution-valued form equality recovers the single
locally Bochner integrable field almost everywhere on the open domain. -/
theorem ae_eq_of_regularFormDistribution_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {r : ℕ}
    (μ : Measure E) {a b : E → E [⋀^Fin r]→L[ℝ] ℝ}
    (ha : LocallyIntegrableOn a Ω μ) (hb : LocallyIntegrableOn b Ω μ)
    (heq : regularFormDistribution μ a ha = regularFormDistribution μ b hb) :
    a =ᵐ[μ.restrict Ω] b := by
  have hzero : ∀ᵐ x ∂μ, x ∈ Ω → (a - b) x = 0 := by
    apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (ha.sub hb)
    intro g hg hgc hgΩ
    let ψ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgΩ⟩
    have hvector : (∫ x, g x • a x ∂μ) = ∫ x, g x • b x ∂μ := by
      apply ContinuousAlternatingMap.ext
      intro v
      have htest := congrArg (fun T : DistributionForm Ω r => T v ψ) heq
      simpa only [regularFormDistribution_apply, ψ, TestFunction.coe_mk] using htest
    have hIa : Integrable (fun x => g x • a x) μ :=
      ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) ha
    have hIb : Integrable (fun x => g x • b x) μ :=
      ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hb
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hIa hIb]
    exact sub_eq_zero.mpr hvector
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
  exact hzero.mono (fun x hx hxΩ => sub_eq_zero.mp (hx hxΩ))

private theorem regularForm_isOneOne
    {m : ℕ} {Ω : Opens (ComplexModel (m + 1))}
    (α : ComplexModel (m + 1) → RealForm (m + 1) 2)
    (hα : ∀ x, FirstPass.IsOneOne (α x)) (hL : LocallyIntegrableOn α Ω volume) :
    _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne
      (regularFormDistribution volume α hL) := by
  intro v w
  ext χ
  rw [regularFormDistribution_apply, regularFormDistribution_apply]
  have hI : Integrable (fun x => χ x • α x) volume :=
    χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hL
  change (formEvaluationCLM ![Complex.I • v, Complex.I • w]) (∫ x, χ x • α x) =
    (formEvaluationCLM ![v, w]) (∫ x, χ x • α x)
  rw [← (formEvaluationCLM ![Complex.I • v, Complex.I • w]).integral_comp_comm hI,
    ← (formEvaluationCLM ![v, w]).integral_comp_comm hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [formEvaluationCLM_apply, ContinuousAlternatingMap.smul_apply]
    rw [hα x v w]

/-- The complete complementary current determines one type-(1,1) vector-L1
field, with no positivity or desired density equality assumption. -/
theorem ae_eq_of_complementary_regularForm_eq
    {m : ℕ} {Ω : Opens (ComplexModel (m + 1))}
    {α β : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hα : ∀ x, FirstPass.IsOneOne (α x)) (hβ : ∀ x, FirstPass.IsOneOne (β x))
    (hLα : LocallyIntegrableOn α Ω volume) (hLβ : LocallyIntegrableOn β Ω volume)
    (heq : complementaryRead (regularFormDistribution volume α hLα) =
      complementaryRead (regularFormDistribution volume β hLβ)) :
    α =ᵐ[volume.restrict Ω] β := by
  apply ae_eq_of_regularFormDistribution_eq volume hLα hLβ
  exact ActualOneOneComplementaryReadingInjectivity.eq_of_complementaryRead_eq
    (regularForm_isOneOne α hα hLα) (regularForm_isOneOne β hβ hLβ) heq

end SGPT.Foundations.Analysis.Pending.ActualLocallyIntegrableFormDensityUniqueness
