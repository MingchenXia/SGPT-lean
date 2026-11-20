import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import SGPT.Foundations.Analysis.PositiveDistributionMeasure

/-! Actual smooth compact-test positive generators: every REAL test is a
difference of two NONNEGATIVE actual smooth tests. Positivity therefore
forces a genuinely COMPLEX-valued scalar LF functional to have zero imaginary
part on ALL real tests, without assuming reality or a real presentation. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Distributions
variable {n : ℕ} (U : Opens (ComplexModel n))

/-- Actual compactness and genuine smooth cutoff construction manufacture
two nonnegative smooth compact tests whose DIFFERENCE is the original test.
No supplied cutoff, scalar bound, support catalog or decomposition certificate. -/
theorem real_test_exists_nonnegative_difference (phi : 𝓓(U,ℝ)) :
    ∃ a b : 𝓓(U,ℝ),(∀ x,0≤a x) ∧ (∀ x,0≤b x) ∧ phi=a-b := by
  obtain ⟨chi,hchi,hdom⟩ := exists_nonneg_testFunction_abs_le (testFunctionToCompactlySupportedLM U phi)
  have hdomall (x : ComplexModel n) : |phi x|≤chi x := by
    by_cases hx : x∈U
    · exact hdom ⟨x,hx⟩
    · have hzero : phi x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (phi.tsupport_subset h))
      rw [hzero,abs_zero]
      exact hchi x
  refine ⟨chi+phi,chi,?_,hchi,?_⟩
  · intro x
    change 0≤chi x+phi x
    have h := (abs_le.mp (hdomall x)).1
    linarith
  · abel

/-- Vanishing on actual nonnegative tests forces vanishing on EVERY real
test, by the INTERNALLY PRODUCED genuine smooth difference decomposition. -/
theorem scalar_test_linear_eq_zero_of_nonnegative_zero
    (G : 𝓓(U,ℝ) →ₗ[ℝ] ℝ) (hG : ∀ phi : 𝓓(U,ℝ),(∀ x,0≤phi x) → G phi=0) : G=0 := by
  ext phi
  obtain ⟨a,b,ha,hb,hphi⟩ := real_test_exists_nonnegative_difference U phi
  rw [hphi,map_sub,hG a ha,hG b hb]
  simp

/-- Source positivity of a COMPLEX-valued scalar functional: on each actual
nonnegative real smooth test its value is real and nonnegative. Reality on
arbitrary signed tests is NOT part of this hypothesis. -/
def ComplexScalarPositive (T : 𝓓(U,ℝ) →L[ℝ] ℂ) : Prop :=
  ∀ phi : 𝓓(U,ℝ),(∀ x,0≤phi x) → (T phi).im=0 ∧ 0≤(T phi).re

/-- Actual positivity INTERNALLY kills the entire imaginary functional;
no reality/class/output certificate or real-current presentation is assumed. -/
theorem positive_complex_scalar_im_eq_zero (T : 𝓓(U,ℝ) →L[ℝ] ℂ)
    (hT : ComplexScalarPositive U T) : ∀ phi : 𝓓(U,ℝ),(T phi).im=0 := by
  have h := scalar_test_linear_eq_zero_of_nonnegative_zero U
    (Complex.imCLM.comp T).toLinearMap (fun phi hphi => (hT phi hphi).1)
  intro phi
  exact congrArg (fun G : 𝓓(U,ℝ) →ₗ[ℝ] ℝ => G phi) h

/-- A genuinely COMPLEX-valued positive scalar LF functional gives an
ACTUAL positive real distribution with the SAME value on EVERY actual test.
The output real functional is manufactured by genuine continuous composition. -/
theorem positive_complex_scalar_exists_real_distribution
    (T : 𝓓(U,ℝ) →L[ℝ] ℂ) (hT : ComplexScalarPositive U T) :
    ∃ S : 𝓓'(U,ℝ),PositiveDistribution S ∧ ∀ phi : 𝓓(U,ℝ),T phi=(S phi : ℂ) := by
  refine ⟨Complex.reCLM.comp T,?_,?_⟩
  · intro phi hphi
    exact (hT phi hphi).2
  · intro phi
    apply Complex.ext
    · rfl
    · exact positive_complex_scalar_im_eq_zero U T hT phi

end SGPT.PSH.ComplexCurrentDraft
