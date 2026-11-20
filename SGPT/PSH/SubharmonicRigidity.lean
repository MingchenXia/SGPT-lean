import SGPT.PSH.SubharmonicStrip
import SGPT.PSH.DistributionRigidity
import SGPT.Foundations.Analysis.Pending.PshRepresentative
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

set_option autoImplicit false

noncomputable section
namespace SGPT.PSH
open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis
open scoped Distributions Topology

variable {Ω : Opens ℂ}

/-- Actual distributional real Laplacian, with both derivatives in their
original real coordinate directions and their genuine distribution topology. -/
def sourceLaplacian (T : 𝓓'(Ω, ℝ)) : 𝓓'(Ω, ℝ) :=
  Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ) T) +
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I T)

/-- The original Laplacian is exactly four times the actual unit Levi distribution. -/
theorem sourceLaplacian_eq_four_levi (T : 𝓓'(Ω, ℝ)) :
    sourceLaplacian T = (4 : ℝ) • distributionalLeviCLM (1 : ℂ) T := by
  simp [sourceLaplacian, distributionalLeviCLM, smul_eq_mul]

/-- In one complex dimension every original directional Levi test is the unit
test multiplied by the genuine squared coordinate modulus. -/
theorem distributionalLevi_complex_direction (T : 𝓓'(Ω, ℝ)) (v : ℂ) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM v T φ =
      (v.re ^ 2 + v.im ^ 2) * distributionalLeviCLM (1 : ℂ) T φ := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  have hIv : Complex.I • v = (-v.im) • (1 : ℂ) + v.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul, smul_eq_mul]
  have hD : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) (Ω := Ω) (F := ℝ) ℝ v =
      v.re • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ) +
        v.im • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I := by
    calc
      _ = TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg _ hv
      _ = _ := by rw [TestFunction.lineDerivCLM_add,
        TestFunction.lineDerivCLM_smul, TestFunction.lineDerivCLM_smul]
  have hJ : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) (Ω := Ω) (F := ℝ) ℝ (Complex.I • v) =
      (-v.im) • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ) +
        v.re • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I := by
    calc
      _ = TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
          ((-v.im) • (1 : ℂ) + v.re • Complex.I) := congrArg _ hIv
      _ = _ := by rw [TestFunction.lineDerivCLM_add,
        TestFunction.lineDerivCLM_smul, TestFunction.lineDerivCLM_smul]
  rw [distributionalLeviCLM_apply, distributionalLeviCLM_apply, hD, hJ]
  simp only [smul_eq_mul, mul_one]
  simp only [_root_.add_apply, _root_.smul_apply, map_add, map_smul, smul_eq_mul]
  ring

/-- Positivity of the original Laplacian is the complete one-dimensional Levi
criterion, without a finite density or a smoothness assumption. -/
theorem positive_sourceLaplacian_iff_nonnegativeLevi (T : 𝓓'(Ω, ℝ)) :
    PositiveDistribution (sourceLaplacian T) ↔ HasNonnegativeDistributionalLevi T := by
  rw [sourceLaplacian_eq_four_levi]
  constructor
  · intro hT v φ hφ
    have hunit := hT φ hφ
    change 0 ≤ 4 * distributionalLeviCLM (1 : ℂ) T φ at hunit
    rw [distributionalLevi_complex_direction]
    exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  · intro hT
    exact (hT 1).smul (by norm_num)

/-- The literal source measurable extended function has a positive actual
Laplacian exactly when it has a genuine original subharmonic representative. -/
theorem subharmonic_distribution_rigidity {u : ℂ → EReal}
    (hΩ : IsConnected (Ω : Set ℂ))
    (_hu : Measurable (fun x : Ω ↦ u x)) (_htop : ∀ x ∈ Ω, u x ≠ ⊤) :
    (∃ hL : SourceLocallyIntegrableOn volume u Ω,
      PositiveDistribution (sourceLaplacian
        (regularDistribution volume (fun x ↦ (u x).toReal) hL.2))) ↔
      ∃ v : ℂ → EReal, SubharmonicOn v Ω ∧ u =ᵐ[volume.restrict Ω] v := by
  constructor
  · rintro ⟨hL, hpos⟩
    obtain ⟨v, hv, hae⟩ := exists_pshOn_ae_eq_of_nonnegativeLevi
      volume hΩ.nonempty hL ((positive_sourceLaplacian_iff_nonnegativeLevi _).mp hpos)
    exact ⟨v, (subharmonicOn_iff_pshOn v Ω).mpr hv, hae⟩
  · rintro ⟨v, hv, hae⟩
    obtain ⟨hL, hLevi⟩ := sourceLocallyIntegrableOn_nonnegativeLevi_of_ae_eq_pshOn
      volume hΩ.isPreconnected ((subharmonicOn_iff_pshOn v Ω).mp hv) hae
    exact ⟨hL, (positive_sourceLaplacian_iff_nonnegativeLevi _).mpr hLevi⟩

/-- Original subharmonic uniqueness is pointwise, including negative poles. -/
theorem SubharmonicOn.eqOn_of_original_ae_eq {u v w : ℂ → EReal}
    (hv : SubharmonicOn v Ω) (hw : SubharmonicOn w Ω)
    (huv : u =ᵐ[volume.restrict Ω] v) (huw : u =ᵐ[volume.restrict Ω] w) :
    EqOn v w Ω :=
  PSHOn.eqOn_of_original_ae_eq volume
    ((subharmonicOn_iff_pshOn v Ω).mp hv)
    ((subharmonicOn_iff_pshOn w Ω).mp hw) huv huw

end SGPT.PSH
