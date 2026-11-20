import SGPT.Trace.OptimalNormalResidueKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact product normal residue kernel limit

These are the original ordinary PRODUCT Lebesgue measures. Intrinsic native
canonical/Hodge density and the original model/product Jacobian dictionary
remain separate; no arbitrary coordinate norm is called a Hodge norm.
Blueprint: work/sgpt-resume-20261114/bert-e2-product-residue/blueprint/bert-e2-product-residue.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalProductNormalResidue
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalNormalResidueKernel

/-- The literal ordinary tangential marginal of the SAME original test. -/
def normalMarginal {d : ℕ} (χ : ComplexModel d × ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ u : ComplexModel d, χ (u, z)

theorem continuous_residueKernel {ε : ℝ} (hε : 0 < ε) : Continuous (residueKernel ε) := by
  change Continuous (fun z : ℂ => ε / (ε + ‖z‖ ^ 2) ^ 2)
  exact continuous_const.div ((continuous_const.add (continuous_norm.pow 2)).pow 2)
    (fun z => pow_ne_zero 2 (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z‖)).ne')

theorem integrable_product_normal_kernel {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {χ : ComplexModel d × ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun q : ComplexModel d × ℂ => residueKernel ε q.2 * χ q)
      ((volume : Measure (ComplexModel d)).prod (volume : Measure ℂ)) :=
  (((continuous_residueKernel hε).comp continuous_snd).mul hχ).integrable_of_hasCompactSupport
    hχc.mul_left

theorem continuous_normalMarginal {d : ℕ} {χ : ComplexModel d × ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) : Continuous (normalMarginal χ) := by
  let K : Set (ComplexModel d) := Prod.fst '' tsupport χ
  have hK : IsCompact K := hχc.isCompact.image continuous_fst
  have hzero : ∀ u ∉ K, ∀ z : ℂ, χ (u, z) = 0 := by
    intro u hu z
    by_contra hne
    exact hu ⟨(u, z), subset_tsupport χ hne, rfl⟩
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support hK
    (hχ.comp continuous_swap).continuousOn (fun z u _ hu => hzero u hu z)

theorem hasCompactSupport_normalMarginal {d : ℕ} {χ : ComplexModel d × ℂ → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (normalMarginal χ) := by
  let K : Set ℂ := Prod.snd '' tsupport χ
  have hK : IsCompact K := hχc.isCompact.image continuous_snd
  refine HasCompactSupport.intro hK fun z hz => ?_
  have hzero : ∀ u : ComplexModel d, χ (u, z) = 0 := by
    intro u
    by_contra hne
    exact hz ⟨(u, z), subset_tsupport χ hne, rfl⟩
  simp only [normalMarginal, hzero, integral_zero]

/-- Exact Fubini identity for the literal product kernel, not a supplied
residue/coarea normalization certificate. -/
theorem integral_product_normal_kernel_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {χ : ComplexModel d × ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    (∫ q : ComplexModel d × ℂ, residueKernel ε q.2 * χ q
      ∂(volume : Measure (ComplexModel d)).prod (volume : Measure ℂ)) =
      ∫ z : ℂ, residueKernel ε z * normalMarginal χ z := by
  rw [integral_prod_symm _ (integrable_product_normal_kernel hε hχ hχc)]
  congr 1
  funext z
  exact integral_const_mul (residueKernel ε z) (fun u : ComplexModel d => χ (u, z))

/-- The SAME ordinary product kernel tends to pi times the SAME original
central tangential test. No native canonical/Hodge measure is identified. -/
theorem tendsto_integral_product_normal_kernel {d : ℕ} {χ : ComplexModel d × ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun ε : ℝ => ∫ q : ComplexModel d × ℂ, residueKernel ε q.2 * χ q
        ∂(volume : Measure (ComplexModel d)).prod (volume : Measure ℂ))
      (𝓝[>] 0) (𝓝 (Real.pi * ∫ u : ComplexModel d, χ (u, 0))) := by
  have hlim := tendsto_integral_residueKernel_mul (continuous_normalMarginal hχ hχc)
    (hasCompactSupport_normalMarginal hχc)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_product_normal_kernel_eq hε hχ hχc).symm

end SGPT.Trace.OptimalProductNormalResidue
