import SGPT.Okounkov.TranscendentalSkodaRegularization

/-!
# The auxiliary coordinate in the regularized Skoda tuple

The added generator is `sqrt(1/(j+1))`.  Once the same normal-family
subsequence has been extracted for the auxiliary holomorphic component, its
product with that generator tends to zero.  No separate boundedness
certificate or divided solution is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Filter Set
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- A locally uniformly convergent auxiliary component vanishes after
multiplication by the extra regularizing generator. -/
theorem regularized_auxiliary_tendsto_zero {n : ℕ} {U : Set (ComplexModel n)}
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {H : ℕ → ComplexModel n → ℂ}
    {Hlim : ComplexModel n → ℂ}
    (hH : TendstoLocallyUniformlyOn (fun j => H (σ j)) Hlim atTop U)
    {z : ComplexModel n} (hz : z ∈ U) :
    Tendsto (fun j => ((Real.sqrt (1 / ((σ j : ℝ) + 1)) : ℝ) : ℂ) * H (σ j) z)
      atTop (𝓝 0) := by
  have hδ : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp (hδ.comp hσ.tendsto_atTop)
  have hc := (Complex.continuous_ofReal.tendsto 0).comp (by simpa only [Real.sqrt_zero] using hsqrt)
  have h := hc.mul (hH.tendsto_at hz)
  simpa only [Function.comp_apply, Complex.ofReal_zero, zero_mul] using h

end SGPT.NAPotential.GAGAMult
