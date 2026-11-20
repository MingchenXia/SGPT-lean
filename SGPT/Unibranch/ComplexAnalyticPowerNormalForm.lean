import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Actual analytic root and inverse construction of a finite-power germ.
Blueprint: complex-analytic-power-normal-form.tex. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SGPT.Unibranch.RamifiedPower

/-- A genuine analytic unit has an actual analytic root, constructed from
an actual constant root and the genuine local principal-power branch. -/
theorem exists_analytic_unit_root {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    ∃ v : ℂ → ℂ,AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧ ∀ z : ℂ,(v z)^k = u z := by
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq (u 0) hk
  have hc0 : c ≠ 0 := by
    intro h
    rw [h,zero_pow (Nat.ne_of_gt hk)] at hc
    exact hu0 hc.symm
  let v : ℂ → ℂ := fun z => c*((u z/u 0) ^ ((k : ℂ)⁻¹ : ℂ))
  have hv : AnalyticAt ℂ v 0 := by
    have hratio : AnalyticAt ℂ (fun z => u z/u 0) 0 := hu.div_const
    have hslit : u 0/u 0 ∈ Complex.slitPlane := by simpa only [div_self hu0] using Complex.one_mem_slitPlane
    exact analyticAt_const.mul (hratio.cpow analyticAt_const hslit)
  have hv0 : v 0 ≠ 0 := by simpa only [v,div_self hu0,Complex.one_cpow,mul_one] using hc0
  refine ⟨v,hv,hv0,?_⟩
  intro z
  dsimp only [v]
  rw [mul_pow,hc,Complex.cpow_nat_inv_pow _ (Nat.ne_of_gt hk)]
  field_simp [hu0]

/-- The actual analytic inverse internally normalizes the SAME unit factor,
with no inverse/branch/finite-power certificate among the input hypotheses. -/
theorem exists_analytic_power_normalizer {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    ∃ ψ : ℂ → ℂ,AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ),(ψ t)^k*u (ψ t) = t^k := by
  obtain ⟨v,hv,hv0,hvpow⟩ := exists_analytic_unit_root hu hu0 k hk
  let χ : ℂ → ℂ := fun z => z*v z
  have hχ : AnalyticAt ℂ χ 0 := analyticAt_id.mul hv
  have hχ0 : χ 0 = 0 := by simp [χ]
  have hχderiv : HasDerivAt χ (v 0) 0 := by
    have hd := (hasDerivAt_id (0 : ℂ)).mul hv.differentiableAt.hasDerivAt
    change HasDerivAt (fun z : ℂ => z*v z) (1*v 0+0*deriv v 0) 0 at hd
    simpa only [χ,one_mul,zero_mul,add_zero] using hd
  have hderiv : deriv χ 0 ≠ 0 := by rw [hχderiv.deriv];exact hv0
  let ψ : ℂ → ℂ := hχ.hasStrictDerivAt.localInverse χ (deriv χ 0) 0 hderiv
  have hψ : AnalyticAt ℂ ψ 0 := by
    have h := hχ.analyticAt_localInverse hderiv
    rwa [hχ0] at h
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ),ψ (χ z) = z :=
    hχ.hasStrictDerivAt.eventually_left_inverse hderiv
  have hψ0 : ψ 0 = 0 := by
    have h := hleft.self_of_nhds
    rwa [hχ0] at h
  have hright : ∀ᶠ z in 𝓝 (0 : ℂ),χ (ψ z) = z := by
    have h := hχ.hasStrictDerivAt.eventually_right_inverse hderiv
    rwa [hχ0] at h
  refine ⟨ψ,hψ,hψ0,?_⟩
  filter_upwards [hright] with z hz
  calc
    (ψ z)^k*u (ψ z) = (χ (ψ z))^k := by
      dsimp only [χ]
      rw [mul_pow,hvpow]
    _ = z^k := congrArg (fun w : ℂ => w^k) hz

end SGPT.Unibranch.RamifiedPower
