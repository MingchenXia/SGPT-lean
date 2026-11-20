import SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront

set_option autoImplicit false

/-!
# The Chern--Levine--Nirenberg cutoff bound on the Stokes telescope defect

`Pending.TelescopeMixedDensityFront` put the Stokes telescope in the shape the
Chern--Levine--Nirenberg cutoff estimate of
`Pending.MixedCoefficientSlotBound` consumes: the signed potential `ψ` in the
first slot, the `m = \dim V - 1` plurisubharmonic fixed slots behind it, and the
`π ^ n` normalization made explicit.  This module performs the substitution.

Two conclusions are recorded.

* The direct one, `abs_re_integral_mul_mixedC_telescope_le_of_contDiffOn`, is
  the cutoff estimate read on the telescope, with all data merely smooth on an
  open parameter set.  Its left-hand side is the real part of a complex
  integral, which is the shape the estimate produces.

* The one a consumer of the Stokes telescope wants,
  `abs_integral_mul_mixedDensity_telescope_le`, bounds the *real* integral of
  `χ` against the telescope density itself.  Converting the real part of the
  integral into the integral of the real part needs integrability, so this form
  is stated with the data smooth on all of `ℂ^n`; the cutoff still localizes it.

Both bounds have the same shape:
\[
  \Bigl|\int\chi\cdot(\text{telescope defect})\Bigr|
    \;\le\;\frac{C\,A}{\pi^{n}}\int_{\operatorname{supp}\chi}
      \operatorname{Re}C_{|\cdot|^{2}}[\text{fixed slots}],
\]
with `C` a sup-norm bound for `ψ` on `supp χ` and `A` the squeeze constant of
`ddᶜχ`.  What the Stokes collar step still owes is NOT this inequality but a
family of cutoffs along a good exhaustion whose `A_m` times the flat collar
mass tends to zero; neither factor controls the product on its own.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity
open SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront

noncomputable section

variable {m : ℕ}

/-! ### Smoothness of the telescope slots on the whole space -/

/-- Every slot of a telescope family is one of `g + h`, `h`, `g`. -/
theorem telescopeFunctions_eq_three {k : ℕ} (g h : ComplexModel k → ℝ) (j i : Fin k) :
    telescopeFunctions g h j i = (fun y => g y + h y) ∨
      telescopeFunctions g h j i = h ∨ telescopeFunctions g h j i = g := by
  by_cases h1 : (i : ℕ) < (j : ℕ)
  · exact Or.inl (by simp [telescopeFunctions, h1])
  · by_cases h2 : i = j
    · exact Or.inr (Or.inl (by simp [telescopeFunctions, h2]))
    · exact Or.inr (Or.inr (by simp [telescopeFunctions, h1, h2]))

theorem contDiff_telescopeFunctions {k : ℕ} {g h : ComplexModel k → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (j i : Fin k) :
    ContDiff ℝ ∞ (telescopeFunctions g h j i) := by
  rcases telescopeFunctions_eq_three g h j i with h' | h' | h' <;> rw [h']
  · exact hg.add hh
  · exact hh
  · exact hg

theorem contDiff_telescopeFixed {phi psi : ComplexModel (m + 1) → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hpsi : ContDiff ℝ ∞ psi) (j : Fin (m + 1)) (i : Fin m) :
    ContDiff ℝ ∞ (telescopeFixed phi psi j i) :=
  contDiff_telescopeFunctions hphi hpsi j _

/-! ### The estimate on an open parameter set -/

/-- **The Chern--Levine--Nirenberg cutoff estimate, read on the Stokes
telescope.**  All the data are smooth only on an open parameter set `Omega`
containing the support of the cutoff, which is what a regular patch supplies.
The positivity hypotheses are exactly the two certificates produced by
`TelescopeSlotPositivity.exists_localPotential_telescope_posSemidef`. -/
theorem abs_re_integral_mul_mixedC_telescope_le_of_contDiffOn
    {Omega : Set (ComplexModel (m + 1))} (hOmega : IsOpen Omega)
    {phi psi : ComplexModel (m + 1) → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi Omega) (hpsi : ContDiffOn ℝ ∞ psi Omega)
    {chi : ComplexModel (m + 1) → ℝ} (hchi : ContDiffOn ℝ ∞ chi Omega)
    (hchic : HasCompactSupport chi) (hchiO : tsupport chi ⊆ Omega)
    (hphiP : ∀ z ∈ tsupport chi, (complexHessian phi z).PosSemidef)
    (hsumP : ∀ z ∈ tsupport chi,
      (complexHessian (fun y => phi y + psi y) z).PosSemidef)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) -
      complexHessian chi z).PosSemidef)
    (hadd : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) +
      complexHessian chi z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |psi z| ≤ C)
    (j : Fin (m + 1)) :
    |(∫ z, (chi z : ℂ) * mixedC psi (telescopeFixed phi psi j) z).re| ≤
      C * A * ∫ z in tsupport chi,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
          (telescopeFixed phi psi j) z).re :=
  abs_re_integral_mul_mixedC_le_of_contDiffOn hOmega
    (fun i => contDiffOn_telescopeFixed hphi hpsi j i) hchi hchic hchiO
    (fun i z hz => posSemidef_complexHessian_telescopeFixed (hphiP z hz) (hsumP z hz) j i)
    hpsi hsub hadd hC

/-! ### The estimate on the telescope density itself -/

/-- The cutoff against the telescope density, pointwise, is the real part of the
cutoff against the front-slot mixed coefficient, divided by `π ^ n`. -/
theorem mul_mixedDensity_telescope_eq (phi psi : ComplexModel (m + 1) → ℝ)
    (chi : ComplexModel (m + 1) → ℝ) (j : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    chi z * mixedDensity (telescopeFunctions phi psi j) z =
      ((chi z : ℂ) * mixedC psi (telescopeFixed phi psi j) z).re / Real.pi ^ (m + 1) := by
  rw [mixedDensity_telescopeFunctions_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- **The Chern--Levine--Nirenberg cutoff bound on the Stokes telescope
defect.**  For a cutoff `χ` of compact support whose complex Hessian is squeezed
between `-A` and `A` times the flat Kähler form, and a signed potential `ψ`
bounded by `C` on `supp χ`,
\[
  \Bigl|\int\chi\,D_{u_{j}}\Bigr|
   \le\frac{C\,A}{\pi^{n}}\int_{\operatorname{supp}\chi}
      \operatorname{Re}C_{|\cdot|^{2}}[\text{fixed slots}],
\]
where `u_j` is the telescope family with signed index `j`. -/
theorem abs_integral_mul_mixedDensity_telescope_le
    {phi psi : ComplexModel (m + 1) → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hpsi : ContDiff ℝ ∞ psi)
    {chi : ComplexModel (m + 1) → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hchic : HasCompactSupport chi)
    (hphiP : ∀ z ∈ tsupport chi, (complexHessian phi z).PosSemidef)
    (hsumP : ∀ z ∈ tsupport chi,
      (complexHessian (fun y => phi y + psi y) z).PosSemidef)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) -
      complexHessian chi z).PosSemidef)
    (hadd : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) +
      complexHessian chi z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |psi z| ≤ C)
    (j : Fin (m + 1)) :
    |∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z| ≤
      C * A / Real.pi ^ (m + 1) * ∫ z in tsupport chi,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
          (telescopeFixed phi psi j) z).re := by
  have hpi : (0 : ℝ) < Real.pi ^ (m + 1) := pow_pos Real.pi_pos _
  have hg : ∀ i, ContDiff ℝ ∞ (telescopeFixed phi psi j i) :=
    fun i => contDiff_telescopeFixed hphi hpsi j i
  have hmain := abs_re_integral_mul_mixedC_le (g := telescopeFixed phi psi j) hg hchi hchic
    (fun i z hz => posSemidef_complexHessian_telescopeFixed (hphiP z hz) (hsumP z hz) j i)
    hpsi hsub hadd hC
  -- the integrand is continuous and supported in the compact `tsupport chi`
  set F : ComplexModel (m + 1) → ℂ :=
    fun z => (chi z : ℂ) * mixedC psi (telescopeFixed phi psi j) z with hFdef
  have hFcont : Continuous F :=
    (Complex.continuous_ofReal.comp hchi.continuous).mul
      (continuous_mixedCoefficient_cons hg hpsi)
  have hF0 : ∀ z ∉ tsupport chi, F z = 0 := by
    intro z hz
    simp [hFdef, image_eq_zero_of_notMem_tsupport hz]
  have hFint : Integrable F :=
    hFcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hchic hF0)
  have hre : (∫ z, F z).re = ∫ z, (F z).re := by
    simpa using (Complex.reCLM.integral_comp_comm hFint).symm
  have hint : ∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z =
      (∫ z, F z).re / Real.pi ^ (m + 1) := by
    rw [hre, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun z => mul_mixedDensity_telescope_eq phi psi chi j z))
  calc |∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z|
      = |(∫ z, F z).re| / Real.pi ^ (m + 1) := by
        rw [hint, abs_div, abs_of_pos hpi]
    _ ≤ (C * A * ∫ z in tsupport chi,
          (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
            (telescopeFixed phi psi j) z).re) / Real.pi ^ (m + 1) := by
        gcongr
    _ = C * A / Real.pi ^ (m + 1) * ∫ z in tsupport chi,
          (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
            (telescopeFixed phi psi j) z).re := by
        ring

end

end SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate
