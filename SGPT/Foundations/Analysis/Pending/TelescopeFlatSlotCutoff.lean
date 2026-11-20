import SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimateLocal

set_option autoImplicit false

/-!
# The Chern--Levine--Nirenberg cutoff bound with a dimension-free right-hand side

`Pending.TelescopeCutoffEstimate.abs_integral_mul_mixedDensity_telescope_le_of_contDiffOn`
bounds `|∫ χ · D_{u_j}|` by `C A / π ^ n` times the integral of
`Re C_{|·|²}[telescopeFixed φ ψ j]`, where `telescopeFixed` lists the `n - 1`
fixed slots through `Fin.succAbove`.  That right-hand side can only be written
once the complex dimension has been split as `m + 1`, which makes the estimate
awkward to use at the dimension `dim V` of a subvariety: `dim V` is a field of a
structure, not a pattern variable.

This module removes the splitting from the STATEMENT.  The observation is that
the comparison integrand is itself a mixed Monge--Ampère density of a family of
`n` functions, namely the telescope family with its signed slot `j` replaced by
the flat potential `|z|²`:

`flatTelescopeSlot φ ψ j = Function.update (telescopeFunctions φ ψ j) j ‖·‖²`.

`Pending.TelescopeMixedDensityFront.mixedDensity_eq_mixedC_succAbove`, applied to
that family at the slot `j`, turns `mixedDensity (flatTelescopeSlot φ ψ j)` into
`Re C_{|·|²}[telescopeFixed φ ψ j] / π ^ n`, so the two `π ^ n` normalizations
cancel and the estimate reads

`|∫ χ · D_{u_j}| ≤ C · A · ∫_{supp χ} D_{flat slot j}`,

with every object living on `ComplexModel k` for an unsplit `k`.  The hypothesis
`j : Fin k` already forces `k ≠ 0`, so no positivity assumption has to be added.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeFlatSlotCutoff

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront
open SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate

noncomputable section

/-- **The flat comparison family of a telescope slot.**  The telescope family
with signed index `j`, with the signed slot itself replaced by the flat Kähler
potential `|z|²`.  Its mixed Monge--Ampère density is the Chern--Levine--Nirenberg
comparison mass of the fixed slots. -/
def flatTelescopeSlot {k : ℕ} (phi psi : ComplexModel k → ℝ) (j : Fin k) :
    Fin k → ComplexModel k → ℝ :=
  Function.update (telescopeFunctions phi psi j) j (fun w => ‖w‖ ^ 2)

@[simp] theorem flatTelescopeSlot_self {k : ℕ} (phi psi : ComplexModel k → ℝ) (j : Fin k) :
    flatTelescopeSlot phi psi j j = fun w => ‖w‖ ^ 2 := by
  simp [flatTelescopeSlot]

theorem flatTelescopeSlot_of_ne {k : ℕ} (phi psi : ComplexModel k → ℝ) {j i : Fin k}
    (hij : i ≠ j) : flatTelescopeSlot phi psi j i = telescopeFunctions phi psi j i := by
  simp [flatTelescopeSlot, hij]

variable {m : ℕ}

theorem flatTelescopeSlot_succAbove (phi psi : ComplexModel (m + 1) → ℝ)
    (j : Fin (m + 1)) (i : Fin m) :
    flatTelescopeSlot phi psi j (j.succAbove i) = telescopeFixed phi psi j i :=
  flatTelescopeSlot_of_ne phi psi (Fin.succAbove_ne j i)

/-- The flat comparison density is exactly the Chern--Levine--Nirenberg
comparison integrand, with the `π ^ n` normalization included. -/
theorem mixedDensity_flatTelescopeSlot (phi psi : ComplexModel (m + 1) → ℝ)
    (j : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    mixedDensity (flatTelescopeSlot phi psi j) z =
      (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
        (telescopeFixed phi psi j) z).re / Real.pi ^ (m + 1) := by
  rw [mixedDensity_eq_mixedC_succAbove (flatTelescopeSlot phi psi j) j z,
    flatTelescopeSlot_self]
  simp only [flatTelescopeSlot_succAbove]

/-- **The Chern--Levine--Nirenberg cutoff bound on the Stokes telescope defect,
with an unsplit dimension.**  Identical in content to
`Pending.TelescopeCutoffEstimate.abs_integral_mul_mixedDensity_telescope_le_of_contDiffOn`;
the comparison mass is written as the mixed density of the flat comparison
family, so that nothing in the statement mentions `k - 1`. -/
theorem abs_integral_mul_mixedDensity_telescope_le_flat {k : ℕ}
    {Omega : Set (ComplexModel k)} (hOmega : IsOpen Omega)
    {phi psi : ComplexModel k → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi Omega) (hpsi : ContDiffOn ℝ ∞ psi Omega)
    {chi : ComplexModel k → ℝ} (hchi : ContDiffOn ℝ ∞ chi Omega)
    (hchic : HasCompactSupport chi) (hchiO : tsupport chi ⊆ Omega)
    (hphiP : ∀ z ∈ tsupport chi, (complexHessian phi z).PosSemidef)
    (hsumP : ∀ z ∈ tsupport chi,
      (complexHessian (fun y => phi y + psi y) z).PosSemidef)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) -
      complexHessian chi z).PosSemidef)
    (hadd : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) +
      complexHessian chi z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |psi z| ≤ C) (j : Fin k) :
    |∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z| ≤
      C * A * ∫ z in tsupport chi, mixedDensity (flatTelescopeSlot phi psi j) z := by
  have hk : k ≠ 0 := by rintro rfl; exact j.elim0
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hmain := abs_integral_mul_mixedDensity_telescope_le_of_contDiffOn hOmega hphi hpsi
    hchi hchic hchiO hphiP hsumP hsub hadd hC j
  have hrw : ∫ z in tsupport chi, mixedDensity (flatTelescopeSlot phi psi j) z =
      (∫ z in tsupport chi, (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
        (telescopeFixed phi psi j) z).re) / Real.pi ^ (m + 1) := by
    rw [← integral_div]
    exact setIntegral_congr_fun measurableSet_closure
      fun z _ => mixedDensity_flatTelescopeSlot phi psi j z
  rw [hrw]
  refine hmain.trans_eq ?_
  ring

end

end SGPT.Foundations.Analysis.Pending.TelescopeFlatSlotCutoff
