import SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate
import SGPT.Foundations.Analysis.Pending.DistributionRegularization
import SGPT.Foundations.Analysis.Pending.LocalTwoFormPoincare

set_option autoImplicit false

/-!
# The telescope cutoff bound where the data live: an open parameter set

`Pending.TelescopeCutoffEstimate.abs_integral_mul_mixedDensity_telescope_le`
bounds the real integral of a cutoff against the Stokes telescope density, but
asks for `φ` and `ψ` smooth on all of `ℂ^n`.  A regular patch supplies them only
on an open parameter set `Ω` — that is exactly what
`Pending.TelescopeSlotPositivity.exists_localPotential_telescope_posSemidef`
produces.  This module removes the global hypothesis.

The transfer is the standard one: multiply `φ` and `ψ` by a test function `η`
supported in `Ω` and equal to one on a neighbourhood of the compact
`supp χ`.  Both integrals are unchanged, because every complex Hessian
appearing in them depends only on the germ at a point of `supp χ`, and both
integrands vanish off `supp χ`.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront

noncomputable section

variable {m : ℕ}

/-! ### Germ dependence -/

/-- The mixed density at a point depends only on the complex Hessians there. -/
theorem mixedDensity_congr {k : ℕ} {u u' : Fin k → ComplexModel k → ℝ}
    {z : ComplexModel k} (h : ∀ i, complexHessian (u i) z = complexHessian (u' i) z) :
    mixedDensity u z = mixedDensity u' z := by
  simp only [mixedDensity]
  rw [show (fun i => complexHessian (u i) z) = fun i => complexHessian (u' i) z from funext h]

theorem telescopeFunctions_of_lt {k : ℕ} (g h : ComplexModel k → ℝ) (j i : Fin k)
    (hij : (i : ℕ) < (j : ℕ)) :
    telescopeFunctions g h j i = fun y => g y + h y := by
  simp [telescopeFunctions, hij]

theorem telescopeFunctions_of_gt {k : ℕ} (g h : ComplexModel k → ℝ) (j i : Fin k)
    (h1 : ¬ (i : ℕ) < (j : ℕ)) (h2 : i ≠ j) :
    telescopeFunctions g h j i = g := by
  simp [telescopeFunctions, h1, h2]

/-- A telescope slot depends on its two potentials only through their germs. -/
theorem telescopeFunctions_eventuallyEq {k : ℕ}
    {phi psi phi' psi' : ComplexModel k → ℝ} {z : ComplexModel k}
    (hp : phi =ᶠ[𝓝 z] phi') (hq : psi =ᶠ[𝓝 z] psi') (j i : Fin k) :
    telescopeFunctions phi psi j i =ᶠ[𝓝 z] telescopeFunctions phi' psi' j i := by
  by_cases h1 : (i : ℕ) < (j : ℕ)
  · rw [telescopeFunctions_of_lt phi psi j i h1, telescopeFunctions_of_lt phi' psi' j i h1]
    filter_upwards [hp, hq] with y hy hy'
    rw [hy, hy']
  · by_cases h2 : i = j
    · subst h2
      rw [telescopeFunctions_self, telescopeFunctions_self]
      exact hq
    · rw [telescopeFunctions_of_gt phi psi j i h1 h2, telescopeFunctions_of_gt phi' psi' j i h1 h2]
      exact hp

/-! ### The localized bound -/

/-- **The Chern--Levine--Nirenberg cutoff bound on the Stokes telescope
defect, on an open parameter set.**  Identical to
`abs_integral_mul_mixedDensity_telescope_le` except that `φ`, `ψ` and `χ` are
only smooth on an open `Ω` containing `supp χ`. -/
theorem abs_integral_mul_mixedDensity_telescope_le_of_contDiffOn
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
    |∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z| ≤
      C * A / Real.pi ^ (m + 1) * ∫ z in tsupport chi,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
          (telescopeFixed phi psi j) z).re := by
  classical
  obtain ⟨eta, heta1, -⟩ :=
    exists_testFunction_eq_one_nhds_compact (Ω := ⟨Omega, hOmega⟩) hchic hchiO
  have hetas : ContDiff ℝ ∞ (eta : ComplexModel (m + 1) → ℝ) := eta.contDiff
  have hetaO : tsupport (eta : ComplexModel (m + 1) → ℝ) ⊆ Omega := eta.tsupport_subset
  have hchi' : ContDiff ℝ ∞ chi :=
    contDiff_of_contDiffOn_of_tsupport_subset hOmega hchi hchiO
  have hphi' : ContDiff ℝ ∞ (fun y => eta y • phi y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hOmega hetas hetaO hphi
  have hpsi' : ContDiff ℝ ∞ (fun y => eta y • psi y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hOmega hetas hetaO hpsi
  -- `eta` is one on a neighbourhood of every point of `tsupport chi`
  have hone : ∀ z ∈ tsupport chi, ∀ᶠ y in 𝓝 z, (eta : ComplexModel (m + 1) → ℝ) y = 1 :=
    fun z hz => heta1.filter_mono (nhds_le_nhdsSet hz)
  have hev : ∀ z ∈ tsupport chi, ∀ f : ComplexModel (m + 1) → ℝ,
      (fun y => eta y • f y) =ᶠ[𝓝 z] f := by
    intro z hz f
    filter_upwards [hone z hz] with y hy
    simp [hy]
  have hevsum : ∀ z ∈ tsupport chi,
      (fun y => eta y • phi y + eta y • psi y) =ᶠ[𝓝 z] fun y => phi y + psi y := by
    intro z hz
    filter_upwards [hone z hz] with y hy
    simp [hy]
  have hHphi : ∀ z ∈ tsupport chi,
      complexHessian (fun y => eta y • phi y) z = complexHessian phi z :=
    fun z hz => complexHessian_congr (hev z hz phi)
  have hHsum : ∀ z ∈ tsupport chi,
      complexHessian (fun y => eta y • phi y + eta y • psi y) z =
        complexHessian (fun y => phi y + psi y) z :=
    fun z hz => complexHessian_congr (hevsum z hz)
  have hmain := abs_integral_mul_mixedDensity_telescope_le hphi' hpsi' hchi' hchic
    (fun z hz => by rw [hHphi z hz]; exact hphiP z hz)
    (fun z hz => by rw [hHsum z hz]; exact hsumP z hz)
    hsub hadd
    (C := C)
    (fun z hz => by
      have hz1 : (eta : ComplexModel (m + 1) → ℝ) z = 1 := (hone z hz).self_of_nhds
      simpa [hz1] using hC z hz)
    j
  -- both integrals are unchanged
  have hslot : ∀ z ∈ tsupport chi, ∀ i : Fin (m + 1),
      complexHessian (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j i) z =
        complexHessian (telescopeFunctions phi psi j i) z := by
    intro z hz i
    exact complexHessian_congr
      (telescopeFunctions_eventuallyEq (hev z hz phi) (hev z hz psi) j i)
  have hLHS : ∫ z, chi z *
        mixedDensity (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j) z =
      ∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show chi z * mixedDensity (telescopeFunctions (fun y => eta y • phi y)
        (fun y => eta y • psi y) j) z =
      chi z * mixedDensity (telescopeFunctions phi psi j) z
    by_cases hz : z ∈ tsupport chi
    · rw [mixedDensity_congr (fun i => hslot z hz i)]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  have hRHS : ∫ z in tsupport chi,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
          (telescopeFixed (fun y => eta y • phi y) (fun y => eta y • psi y) j) z).re =
      ∫ z in tsupport chi,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2)
          (telescopeFixed phi psi j) z).re := by
    refine setIntegral_congr_fun measurableSet_closure fun z hz => ?_
    refine congrArg Complex.re ?_
    exact mixedC_congr (Filter.EventuallyEq.rfl)
      (fun i => telescopeFunctions_eventuallyEq (hev z hz phi) (hev z hz psi) j (j.succAbove i))
  rw [← hLHS, ← hRHS]
  exact hmain

end

end SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate
