import SGPT.Foundations.Analysis.Pending.MixedCoefficientSlotBound
import SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity

set_option autoImplicit false

/-!
# The Chern--Levine--Nirenberg estimate, applied to the Stokes telescope

`Pending.MixedCoefficientSlotBound.abs_re_integral_mul_mixedC_le_of_contDiffOn`
estimates `|Re ∫ χ · C(u, g₁, …, g_m)|` when the `m` *fixed* slots `gᵢ` have
positive semidefinite complex Hessians and the *first* slot `u` is an arbitrary
bounded smooth function.  Its docstring names the three things that still stood
between it and the Stokes telescope of `Pending.PatchDensityLocalPotential`:

1. plurisubharmonicity of the local potential `φ` of the background and of its
   sum with `v ∘ P.toManifold` — supplied by
   `Pending.TelescopeSlotPositivity.exists_localPotential_telescope_posSemidef`;
2. `mixedCoefficient_perm`, to move the signed slot of `telescopeFunctions`
   from its index `j` to the front, where `mixedC` expects it;
3. the `π ^ dim V` normalization between `mixedDensity` and `mixedC`.

This module supplies 2 and 3 and then assembles all three.  Nothing here is
analytic: the front-slot move is `Fin.cons_removeNth_eq_comp_cycleRange_symm`
followed by the permutation invariance of `mixedCoefficient`, and the
normalization is the definition of `mixedDensity`.

The signed slot of `telescopeFunctions φ ψ j` is the slot `j` itself, carrying
`ψ`; every other slot carries `φ` or `φ + ψ`, and `j.succAbove` enumerates
exactly those.  So the telescope density is `mixedC ψ (fixed slots) / π ^ n`,
which is the shape the cutoff estimate consumes.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity

noncomputable section

variable {m : ℕ}

/-! ### Moving a chosen slot to the front -/

/-- The mixed coefficient is unchanged when the slot `j` is moved to the front
and the remaining slots are listed in their original order by `j.succAbove`.
This is `mixedCoefficient_perm` for the cycle `Fin.cycleRange j`. -/
theorem mixedCoefficient_eq_cons_succAbove
    (H : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j : Fin (m + 1)) :
    mixedCoefficient H =
      mixedCoefficient (Fin.cons (H j) (fun i => H (j.succAbove i)) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have hcons : (Fin.cons (H j) (fun i => H (j.succAbove i)) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      = fun l => H (j.cycleRange.symm l) := by
    funext l
    refine Fin.cases ?_ ?_ l
    · simp
    · intro i; simp
  rw [hcons, mixedCoefficient_perm]

/-- **The normalization bridge.**  The mixed density of a family is the real
part of the mixed coefficient with any chosen slot in front, divided by
`π ^ n`. -/
theorem mixedDensity_eq_mixedC_succAbove (u : Fin (m + 1) → ComplexModel (m + 1) → ℝ)
    (j : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    mixedDensity u z =
      (mixedC (u j) (fun i => u (j.succAbove i)) z).re / Real.pi ^ (m + 1) := by
  rw [mixedDensity, mixedC,
    mixedCoefficient_eq_cons_succAbove (fun i => complexHessian (u i) z) j]

/-! ### The telescope in front-slot shape -/

/-- The slot `j` of the telescope with signed index `j` carries `h`. -/
@[simp] theorem telescopeFunctions_self {k : ℕ} (g h : ComplexModel k → ℝ) (j : Fin k) :
    telescopeFunctions g h j j = h := by
  simp [telescopeFunctions]

/-- The fixed slots of the telescope with signed index `j`, listed in order. -/
def telescopeFixed (phi psi : ComplexModel (m + 1) → ℝ) (j : Fin (m + 1)) :
    Fin m → ComplexModel (m + 1) → ℝ :=
  fun i => telescopeFunctions phi psi j (j.succAbove i)

theorem contDiffOn_telescopeFixed {Omega : Set (ComplexModel (m + 1))}
    {phi psi : ComplexModel (m + 1) → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi Omega) (hpsi : ContDiffOn ℝ ∞ psi Omega)
    (j : Fin (m + 1)) (i : Fin m) : ContDiffOn ℝ ∞ (telescopeFixed phi psi j i) Omega :=
  contDiffOn_telescopeFunctions hphi hpsi j _

/-- Every fixed slot of the telescope is plurisubharmonic where `φ` and
`φ + ψ` are. -/
theorem posSemidef_complexHessian_telescopeFixed
    {phi psi : ComplexModel (m + 1) → ℝ} {w : ComplexModel (m + 1)}
    (hphi : (complexHessian phi w).PosSemidef)
    (hsum : (complexHessian (fun y => phi y + psi y) w).PosSemidef)
    (j : Fin (m + 1)) (i : Fin m) :
    (complexHessian (telescopeFixed phi psi j i) w).PosSemidef :=
  posSemidef_complexHessian_telescopeFunctions_of_ne hphi hsum j _ (Fin.succAbove_ne j i)

/-- **The telescope density in the shape the cutoff estimate consumes**: the
signed potential `ψ` in the first slot, the `m` plurisubharmonic fixed slots
behind it, and the `π ^ n` normalization made explicit. -/
theorem mixedDensity_telescopeFunctions_eq (phi psi : ComplexModel (m + 1) → ℝ)
    (j : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    mixedDensity (telescopeFunctions phi psi j) z =
      (mixedC psi (telescopeFixed phi psi j) z).re / Real.pi ^ (m + 1) := by
  rw [mixedDensity_eq_mixedC_succAbove (telescopeFunctions phi psi j) j z,
    telescopeFunctions_self]
  rfl

end

end SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront
