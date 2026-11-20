import SGPT.Foundations.Analysis.Pending.TelescopeFlatSlotCutoff

set_option autoImplicit false

/-!
# The cutoff bound on the WHOLE Stokes telescope defect

`Pending.TelescopeFlatSlotCutoff.abs_integral_mul_mixedDensity_telescope_le_flat` bounds
the cutoff against ONE slot `D_{u_j}` of the Stokes telescope.  The Stokes defect on a
regular piece is the SUM of the `dim V` slots, and exchanging that finite sum with the
integral is not free: it needs each `χ · D_{u_j}` to be integrable, which a `ContDiffOn`
hypothesis on the potentials does not give directly.

This module supplies the exchange and sums the bounds.

* `integrable_mul_mixedDensity_telescope`: for globally smooth potentials, `χ · D_{u_j}` is
  continuous — through `mixedDensity_telescopeFunctions_eq` and the continuity of the mixed
  coefficient in `Pending.MixedHessianDivergence` — and supported in the compact
  `tsupport χ`, hence integrable.
* `mul_mixedDensity_telescope_congr`: the product `χ · D_{u_j}` depends on the potentials
  only through their germs at points of `tsupport χ`, being zero elsewhere.

Together these reduce the `ContDiffOn` case to the global one by the `η`-multiplication of
`Pending.TelescopeCutoffEstimateLocal`, and give

`|∫ χ · (Stokes defect)| ≤ C · A · ∑_{j} ∫_{supp χ} D_{flat slot j}`,

which is the shape the collar step of subvariety Stokes has to make small.  What is still
owed is only the CHOICE of cutoffs: a family `χ_m` along a good exhaustion whose squeeze
constants `A_m` times that flat comparison mass tend to zero.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeDefectCutoffSum

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeMixedDensityFront
open SGPT.Foundations.Analysis.Pending.TelescopeCutoffEstimate
open SGPT.Foundations.Analysis.Pending.TelescopeFlatSlotCutoff

noncomputable section

variable {m : ℕ}

/-! ### Integrability of one cutoff slot -/

/-- For globally smooth potentials and a compactly supported smooth cutoff, the cutoff
against one telescope slot is integrable: the mixed density is continuous by the continuity
of the mixed coefficient, and the product vanishes off the compact `tsupport χ`. -/
theorem integrable_mul_mixedDensity_telescope
    {phi psi : ComplexModel (m + 1) → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hpsi : ContDiff ℝ ∞ psi)
    {chi : ComplexModel (m + 1) → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hchic : HasCompactSupport chi) (j : Fin (m + 1)) :
    Integrable (fun z => chi z * mixedDensity (telescopeFunctions phi psi j) z) := by
  have hg : ∀ i, ContDiff ℝ ∞ (telescopeFixed phi psi j i) :=
    fun i => contDiff_telescopeFixed hphi hpsi j i
  have hmc : Continuous fun z => mixedC psi (telescopeFixed phi psi j) z :=
    continuous_mixedCoefficient_cons hg hpsi
  have heq : (fun z => chi z * mixedDensity (telescopeFunctions phi psi j) z) =
      fun z => chi z * ((mixedC psi (telescopeFixed phi psi j) z).re / Real.pi ^ (m + 1)) := by
    funext z
    rw [mixedDensity_telescopeFunctions_eq]
  have hcont : Continuous fun z => chi z * mixedDensity (telescopeFunctions phi psi j) z := by
    rw [heq]
    exact hchi.continuous.mul ((Complex.continuous_re.comp hmc).div_const _)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hchic ?_)
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-! ### Germ dependence of a cutoff slot -/

/-- `χ · D_{u_j}` depends on the two potentials only through their germs at the points of
`tsupport χ`: elsewhere the factor `χ` vanishes. -/
theorem mul_mixedDensity_telescope_congr {k : ℕ}
    {chi phi psi phi' psi' : ComplexModel k → ℝ}
    (hp : ∀ z ∈ tsupport chi, phi =ᶠ[𝓝 z] phi')
    (hq : ∀ z ∈ tsupport chi, psi =ᶠ[𝓝 z] psi')
    (j : Fin k) (z : ComplexModel k) :
    chi z * mixedDensity (telescopeFunctions phi psi j) z =
      chi z * mixedDensity (telescopeFunctions phi' psi' j) z := by
  by_cases hz : z ∈ tsupport chi
  · rw [mixedDensity_congr fun i =>
      complexHessian_congr (telescopeFunctions_eventuallyEq (hp z hz) (hq z hz) j i)]
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]

/-! ### The bound on the whole defect -/

/-- **The Chern--Levine--Nirenberg cutoff bound on the full Stokes telescope defect.**
The hypotheses are those of
`Pending.TelescopeFlatSlotCutoff.abs_integral_mul_mixedDensity_telescope_le_flat`; the
conclusion bounds the cutoff against the SUM of the `k` telescope slots, which is the
Stokes defect of the two parameter densities.  The dimension is unsplit, and `k = 0` is
allowed (both sides are then `0`). -/
theorem abs_integral_mul_telescopeDefect_le {k : ℕ}
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
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |psi z| ≤ C) :
    |∫ z, chi z * ∑ j : Fin k, mixedDensity (telescopeFunctions phi psi j) z| ≤
      C * A * ∑ j : Fin k, ∫ z in tsupport chi,
        mixedDensity (flatTelescopeSlot phi psi j) z := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  -- the per-slot bounds, which is all the analysis
  have hslot : ∀ j : Fin (m + 1),
      |∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z| ≤
        C * A * ∫ z in tsupport chi, mixedDensity (flatTelescopeSlot phi psi j) z :=
    fun j => abs_integral_mul_mixedDensity_telescope_le_flat hOmega hphi hpsi hchi hchic hchiO
      hphiP hsumP hsub hadd hC j
  -- an `η` supported in `Omega` and equal to one near `supp χ` makes the data global
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
  have hone : ∀ z ∈ tsupport chi, ∀ᶠ y in 𝓝 z, (eta : ComplexModel (m + 1) → ℝ) y = 1 :=
    fun z hz => heta1.filter_mono (nhds_le_nhdsSet hz)
  have hev : ∀ z ∈ tsupport chi, ∀ f : ComplexModel (m + 1) → ℝ,
      f =ᶠ[𝓝 z] fun y => eta y • f y := by
    intro z hz f
    filter_upwards [hone z hz] with y hy
    simp [hy]
  have hpt : ∀ (j : Fin (m + 1)) (z : ComplexModel (m + 1)),
      chi z * mixedDensity (telescopeFunctions phi psi j) z =
        chi z * mixedDensity
          (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j) z :=
    fun j z => mul_mixedDensity_telescope_congr
      (fun z' hz' => hev z' hz' phi) (fun z' hz' => hev z' hz' psi) j z
  -- exchange the finite sum with the integral, through the globalized data
  have hsw : ∫ z, chi z * ∑ j : Fin (m + 1), mixedDensity (telescopeFunctions phi psi j) z =
      ∑ j : Fin (m + 1), ∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z := by
    calc ∫ z, chi z * ∑ j : Fin (m + 1), mixedDensity (telescopeFunctions phi psi j) z
        = ∫ z, ∑ j : Fin (m + 1), chi z * mixedDensity
            (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j) z := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show chi z * ∑ j : Fin (m + 1), mixedDensity (telescopeFunctions phi psi j) z =
            ∑ j : Fin (m + 1), chi z * mixedDensity
              (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j) z
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => hpt j z
      _ = ∑ j : Fin (m + 1), ∫ z, chi z * mixedDensity
            (telescopeFunctions (fun y => eta y • phi y) (fun y => eta y • psi y) j) z :=
          integral_finsetSum Finset.univ fun j _ =>
            integrable_mul_mixedDensity_telescope hphi' hpsi' hchi' hchic j
      _ = ∑ j : Fin (m + 1), ∫ z, chi z * mixedDensity (telescopeFunctions phi psi j) z :=
          Finset.sum_congr rfl fun j _ =>
            integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt j z).symm)
  rw [hsw, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hslot j)

end

end SGPT.Foundations.Analysis.Pending.TelescopeDefectCutoffSum
