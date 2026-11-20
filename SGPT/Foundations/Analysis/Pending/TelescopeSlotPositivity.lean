import SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
import SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity

set_option autoImplicit false

/-!
# The fixed slots of the Stokes telescope are plurisubharmonic

`Pending.PatchDensityLocalPotential.exists_localPotential_patchFormDensity_currentForm_sub`
writes the Stokes defect on a parameter neighbourhood as a sum of `dim V` mixed
Monge--Ampère densities of the families
`telescopeFunctions φ (v ∘ P) j`, where `φ` is a local potential of the
background read in the patch parameters.  It supplies `ContDiffOn` for `φ` and
for `v ∘ P` and nothing else.

The Chern--Levine--Nirenberg cutoff estimate of
`Pending.MixedCoefficientSlotBound` needs more: every slot other than the signed
one must have a positive semidefinite complex Hessian.  That is true, and this
module proves it.  In the telescope family with signed index `j`, the slots
`i < j` carry `φ + v ∘ P` and the slots `i > j` carry `φ`; the first is a local
potential of `β + ddᶜv`, which is semipositive because the presentation is
admissible with empty pole set, and the second is a local potential of the
Kähler background `β`.  Semipositivity of a `ddᶜ` gives semidefiniteness of the
complex Hessian by `Pending.SmoothDDCHessianPositivity`.

The statement below bundles the potential, its smoothness, the two
semidefiniteness certificates and the density identity into a single
existential, so that a consumer gets one `φ` satisfying all of them rather than
two unrelated ones.
-/

open Set MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope
open SGPT.Foundations.Analysis.Pending.PatchDensityTelescope
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The pulled-back Kähler background is semipositive at every parameter of a
regular patch. -/
theorem coefficientSemipositive_patchCoordinateForm_kahler (beta : KahlerBackground n M)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    CoefficientSemipositive
      (RegularPatchTransition.patchCoordinateForm beta.form.val P w) := by
  have hz : P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  exact (isOneOne_and_semipositive_patchCoordinateForm beta.form.val P hw
    (fun a b => beta.form.property.2 _ _ hz a b) (fun v => beta.isSemipositive _ _ hz v)).2

/-- The pulled-back current form of a smooth-potential presentation is
semipositive at every parameter of a regular patch: the pole set is empty, so
the ambient semipositivity of an admissible presentation holds at the centre
chart image of the parameter. -/
theorem coefficientSemipositive_patchCoordinateForm_currentForm
    {beta : KahlerBackground n M} {alpha : RealBottChern n M} {epsilon : PositiveError}
    (q : AdmissibleRestrictedCurrentPresentation beta alpha V epsilon)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    CoefficientSemipositive
      (RegularPatchTransition.patchCoordinateForm
        (ACTopMassComparison.currentForm q hvs) P w) := by
  have hz : P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hpole : (complexChartAt (n := n) P.center).val.symm
      (P.coordinateParametrization w) ∉ poleSet q.potential := by
    rw [ACTopMassComparison.poleSet_eq_empty q hpot]
    simp
  obtain ⟨h11, hpos⟩ :=
    AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive q
      (complexChartAt (n := n) P.center) hz hpole
  rw [ACTopMassComparison.coordinateCurrentForm_eq q hvs hpot] at h11 hpos
  exact (isOneOne_and_semipositive_patchCoordinateForm
    (ACTopMassComparison.currentForm q hvs) P hw h11 hpos).2

/-- **The local telescope datum, with plurisubharmonicity of both fixed slots.**
Every parameter of every regular patch has a neighbourhood carrying a local
potential `φ` of the background in the parameters such that

* `φ` and `v ∘ P` are smooth there;
* the complex Hessians of `φ` and of `φ + v ∘ P` are positive semidefinite
  there;
* the Stokes defect of the parameter densities is the sum of the `dim V` mixed
  densities of the telescope families built from `φ` and `v ∘ P`.

The first two items are exactly the positivity the Chern--Levine--Nirenberg
cutoff estimate requires of its fixed slots; the third is the identity of
`Pending.PatchDensityLocalPotential`, reproved here so that the SAME `φ`
carries all three. -/
theorem exists_localPotential_telescope_posSemidef
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    ∃ (Omega : Set (ComplexModel V.dim)) (phi : ComplexModel V.dim → ℝ),
      w ∈ Omega ∧ IsOpen Omega ∧ Omega ⊆ P.parameterDomain ∧
        ContDiffOn ℝ ∞ phi Omega ∧
        ContDiffOn ℝ ∞ (fun y => v (P.toManifold y)) Omega ∧
        (∀ w' ∈ Omega, (complexHessian phi w').PosSemidef) ∧
        (∀ w' ∈ Omega,
          (complexHessian (fun y => phi y + v (P.toManifold y)) w').PosSemidef) ∧
        ∀ w' ∈ Omega,
          PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w' -
              PatchFormMass.patchFormDensity beta.form.val P w' =
            ∑ j : Fin V.dim, MixedMongeAmpere.mixedDensity
              (telescopeFunctions phi (fun y => v (P.toManifold y)) j) w' := by
  obtain ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hform⟩ :=
    exists_localPotential_patchCoordinateForm beta.form P hw
  set psi : ComplexModel V.dim → ℝ := fun y => v (P.toManifold y) with hpsi
  have hmapsP : MapsTo P.coordinateParametrization Omega
      (complexChartAt (n := n) P.center).val.target :=
    fun y hy => P.source_subset (P.flattening.mapsTo_invFun (hOsub hy))
  have hpsis : ContDiffOn ℝ ∞ psi Omega :=
    (hvs (complexChartAt (n := n) P.center)).comp
      (((contDiffOn_complex_coordinateParametrization P).restrict_scalars ℝ).mono hOsub) hmapsP
  -- `ddᶜψ` is the pulled-back `ddᶜv`, on all of the parameter domain
  have hddc : ∀ w' ∈ Omega,
      RegularPatchTransition.patchCoordinateForm (SmoothDDCForm.ddcForm v hvs) P w' =
        smoothDDC psi w' := fun w' hw' => patchCoordinateForm_ddcForm P hvs (hOsub hw')
  -- the sum `φ + ψ` is a local potential of the current form
  have hsum : ∀ w' ∈ Omega,
      RegularPatchTransition.patchCoordinateForm
          (ACTopMassComparison.currentForm q hvs) P w' =
        smoothDDC (fun y => phi y + psi y) w' := by
    intro w' hw'
    have hadd := patchCoordinateForm_add beta.form.val (SmoothDDCForm.ddcForm v hvs)
      (ACTopMassComparison.currentForm q hvs)
      (fun e z => by
        rw [ACTopMassComparison.currentForm_coeff,
          coeff_perturbedRepresentative_of_representative_eq_zero q hq e z,
          SmoothDDCForm.ddcForm_coeff]) P w'
    rw [hadd, hform w' hw', hddc w' hw', smoothDDC_add hOopen hphi hpsis hw']
  refine ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hpsis, ?_, ?_, ?_⟩
  · refine complexHessian_posSemidef_of_contDiffOn hOopen hphi fun w' hw' => ?_
    rw [← hform w' hw']
    exact coefficientSemipositive_patchCoordinateForm_kahler beta P (hOsub hw')
  · refine complexHessian_posSemidef_of_contDiffOn hOopen (hphi.add hpsis) fun w' hw' => ?_
    rw [← hsum w' hw']
    exact coefficientSemipositive_patchCoordinateForm_currentForm q hvs hpot P (hOsub hw')
  · intro w' hw'
    rw [patchFormDensity_currentForm_sub beta q hq hvs P w', hform w' hw', hddc w' hw']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [telescopeFamily_smoothDDC hOopen hphi hpsis hw' j]
    exact actualMixedTopDensity_smoothDDC fun i =>
      ((contDiffOn_telescopeFunctions hphi hpsis j i) w' hw').contDiffAt
        (hOopen.mem_nhds hw') |>.of_le (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The complex Hessian of every FIXED slot of a telescope family is positive
semidefinite: the slots below the signed index carry `φ + ψ` and those above it
carry `φ`. -/
theorem posSemidef_complexHessian_telescopeFunctions_of_ne {k : ℕ}
    {phi psi : ComplexModel k → ℝ} {w : ComplexModel k}
    (hphi : (complexHessian phi w).PosSemidef)
    (hsum : (complexHessian (fun y => phi y + psi y) w).PosSemidef)
    (j i : Fin k) (hij : i ≠ j) :
    (complexHessian (telescopeFunctions phi psi j i) w).PosSemidef := by
  have hcases : telescopeFunctions phi psi j i = (fun y => phi y + psi y) ∨
      telescopeFunctions phi psi j i = phi := by
    by_cases h : (i : ℕ) < (j : ℕ)
    · exact Or.inl (by simp [telescopeFunctions, h])
    · exact Or.inr (by simp [telescopeFunctions, h, hij])
  rcases hcases with h | h <;> rw [h]
  · exact hsum
  · exact hphi

end

end SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity
