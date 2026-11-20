import SGPT.Foundations.Analysis.Pending.PatchDensityTelescope
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.MixedCoordinateDensity

set_option autoImplicit false

/-!
# The Stokes defect is locally a mixed Monge--Ampere density of the parameters

`Pending.PatchDensityTelescope` writes the Stokes defect
`(\beta + dd^cv)^k - \beta^k` in the parameters of a regular patch as a sum of `k` mixed
densities, the slot carrying `dd^cv` being the genuine `dd^c` of `v` restricted to the
branch.  The remaining slots are pullbacks of `\beta`.

This module removes the last trace of an ambient form from that expression.  Near any
parameter the background has a smooth local potential in the chart at the centre of the
patch (the local `dd`-bar lemma, `Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials`),
and the parametrization is holomorphic, so the pullback of `\beta` is the `dd^c` of that
potential composed with the parametrization.  Every slot of every telescope term is then
the `dd^c` of a smooth real function of the `k = \dim V` complex parameters, and the mixed
exterior density of such a family is the mixed determinant density of the complex Hessians
(`fpmma:geometric-density`).  Hence, on a parameter neighbourhood,

`\rho_{\beta + dd^cv}(w) - \rho_{\beta}(w)
  = \sum_{j<k} D_{u_{j,1},\dots,u_{j,k}}(w)`,

with each family `u_j` consisting of `\varphi + v\circ\gamma`, `v\circ\gamma` and
`\varphi` in the pattern of the telescope, `\varphi` a local potential of `\beta` read in
the parameters.

That is exactly the shape of the integration by parts proved in
`Pending.MixedHessian` (`fpmma:hessian-ibp`): for smooth real functions
`a, b, g_1, \dots, g_{k-1}` on `\mathbf C^k` with `a` compactly supported,
`\int a\,C(H_b, H_{g_1},\dots) = \int b\,C(H_a, H_{g_1},\dots)`.

Four things still separate the present identity from Stokes along `V_{\mathrm{reg}}`, and
none of them is algebra.  The obligation is an equality of two `ENNReal` suprema, so the
signed densities have to be brought to it (nonnegativity is proved in
`Pending.PatchDensityTelescope`, the rest is not).  The local potential `\varphi` lives on a
neighbourhood of ONE parameter, while a piece of a regular-piece family is an arbitrary
measurable subset of the whole parameter domain, so the exhaustion must first be refined so
that every piece lies in one such neighbourhood.  The per-piece identities then have to be
summed with a PARTITION OF UNITY subordinate to the patches -- disjoint pieces have no
cancelling boundary terms -- and the integration by parts above hypothesises smoothness on
all of `\mathbf C^k` and excludes `k = 0`, so the potentials must be extended.  Finally the
cut-off error needs SMALLNESS of the background mass on a collar around `V_{\mathrm{sing}}`,
not merely its finiteness; that is the genuine remainder.

`Pending.GlobalSlotStokes` is a proved template for the partition-of-unity step in the
ambient compact case (`sum_defectMeasure_eq`: the defects of a partition of unity telescope);
it is not a substitute here, `V_{\mathrm{reg}}` being non-compact and of lower dimension with
patch-parameter integrals rather than Bedford--Taylor measures.
-/

open Set MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope
open SGPT.Foundations.Analysis.Pending.PatchDensityTelescope

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **A local potential of a closed real `(1,1)`-form, read in patch parameters.**  Near
any parameter of a regular patch the pullback of a closed real `(1,1)`-form is the `dd^c`
of a smooth real function of the parameters. -/
theorem exists_localPotential_patchCoordinateForm (theta : ClosedRealOneOneForm n M)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    ∃ (Omega : Set (ComplexModel V.dim)) (phi : ComplexModel V.dim → ℝ),
      w ∈ Omega ∧ IsOpen Omega ∧ Omega ⊆ P.parameterDomain ∧
        ContDiffOn ℝ ∞ phi Omega ∧
        ∀ w' ∈ Omega,
          RegularPatchTransition.patchCoordinateForm theta.val P w' = smoothDDC phi w' := by
  set eP := complexChartAt (n := n) P.center with heP
  have hzt : P.coordinateParametrization w ∈ eP.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  obtain ⟨W, rho, hzW, hWopen, hWsub, hrho, heq⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials theta eP _ hzt
  have hPopen : IsOpen P.parameterDomain :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P
  set Omega : Set (ComplexModel V.dim) :=
    P.parameterDomain ∩ P.coordinateParametrization ⁻¹' W with hOmega
  have hOmegaOpen : IsOpen Omega :=
    ((contDiffOn_complex_coordinateParametrization P).restrict_scalars ℝ).continuousOn.isOpen_inter_preimage
      hPopen hWopen
  have hmaps : MapsTo P.coordinateParametrization Omega W := fun _ hw' => hw'.2
  have hgamma : ContDiffOn ℂ ∞ P.coordinateParametrization Omega :=
    (contDiffOn_complex_coordinateParametrization P).mono inter_subset_left
  refine ⟨Omega, fun y => rho (P.coordinateParametrization y), ⟨hw, hzW⟩, hOmegaOpen,
    inter_subset_left, ?_, ?_⟩
  · exact hrho.comp ((contDiffOn_complex_coordinateParametrization P).restrict_scalars ℝ |>.mono
      inter_subset_left) hmaps
  · intro w' hw'
    have hcomp := HolomorphicDDC.smoothDDC_comp hOmegaOpen hWopen hgamma hrho hmaps hw'
    rw [hcomp, RegularPatchTransition.patchCoordinateForm, heq hw'.2]

/-- The telescope pattern applied to real functions of the parameters: `g + h` below the
slot `j`, `h` in the slot `j` itself, and `g` above it. -/
def telescopeFunctions {k : ℕ} (g h : ComplexModel k → ℝ) (j : Fin k) :
    Fin k → ComplexModel k → ℝ :=
  fun i => if (i : ℕ) < (j : ℕ) then (fun y => g y + h y) else if i = j then h else g

theorem contDiffOn_telescopeFunctions {k : ℕ} {g h : ComplexModel k → ℝ}
    {Omega : Set (ComplexModel k)} (hg : ContDiffOn ℝ ∞ g Omega) (hh : ContDiffOn ℝ ∞ h Omega)
    (j : Fin k) (i : Fin k) : ContDiffOn ℝ ∞ (telescopeFunctions g h j i) Omega := by
  unfold telescopeFunctions
  split
  · exact hg.add hh
  · split
    · exact hh
    · exact hg

/-- **The telescope of two `dd^c`s is the `dd^c` of the telescope of the potentials.** -/
theorem telescopeFamily_smoothDDC {k : ℕ} {g h : ComplexModel k → ℝ}
    {Omega : Set (ComplexModel k)} (hOmega : IsOpen Omega)
    (hg : ContDiffOn ℝ ∞ g Omega) (hh : ContDiffOn ℝ ∞ h Omega)
    {w : ComplexModel k} (hw : w ∈ Omega) (j : Fin k) :
    telescopeFamily (smoothDDC g w) (smoothDDC h w) j =
      fun i => smoothDDC (telescopeFunctions g h j i) w := by
  funext i
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | hij | hij
  · rw [telescopeFamily_apply_of_lt _ _ hij]
    have : telescopeFunctions g h j i = fun y => g y + h y := by
      simp [telescopeFunctions, hij]
    rw [this, smoothDDC_add hOmega hg hh hw]
  · have hije : i = j := Fin.ext hij
    subst hije
    rw [telescopeFamily_apply_self]
    have : telescopeFunctions g h i i = h := by simp [telescopeFunctions]
    rw [this]
  · rw [telescopeFamily_apply_of_gt _ _ hij]
    have hne : i ≠ j := fun hij' => absurd (congrArg Fin.val hij') (Nat.ne_of_gt hij)
    have : telescopeFunctions g h j i = g := by
      simp [telescopeFunctions, Nat.not_lt_of_gt hij, hne]
    rw [this]

/-- **The Stokes defect, locally, is a sum of mixed Monge--Ampere densities of the
parameters.**  For a presentation of the zero class with zero representative, unit error
and chart-smooth real potential `v`, every parameter of every regular patch has a
neighbourhood on which the difference of the parameter densities of `\beta + dd^cv` and of
`\beta` is the sum of the `\dim V` mixed determinant densities of the telescope families
built from a local potential of `\beta` in the parameters and from `v` restricted to the
branch.

Nothing ambient is left in the right-hand side: it is the mixed Monge--Ampere density of
`\dim V` smooth real functions of `\dim V` complex variables, the shape for which
integration by parts against a compactly supported test function is proved in
`Pending.MixedHessian`. -/
theorem exists_localPotential_patchFormDensity_currentForm_sub
    (beta : KahlerBackground n M) {V : ClosedIrreducibleAnalyticSubvariety n M}
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    ∃ (Omega : Set (ComplexModel V.dim)) (phi : ComplexModel V.dim → ℝ),
      w ∈ Omega ∧ IsOpen Omega ∧ Omega ⊆ P.parameterDomain ∧
        ContDiffOn ℝ ∞ phi Omega ∧
        ContDiffOn ℝ ∞ (fun y => v (P.toManifold y)) Omega ∧
        ∀ w' ∈ Omega,
          PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w' -
              PatchFormMass.patchFormDensity beta.form.val P w' =
            ∑ j : Fin V.dim, MixedMongeAmpere.mixedDensity
              (telescopeFunctions phi (fun y => v (P.toManifold y)) j) w' := by
  obtain ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hpot⟩ :=
    exists_localPotential_patchCoordinateForm beta.form P hw
  set psi : ComplexModel V.dim → ℝ := fun y => v (P.toManifold y) with hpsi
  have hmapsP : MapsTo P.coordinateParametrization Omega
      (complexChartAt (n := n) P.center).val.target :=
    fun y hy => P.source_subset (P.flattening.mapsTo_invFun (hOsub hy))
  have hpsis : ContDiffOn ℝ ∞ psi Omega :=
    (hvs (complexChartAt (n := n) P.center)).comp
      (((contDiffOn_complex_coordinateParametrization P).restrict_scalars ℝ).mono hOsub) hmapsP
  refine ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hpsis, ?_⟩
  intro w' hw'
  have hddc : RegularPatchTransition.patchCoordinateForm
      (SmoothDDCForm.ddcForm v hvs) P w' = smoothDDC psi w' :=
    patchCoordinateForm_ddcForm P hvs (hOsub hw')
  rw [patchFormDensity_currentForm_sub beta q hq hvs P w', hpot w' hw', hddc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [telescopeFamily_smoothDDC hOopen hphi hpsis hw' j]
  exact actualMixedTopDensity_smoothDDC fun i =>
    ((contDiffOn_telescopeFunctions hphi hpsis j i) w' hw').contDiffAt
      (hOopen.mem_nhds hw') |>.of_le (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

end

end SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
