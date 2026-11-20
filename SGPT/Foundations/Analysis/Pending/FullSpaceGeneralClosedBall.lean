import SGPT.Foundations.Analysis.Pending.FullSpaceLowDimClosedBall
import SGPT.Foundations.Analysis.Pending.FullSpaceGeneralDensity
import SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
import SGPT.Foundations.Analysis.Pending.FullSpaceAutomaticPatch

set_option autoImplicit false

/-!
# A smooth current on one full-space regular closed ball, in every dimension

`Pending.FullSpaceLowDimClosedBall` and `Pending.FullSpacePatchMeasure` prove
the single-piece bridge from the actual restricted-mass density `patchDensity`
to a genuine smooth measure, and then to the global diagonal non-pluripolar
measure, only in complex dimension one (and, for the intermediate step, two).
The dimension restriction came exclusively from the algebraic identity between
the genuine exterior-power density and the determinant coefficient.

`Pending.CoordinateDensityGeneral` proves that identity in every dimension for
semipositive real `(1,1)`-forms, and `Pending.FullSpaceGeneralDensity` supplies
it for the pulled-back current form at any regular parameter point off the pole
set.  This module therefore repeats the dimension-two chain verbatim with no
dimension hypothesis:

* `patchDensity_eq_smoothDensity_corrected`,
* `lintegral_patchDensity_eq_smoothMeasure_coordinateImage`,
* `closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage`,
* `closedBall_lintegral_patchDensity_eq_globalMixedMeasure`, and
* `exists_fullSpace_closedBall_lintegral_eq_globalMixedMeasure`, the automatic
  version in which all local data is chosen from the presentation itself.

The pole-free premise is the same explicit property of the chosen coordinate
neighbourhood that the dimension-two statements already carry; the automatic
version discharges it from `SmoothOffPoleSet` at the chosen point.  Nothing
here identifies `acTopMass p` with the ambient mass: that still needs the
finite/countable regular-piece localization.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceGeneralClosedBall

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches
open FullSpaceRegularPatch FullSpaceClosedBallDomains FullSpaceClosedBallTransport
  FullSpaceLocalCurrent FullSpaceGeneralDensity FullSpacePatchMeasure BedfordTaylor
  MixedNonPluripolar GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

omit [IsComplexManifold n M] in
/-- A chart-smooth real representative of a potential on an open set certifies
that the set avoids the pole locus.  This is what makes the pole-free premise of
the dimension-two statements redundant: it already follows from the local
smooth-representative hypothesis those statements carry. -/
theorem notMem_poleSet_of_chartFunction_eq {u : M → EReal} {e : ComplexChart n M}
    {U : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hpot : EqOn (chartFunction u e) (fun y => (g y : EReal)) U)
    {z : ComplexModel n} (hz : z ∈ U) : e.val.symm z ∉ poleSet u := by
  intro hmem
  have hval : u (e.val.symm z) = (g z : EReal) := hpot hz
  rw [mem_poleSet.mp hmem] at hval
  exact (EReal.coe_ne_bot (g z)) hval.symm

/-- **The local density identification on a full-space regular patch, in every
complex dimension.**  On a pole-free coordinate neighbourhood the actual
parameter density is the smooth density of the pulled-back corrected local
potential.  This is the dimension-free form of
`FullSpaceLowDimClosedBall.patchDensity_eq_smoothDensity_corrected_of_dim_eq_two`. -/
theorem patchDensity_eq_smoothDensity_corrected
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {w : ComplexModel n} (hw : w ∈ regularParameterDomain P U) :
    patchDensity p P w =
      smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w := by
  let hbio := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hwA : w ∈ fullParameterDomain P :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.1
  have hwU : P.coordinateParametrization w ∈ U :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.2
  have hsub : (regularParameterDomain P U : Set (ComplexModel n)) ⊆
      (fullParameterDomain P : Set (ComplexModel n)) := fun x hx =>
    (mem_regularParameterDomain_iff P U x).mp hx |>.1
  have hmap : MapsTo (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n))
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := (mem_regularParameterDomain_iff P U x).mp hx
    exact ⟨hxU, hbio.mapsTo hxA⟩
  have hF : ContDiffOn ℂ ∞ (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n)) := hbio.holo.mono hsub
  have hF_eq : fullSpaceCoordinateParametrization P = P.coordinateParametrization := rfl
  have hcorrected : ContDiffOn ℝ ∞ (fun y => g y + rho y)
      (regularPotentialDomain P U : Set (ComplexModel n)) :=
    (hg.add hrho.2.2.1).mono fun _ hy => hy.1
  have hpull : ContDiffOn ℝ ∞
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x))
      (regularParameterDomain P U : Set (ComplexModel n)) :=
    hcorrected.comp (hF.restrict_scalars ℝ) hmap
  have htwo : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hw_nhds : (regularParameterDomain P U : Set (ComplexModel n)) ∈ nhds w :=
    (regularParameterDomain P U).isOpen.mem_nhds hw
  have hpull2 : ContDiffAt ℝ 2
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w :=
    ((hpull w hw).contDiffAt hw_nhds).of_le htwo
  have hcurrent : coordinateCurrentForm p (complexChartAt (n := n) P.center)
      (fullSpaceCoordinateParametrization P w) =
      smoothDDC (fun y => g y + rho y) (fullSpaceCoordinateParametrization P w) := by
    simpa only [fullSpaceCoordinateParametrization_apply] using
      (coordinateCurrentForm_eq_smoothDDC_corrected p
        (complexChartAt (n := n) P.center) hrho hg hpot hwU)
  have hddc : smoothDDC
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w =
      (smoothDDC (fun y => g y + rho y)
          (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
        (fderiv ℝ (fullSpaceCoordinateParametrization P) w) :=
    FirstPass.HolomorphicDDC.smoothDDC_comp
      (regularParameterDomain P U).isOpen (regularPotentialDomain P U).isOpen hF
      hcorrected hmap hw
  calc
    patchDensity p P w =
        normalizedTopPowerDensity
          ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by
          rw [hF_eq]
          exact patchDensity_eq_normalizedTopPowerDensity p P w hwA
            (notMem_poleSet_of_chartFunction_eq hpot hwU)
    _ = normalizedTopPowerDensity
          ((smoothDDC (fun y => g y + rho y)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by rw [hcurrent]
    _ = normalizedTopPowerDensity
          (smoothDDC (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) :=
      congrArg normalizedTopPowerDensity hddc.symm
    _ = smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
      rho (fullSpaceCoordinateParametrization P x)) w :=
      normalizedTopPowerDensity_smoothDDC hpull2

/-- A compact pole-free parameter piece has exactly the smooth mass of its
coordinate image, in every complex dimension. -/
theorem lintegral_patchDensity_eq_smoothMeasure_coordinateImage
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y)) :
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' K) := by
  calc
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        ∫⁻ w in K, ENNReal.ofReal
          (smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
      refine setLIntegral_congr_fun hK.measurableSet fun w hw => ?_
      rw [patchDensity_eq_smoothDensity_corrected p P U hrho hg hpot (hKU hw)]
    _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) :=
      (smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp P U hK hKU hsmooth).symm

/-- A pole-free closed parameter ball has the exact smooth-mass identity in
every complex dimension. -/
theorem closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (w : ComplexModel n) {r : ℝ}
    (hball : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y)) :
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' closedBall w r) :=
  lintegral_patchDensity_eq_smoothMeasure_coordinateImage p P U hrho hg hpot
    (isCompact_closedBall w r) hball hsmooth

section GlobalMeasure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **One full-space closed ball is measured exactly by the global diagonal
non-pluripolar measure, in every complex dimension.**  This is the dimension-free
form of
`FullSpacePatchMeasure.closedBall_lintegral_patchDensity_eq_globalMixedMeasure_of_dim_eq_one`;
the proof is that statement's smooth-measure localization with the general
density identification substituted for the dimension-one one. -/
theorem closedBall_lintegral_patchDensity_eq_globalMixedMeasure
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (w : ComplexModel n) {r : ℝ}
    (hball : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (Q : Patch (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential))
    (hchart : Q.chart = complexChartAt (n := n) P.center)
    (W : Opens (ComplexModel n)) (hWD : W ≤ regularPotentialDomain P U)
    (hWQ : W ≤ Q.domain) (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    (hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal)
      (fun z => g z + rho z) W)
    (himage : fullSpaceCoordinateParametrization P '' closedBall w r ⊆ W) :
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
      globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
        (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
  have hsmoothW : IsSmoothPshOn W (fun y => g y + rho y) :=
    ⟨hsmooth.1.mono hWD, hsmooth.2.1.mono hWD,
      fun z hz => hsmooth.2.2 z (hWD hz)⟩
  have hsmooth_restrict :
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' closedBall w r) =
      smoothMeasure W (fun y => g y + rho y) hsmoothW
        (fullSpaceCoordinateParametrization P '' closedBall w r) := by
    symm
    calc
      smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' closedBall w r) =
        (smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth).restrict
          (W : Set (ComplexModel n))
          (fullSpaceCoordinateParametrization P '' closedBall w r) :=
        congrArg (fun mu : Measure (ComplexModel n) =>
          mu (fullSpaceCoordinateParametrization P '' closedBall w r))
          (smoothMeasure_restrict hWD (fun y => g y + rho y) hsmooth hsmoothW).symm
      _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' closedBall w r) := by
        rw [Measure.restrict_apply' W.isOpen.measurableSet,
          inter_eq_self_of_subset_left himage]
  calc
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
        smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' closedBall w r) :=
      closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage
        p P U hrho hg hpot w hball hsmooth
    _ = smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' closedBall w r) := hsmooth_restrict
    _ = globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
          (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
      simpa only [hchart, perturbedRepresentative] using
        (globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
          p.potential_psh.1 Q W hWQ k hW hWk hsmoothW hcorrected himage).symm

/-- **The automatic version, in every complex dimension.**  At a regular
full-space parameter point away from the pole set, all the local data of the
preceding theorem is chosen canonically from the admissible presentation
(`FullSpaceAutomaticPatch.exists_fullSpace_closedBall_patch_data`), so a closed
parameter ball around that point is measured exactly by the global diagonal
non-pluripolar measure of its coordinate image. -/
theorem exists_fullSpace_closedBall_lintegral_eq_globalMixedMeasure
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {w : ComplexModel n} (hw : w ∈ fullParameterDomain P)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (fullSpaceCoordinateParametrization P w) ∉ poleSet p.potential) :
    ∃ r > 0,
      ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
        globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
          (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
  obtain ⟨U, rho, g, Q, W, k, r, hrho, hg, hpot, hsmooth, hchart, hWD, hWQ,
      hWrel, hWstrict, hcorrected, hr, hball, himage⟩ :=
    FullSpaceAutomaticPatch.exists_fullSpace_closedBall_patch_data p P hw hpole
  refine ⟨r, hr, ?_⟩
  exact closedBall_lintegral_patchDensity_eq_globalMixedMeasure
    p P U hrho hg hpot w hball hsmooth Q hchart W hWD hWQ k hWrel hWstrict hcorrected himage

end GlobalMeasure

end SGPT.Foundations.Analysis.Pending.FullSpaceGeneralClosedBall
