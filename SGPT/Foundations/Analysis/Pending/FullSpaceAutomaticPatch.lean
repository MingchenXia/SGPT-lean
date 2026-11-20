import SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
import SGPT.Foundations.Analysis.Pending.IncreasingLimitMass
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

set_option autoImplicit false

/-!
# Automatic local data for a full-space regular closed ball

The preceding full-space patch comparison was stated for one concrete smooth
chart patch, a relatively compact strict-truncation neighbourhood, and a
parameter closed ball.  This module constructs all of that data from an
admissible presentation at one regular parameter point outside its pole set.

The construction combines the actual smooth-off-poles witness supplied by
analytic singularities with a local potential supplied by theta-PSH.  It then
shrinks twice: first to make the two local representatives agree smoothly, and
then to a relatively compact coordinate ball lying in one finite truncation
level.  Finally the full-space biholomorphism supplies a parameter closed ball.
No total-mass or `acTopMass` comparison appears here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ContDiff Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceAutomaticPatch

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.MixedNonPluripolar FirstPass.GlobalPotentialPatches
open FullSpaceRegularPatch FullSpaceClosedBallDomains FullSpaceClosedBallTransport
  FullSpacePatchMeasure BedfordTaylor MixedNonPluripolar IncreasingLimitMass GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- At a regular full-space parameter point away from the pole set, all local
inputs required by the one-piece global-patch comparison can be chosen
canonically from the admissible presentation.  In particular the returned
`Q` is the diagonal patch built from the returned local potential; `W` is
relatively compact in its coordinate domain and lies in one common strict
truncation locus. -/
theorem exists_fullSpace_closedBall_patch_data
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {w : ComplexModel n} (hw : w ∈ fullParameterDomain P)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (fullSpaceCoordinateParametrization P w) ∉ poleSet p.potential) :
    ∃ (U : Opens (ComplexModel n)) (rho g : ComplexModel n → ℝ)
      (Q : Patch (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential))
      (W : Opens (ComplexModel n)) (k : ℕ) (r : ℝ),
      IsSmoothLocalPotential (perturbedRepresentative p).val
          (complexChartAt (n := n) P.center) U rho ∧
      ContDiffOn ℝ ∞ g U ∧
      EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
        (fun y => (g y : EReal)) U ∧
      IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y) ∧
      Q.chart = complexChartAt (n := n) P.center ∧
      W ≤ regularPotentialDomain P U ∧ W ≤ Q.domain ∧ RelativelyCompactIn W Q.domain ∧
      (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k ∧
      (∀ i, EqOn (fun y => (Q.corrected i y).toReal) (fun y => g y + rho y) W) ∧
      0 < r ∧
      closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)) ∧
      fullSpaceCoordinateParametrization P '' closedBall w r ⊆ W := by
  let e : ComplexChart n M := complexChartAt (n := n) P.center
  let z : ComplexModel n := fullSpaceCoordinateParametrization P w
  have hzTarget : z ∈ e.val.target := by
    change P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target
    exact P.source_subset (P.flattening.mapsTo_invFun hw)
  have hsmoothOff : SmoothOffPoleSet (n := n) p.potential :=
    SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
      p.smoothAnalyticSingularities
  obtain ⟨g, hgNear, hpotNear⟩ := hsmoothOff e z hzTarget (by simpa [e, z] using hpole)
  obtain ⟨R, rho, hzR, hrhoR, hpshR⟩ := p.potential_psh.1 e z hzTarget
  have hgood : {y | ContDiffAt ℝ ∞ g y ∧
      chartFunction p.potential e y = (g y : EReal)} ∩ R ∈ 𝓝 z :=
    inter_mem (hgNear.and hpotNear) (hrhoR.1.mem_nhds hzR)
  obtain ⟨A, hAsub, hAopen, hzA⟩ := _root_.mem_nhds_iff.mp hgood
  let U : Opens (ComplexModel n) := ⟨A, hAopen⟩
  have hUR : (U : Set (ComplexModel n)) ⊆ R := fun y hy => (hAsub hy).2
  have hrhoU : IsSmoothLocalPotential (perturbedRepresentative p).val e U rho :=
    hrhoR.mono U.isOpen hUR
  have hgU : ContDiffOn ℝ ∞ g U := fun y hy =>
    (hAsub hy).1.1.contDiffWithinAt
  have hpotU : EqOn (chartFunction p.potential e) (fun y => (g y : EReal)) U := fun y hy =>
    (hAsub hy).1.2
  let f : ComplexModel n → ℝ := fun y => g y + rho y
  have hpshU : PlurisubharmonicOn (fun y => (f y : EReal)) U := by
    intro y hy
    apply (hpshR y (hUR hy)).congr
    filter_upwards [U.isOpen.mem_nhds hy] with x hx
    simp only [f, EReal.coe_add, hpotU hx]
  have hfgU : ContDiffOn ℝ ∞ f U := hgU.add hrhoU.2.2.1
  have hsmoothD : IsSmoothPshOn (regularPotentialDomain P U) f :=
    isSmoothPshOn_of_psh (hfgU.mono fun _ hy => hy.1) (hpshU.mono fun _ hy => hy.1)
  have hbio := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hzD : z ∈ regularPotentialDomain P U := by
    refine ⟨hzA, ?_⟩
    exact hbio.mapsTo hw
  obtain ⟨k, hk⟩ := exists_nat_gt (-f z)
  have hkf : -(k : ℝ) < f z := by linarith
  have hfcont : ContinuousAt f z :=
    ((hfgU z hzA).contDiffAt (U.isOpen.mem_nhds hzA)).continuousAt
  have hthreshold : ∀ᶠ y in 𝓝 z, -(k : ℝ) < f y :=
    hfcont.eventually (Ioi_mem_nhds hkf)
  have htarget : {y | -(k : ℝ) < f y} ∩
      (regularPotentialDomain P U : Set (ComplexModel n)) ∈ 𝓝 z :=
    hthreshold.and ((regularPotentialDomain P U).isOpen.mem_nhds hzD)
  obtain ⟨delta, hdelta, hdeltaSub⟩ := Metric.mem_nhds_iff.mp htarget
  let W : Opens (ComplexModel n) := ⟨ball z (delta / 2), isOpen_ball⟩
  have hWtarget : (W : Set (ComplexModel n)) ⊆
      {y | -(k : ℝ) < f y} ∩ (regularPotentialDomain P U : Set (ComplexModel n)) := fun y hy =>
    hdeltaSub (ball_subset_ball (by linarith) hy)
  have hWD : W ≤ regularPotentialDomain P U := fun y hy => (hWtarget hy).2
  have hppsh : IsThetaPshPotential (perturbedRepresentative p).val p.potential := by
    simpa only [perturbedRepresentative] using p.potential_psh
  let Q : Patch (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential) :=
    diagonalPatch hppsh e hrhoU
  have hWQ : W ≤ Q.domain := by
    change W ≤ U
    exact fun y hy => (hWD hy).1
  have hWrel : RelativelyCompactIn W Q.domain := by
    change IsCompact (closure (W : Set (ComplexModel n))) ∧
      closure (W : Set (ComplexModel n)) ⊆ U
    refine ⟨(isCompact_closedBall z (delta / 2)).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall, ?_⟩
    intro y hy
    exact (hdeltaSub (closedBall_subset_ball (by linarith)
      (closure_ball_subset_closedBall hy))).2.1
  have hWstrict : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k := by
    intro y hy
    refine ⟨hWQ hy, fun i => ?_⟩
    change ((-(k : ℝ) : ℝ) : EReal) <
      chartFunction p.potential e y + (rho y : EReal)
    rw [hpotU ((hWD hy).1), ← EReal.coe_add]
    exact EReal.coe_lt_coe_iff.mpr (hWtarget hy).1
  have hcorrected : ∀ i, EqOn (fun y => (Q.corrected i y).toReal) f W := by
    intro i y hy
    change (chartFunction p.potential e y + (rho y : EReal)).toReal = f y
    rw [hpotU ((hWD hy).1), ← EReal.coe_add, EReal.toReal_coe]
  have hwW : w ∈ regularParameterDomain P W := by
    apply (mem_regularParameterDomain_iff P W w).mpr
    refine ⟨hw, ?_⟩
    change P.coordinateParametrization w ∈ ball z (delta / 2)
    simpa only [z, fullSpaceCoordinateParametrization_apply] using
      mem_ball_self (half_pos hdelta)
  obtain ⟨r, hr, hballW⟩ := exists_closedBall_subset_regularParameterDomain P W hwW
  have hballU : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨hxA, hxW⟩ := (mem_regularParameterDomain_iff P W x).mp (hballW hx)
    exact (mem_regularParameterDomain_iff P U x).mpr ⟨hxA, (hWD hxW).1⟩
  have himage : fullSpaceCoordinateParametrization P '' closedBall w r ⊆ W := by
    rintro y ⟨x, hx, rfl⟩
    exact (mem_regularParameterDomain_iff P W x).mp (hballW hx) |>.2
  refine ⟨U, rho, g, Q, W, k, r, ?_, ?_, ?_, ?_, ?_, hWD, hWQ, hWrel,
    hWstrict, hcorrected, hr, hballU, himage⟩
  · simpa only [e] using hrhoU
  · simpa only [e] using hgU
  · simpa only [e] using hpotU
  · simpa only [f] using hsmoothD
  · change e = complexChartAt (n := n) P.center
    rfl

/-- In complex dimension one, the automatic local choice above removes the
manual chart, patch and strict-locus data from the closed-ball comparison with
the global non-pluripolar measure. -/
theorem exists_fullSpace_closedBall_lintegral_eq_globalMixedMeasure_of_dim_eq_one
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {w : ComplexModel n} (hw : w ∈ fullParameterDomain P)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (fullSpaceCoordinateParametrization P w) ∉ poleSet p.potential)
    (hn : n = 1) :
    ∃ r > 0,
      ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
        globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
          (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
  obtain ⟨U, rho, g, Q, W, k, r, hrho, hg, hpot, hsmooth, hchart, hWD, hWQ,
      hWrel, hWstrict, hcorrected, hr, hball, himage⟩ :=
    exists_fullSpace_closedBall_patch_data p P hw hpole
  refine ⟨r, hr, ?_⟩
  exact closedBall_lintegral_patchDensity_eq_globalMixedMeasure_of_dim_eq_one
    p P U hrho hg hpot w hball hsmooth hn Q hchart W hWD hWQ k hWrel hWstrict
      hcorrected himage

end SGPT.Foundations.Analysis.Pending.FullSpaceAutomaticPatch
