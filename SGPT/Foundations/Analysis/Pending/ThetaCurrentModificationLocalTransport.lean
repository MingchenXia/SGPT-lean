import SGPT.Foundations.Analysis.Pending.AnalyticModificationCoordinatePairs
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
import SGPT.Foundations.Analysis.Pending.ActualUnboundedScalarCurrentPullback
import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

set_option autoImplicit false

/-! Full mathematical statement and ENTIRE BP proof precede Lean.
The original unbounded theta potentials and SAME global currents are retained.
No incoming coordinate, integrability, current or calibration certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
universe u
namespace SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationLocalTransport
open FirstPass FirstPass.HolomorphicMaps FirstPass.LocalPotentialPullback
  _root_.SGPT.Foundations.Analysis.LocalCurrents GlobalCurrents CanonicalCurrentFrame
  NaturalThetaPshGeometricCurrent GlobalPositiveCurrentACRestriction ActualAnalyticCurrentLocalDensity
  ThetaPotentialPrescribedChartReader AnalyticModificationLocalDiscrepancy
  AnalyticModificationCoordinatePairs AnalyticModificationStrongPullback
  ActualUnboundedScalarCurrentPullback LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalBedfordTaylorProducts ScalarLeviPositiveCurrent
  LocalCurrentPullback LocalCurrentPullbackDdc PositiveCurrentACTopMeasure
  LocalCurrentDeterminant BedfordTaylor

private theorem noncollapse_of_ae_finite {n : ℕ} {W : Opens (ComplexModel n)}
    {v : ComplexModel n → EReal}
    (hfin : ∀ᵐ z ∂volume.restrict (W : Set (ComplexModel n)), v z ≠ ⊤ ∧ v z ≠ ⊥) :
    ∀ z ∈ W, ∀ O : Set (ComplexModel n), IsOpen O → z ∈ O →
      ∃ y ∈ (W : Set (ComplexModel n)) ∩ O, v y ≠ ⊥ := by
  intro z hz O hO hzO
  have hpos : volume ((W : Set (ComplexModel n)) ∩ O) ≠ 0 :=
    ((W.isOpen.inter hO).measure_pos volume ⟨z, hz, hzO⟩).ne'
  have : (ae (volume.restrict ((W : Set (ComplexModel n)) ∩ O))).NeBot :=
    ae_restrict_neBot.mpr hpos
  have hfin' : ∀ᵐ y ∂volume.restrict ((W : Set (ComplexModel n)) ∩ O),
      v y ≠ ⊤ ∧ v y ≠ ⊥ :=
    hfin.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_left))
  obtain ⟨y, hy, hyv⟩ := ((ae_restrict_mem (W.isOpen.inter hO).measurableSet).and hfin').exists
  exact ⟨y, hy, hyv.2⟩

private theorem acForm_congr {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (h : S = R) : acForm hS = acForm hR := by
  subst R
  rfl

private theorem acTopMeasure_congr {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (h : S = R) :
    acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Natural modification and original theta-potential data internally produce
actual full SAME-current transport and ENTIRE ACmeasure covariance off one
analytic set. No bounded/analytic/compact/finite/current/calibration input. -/
theorem exists_original_theta_current_transport
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    let θY := ClosedRealOneOneForm.pullback hπ.1 θ
    ∃ huY : IsThetaPshPotential θY.val (fun y => u (π y)),
      ∃ (E : Set X) (s : X → Y), IsClosed E ∧ IsComplexAnalyticSubset (n := m + 1) E ∧
        interior E = ∅ ∧ IsComplexAnalyticSubset (n := m + 1) (π ⁻¹' E) ∧
        interior (π ⁻¹' E) = ∅ ∧
        ∀ (y : Y), π y ∉ E →
          ∀ (e : ComplexChart (m + 1) Y) (d : ComplexChart (m + 1) X),
            y ∈ e.val.source → π y ∈ d.val.source →
            ∃ (A B : Opens (ComplexModel (m + 1)))
              (hAe : A ≤ chartTarget e) (hBd : B ≤ chartTarget d),
              e.val y ∈ A ∧ ((A : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d) ∧
              (∀ z ∈ B, d.val.symm z ∉ E) ∧
              ∃ hpair : IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e),
                let TX := thetaPotentialCurrent θ.val u hu
                let TY := thetaPotentialCurrent θY.val (fun y => u (π y)) huY
                let hTX : IsFullPositive TX := fun e α hα =>
                  thetaPotentialCurrent_full_positive θ.val u hu e α hα
                let hTY : IsFullPositive TY := fun e α hα =>
                  thetaPotentialCurrent_full_positive θY.val (fun y => u (π y)) huY e α hα
                let hSX := isPositive_chartSpanCurrent TX hTX d
                let hSY := isPositive_chartSpanCurrent TY hTY e
                let CB := restrict hBd (chartSpanCurrent TX d)
                let CA := restrict hAe (chartSpanCurrent TY e)
                let hCB : IsPositive CB := isPositive_restrict hSX hBd
                let hCA := isPositive_restrict hSY hAe
                pullback hpair hCB = CA ∧
                (∀ᵐ z ∂(volume : Measure (ComplexModel (m + 1))), z ∈ A →
                  acForm hCA z = (acForm hCB (coordinateMap π e d z)).compContinuousLinearMap
                    ((fderiv ℂ (coordinateMap π e d) z).restrictScalars ℝ)) ∧
                ((acTopMeasure hSX).restrict (B : Set (ComplexModel (m + 1)))).map
                    (onOpen B (coordinateMap s d e)) =
                  (acTopMeasure hSY).restrict (A : Set (ComplexModel (m + 1))) := by
  let θY := ClosedRealOneOneForm.pullback hπ.1 θ
  let huY : IsThetaPshPotential θY.val (fun y => u (π y)) :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu
  obtain ⟨E, s, hEc, hEa, hEi, hprea, hprei, hpairs⟩ :=
    exists_coordinate_pairs_off_analytic_set hπ
  refine ⟨huY, E, s, hEc, hEa, hEi, hprea, hprei, ?_⟩
  intro y hy e d hye hyd
  obtain ⟨A0, B0, hyA0, hA0e, hB0d, hA0dom, hB0off, hpair0⟩ :=
    hpairs y hy e d hye hyd
  let τ := coordinateMap π e d
  let σ := coordinateMap s d e
  have hτy : τ (e.val y) = d.val (π y) := by
    dsimp [τ, coordinateMap]
    rw [e.val.left_inv hye]
  obtain ⟨W0, ρ, hzW0, hpot0, _hp0⟩ :=
    hu.1 d (τ (e.val y)) (hB0d (hpair0.mapsTo hyA0))
  let B : Opens (ComplexModel (m + 1)) := ⟨W0 ∩ B0, hpot0.1.inter B0.isOpen⟩
  have hBW0 : (B : Set (ComplexModel (m + 1))) ⊆ W0 := fun _ hz => hz.1
  have hBB0 : B ≤ B0 := fun _ hz => hz.2
  have hBd : B ≤ chartTarget d := hBB0.trans hB0d
  have hpotB : IsSmoothLocalPotential θ.val d B ρ :=
    ⟨B.isOpen, hBd, hpot0.2.2.1.mono hBW0, fun _ hz => hpot0.2.2.2 hz.1⟩
  let A := preOpen hpair0 B
  have hAA0 : A ≤ A0 := preOpen_le hpair0 B
  have hAe : A ≤ chartTarget e := hAA0.trans hA0e
  have hAdom : (A : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d :=
    fun _ hz => hA0dom (hAA0 hz)
  have hyA : e.val y ∈ A := ⟨hyA0, hzW0, hpair0.mapsTo hyA0⟩
  let hpair : IsBiholomorphicPair A B τ σ := isBiholomorphicPair_preOpen hpair0 hBB0
  have hBoff : ∀ z ∈ B, d.val.symm z ∉ E := fun _ hz => hB0off _ (hBB0 hz)
  have hpotLarge := isSmoothLocalPotential_pullback hπ.1 e hpotB
  have hAlarge : (A : Set (ComplexModel (m + 1))) ⊆ potentialDomain π e d B :=
    fun _ hz => ⟨hAdom hz, hz.2⟩
  have hpotA : IsSmoothLocalPotential θY.val e A (ρ ∘ τ) :=
    ⟨A.isOpen, hAe, hpotLarge.2.2.1.mono hAlarge,
      fun _ hz => hpotLarge.2.2.2 (hAlarge hz)⟩
  let vX := fun z => chartFunction u d z + (ρ z : EReal)
  let vY := fun z => chartFunction (fun y => u (π y)) e z + (ρ (τ z) : EReal)
  have heq : ∀ z ∈ A, vY z = vX (τ z) := by
    intro z hz
    dsimp only [vX, vY, chartFunction, τ, coordinateMap, Function.comp_apply]
    rw [d.val.left_inv (hAdom hz).2]
  obtain ⟨hpX, hfinX, hLX, _hcoeffX, hreaderX, _hRX, _hmeasureX⟩ :=
    exists_corrected_original_chart_reader θ.val hu d ρ hpotB
  obtain ⟨_hpY, _hfinY, hLY, _hcoeffY, hreaderY, _hRY, _hmeasureY⟩ :=
    exists_corrected_original_chart_reader θY.val huY e (ρ ∘ τ) hpotA
  obtain ⟨hLX', hLcomp, _hPA, hPB, hpb⟩ :=
    exists_unbounded_psh_current_pullback hpair hpX (noncollapse_of_ae_finite hfinX)
  let TX := thetaPotentialCurrent θ.val u hu
  let TY := thetaPotentialCurrent θY.val (fun y => u (π y)) huY
  let hTX : IsFullPositive TX := fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
  let hTY : IsFullPositive TY := fun e α hα =>
    thetaPotentialCurrent_full_positive θY.val (fun y => u (π y)) huY e α hα
  let hSX := isPositive_chartSpanCurrent TX hTX d
  let hSY := isPositive_chartSpanCurrent TY hTY e
  let CB := restrict hBd (chartSpanCurrent TX d)
  let CA := restrict hAe (chartSpanCurrent TY e)
  let hCB := isPositive_restrict hSX hBd
  let hCA := isPositive_restrict hSY hAe
  have hcurX : CB = ddc (scalarTopCurrent (regularDistribution volume
      (fun z => (vX z).toReal) hLX')) := hreaderX
  have hcurY : CA = ddc (scalarTopCurrent (regularDistribution volume
      (fun z => (vX (τ z)).toReal) hLcomp)) := by
    have hreg : regularDistribution volume (fun z => (vY z).toReal) hLY =
        regularDistribution volume (fun z => (vX (τ z)).toReal) hLcomp :=
      regularDistribution_congr_ae_on hLY hLcomp
        ((ae_restrict_mem A.isOpen.measurableSet).mono fun z hz => congrArg EReal.toReal (heq z hz))
    exact hreaderY.trans (congrArg (fun D => ddc (scalarTopCurrent D)) hreg)
  have htransport : pullback hpair hCB = CA :=
    (pullback_congr hpair hCB hPB hcurX).trans (hpb.trans hcurY.symm)
  have hform := acForm_congr (isPositive_pullback hpair hCB) hCA htransport
  have hmeasure := acTopMeasure_congr (isPositive_pullback hpair hCB) hCA htransport
  refine ⟨A, B, hAe, hBd, hyA, hAdom, hBoff, hpair, htransport, ?_, ?_⟩
  · rw [← hform]
    exact ae_acForm_pullback hpair hCB
  · rw [← acTopMeasure_restrict hSX hBd, ← acTopMeasure_restrict hSY hAe]
    exact (map_acTopMeasure_eq hpair hCB).trans hmeasure

end SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationLocalTransport
