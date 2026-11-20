import SGPT.Foundations.Analysis.Pending.ThetaCurrentPatchACFinite
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure

set_option autoImplicit false

/-! SAME original genuine theta current: global canonical AC measure <= actual
constant-tuple global NP measure. Complete BP math/proof precedes Lean;
repeat correction, true chart transport, internal finite disjointification.
No supplied measure order, reader, atlas, analytic or finite certificate. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
  _root_.SGPT.Foundations.Analysis.LocalCurrents LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality
  GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  GlobalPositiveCurrentACRestriction PositiveCurrentACTopMeasure
  GlobalPositiveCurrentACTopMeasure NaturalThetaPshGeometricCurrent
  ThetaCurrentPatchACFinite ThetaPshPatchACFinite GlobalNonPluripolar MixedNonPluripolar

private theorem ac_congr {m : ℕ} {U : Opens (ComplexModel (m+1))}
    {S R : LocalProductCurrent (m+1) U m} (hS : IsPositive S) (hR : IsPositive R)
    (h : S = R) : acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

private theorem measure_le_of_finite_restrictions {X : Type*} [MeasurableSpace X]
    {k : ℕ} (U : Fin k → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ⋃ i, U i = univ) {μ ν : Measure X}
    (hlocal : ∀ i, μ.restrict (U i) ≤ ν.restrict (U i)) : μ ≤ ν := by
  have hμ := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => μ) hU hcover μ (fun _ => rfl)
  have hν := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => ν) hU hcover ν (fun _ => rfl)
  have hdi (i : Fin k) : μ.restrict (disjointed U i) ≤ ν.restrict (disjointed U i) := by
    have h := Measure.restrict_mono_measure (hlocal i) (disjointed U i)
    simpa only [Measure.restrict_restrict_of_subset (disjointed_subset U i)] using h
  apply Measure.le_iff.mpr
  intro A hA
  rw [← hμ, ← hν]
  change (Measure.sum (fun i => μ.restrict (disjointed U i))) A ≤
    (Measure.sum (fun i => ν.restrict (disjointed U i))) A
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  exact ENNReal.tsum_le_tsum fun i => Measure.le_iff'.mp (hdi i) A

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

private theorem chart_measure_apply
    (T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))) (hT : IsFullPositive T)
    (e : ComplexChart (m+1) M) (s : Set M) :
    chartACMeasure T hT e s =
      acTopMeasure (isPositive_chartSpanCurrent T hT e) (e.val.target ∩ e.val.symm ⁻¹' s) := by
  let j : e.val.target → M := fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m+1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  change ((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
    (Subtype.val : e.val.target → ComplexModel (m+1))).map j s = _
  rw [hj.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hz,hzs⟩
    exact ⟨⟨z,hz⟩,hzs,rfl⟩


variable [CompactSpace M]

private theorem restrict_patch_le
    (omega : KahlerBackground (m+1) M) (σ : ClosedRealOneOneForm (m+1) M)
    {u : M → EReal} (hu : IsThetaPshPotential σ.val u)
    (P : Patch (fun _ : Fin (m+1) => σ) (fun _ => u)) :
    let T := thetaPotentialCurrent σ.val u hu
    let hpos : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive σ.val u hu e α hα
    (globalACtopMeasure T hpos).restrict P.source ≤
      (globalMixedMeasure (fun _ => σ) (fun _ => u) (fun _ => hu.1)).restrict P.source := by
  classical
  dsimp only
  let T := thetaPotentialCurrent σ.val u hu
  let hpos : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive σ.val u hu e α hα
  let μ := globalACtopMeasure T hpos
  let ν := globalMixedMeasure (fun _ : Fin (m+1) => σ) (fun _ => u) (fun _ => hu.1)
  let Q : Patch (fun _ : Fin (m+1) => σ) (fun _ => u) := {
    chart := P.chart
    domain := P.domain
    domain_le_target := P.domain_le_target
    potential := fun _ => P.potential 0
    localPotential := fun _ => P.localPotential 0
    plurisubharmonic := fun _ => P.plurisubharmonic 0 }
  let hS := isPositive_chartSpanCurrent T hpos Q.chart
  obtain ⟨hL,hcurrent,_hfinite⟩ := exists_original_chart_ac_finite omega σ hu Q
  obtain ⟨hL',hTv,hle,_hfinite'⟩ := exists_patch_ac_domination_and_finite omega σ hu Q
  have hAC : (acTopMeasure hS).restrict Q.domain = acTopMeasure hTv := by
    exact (acTopMeasure_restrict hS Q.domain_le_target).symm.trans
      (ac_congr (isPositive_restrict hS Q.domain_le_target) hTv hcurrent)
  have hdiag : mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic =
      MongeAmpere.truncationLimitMeasure Q.domain (Q.corrected 0) (Q.plurisubharmonic 0) :=
    mixedTruncationLimitMeasure_diagonal (Nat.succ_pos m) (Q.plurisubharmonic 0)
  have hμ (A : Set M) (hA : MeasurableSet A) :
      μ.restrict Q.source A = acTopMeasure hS ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A) := by
    have hAs := hA.inter Q.source.isOpen.measurableSet
    calc
      μ.restrict Q.source A = μ (A ∩ Q.source) := Measure.restrict_apply hA
      _ = μ.restrict Q.chart.val.source (A ∩ Q.source) := by
        rw [Measure.restrict_apply hAs]
        congr 1
        exact (inter_eq_left.mpr (inter_subset_right.trans Q.source_subset)).symm
      _ = chartACMeasure T hpos Q.chart (A ∩ Q.source) :=
        congrArg (fun κ => κ (A ∩ Q.source)) (globalACtopMeasure_restrict_chart T hpos Q.chart)
      _ = acTopMeasure hS (Q.chart.val.target ∩ Q.chart.val.symm ⁻¹' (A ∩ Q.source)) :=
        chart_measure_apply T hpos Q.chart (A ∩ Q.source)
      _ = _ := by
        congr 1
        ext z
        constructor
        · rintro ⟨hz,hzA,hzs,hzd⟩
          change Q.chart.val (Q.chart.val.symm z) ∈ Q.domain at hzd
          rw [Q.chart.val.right_inv hz] at hzd
          exact ⟨hzd,hzA⟩
        · rintro ⟨hzd,hzA⟩
          exact ⟨Q.domain_le_target hzd,hzA,Q.map_target hzd⟩
  apply Measure.le_iff.mpr
  intro A hA
  change μ.restrict Q.source A ≤ ν.restrict Q.source A
  rw [hμ A hA]
  have hcoord : (Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A ⊆ (Q.domain : Set (ComplexModel (m+1))) :=
    inter_subset_left
  have hACEval : acTopMeasure hS ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A) =
      acTopMeasure hTv ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A) := by
    calc
      _ = (acTopMeasure hS).restrict Q.domain ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A) := by
        rw [Measure.restrict_apply' Q.domain.isOpen.measurableSet,inter_eq_left.mpr hcoord]
      _ = _ := congrArg (fun κ => κ ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A)) hAC
  rw [hACEval]
  calc
    _ ≤ MongeAmpere.truncationLimitMeasure Q.domain (Q.corrected 0) (Q.plurisubharmonic 0)
        ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' A) := Measure.le_iff'.mp hle _
    _ = patchMeasure Q A := by rw [patchMeasure,Q.pushMeasure_apply,hdiag]
    _ = ν.restrict Q.source A :=
      congrArg (fun κ => κ A) (globalMixedMeasure_restrict_patch (fun _ => hu.1) Q).symm

/-- ALL measurable sets of the SAME original theta current satisfy AC<=NP;
actual cover, correction and full-current identities are internally supplied. -/
theorem globalACtopMeasure_le_globalMixedMeasure
    (omega : KahlerBackground (m+1) M) (σ : ClosedRealOneOneForm (m+1) M)
    {u : M → EReal} (hu : IsThetaPshPotential σ.val u) :
    let T := thetaPotentialCurrent σ.val u hu
    let hpos : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive σ.val u hu e α hα
    globalACtopMeasure T hpos ≤
      globalMixedMeasure (fun _ : Fin (m+1) => σ) (fun _ => u) (fun _ => hu.1) := by
  classical
  dsimp only
  let C := Classical.choice (nonempty_finiteCover (fun _ : Fin (m+1) => hu.1))
  have hcover : (⋃ i, ((C.patch i).source : Set M)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i,hx⟩ := C.covers x
    exact mem_iUnion.mpr ⟨i,hx⟩
  exact measure_le_of_finite_restrictions (fun i => (C.patch i).source)
    (fun i => (C.patch i).source.isOpen.measurableSet) hcover
    (fun i => restrict_patch_le omega σ hu (C.patch i))

end SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
