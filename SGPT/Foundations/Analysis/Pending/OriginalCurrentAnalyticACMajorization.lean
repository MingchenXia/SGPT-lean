import SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarRNIntegral
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
import SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticWeakRegularization
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-! Complete BP statements and ENTIRE mathematical proofs precede Lean.
SAME analytic theta current AC=NP on all measurable sets, and ANY original
positive closed current internally has an analytic positive AC mass majorant.
No AC coefficient convergence, smooth cross-pole remainder or CY is asserted. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalPotentialPatches FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.GlobalAnalyticSingularities CanonicalCurrentFrame CurrentBottChernClass
  GlobalCurrentPotentials GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  PositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  ThetaPotentialCurrentBottChernClass GlobalNonPluripolar MixedMass
  GlobalMixedMassMonotone AmbientMassBackgroundMonotone
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

omit [CompactSpace M] in
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
  rw [hj.map_apply,hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hz,hzs⟩
    exact ⟨⟨z,hz⟩,hzs,rfl⟩

/-- The SAME genuinely analytic theta current has its canonical AC top
measure equal to its original diagonal NP measure, on ALL measurable sets. -/
theorem globalACtopMeasure_theta_analytic_eq
    (θ : ClosedRealOneOneForm (m+1) M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m+1) u) :
    globalACtopMeasure (thetaPotentialCurrent θ.val u hu)
      (fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα) =
      globalMixedMeasure (fun _ : Fin (m+1) => θ) (fun _ => u) (fun _ => hu.1) := by
  classical
  let T := thetaPotentialCurrent θ.val u hu
  let hT : IsFullPositive T :=
    fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
  let μ := globalACtopMeasure T hT
  obtain ⟨C,hC⟩ :=
    ActualAnalyticNonPluripolarRNIntegral.exists_finite_cover_original_measure_eq_acForm_top_lintegral
      hu han
  let E : Fin C.count → Set M := disjointed (fun j => (C.patch j).source)
  have hE : ∀ j, MeasurableSet (E j) :=
    FiniteMeasureGluing.measurableSet_disjointed
      (fun j : Fin C.count => ((C.patch j).source : Set M))
      (fun j => (C.patch j).source.isOpen.measurableSet)
  have hcover : ⋃ j, E j = univ := by
    rw [iUnion_disjointed]
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨j,hj⟩ := C.covers x
    exact mem_iUnion.mpr ⟨j,hj⟩
  have hpiece (A : Set M) (hA : MeasurableSet A) (j : Fin C.count) :
      μ (A ∩ E j) =
        ∫⁻ y in (C.patch j).domain ∩ (C.patch j).chart.val.symm ⁻¹' (A ∩ E j),
          ENNReal.ofReal (actualTopPowerDensity
            (LocalCurrentDeterminant.acForm
              (ActualAnalyticCurrentLocalDensity.isPositive_chartSpanCurrent
                θ.val u hu (C.patch j).chart) y)) := by
    let Q := C.patch j
    have hsub : E j ⊆ Q.source := disjointed_subset _ j
    have hsubchart : A ∩ E j ⊆ Q.chart.val.source :=
      inter_subset_right.trans (hsub.trans Q.source_subset)
    have h := congrArg (fun ν : Measure M => ν (A ∩ E j))
      (globalACtopMeasure_restrict_chart T hT Q.chart)
    rw [Measure.restrict_apply (hA.inter (hE j)),
      inter_eq_left.mpr hsubchart] at h
    change μ (A ∩ E j) = _ at h
    rw [h,chart_measure_apply]
    have hsets : Q.chart.val.target ∩ Q.chart.val.symm ⁻¹' (A ∩ E j) =
        (Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' (A ∩ E j) := by
      ext z
      constructor
      · rintro ⟨hz,hzA,hzE⟩
        have hdom := Q.map_source (hsub hzE)
        rw [Q.chart.val.right_inv hz] at hdom
        exact ⟨hdom,hzA,hzE⟩
      · rintro ⟨hz,hzA,hzE⟩
        exact ⟨Q.domain_le_target hz,hzA,hzE⟩
    rw [hsets,acTopMeasure]
    have hS : MeasurableSet
        ((Q.domain : Set (ComplexModel (m+1))) ∩ Q.chart.val.symm ⁻¹' (A ∩ E j)) :=
      SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
        Q.domain.isOpen.measurableSet
        (Q.chart.val.continuousOn_symm.mono Q.domain_le_target) (hA.inter (hE j))
    have ht : ((Q.domain : Set (ComplexModel (m+1))) ∩
        Q.chart.val.symm ⁻¹' (A ∩ E j)) ⊆ chartTarget Q.chart :=
      inter_subset_left.trans Q.domain_le_target
    rw [Measure.restrict_apply hS,inter_eq_left.mpr ht,withDensity_apply _ hS]
  ext A hA
  change μ A = _
  rw [hC A hA]
  calc
    μ A = μ (⋃ j, A ∩ E j) := by rw [← inter_iUnion,hcover,inter_univ]
    _ = ∑ j : Fin C.count, μ (A ∩ E j) := by
      rw [measure_iUnion (fun i j hij => (disjoint_disjointed
        (fun j : Fin C.count => ((C.patch j).source : Set M)) hij).mono
        inter_subset_right inter_subset_right) (fun j => hA.inter (hE j)),tsum_fintype]
    _ = _ := Finset.sum_congr rfl fun j _ => hpiece A hA j

private theorem global_ac_congr
    {T S : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) (hS : IsFullPositive S) (heq : T = S) :
    globalACtopMeasure T hT = globalACtopMeasure S hS := by
  subst S
  rfl

/-- ANY original positive closed current internally has an analytic positive
current in its epsilon-enlarged class, with no loss of its original AC mass. -/
theorem exists_analytic_positive_current_ac_mass_majorant
    (ω : KahlerBackground (m+1) M)
    (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) {ε : ℝ} (hε : 0 < ε) :
    ∃ (θ : ClosedRealOneOneForm (m+1) M) (v : M → EReal)
      (hv : IsThetaPshPotential (θ + ε • ω.form).val v),
      RealBottChern.ofRepresentative θ =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T ∧
      HasAnalyticSingularities (n := m+1) v ∧
      HasManifoldAnalyticSingularitiesSmoothOffPole (n := m+1) v ∧
      let S := thetaClosedCurrent (θ + ε • ω.form) v hv
      let hS : IsFullPositive S.val := fun e α hα =>
        thetaPotentialCurrent_full_positive (θ + ε • ω.form).val v hv e α hα
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) S =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T +
          ε • RealBottChern.ofRepresentative ω.form ∧
      globalACtopMeasure T.val hT univ ≤ globalACtopMeasure S.val hS univ := by
  classical
  obtain ⟨θ,u,hu,heq,_⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T.val T.property.1 T.property.2 hT
  have hTc : T = thetaClosedCurrent θ u hu := Subtype.ext heq
  have hclass : RealBottChern.ofRepresentative θ =
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T := by
    rw [hTc,bottChernClass_thetaClosedCurrent]
  obtain ⟨v,δ,han,hsmooth,_hanti,hinf,_hδnon,hδlim,hv⟩ :=
    Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation ω θ u hu
  have hevent : ∀ᶠ k in atTop, δ k < ε :=
    hδlim.eventually (eventually_lt_nhds hε)
  obtain ⟨k,hk⟩ := hevent.exists
  have hve : IsThetaPshPotential (θ + ε • ω.form).val (v k) := by
    have hs := LocalPotentials.isThetaPshPotential_add_of_semipositive (hv k)
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr hk.le))
    have he : (θ + δ k • ω.form) + (ε-δ k) • ω.form = θ + ε • ω.form := by module
    simpa only [he] using hs
  have hue : IsThetaPshPotential (θ + ε • ω.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul ω.isSemipositive hε.le)
  refine ⟨θ,v k,hve,hclass,han k,hsmooth k,?_,?_⟩
  · rw [bottChernClass_thetaClosedCurrent,RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul,hclass]
  · let hpos : IsFullPositive (thetaPotentialCurrent θ.val u hu) :=
      fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
    rw [global_ac_congr hT hpos heq]
    have hAC := ThetaCurrentGlobalACDomination.globalACtopMeasure_le_globalMixedMeasure ω θ hu
    have hbg := globalMixedMeasure_diagonal_le_add_smul ω.isSemipositive hε hu hue.1
    have horder : MoreSingularOn u (v k) univ := MoreSingularOn.of_le fun x _ => by
      rw [← hinf x]
      exact iInf_le _ k
    have hmass := globalMixedMass_mono_of_isThetaPshPotential ω
      (fun _ : Fin (m+1) => hue) (fun _ => hve) (fun _ => horder)
    have heqAC := congrArg (fun μ : Measure M => μ univ)
      (globalACtopMeasure_theta_analytic_eq (θ + ε • ω.form) hve (hsmooth k))
    exact (Measure.le_iff'.mp hAC univ).trans
      ((Measure.le_iff'.mp hbg univ).trans (hmass.trans_eq heqAC.symm))

end SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
