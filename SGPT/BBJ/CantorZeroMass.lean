import SGPT.BBJ.CantorGlobalTrace
import SGPT.BBJ.CantorOffPoles
import SGPT.BBJ.BoundedBedfordTaylorCalibration
import SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader

set_option autoImplicit false

/-! # The actual Cantor non-pluripolar measure in the FS background

Full coefficient vanishing away from the poles feeds the actual bounded
Bedford–Taylor reader and the existing native patch gluing construction.
-/

noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalPotentialPatches GlobalNonPluripolar DiagonalMass
open BoundedGlobalProduct PatchLocalBoundedMeasure PatchLocalVanishingMass
open CanonicalCurrentFrame GlobalCurrents GlobalCurrentPotentials
open ThetaPotentialPrescribedChartReader LelongPoincareDivisor
open LocalBedfordTaylorLocality FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open scoped Topology ENNReal Classical Distributions ContDiff ComplexConjugate
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- Every actual coefficient of the original local current vanishes on
compact tests supported off the actual Cantor poles. -/
theorem cantorAverage_full_current_off_poles_apply (j : Bool)
    {U : Opens (ComplexModel 1)}
    (hUK : ∀ z ∈ U, (projectiveModelChart j).symm z ∉ projectiveCantorSet)
    (v w : ComplexModel 1) (φ : 𝓓(U, ℝ)) :
    (projectiveFSCurvatureCurrent+cantorAverageMetricCurrent j) ![v,w]
      (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens (ComplexModel 1)), ℝ)) = 0 := by
  have hzero (z : ComplexModel 1)
      (hz : (projectiveModelChart j).symm z ∈ projectiveCantorSet) : φ z = 0 := by
    by_contra hφ
    exact hUK z (φ.tsupport_subset (subset_tsupport φ hφ)) hz
  cases j
  · rw [cantorAverage_full_current_finite_apply]
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun b => ?_
    dsimp only
    have hroot : φ (projectiveModelEquiv (cantorCode b : ℂ)) = 0 := by
      apply hzero
      rw [movingSection_finite_root]
      exact ⟨b,rfl⟩
    rw [congrFun (testFunction_inclusion_coe (show U ≤ ⊤ from le_top) φ) _, hroot, zero_mul]
    rfl
  · rw [cantorAverage_full_current_infinity_apply]
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun b => ?_
    dsimp only
    by_cases hb : cantorCode b = 0
    · exact if_pos hb
    · rw [if_neg hb]
      have hroot : φ (projectiveModelEquiv ((cantorCode b : ℂ)⁻¹)) = 0 := by
        apply hzero
        rw [movingSection_infinity_root _ hb]
        exact ⟨b,rfl⟩
      rw [congrFun (testFunction_inclusion_coe (show U ≤ ⊤ from le_top) φ) _, hroot, zero_mul]
      rfl

/-- The SAME actual native current has zero full coefficient two-form on
every genuine off-pole coordinate domain, in every native chart. -/
theorem cantorNativeCurrent_coefficients_restrict_eq_zero
    (e : ComplexChart 1 P1) {U : Opens (ComplexModel 1)}
    (hU : U ≤ chartTarget e)
    (hUK : ∀ z ∈ U, e.val.symm z ∉ projectiveCantorSet) :
    restrictForm (cantorNativeCurrent.coefficients (canonicalBasis 1) e) hU = 0 := by
  obtain ⟨j,rfl⟩ := projectiveNativeChart_exhaustive e
  have htarget : chartTarget (projectiveNativeChart j) = ⊤ := by
    apply Opens.ext
    change (projectiveModelChart j).target = univ
    simp [projectiveModelChart,projectiveQuotientScalarChart_target]
  ext v φ
  have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
  change cantorNativeCurrent.coefficients (canonicalBasis 1) (projectiveNativeChart j) v
    (TestFunction.monoCLM ℝ φ) = 0
  have hcompare :
      cantorNativeCurrent.coefficients (canonicalBasis 1) (projectiveNativeChart j) v
          (TestFunction.monoCLM ℝ φ) =
        cantorNativePreferredCoefficients j v
          (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens (ComplexModel 1)), ℝ)) := by
    unfold cantorNativePreferredCoefficients
    rw [restrictForm_apply]
    congr 1
    apply TestFunction.ext
    intro z
    rw [congrFun (testFunction_inclusion_coe hU φ) z,
      congrFun (testFunction_inclusion_coe
        (show (⊤ : Opens (ComplexModel 1)) ≤ chartTarget (projectiveNativeChart j) by rw [htarget])
        (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens (ComplexModel 1)), ℝ))) z,
      congrFun (testFunction_inclusion_coe (show U ≤ ⊤ from le_top) φ) z]
  rw [hcompare, cantorNativePreferredCoefficients_eq, hv]
  exact cantorAverage_full_current_off_poles_apply j hUK _ _ φ

/-- The actual canonical bounded BT measure is zero on every relatively
compact subdomain of a genuine bounded off-pole patch. -/
theorem canonicalBoundedBT_cantor_off_poles_eq_zero
    (P : Patch (fun _ : Fin 1 => projectiveNativeFSBackground.form)
      (fun _ => cantorLogPotential))
    (hb : IsBoundedPotentialOn cantorLogPotential P.source)
    (hPK : (P.source : Set P1) ⊆ projectiveCantorSetᶜ)
    {V : Opens (ComplexModel 1)} (hV : RelativelyCompactIn V P.domain) :
    let hu := correctedReal_isLocallyBoundedPshOn_of_boundedOn (P := P) (i := 0) hb
    let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
    MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure V
      (fun _ : Fin 1 => correctedReal P 0) (fun _ => huV) = 0 := by
  dsimp only
  let hu := correctedReal_isLocallyBoundedPshOn_of_boundedOn (P := P) (i := 0) hb
  let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
  have hspec := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec V
    (fun _ : Fin 1 => correctedReal P 0) (fun _ => huV)
  apply eq_of_forall_testFunction_integral_eq hspec.2.1 (by simp)
    hspec.2.2.1 (by intro K _ _; simp)
  intro φ
  rw [integral_canonicalBoundedBT_one_dim hu hV φ, integral_zero_measure]
  have hpot := (P.localPotential 0).mono V.isOpen (subset_closure.trans hV.2)
  obtain ⟨_,_,hL,hcoeff,_⟩ := @exists_corrected_original_chart_reader
    0 P1 inferInstance projectiveNativeChartedSpace projectiveNativeComplexManifold
    projectiveNativeFSBackground.form.val cantorLogPotential isThetaPshPotential_cantorLogPotential
      P.chart V (P.potential 0) hpot
  change restrictForm (cantorNativeCurrent.coefficients (canonicalBasis 1) P.chart)
    hpot.2.1 = _ at hcoeff
  rw [cantorNativeCurrent_coefficients_restrict_eq_zero P.chart hpot.2.1
    (fun z hz => hPK (P.map_target ((subset_closure.trans hV.2) hz)))] at hcoeff
  exact congrArg (fun A : LocalCurrents.DistributionForm V 2 => A _ φ) hcoeff.symm

/-- The LITERAL actual native non-pluripolar measure of the original
Cantor potential vanishes in the FS background. -/
theorem diagonalPotentialMeasure_cantorLogPotential_eq_zero :
    diagonalPotentialMeasure projectiveNativeFSBackground.form cantorLogPotential
      isThetaPshPotential_cantorLogPotential = 0 := by
  let μ := diagonalPotentialMeasure projectiveNativeFSBackground.form cantorLogPotential
    isThetaPshPotential_cantorLogPotential
  have hcompl : μ projectiveCantorSetᶜ = 0 := by
    apply measure_eq_zero_of_locally_eq_zero
    intro p hp
    obtain ⟨O, hO, hpO, hOK, hbO⟩ := exists_bounded_cantorLogPotential_neighborhood p hp
    obtain ⟨P, hpP⟩ := exists_patch_containing
      (θ := fun _ : Fin 1 => projectiveNativeFSBackground.form)
      (u := fun _ => cantorLogPotential) (fun _ => isThetaPshPotential_cantorLogPotential.1) p
    let W : Opens (ComplexModel 1) :=
      ⟨(P.domain : Set (ComplexModel 1)) ∩ (P.chart.val.target ∩ P.chart.val.symm ⁻¹' O),
        P.domain.isOpen.inter (P.chart.val.isOpen_inter_preimage_symm hO)⟩
    let Q := P.restrict W (fun _ hz => hz.1)
    have hpQ : p ∈ Q.source := by
      refine ⟨hpP.1, hpP.2, P.domain_le_target hpP.2, ?_⟩
      change P.chart.val.symm (P.chart.val p) ∈ O
      rwa [P.chart.val.left_inv hpP.1]
    have hQO : (Q.source : Set P1) ⊆ O := by
      intro q hq
      have hqO : P.chart.val.symm (P.chart.val q) ∈ O := hq.2.2.2
      rwa [P.chart.val.left_inv hq.1] at hqO
    have hbQ : IsBoundedPotentialOn cantorLogPotential Q.source := hbO.mono hQO
    have hQK : (Q.source : Set P1) ⊆ projectiveCantorSetᶜ := hQO.trans hOK
    let z := Q.chart.val p
    have hz : z ∈ Q.domain := Q.map_source hpQ
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Q.domain.isOpen.mem_nhds hz)
    let V : Opens (ComplexModel 1) := ⟨ball z (r/2), isOpen_ball⟩
    have hclosure : closure (V : Set (ComplexModel 1)) ⊆ closedBall z (r/2) :=
      closure_minimal ball_subset_closedBall isClosed_closedBall
    have hV : RelativelyCompactIn V Q.domain :=
      ⟨(isCompact_closedBall z (r/2)).of_isClosed_subset isClosed_closure hclosure,
        hclosure.trans ((closedBall_subset_ball (by linarith)).trans hball)⟩
    have hVQ : V ≤ Q.domain := subset_closure.trans hV.2
    let R := Q.restrict V hVQ
    have hpR : p ∈ R.source := ⟨hpQ.1, mem_ball_self (by linarith)⟩
    have hRQ : (R.source : Set P1) ⊆ Q.source := fun q hq => ⟨hq.1,hVQ hq.2⟩
    have hbR : IsBoundedPotentialOn cantorLogPotential R.source := hbQ.mono hRQ
    have htuple : correctedReal R = fun _ : Fin 1 => correctedReal Q 0 := by
      funext i w
      fin_cases i
      rfl
    have hBT : MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure R.domain (correctedReal R)
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn R (fun _ => hbR)) = 0 := by
      change MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure V (correctedReal R) _ = 0
      have hcongr (a b : Fin 1 → ComplexModel 1 → ℝ)
          (ha : ∀ i, IsLocallyBoundedPshOn V (a i))
          (hb : ∀ i, IsLocallyBoundedPshOn V (b i)) (hab : a = b) :
          MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure V a ha =
            MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure V b hb := by
        subst b
        rfl
      exact (hcongr (correctedReal R) _
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn R (fun _ => hbR))
        (fun _ => isLocallyBoundedPshOn_mono
          (correctedReal_isLocallyBoundedPshOn_of_boundedOn (P := Q) (i := 0) hbQ) hVQ)
        htuple).trans (canonicalBoundedBT_cantor_off_poles_eq_zero Q hbQ hQK hV)
    have hres := globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn
      (fun _ => isThetaPshPotential_cantorLogPotential.1) R (fun _ => hbR)
    change μ.restrict (R.source : Set P1) = _ at hres
    rw [hBT] at hres
    have hnull : μ (R.source : Set P1) = 0 := by
      have hkey : μ.restrict (R.source : Set P1) (R.source : Set P1) = 0 := by
        rw [hres,R.pushMeasure_apply]
        simp
      rwa [Measure.restrict_apply R.source.isOpen.measurableSet,inter_self] at hkey
    exact ⟨R.source,R.source.isOpen,hpR,hnull⟩
  have hpoles : μ {p : P1 | cantorLogPotential p = ⊥} = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin 1 => isThetaPshPotential_cantorLogPotential.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar isThetaPshPotential_cantorLogPotential.quasiPshPotential)
  have hpoleSet : {p : P1 | cantorLogPotential p = ⊥} = projectiveCantorSet := by
    ext p
    exact cantorLogPotential_eq_bot_iff p
  rw [hpoleSet] at hpoles
  have huniv : μ univ = 0 := by
    apply le_antisymm _ bot_le
    calc μ univ = μ (projectiveCantorSet ∪ projectiveCantorSetᶜ) := by rw [union_compl_self]
      _ ≤ μ projectiveCantorSet+μ projectiveCantorSetᶜ := measure_union_le _ _
      _ = 0 := by rw [hpoles,hcompl,add_zero]
  apply Measure.ext
  intro S _
  exact measure_mono_null (subset_univ S) huniv

/-- The actual native non-pluripolar whole-space mass is zero. -/
theorem diagonalPotentialMass_cantorLogPotential_eq_zero :
    diagonalPotentialMass projectiveNativeFSBackground.form cantorLogPotential
      isThetaPshPotential_cantorLogPotential = 0 := by
  rw [diagonalPotentialMass,diagonalPotentialMeasure_cantorLogPotential_eq_zero]
  rfl

end SGPT.BBJ
