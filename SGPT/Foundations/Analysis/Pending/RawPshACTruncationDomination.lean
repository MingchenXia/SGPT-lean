import SGPT.Foundations.Analysis.Pending.RawPshWeightedACBTDomination
import SGPT.Foundations.Analysis.Pending.NonPluripolarLimit

set_option autoImplicit false

/-! Actual AC top measure of the SAME raw PSH current is internally below
EVERY original strict truncation step and the actual increasing NP measure.
Natural raw PSH/AEfinite/localL1 reader only. No small unbounded locus,
analyticity, input massbound/comparison/limit. Entire BP proof precedes Lean.
The NP measure may have infinite mass; no global class bound is claimed. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.RawPshACTruncationDomination
open MongeAmpere FirstPass FirstPass.MongeAmpere LocalProductCurrents LocalCurrentDeterminant
  ScalarLeviPositiveCurrent RawPshWeightedACBTDomination RawPshConvexCutoff PositiveCurrentACTopMeasure
  HolomorphicPullback LocalBedfordTaylorProducts

variable {m : ℕ} {U : Opens (ComplexModel (m+1))}

/-- Internal positivity, sharp cutoff and genuine BT max-locality yield all
strict-step inequalities and actual NP domination of the SAME original AC. -/
theorem acTopMeasure_le_truncationLimitMeasure
    {u : ComplexModel (m+1) → EReal} (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥)
    (hL : LocallyIntegrableOn (fun z => (u z).toReal) U volume) :
    let D := regularDistribution volume (fun z => (u z).toReal) hL
    ∃ hT : IsPositive (ddc (scalarTopCurrent D)),
      (∀ k : ℕ, (acTopMeasure hT).restrict (strictTruncationLocus U u k) ≤ truncationMeasure U u hu k) ∧
      acTopMeasure hT ≤ truncationLimitMeasure U u hu := by
  classical
  obtain ⟨hT,hw⟩ := weighted_ac_measure_le_canonicalBedfordTaylorMeasure hu hfin hL
  have hstep (k : ℕ) : (acTopMeasure hT).restrict (strictTruncationLocus U u k) ≤
      truncationMeasure U u hu k := by
    let b : ℝ := -(k : ℝ)-1
    let q : ComplexModel (m+1) → ℝ := fun z =>
      b+SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal-b)
    let hq := isLocallyBoundedPshOn_convexCutoff U hu b
    let G := strictTruncationLocus U u k
    let W := (volume.withDensity (fun z => ENNReal.ofReal (SmoothMax.trans ((u z).toReal-b)^(m+1) *
      actualTopPowerDensity (acForm hT z)))).restrict U
    have hb : b+1 = -(k : ℝ) := by dsimp only [b]; ring
    have hG : MeasurableSet G := measurableSet_strictTruncationLocus hu k
    have hGU : G ⊆ U := fun _ hz => hz.1
    have hsame : (acTopMeasure hT).restrict G = W.restrict G := by
      dsimp only [acTopMeasure,W]
      rw [Measure.restrict_restrict_of_subset hGU,Measure.restrict_restrict_of_subset hGU,
        restrict_withDensity hG,restrict_withDensity hG]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hG] with z hz
      have htop := (hu z hz.1).ne_top
      have hbot : u z ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans hz.2)
      have hc := EReal.coe_toReal htop hbot
      have hl : -(k : ℝ) < (u z).toReal := by
        have hh := hz.2
        rw [← hc] at hh
        exact_mod_cast hh
      have ht : SmoothMax.trans ((u z).toReal-b) = 1 :=
        SmoothMax.trans_eq_one (by dsimp only [b]; linarith)
      rw [ht,one_pow,one_mul]
    have hmax : EqOn (truncationReal u k) (fun z => max (q z) (-(k : ℝ))) U := by
      intro z hz
      have he := (convexCutoff_sharp_properties (hu z hz).ne_top b).2.2.1
      change max (q z : EReal) ((b+1 : ℝ) : EReal) = max (u z) ((b+1 : ℝ) : EReal) at he
      rw [hb] at he
      have hr := congrArg EReal.toReal he
      rw [PshRadialRegularization.toReal_max_coe (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe] at hr
      exact hr.symm
    have hset : {z | z ∈ U ∧ -(k : ℝ) < q z} = G := by
      ext z
      by_cases hz : z ∈ U
      · have he := (convexCutoff_sharp_properties (hu z hz).ne_top b).2.2.2
        change (((b+1 : ℝ) : EReal) < (q z : EReal) ↔ ((b+1 : ℝ) : EReal) < u z) at he
        rw [hb] at he
        simpa only [G,strictTruncationLocus,mem_ofPred_eq,hz,true_and,EReal.coe_lt_coe_iff] using he
      · simp only [G,strictTruncationLocus,mem_ofPred_eq,hz,false_and]
    have hBT := localBedfordTaylorMeasure_max_const_locality
      (canonicalBedfordTaylorMeasure_spec U q hq)
      (canonicalBedfordTaylorMeasure_spec U (truncationReal u k) (truncationReal_isLocallyBoundedPshOn hu k))
      (-(k : ℝ)) hmax
    rw [hset] at hBT
    change (acTopMeasure hT).restrict G ≤
      (canonicalBedfordTaylorMeasure U (truncationReal u k) (truncationReal_isLocallyBoundedPshOn hu k)).restrict G
    rw [hsame,hBT]
    exact Measure.restrict_mono (Subset.rfl : G ⊆ G) (hw b)
  refine ⟨hT,hstep,?_⟩
  have hae : ∀ᵐ z ∂acTopMeasure hT, z ∈ ⋃ k, strictTruncationLocus U u k := by
    rw [acTopMeasure,restrict_withDensity U.isOpen.measurableSet,
      ae_withDensity_iff (measurable_acTopDensity hT).ennreal_ofReal]
    filter_upwards [hfin,ae_restrict_mem U.isOpen.measurableSet] with z hz hzU
    intro _
    rw [iUnion_strictTruncationLocus]
    exact ⟨hzU,hz.2⟩
  apply Measure.le_iff.mpr
  intro B hB
  have hmono : Monotone (fun k => B ∩ strictTruncationLocus U u k) :=
    fun k l hkl => inter_subset_inter_right B (strictTruncationLocus_mono U u hkl)
  rw [← Measure.restrict_eq_self_of_ae_mem hae,Measure.restrict_apply hB,inter_iUnion,hmono.measure_iUnion]
  apply iSup_le
  intro k
  have hk := Measure.le_iff'.mp (hstep k) B
  rw [Measure.restrict_apply hB] at hk
  exact hk.trans (Measure.le_iff'.mp (truncationMeasure_le_limit hu k) B)

end SGPT.Foundations.Analysis.Pending.RawPshACTruncationDomination
