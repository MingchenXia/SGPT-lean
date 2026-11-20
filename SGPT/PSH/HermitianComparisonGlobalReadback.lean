import SGPT.PSH.HermitianComparisonGlobalStrict
import SGPT.PSH.HermitianTopCurrentBorelTrace
import SGPT.PSH.HermitianProductsBoundedBorelTransgression
import SGPT.PSH.HermitianProductsCanonicalMassContinuity

/-! Literal strict-set trace integrals reconstruct the actual canonical
global mixed measure through the original compact chart partition. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents HermitianProducts ChartPartitionRelativeSupports
open scoped Topology Distributions

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M]

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] in
/-- A genuine open manifold set has its actual measurable coordinate
preimage inside the original coordinate domain. -/
theorem CoordinatePatch.isOpen_coordinate_preimage (P : CoordinatePatch n M)
    {E : Set M} (hE : IsOpen E) :
    IsOpen ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' E) := by
  have heq : (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' E =
      (P.domain : Set (ComplexModel n)) ∩
        (P.chart.val.target ∩ P.chart.val.symm ⁻¹' E) := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1, P.domain_le_target hz.1, hz.2⟩
    · exact fun hz => ⟨hz.1, hz.2.2⟩
  rw [heq]
  exact P.domain.isOpen.inter (P.chart.val.isOpen_inter_preimage_symm hE)

omit [IsComplexManifold n M] in
/-- The original compact coordinate test reads the actual weighted
transported trace on an open set, with no coordinate-measure premise. -/
theorem CoordinatePatch.weightedTraceMeasure_open_toReal
    (P : CoordinatePatch n M) (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T)
    (χ : M → ℝ) (θ : 𝓓(P.domain, ℝ))
    (hθ : ∀ z, θ z = chartWeight P.chart χ z) (hθ0 : ∀ z, 0 ≤ θ z)
    {E : Set M} (hE : IsOpen E) :
    (P.weightedTraceMeasure T hT χ E).toReal =
      ∫ z in (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' E,
        θ z ∂hT.traceMeasure := by
  let V : Set (ComplexModel n) := (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' E
  have hV : MeasurableSet V := (P.isOpen_coordinate_preimage hE).measurableSet
  have hL : (∫⁻ x in E, ENNReal.ofReal (χ x) ∂P.pushTraceMeasure T hT) =
      ∫⁻ z in V, ENNReal.ofReal (θ z) ∂hT.traceMeasure := by
    rw [← lintegral_indicator hE.measurableSet _, CoordinatePatch.pushTraceMeasure,
      CoordinatePatch.pushMeasure, P.measurableEmbedding_toManifold.lintegral_map]
    change (∫⁻ z : P.domain, E.indicator (fun x => ENNReal.ofReal (χ x))
      (P.chart.val.symm z) ∂hT.traceMeasure.comap (Subtype.val : P.domain → ComplexModel n)) = _
    have ht := lintegral_subtype_comap (μ := hT.traceMeasure) P.domain.isOpen.measurableSet
      (fun z => E.indicator (fun x => ENNReal.ofReal (χ x)) (P.chart.val.symm z))
    refine ht.trans ?_
    rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hT.traceMeasure_compl),
      ← lintegral_indicator hV _]
    apply lintegral_congr_ae
    filter_upwards [ae_iff.mpr hT.traceMeasure_compl] with z hz
    have hread : θ z = χ (P.chart.val.symm z) := by
      rw [hθ, chartWeight, indicator_of_mem (P.domain_le_target hz)]
    by_cases hzE : P.chart.val.symm z ∈ E
    · rw [indicator_of_mem hzE, indicator_of_mem (show z ∈ V from ⟨hz, hzE⟩), hread]
    · rw [indicator_of_notMem hzE, indicator_of_notMem (show z ∉ V from fun h => hzE h.2)]
  rw [CoordinatePatch.weightedTraceMeasure, withDensity_apply _ hE.measurableSet, hL]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hθ0)
    θ.contDiff.continuous.aestronglyMeasurable).symm

end SGPT.PSH.HermitianGlobalProducts

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalBedfordTaylorCollar StronglyPositiveForms
open Hermitian HermitianProducts HermitianGlobalProducts
open HermitianComparisonOneFactor HermitianComparisonStrict HermitianComparisonCutoff
open scoped Topology Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The literal global distinguished tuple is the same original local
background expansion, with only degree transports simplified. -/
theorem current_cons_eq_backgroundExpansion (P : BackgroundPatch omega)
    (u : Fin m → M → EReal) (a : M → EReal) :
    P.current (Fin.cons a u) =
      backgroundExpansion (m + 1) 0
        (Fin.cons (P.correctedReal a) (fun i => P.correctedReal (u i))) P.residual_smooth
        (castLPC (by omega) (oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1))) := by
  rw [castLPC_oneCurrentOf (by omega : 1 + m = m + 1)
    (by omega : 0 + (m + 1) = m + 1)]
  unfold BackgroundPatch.current
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Real boundedness gives exactly the original strict comparison set
after adding the same genuine smooth correction to both potentials. -/
theorem correctedReal_lt_iff (P : BackgroundPatch omega) {a b : M → EReal}
    (ha : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (hb : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ b x ∧ b x ≤ (d : EReal))
    (z : ComplexModel (m + 1)) :
    P.correctedReal a z < P.correctedReal b z ↔
      a (P.geometry.chart.val.symm z) < b (P.geometry.chart.val.symm z) := by
  obtain ⟨c, d, hbounda⟩ := ha
  obtain ⟨e, f, hboundb⟩ := hb
  have ha' (x : M) : ((a x).toReal : EReal) = a x :=
    EReal.coe_toReal (ne_of_lt ((hbounda x).2.trans_lt (EReal.coe_lt_top d)))
      (ne_of_gt ((EReal.bot_lt_coe c).trans_le (hbounda x).1))
  have hb' (x : M) : ((b x).toReal : EReal) = b x :=
    EReal.coe_toReal (ne_of_lt ((hboundb x).2.trans_lt (EReal.coe_lt_top f)))
      (ne_of_gt ((EReal.bot_lt_coe e).trans_le (hboundb x).1))
  change (a (P.geometry.chart.val.symm z)).toReal + P.correction z <
    (b (P.geometry.chart.val.symm z)).toReal + P.correction z ↔ _
  rw [add_lt_add_iff_right]
  exact EReal.coe_lt_coe_iff.symm.trans (by rw [ha', hb'])

/-- The actual distinguished-factor transgression, Borel extension and
canonical trace tests give literal local strict-set integrals. -/
theorem weightedDifference_patchResidual_eq_strict_integral
    (P : BackgroundPatch omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a b : M → EReal} (ha : IsHermitianPSH omega a) (hbb : IsHermitianPSH omega b)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (hbbound : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ b x ∧ b x ≤ (d : EReal))
    (φ : 𝓓(P.geometry.domain, ℝ)) :
    weightedDifference (patchResidual P u hu hb) (P.correctedReal a) (P.correctedReal b)
      strictIndicator scalarUnit φ =
      (∫ z in (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
        P.geometry.chart.val.symm ⁻¹' {x | a x < b x}, φ z
        ∂(P.current_isPositive (Fin.cons b u) (Fin.cases hbb hu) (Fin.cases hbbound hb)).traceMeasure) -
      ∫ z in (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
        P.geometry.chart.val.symm ⁻¹' {x | a x < b x}, φ z
        ∂(P.current_isPositive (Fin.cons a u) (Fin.cases ha hu) (Fin.cases hab hb)).traceMeasure := by
  let T := oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1)
  have hpA : IsPositive (P.current (Fin.cons a u)) :=
    P.current_isPositive (Fin.cons a u) (Fin.cases ha hu) (Fin.cases hab hb)
  have hpB : IsPositive (P.current (Fin.cons b u)) :=
    P.current_isPositive (Fin.cons b u) (Fin.cases hbb hu) (Fin.cases hbbound hb)
  have hneg : ∀ z ∈ P.geometry.domain, IsSemipositiveOneOne (-P.residual z) := by
    intro z hz
    constructor
    · intro v w
      simp only [ContinuousAlternatingMap.neg_apply]
      rw [P.residual_isOneOne z hz v w]
    · intro v
      simp only [BackgroundPatch.residual, ContinuousAlternatingMap.neg_apply,
        ContinuousAlternatingMap.sub_apply]
      linarith [P.dominates z hz v]
  have haP := P.correctedReal_isLocallyBoundedPshOn ha hab
  have hbP := P.correctedReal_isLocallyBoundedPshOn hbb hbbound
  have h := backgroundExpansion_strict_transgression m T (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) haP hbP
    P.residual_smooth hneg
    (by rw [← current_cons_eq_backgroundExpansion]; exact hpB)
    (by rw [← current_cons_eq_backgroundExpansion]; exact hpA)
  change mulBorel _ _ - mulBorel _ _ =
    weightedDifference (patchResidual P u hu hb) (P.correctedReal a) (P.correctedReal b)
      strictIndicator at h
  rw [← current_cons_eq_backgroundExpansion, ← current_cons_eq_backgroundExpansion] at h
  have hread := mulBorel_strict_difference_scalarUnit_apply hpA hpB
    (measurable_indicator_of_isLocallyBoundedPshOn haP)
    (measurable_indicator_of_isLocallyBoundedPshOn hbP) φ
  rw [h] at hread
  have hset : (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
      {z | P.correctedReal a z < P.correctedReal b z} =
      (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
        P.geometry.chart.val.symm ⁻¹' {x | a x < b x} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    rw [correctedReal_lt_iff P hab hbbound]
  simpa only [hset] using hread

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual canonical product on an open set is its original finite
partition of genuine coordinate trace integrals. -/
theorem globalMixedMeasure_open_toReal_eq_sum (C : CompactPartition omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {E : Set M} (hE : IsOpen E) :
    (globalMixedMeasure omega u hu hb E).toReal =
      ∑ i, ∫ z in ((C.patch i).geometry.domain : Set (ComplexModel (m + 1))) ∩
        (C.patch i).geometry.chart.val.symm ⁻¹' E,
        C.weight i z ∂((C.patch i).current_isPositive u hu hb).traceMeasure := by
  have hfin (i : Fin C.outer.count) :
      ((C.patch i).geometry.weightedTraceMeasure ((C.patch i).current u)
        ((C.patch i).current_isPositive u hu hb) (C.outer.weight i)) E ≠ ⊤ := by
    let _ := (C.patch i).geometry.weightedTraceMeasure_isFiniteMeasure
      ((C.patch i).current u) ((C.patch i).current_isPositive u hu hb) (C.outer.weight i)
      (isClosed_tsupport (C.outer.weight i)).isCompact (C.partition.supported i)
      (C.outer.weight_le_one i)
    exact measure_ne_top _ _
  rw [← C.partition.topMeasure_eq_globalMixedMeasure u hu hb,
    MixedCurrentPartition.topMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  change (∑ i, ((C.patch i).geometry.weightedTraceMeasure ((C.patch i).current u)
    ((C.patch i).current_isPositive u hu hb) (C.outer.weight i)) E).toReal = _
  rw [ENNReal.toReal_sum (fun i _ => hfin i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (C.patch i).geometry.weightedTraceMeasure_open_toReal ((C.patch i).current u)
    ((C.patch i).current_isPositive u hu hb) (C.outer.weight i) (C.weight i)
    (C.weight_eq_partition i) (C.weight_nonneg i) hE

/-- The literal current-side strict difference is the difference of the
original canonical global mixed measures on the actual open strict set.
All transgression, positivity, Borel multiplication, chart transport and
partition readback are proved internally from the actual bounded classes. -/
theorem strictDifference_eq_globalMixedMeasure_sub (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a b : M → EReal} (ha : IsHermitianPSH omega a) (hbb : IsHermitianPSH omega b)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (hbbound : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ b x ∧ b x ≤ (d : EReal))
    (hE : IsOpen {x | a x < b x}) :
    strictDifference C u hu hb a b =
      (globalMixedMeasure omega (Fin.cons b u) (Fin.cases hbb hu)
        (Fin.cases hbbound hb) {x | a x < b x}).toReal -
      (globalMixedMeasure omega (Fin.cons a u) (Fin.cases ha hu)
        (Fin.cases hab hb) {x | a x < b x}).toReal := by
  rw [globalMixedMeasure_open_toReal_eq_sum C _ (Fin.cases hbb hu) (Fin.cases hbbound hb) hE,
    globalMixedMeasure_open_toReal_eq_sum C _ (Fin.cases ha hu) (Fin.cases hab hb) hE,
    ← Finset.sum_sub_distrib]
  unfold strictDifference
  apply Finset.sum_congr rfl
  intro i _
  exact weightedDifference_patchResidual_eq_strict_integral (C.patch i) u hu hb
    ha hbb hab hbbound (C.weight i)

end SGPT.PSH.HermitianComparisonGlobalOneFactor
