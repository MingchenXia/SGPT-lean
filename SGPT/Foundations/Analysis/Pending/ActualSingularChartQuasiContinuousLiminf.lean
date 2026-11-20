import SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousCutoffWeightedLimits
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
import SGPT.Foundations.Analysis.Pending.ChartPartition
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false

/-! # Actual singular chart test mass liminf

Actual nonnegative patch transport and genuine fixed-cutoff integral
limits give chart-test lower semicontinuity for the original global
products. Full internal finite subchart partition assembly is separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousLiminf

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar FirstPass.GlobalPotentialPatches
  GlobalSlotStokes GlobalNonPluripolar MixedNonPluripolar MixedMongeAmpere ThetaCapacity
  ActualLocalNonPluripolarCutoffIntegrals ChartPartition CapacityWeightedConvergence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable [CompactSpace M]

omit [IsComplexManifold n M] [CompactSpace M] in
private theorem measurable_supported_read (e : ComplexChart n M)
    {D : Opens (ComplexModel n)} (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {χ : M → ℝ} (hχ : Measurable χ) {h : ComplexModel n → ℝ} (hc : Continuous h)
    (hz : ∀ z, z ∉ D → h z = 0) :
    Measurable (fun z => χ (e.val.symm z) * h z) := by
  apply measurable_of_restrict_of_restrict_compl e.val.open_target.measurableSet
  · have hi : Measurable (e.val.target.domRestrict e.val.symm) :=
      (continuousOn_iff_continuous_domRestrict.mp e.val.symm.continuousOn).measurable
    exact (hχ.comp hi).mul (hc.measurable.comp measurable_subtype_coe)
  · have heq : e.val.targetᶜ.domRestrict (fun z => χ (e.val.symm z) * h z) = fun _ => (0 : ℝ) := by
      funext z
      exact mul_eq_zero_of_right _ (hz _ (fun hh => z.property (hDt hh)))
    rw [heq]
    exact measurable_const

private theorem global_chart_test_eq
    {θ : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
    (J : SlotChart θ κ) {D : Opens (ComplexModel n)} (hD : D ≤ J.domain)
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hcorr : ∀ i, PlurisubharmonicOn
      (fun z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) D)
    {χ : M → ℝ} {h : ComplexModel n → ℝ} (hzero : ∀ z, z ∉ D → h z = 0) :
    (∫⁻ x, ENNReal.ofReal (χ x * chartExtend J.chart h x) ∂globalMixedMeasure θ u hu) =
    ∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * h z) ∂mixedTruncationLimitMeasure D
      (fun i z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) hcorr := by
  let P : Patch θ u := {
    chart := J.chart
    domain := D
    domain_le_target := fun z hz => J.domain_le_target (hD hz)
    potential := J.potential
    localPotential := fun i => (J.localPotential i).mono D.isOpen hD
    plurisubharmonic := hcorr }
  have hs : Function.support (fun x => ENNReal.ofReal (χ x * chartExtend J.chart h x)) ⊆
      (P.source : Set M) := by
    intro x hx
    by_contra hbad
    apply hx
    change ENNReal.ofReal (χ x * chartExtend J.chart h x) = 0
    by_cases hxs : x ∈ J.chart.val.source
    · rw [chartExtend_of_mem hxs, hzero _ (fun hxD => hbad ⟨hxs, hxD⟩), mul_zero, ENNReal.ofReal_zero]
    · rw [chartExtend_of_notMem hxs, mul_zero, ENNReal.ofReal_zero]
  have hcomp : (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic)
      (P.domain : Set (ComplexModel n))ᶜ = 0 := mixedTruncationLimitMeasure_compl P.plurisubharmonic
  calc
    _ = ∫⁻ x in P.source, ENNReal.ofReal (χ x * chartExtend J.chart h x)
        ∂globalMixedMeasure θ u hu := (setLIntegral_eq_of_support_subset hs).symm
    _ = ∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * chartExtend J.chart h (J.chart.val.symm z))
        ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic := by
      rw [globalMixedMeasure_restrict_patch hu P, patchMeasure,
        ActualSingularChartMassLiminf.lintegral_pushMeasure P hcomp]
    _ = _ := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ z ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic,
          z ∈ P.domain := ae_iff.mpr hcomp
      filter_upwards [hae] with z hz
      rw [chartExtend_of_mem (J.chart.val.map_target (P.domain_le_target hz)),
        J.chart.val.right_inv (P.domain_le_target hz)]

/-- The same original global chart test satisfies the actual mixed-product
liminf inequality, from capacity limits and internally produced cutoffs. -/
theorem chart_quasiContinuous_test_liminf (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (J : SlotChart θ omega.form) {D : Opens (ComplexModel n)}
    (hcompact : IsCompact (closure (D : Set (ComplexModel n))))
    (hclosure : closure (D : Set (ComplexModel n)) ⊆ J.domain)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, 0 ≤ χ x ∧ |χ x| ≤ C)
    (hχm : Measurable χ)
    (hχ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hn : ∀ z, 0 ≤ h z)
    (ht : tsupport h ⊆ K) :
    (∫⁻ x, ENNReal.ofReal (χ x * chartExtend J.chart h x)
      ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
    liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ x * chartExtend J.chart h x)
      ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  let corr (f : Fin n → M → EReal) : Fin n → ComplexModel n → EReal :=
    fun i z => f i (J.chart.val.symm z) + (J.potential i z : EReal)
  have hDJ : D ≤ J.domain := fun z hz => hclosure (subset_closure hz)
  have hCorr (f : Fin n → M → EReal) (hf : ∀ i, IsThetaPshPotential (θ i).val (f i)) :
      ∀ i, PlurisubharmonicOn (corr f i) D := fun i =>
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
      (hf i).1 J.chart (J.localPotential i)).mono hDJ
  have hzD : ∀ z, z ∉ D → h z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hs => hz (hKD (ht hs)))
  obtain ⟨N, hU, hV, hlimits⟩ :=
    ActualSingularChartQuasiContinuousCutoffWeightedLimits.exists_tail_quasiContinuous_cutoff_lintegral_limits
      omega hu hv hcap J hcompact hclosure hK hKD
  let b (j : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (χ x * chartExtend J.chart h x)
    ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  have hbound (k : ℕ) :
      (∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * h z) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
        ∂mixedTruncationLimitMeasure D (corr v) hV) ≤ liminf b atTop := by
    have hlim := (hlimits k χ C hC hχC hχm hχ h hc hn ht).2.2
    have hstage (j : ℕ) :
        (∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * h z) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
          ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) ≤ b (j + N) := by
      exact (lintegral_cutoff_eq_le (hU j) k
        (fun z hz => by rw [hzD z hz, mul_zero, ENNReal.ofReal_zero])).2.trans_eq
        (global_chart_test_eq (χ := χ) J hDJ (fun i => (hu (j + N) i).1) (hU j) hzD).symm
    calc
      _ = liminf (fun j => ∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * h z) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
          ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun j => b (j + N)) atTop := liminf_le_liminf (Eventually.of_forall hstage)
      _ = _ := liminf_nat_add b N
  have htarget := tendsto_lintegral_cutoff hV (measurable_supported_read J.chart (fun z hz => J.domain_le_target (hDJ hz)) hχm hc hzD).ennreal_ofReal
    (fun z hz => by rw [hzD z hz, mul_zero, ENNReal.ofReal_zero])
  rw [global_chart_test_eq (χ := χ) J hDJ (fun i => (hv i).1) (hCorr v hv) hzD]
  exact le_of_tendsto htarget (Eventually.of_forall hbound)

end
end SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousLiminf
