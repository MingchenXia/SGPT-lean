import SGPT.Foundations.Analysis.Pending.ActualSingularChartCutoffWeightedLimits
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

namespace SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar FirstPass.GlobalPotentialPatches
  GlobalSlotStokes GlobalNonPluripolar MixedNonPluripolar MixedMongeAmpere ThetaCapacity
  ActualLocalNonPluripolarCutoffIntegrals ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Nonnegative patch integrals use the actual subtype measurable embedding.
No global measurability of an arbitrary inverse-chart read is required. -/
theorem lintegral_pushMeasure
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (P : Patch θ u) {μ : Measure (ComplexModel n)}
    (hμ : μ (P.domain : Set (ComplexModel n))ᶜ = 0) (G : M → ℝ≥0∞) :
    (∫⁻ x, G x ∂P.pushMeasure μ) = ∫⁻ z, G (P.chart.val.symm z) ∂μ := by
  rw [Patch.pushMeasure, P.measurableEmbedding_toManifold.lintegral_map]
  have h := lintegral_subtype_comap (μ := μ) P.domain.isOpen.measurableSet
    (fun z => G (P.chart.val.symm z))
  refine h.trans ?_
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)]

variable [CompactSpace M]

private theorem global_chart_test_eq
    {θ : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
    (J : SlotChart θ κ) {D : Opens (ComplexModel n)} (hD : D ≤ J.domain)
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hcorr : ∀ i, PlurisubharmonicOn
      (fun z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) D)
    {h : ComplexModel n → ℝ} (hzero : ∀ z, z ∉ D → h z = 0) :
    (∫⁻ x, ENNReal.ofReal (chartExtend J.chart h x) ∂globalMixedMeasure θ u hu) =
    ∫⁻ z, ENNReal.ofReal (h z) ∂mixedTruncationLimitMeasure D
      (fun i z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) hcorr := by
  let P : Patch θ u := {
    chart := J.chart
    domain := D
    domain_le_target := fun z hz => J.domain_le_target (hD hz)
    potential := J.potential
    localPotential := fun i => (J.localPotential i).mono D.isOpen hD
    plurisubharmonic := hcorr }
  have hs : Function.support (fun x => ENNReal.ofReal (chartExtend J.chart h x)) ⊆
      (P.source : Set M) := by
    intro x hx
    by_contra hbad
    apply hx
    change ENNReal.ofReal (chartExtend J.chart h x) = 0
    by_cases hxs : x ∈ J.chart.val.source
    · rw [chartExtend_of_mem hxs, hzero _ (fun hxD => hbad ⟨hxs, hxD⟩), ENNReal.ofReal_zero]
    · rw [chartExtend_of_notMem hxs, ENNReal.ofReal_zero]
  have hcomp : (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic)
      (P.domain : Set (ComplexModel n))ᶜ = 0 := mixedTruncationLimitMeasure_compl P.plurisubharmonic
  calc
    _ = ∫⁻ x in P.source, ENNReal.ofReal (chartExtend J.chart h x)
        ∂globalMixedMeasure θ u hu := (setLIntegral_eq_of_support_subset hs).symm
    _ = ∫⁻ z, ENNReal.ofReal (chartExtend J.chart h (J.chart.val.symm z))
        ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic := by
      rw [globalMixedMeasure_restrict_patch hu P, patchMeasure,
        lintegral_pushMeasure P hcomp]
    _ = _ := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ z ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic,
          z ∈ P.domain := ae_iff.mpr hcomp
      filter_upwards [hae] with z hz
      rw [chartExtend_of_mem (J.chart.val.map_target (P.domain_le_target hz)),
        J.chart.val.right_inv (P.domain_le_target hz)]

/-- The same original global chart test satisfies the actual mixed-product
liminf inequality, from capacity limits and internally produced cutoffs. -/
theorem chart_test_liminf (omega : KahlerBackground n M)
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
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hn : ∀ z, 0 ≤ h z)
    (ht : tsupport h ⊆ K) :
    (∫⁻ x, ENNReal.ofReal (chartExtend J.chart h x)
      ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
    liminf (fun j => ∫⁻ x, ENNReal.ofReal (chartExtend J.chart h x)
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
    ActualSingularChartCutoffWeightedLimits.exists_tail_cutoff_lintegral_limits
      omega hu hv hcap J hcompact hclosure hK hKD
  let b (j : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (chartExtend J.chart h x)
    ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  have hbound (k : ℕ) :
      (∫⁻ z, ENNReal.ofReal (h z) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
        ∂mixedTruncationLimitMeasure D (corr v) hV) ≤ liminf b atTop := by
    have hlim := (hlimits k h hc hn ht).2.2
    have hstage (j : ℕ) :
        (∫⁻ z, ENNReal.ofReal (h z) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
          ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) ≤ b (j + N) := by
      exact (lintegral_cutoff_eq_le (hU j) k
        (fun z hz => by rw [hzD z hz, ENNReal.ofReal_zero])).2.trans_eq
        (global_chart_test_eq J hDJ (fun i => (hu (j + N) i).1) (hU j) hzD).symm
    calc
      _ = liminf (fun j => ∫⁻ z, ENNReal.ofReal (h z) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
          ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun j => b (j + N)) atTop := liminf_le_liminf (Eventually.of_forall hstage)
      _ = _ := liminf_nat_add b N
  have htarget := tendsto_lintegral_cutoff hV hc.measurable.ennreal_ofReal
    (fun z hz => by rw [hzD z hz, ENNReal.ofReal_zero])
  rw [global_chart_test_eq J hDJ (fun i => (hv i).1) (hCorr v hv) hzD]
  exact le_of_tendsto htarget (Eventually.of_forall hbound)

end
end SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf
