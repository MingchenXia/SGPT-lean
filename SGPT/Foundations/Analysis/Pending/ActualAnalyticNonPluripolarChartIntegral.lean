import SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarOffPoleMeasure
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison

set_option autoImplicit false

/-! # Entire original chart density integrals and actual pole removal
Complete NEW statement and ENTIRE proof preceded the import-only baseline.
The actual original reader is preserved; no globally smooth replacement or
supplied cover/polar-nullity/density certificate is assumed.
-/
noncomputable section
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ContDiff Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarChartIntegral
open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.MongeAmpere GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- On any entire measurable non-polar piece of an original chart, the actual
mixed NP measure is the genuine exterior density of the ORIGINAL real reader. -/
theorem original_mixed_measure_chart_piece_eq_lintegral
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (han : ∀ i, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (u i))
    (e : ComplexChart n M) {S : Set (ComplexModel n)}
    (hS : MeasurableSet S) (hSe : S ⊆ e.val.target)
    (hpole : ∀ y ∈ S, ∀ i, chartFunction (u i) e y ≠ ⊥) :
    globalMixedMeasure θ u (fun i => (hu i).1) (e.val.symm '' S) =
      ∫⁻ y in S, ENNReal.ofReal
        (actualMixedTopDensity (fun i => (θ i).val.coeff e y +
          smoothDDC (fun w => (chartFunction (u i) e w).toReal) y)) := by
  classical
  let μ : Measure M := globalMixedMeasure θ u (fun i => (hu i).1)
  let d : ComplexModel n → ℝ≥0∞ := fun y => ENNReal.ofReal
    (actualMixedTopDensity (fun i => (θ i).val.coeff e y +
      smoothDDC (fun w => (chartFunction (u i) e w).toReal) y))
  change μ (e.val.symm '' S) = ∫⁻ y in S, d y
  have hlocal : ∀ x : S, ∃ r : ℝ, 0 < r ∧
      ∀ A : Set (ComplexModel n), MeasurableSet A → A ⊆ ball (x : ComplexModel n) r →
        μ (e.val.symm '' A) = ∫⁻ y in A, d y := by
    intro x
    obtain ⟨r, hr, g, ρ, _, hg, _, hkey⟩ :=
      ActualAnalyticNonPluripolarOffPoleMeasure.exists_ball_original_mixed_measure_eq_density
        hu han e (hSe x.property) (hpole x x.property)
    refine ⟨r, hr, fun A hA hAb => ?_⟩
    have hvalue := hkey A hA hAb
    apply hvalue.trans
    apply setLIntegral_congr_fun hA
    intro y hy
    have hforms : (fun i => (θ i).val.coeff e y + smoothDDC (g i) y) =
        (fun i => (θ i).val.coeff e y +
          smoothDDC (fun w => (chartFunction (u i) e w).toReal) y) := by
      funext i
      have heq : (fun w => (chartFunction (u i) e w).toReal) =ᶠ[𝓝 y] g i := by
        filter_upwards [isOpen_ball.mem_nhds (hAb hy)] with w hw
        rw [(hg i).2.1 hw, EReal.toReal_coe]
      exact congrArg (fun A => (θ i).val.coeff e y + A) (smoothDDC_congr heq).symm
    exact congrArg (fun A => ENNReal.ofReal (actualMixedTopDensity A)) hforms
  choose r hr hkey using hlocal
  rcases Set.eq_empty_or_nonempty S with rfl | hSne
  · rw [Set.image_empty, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  obtain ⟨T, hTcount, hTunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable
      (fun x : S => ball (x : ComplexModel n) (r x)) (fun _ => isOpen_ball)
  have hcover : S ⊆ ⋃ x ∈ T, ball ((x : S) : ComplexModel n) (r x) := by
    intro w hw
    rw [hTunion]
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hr ⟨w, hw⟩)⟩
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := hSne
    obtain ⟨x, hxT, _⟩ := mem_iUnion₂.mp (hcover hw)
    exact ⟨x, hxT⟩
  obtain ⟨f, hf⟩ := hTcount.exists_eq_range hTne
  let A : ℕ → Set (ComplexModel n) := fun k => S ∩ ball ((f k : S) : ComplexModel n) (r (f k))
  have hAmeas : ∀ k, MeasurableSet (A k) := fun _ => hS.inter measurableSet_ball
  have hAunion : (⋃ k, A k) = S := by
    apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro w hw
    obtain ⟨x, hxT, hxb⟩ := mem_iUnion₂.mp (hcover hw)
    rw [hf] at hxT
    obtain ⟨k, rfl⟩ := hxT
    exact mem_iUnion.mpr ⟨k, hw, hxb⟩
  let D : ℕ → Set (ComplexModel n) := disjointed A
  have hDmeas : ∀ k, MeasurableSet (D k) := MeasurableSet.disjointed hAmeas
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed A
  have hDunion : (⋃ k, D k) = S := by
    change (⋃ k, disjointed A k) = S
    rw [iUnion_disjointed, hAunion]
  have hDball : ∀ k, D k ⊆ ball ((f k : S) : ComplexModel n) (r (f k)) :=
    fun k => (disjointed_le A k).trans inter_subset_right
  have hDS : ∀ k, D k ⊆ S := fun k => (disjointed_le A k).trans inter_subset_left
  have hpiece : ∀ k, μ (e.val.symm '' D k) = ∫⁻ y in D k, d y :=
    fun k => hkey (f k) (D k) (hDmeas k) (hDball k)
  have hinj : InjOn e.val.symm e.val.target := e.val.symm.injOn
  have himagedisj : Pairwise (Function.onFun Disjoint (fun k => e.val.symm '' D k)) := by
    intro i j hij
    have hinter := hinj.image_inter ((hDS i).trans hSe) ((hDS j).trans hSe)
    show Disjoint (e.val.symm '' D i) (e.val.symm '' D j)
    rw [Set.disjoint_iff_inter_eq_empty, ← hinter,
      Set.disjoint_iff_inter_eq_empty.mp (hDdisj hij), Set.image_empty]
  have himagemeas : ∀ k, MeasurableSet (e.val.symm '' D k) :=
    fun k => SmoothMixedMeasureDensity.measurableSet_chartSymm_image e
      (hDmeas k) ((hDS k).trans hSe)
  calc
    μ (e.val.symm '' S) = μ (⋃ k, e.val.symm '' D k) := by
      rw [← Set.image_iUnion, hDunion]
    _ = ∑' k, μ (e.val.symm '' D k) := measure_iUnion himagedisj himagemeas
    _ = ∑' k, ∫⁻ y in D k, d y := tsum_congr hpiece
    _ = ∫⁻ y in ⋃ k, D k, d y := (lintegral_iUnion hDmeas hDdisj _).symm
    _ = ∫⁻ y in S, d y := by rw [hDunion]

/-- Every original chart piece is measured by the exterior density only off
its internally null original union of poles. No polar-nullity input is assumed. -/
theorem original_mixed_measure_chart_piece_eq_off_pole_lintegral
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (han : ∀ i, HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (u i))
    (e : ComplexChart n M) {S : Set (ComplexModel n)}
    (hS : MeasurableSet S) (hSe : S ⊆ e.val.target) :
    globalMixedMeasure θ u (fun i => (hu i).1) (e.val.symm '' S) =
      ∫⁻ y in S ∩ e.val.symm ⁻¹' (⋃ i, {x | u i x = ⊥})ᶜ,
        ENNReal.ofReal (actualMixedTopDensity (fun i => (θ i).val.coeff e y +
          smoothDDC (fun w => (chartFunction (u i) e w).toReal) y)) := by
  classical
  let P : Set M := ⋃ i, {x | u i x = ⊥}
  let μ : Measure M := globalMixedMeasure θ u (fun i => (hu i).1)
  have hP : MeasurableSet P := by
    apply MeasurableSet.iUnion
    intro i
    exact measurableSet_eq_fun (hu i).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      measurable_const
  have hPzero : μ P = 0 :=
    measure_iUnion_null (fun i => GlobalSlotComparison.globalMixedMeasure_pole_null
      (fun i => (hu i).1) i)
  let S0 : Set (ComplexModel n) := S ∩ e.val.symm ⁻¹' Pᶜ
  have hS0 : MeasurableSet S0 := by
    have hpre := SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      e.val.open_target.measurableSet e.val.continuousOn_symm hP.compl
    have heq : S0 = S ∩ (e.val.target ∩ e.val.symm ⁻¹' Pᶜ) := by
      rw [← inter_assoc, inter_eq_left.mpr hSe]
    rw [heq]
    exact hS.inter hpre
  have hpole : ∀ y ∈ S0, ∀ i, chartFunction (u i) e y ≠ ⊥ := by
    intro y hy i hi
    apply hy.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  have himage : e.val.symm '' S0 = (e.val.symm '' S) \ P :=
    Set.image_inter_preimage e.val.symm S Pᶜ
  change μ (e.val.symm '' S) = _
  rw [← measure_sdiff_null hPzero, ← himage]
  exact original_mixed_measure_chart_piece_eq_lintegral hu han e hS0
    (inter_subset_left.trans hSe) hpole

end SGPT.Foundations.Analysis.Pending.ActualAnalyticNonPluripolarChartIntegral
