import SGPT.Foundations.Analysis.Pending.SingularSmoothTestLastSlot
import SGPT.Foundations.Analysis.Pending.CompactNonPluripolarChartWeightIntegrability

set_option autoImplicit false

/-! # Genuine finite potential charts transport actual compact singular Stokes -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularSmoothTestChartStokes

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  RelativeEnergy RelativeEnergyIntegrability GlobalSlotStokes GlobalNonPluripolar
  MixedNonPluripolar FiniteGeodesicStripCharts SingularModelEnergyChartIntegrals
  SingularSmoothTestStokes SingularSmoothTestLastSlot
  CompactNonPluripolarChartWeightIntegrability

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]
  {α β : ClosedRealOneOneForm (n + 1) M}

private def commonFirstChart (J : SlotChart (lastHybridForms α β) α) :
    SlotChart (lastHybridForms α β) α where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_le_target
  potential := Function.update (fun _ => J.kahler) (Fin.last n) (J.potential (Fin.last n))
  localPotential i := by
    classical
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [Function.update_self] using J.localPotential (Fin.last n)
    · simp only [Function.update_of_ne hi, lastHybridForms]
      simpa only [Function.update_of_ne hi] using J.kahlerLocal
  kahler := J.kahler
  kahlerLocal := J.kahlerLocal

/-- Actual local potentials and compactness produce a finite smooth subordinate partition with a common first-slot alpha potential. -/
theorem exists_finite_hybrid_chart_partition [CompactSpace M]
    (α β : ClosedRealOneOneForm (n + 1) M) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ)
      (J : Fin m → SlotChart (lastHybridForms α β) α),
      (∀ a, ChartSmooth (n := n + 1) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
      (∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) ∧
      (∀ a, HasCompactSupport (χ a)) ∧ (∀ x, ∑ a, χ a x = 1) ∧
      ∀ a i, i ≠ Fin.last n → ∀ z, (J a).potential i z = (J a).kahler z := by
  classical
  have hcover (x : M) : ∃ J : SlotChart (lastHybridForms α β) α,
      x ∈ (commonFirstChart J).source :=
    SlotChart.exists_mem_source (lastHybridForms α β) α x
  obtain ⟨m, χ, idx, hsm, h0, hsupp, hcpt, h1⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity
      (n := n + 1) (fun J : SlotChart (lastHybridForms α β) α => (commonFirstChart J).source) hcover
  refine ⟨m, χ, fun a => commonFirstChart (idx a), hsm, h0, hsupp, hcpt, h1, ?_⟩
  intro a i hi z
  simp only [commonFirstChart, Function.update_of_ne hi]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {W Φ r : M → EReal}

/-- The actual canonical coordinate measure of a genuine last-slot global hybrid patch. -/
def lastHybridChartMeasure (hW : IsThetaPshPotential α.val W)
    (hΦ : IsThetaPshPotential α.val Φ) (hr : IsThetaPshPotential β.val r)
    (J : SlotChart (lastHybridForms α β) α) (k : Fin (n + 1)) : Measure (ComplexModel (n + 1)) :=
  let P := J.patch (lastHybridPotentials k W Φ r) (lastHybridThetaPlurisubharmonic hW hΦ hr k)
  mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic

/-- The actual zero-extended cutoff multiplied by the common-correction canonical chart gap. -/
def chartWeight (J : SlotChart (lastHybridForms α β) α) (f : M → ℝ)
    (W Φ : M → EReal) : ComplexModel (n + 1) → ℝ :=
  fun z => chartRead J.chart f z * canonicalERealDiffToReal
    (chartFunction W J.chart z + (J.kahler z : EReal))
    (chartFunction Φ J.chart z + (J.kahler z : EReal))

/-- Genuine same-type compact-host integrability produces the actual coordinate hybrid weight integrability for every subordinate smooth cutoff. -/
theorem integrable_chartWeight (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (hr : IsThetaPshPotential β.val r)
    (J : SlotChart (lastHybridForms α β) α) (k : Fin (n + 1))
    {f : M → ℝ} (hf : ChartSmooth (n := n + 1) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ (J.source : Set M)) :
    Integrable (chartWeight J f W Φ) (lastHybridChartMeasure hW hΦ hr J k) := by
  have hsource : tsupport f ⊆ J.chart.val.source := fun _ hx => (hfs hx).1
  let hs := lastHybridThetaPlurisubharmonic hW hΦ hr k
  let P := J.patch (lastHybridPotentials k W Φ r) hs
  exact integrable_mul_corrected_canonicalDiff omega hW.1 hΦ.1 hWΦ hs P
    (continuous_chartRead hf hfc hsource) (hasCompactSupport_chartRead hfc hsource) J.kahler

/-- Actual patch restrictions and inverse-chart integration transport the canonical local hybrid pairing to the actual global cutoff pairing. -/
theorem integral_chart_lastHybrid_eq_global
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hr : IsThetaPshPotential β.val r) (J : SlotChart (lastHybridForms α β) α)
    (k : Fin (n + 1)) {f : M → ℝ} (hfs : tsupport f ⊆ (J.source : Set M)) :
    (∫ z, chartWeight J f W Φ z ∂lastHybridChartMeasure hW hΦ hr J k) =
      ∫ x, f x * canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hr k := by
  let hs := lastHybridThetaPlurisubharmonic hW hΦ hr k
  let P := J.patch (lastHybridPotentials k W Φ r) hs
  let μ := mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic
  have hzero (x : M) (hx : x ∉ (P.source : Set M)) :
      f x * canonicalERealDiffToReal (W x) (Φ x) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfs h)), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  change (∫ z, chartWeight J f W Φ z ∂μ) =
    ∫ x, f x * canonicalERealDiffToReal (W x) (Φ x)
      ∂(globalMixedMeasure (lastHybridForms α β) (lastHybridPotentials k W Φ r) hs).restrict
        (P.source : Set M)
  rw [globalMixedMeasure_restrict_patch hs P, patchMeasure]
  change (∫ z, chartWeight J f W Φ z ∂μ) =
    ∫ x, f x * canonicalERealDiffToReal (W x) (Φ x) ∂P.pushMeasure μ
  rw [Patch.integral_pushMeasure P (μ := μ) (mixedTruncationLimitMeasure_compl P.plurisubharmonic)]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (mixedTruncationLimitMeasure_compl P.plurisubharmonic)] with z hz
  dsimp only [chartWeight]
  rw [canonicalDiff_add_common, chartRead_of_mem (J.domain_le_target hz)]
  rfl

/-- Actual same-type integrability and a genuine finite nonnegative subordinate partition assemble the local hybrid integrals into the actual global integral. -/
theorem sum_chart_integral_lastHybrid_eq_global (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (hr : IsThetaPshPotential β.val r)
    {m : ℕ} (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (lastHybridForms α β) α)
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) (hχ1 : ∀ x, ∑ a, χ a x = 1)
    (k : Fin (n + 1)) :
    (∑ a, ∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hr (J a) k) =
      ∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hr k := by
  classical
  have hi := integrable_canonicalDiff_globalMixedMeasure omega hW.1 hΦ.1 hWΦ
    (lastHybridThetaPlurisubharmonic hW hΦ hr k)
  have hbound (a : Fin m) (x : M) : ‖χ a x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 a x), ← hχ1 x]
    exact Finset.single_le_sum (fun b _ => hχ0 b x) (Finset.mem_univ a)
  have hip (a : Fin m) : Integrable (fun x => χ a x * canonicalERealDiffToReal (W x) (Φ x))
      (lastHybridMixedMeasure hW hΦ hr k) :=
    hi.bdd_mul (ProductTestForms.ChartSmooth.continuous (hχs a)).aestronglyMeasurable
      (Eventually.of_forall (hbound a))
  simp_rw [integral_chart_lastHybrid_eq_global hW hΦ hr _ k (hχJ _)]
  rw [← integral_finsetSum _ (fun a _ => hip a)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ a : Fin m, χ a x * canonicalERealDiffToReal (W x) (Φ x)) = _
    rw [← Finset.sum_mul, hχ1 x, one_mul]

/-- The actual compact smooth-test background, genuine finite potential chart partition, internally produced local integrability and true slot-swap/Stokes producers yield the precise finite coordinate sum. -/
theorem exists_finite_chart_smooth_test_stokes (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (g : M → ℝ) (hg : ChartSmooth (n := n + 1) g) :
    ∃ A : ℝ, 0 < A ∧ ∃ hp : IsThetaPshPotential (A • omega.form).val (fun x => (g x : EReal)),
      ∃ hq : IsThetaPshPotential (A • omega.form).val (fun _ => 0),
      ∃ (m : ℕ) (χ : Fin m → M → ℝ)
        (J : Fin m → SlotChart (lastHybridForms α (A • omega.form)) α),
        (∀ a, ChartSmooth (n := n + 1) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
        (∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) ∧ (∀ a, HasCompactSupport (χ a)) ∧
        (∀ x, ∑ a, χ a x = 1) ∧
        (∀ a i, i ≠ Fin.last n → ∀ z, (J a).potential i z = (J a).kahler z) ∧
        (∀ k a, Integrable (chartWeight (J a) (χ a) W Φ) (lastHybridChartMeasure hW hΦ hp (J a) k) ∧
          Integrable (chartWeight (J a) (χ a) W Φ) (lastHybridChartMeasure hW hΦ hq (J a) k)) ∧
        (∑ k : Fin (n + 1), ∑ a : Fin m,
          ((∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
           (∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hq (J a) k))) =
          (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => W) (fun _ => hW.1)) -
          (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => Φ) (fun _ => hΦ.1)) := by
  classical
  obtain ⟨A, hA, hp, hq, hstokes⟩ := exists_integral_smooth_test_stokes omega hW hΦ hWΦ g hg
  obtain ⟨m, χ, J, hχs, hχ0, hχJ, hχc, hχ1, hcommon⟩ :=
    exists_finite_hybrid_chart_partition α (A • omega.form)
  refine ⟨A, hA, hp, hq, m, χ, J, hχs, hχ0, hχJ, hχc, hχ1, hcommon, ?_, ?_⟩
  · intro k a
    exact ⟨integrable_chartWeight omega hW hΦ hWΦ hp (J a) k (hχs a) (hχc a) (hχJ a),
      integrable_chartWeight omega hW hΦ hWΦ hq (J a) k (hχs a) (hχc a) (hχJ a)⟩
  · calc
      _ = ∑ k : Fin (n + 1), ((∫ x, canonicalERealDiffToReal (W x) (Φ x)
          ∂lastHybridMixedMeasure hW hΦ hp k) -
          (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hq k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_sub_distrib,
          sum_chart_integral_lastHybrid_eq_global omega hW hΦ hWΦ hp χ J hχs hχ0 hχJ hχ1 k,
          sum_chart_integral_lastHybrid_eq_global omega hW hΦ hWΦ hq χ J hχs hχ0 hχJ hχ1 k]
      _ = _ := by
        simp_rw [← hybridUpdatedMixedMeasure_eq_last hW hΦ]
        exact hstokes

end

end SGPT.Foundations.Analysis.Pending.SingularSmoothTestChartStokes
