import SGPT.PSH.SourceConnectedAtlasL1
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshWeakLimitRealization
import SGPT.Foundations.Analysis.Pending.NaturalWeightedThetaPshMonotoneGaps
import SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshWeakLimit
import SGPT.Foundations.Analysis.FirstPass.FiniteVaryingTranslation
import SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate
import SGPT.PSH.ThetaDecreasingNets
import SGPT.PSH.SupremumPluripolar

/-! Original connected theta-PSH compactness.  The complete chosen pure
proofs precede this file. Actual source classes, tensors, chart-Lp topology,
all original index filters, dimension zero and poles are retained. -/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.PSH.ConnectedThetaPSHCompactness

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open NaturalCountableWeakHartogsEvents NaturalWeakThetaPshOrder
open NaturalNormalizedThetaPshWeakLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : ClosedRealOneOneForm n M}

/-- The existing arbitrary-family ORIGINAL universal-PSH supremum theorem
removes the native countable-index bottleneck for the given closed form. -/
theorem native_usc_iSup_of_le {I : Type*} [Nonempty I]
    {u : I → M → EReal} (hu : ∀ i, IsThetaPshPotential θ.val (u i))
    {C : ℝ} (hC : ∀ i x, u i x ≤ (C : EReal)) :
    IsThetaPshPotential θ.val (uscRegularization (⨆ i, u i)) := by
  have hs (i : I) : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) (u i) := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using hu i
  have hsup := isThetaPSH_uscSup_of_majorant hs upperSemicontinuous_const
    (fun _ => EReal.coe_ne_top C) hC
  have hn := (isThetaPSH_iff_nativeThetaPotential _ _).mp hsup
  simpa only [sourceNativeAtlasForm_roundTrip, sourceUscSup_eq_native] using hn

/-- Actual original weak-filter events, with genuine USC suprema and their
EXACT pointwise infimum, for ANY original index type. -/
theorem native_exists_genuine_events {I : Type*} {F : Filter I} [NeBot F]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ∀ (e : ComplexChart n M) (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) F
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i x, u i x ≤ (C : EReal)) :
    ∃ S : ℕ → Set I, (∀ k, S k ∈ F) ∧ (∀ k, (S k).Nonempty) ∧ Antitone S ∧
      (∀ k, IsThetaPshPotential θ.val (uscRegularization (⨆ i : S k, u i.val))) ∧
      Antitone (fun k => uscRegularization (⨆ i : S k, u i.val)) ∧
      (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val)) = v := by
  obtain ⟨S, hS, hSne, hantiS, hantiW, hupper⟩ :=
    exists_antitone_events_and_usc_inf_le_of_chart_weak_tests hu hv hlim hC
  have hg (k : ℕ) : IsThetaPshPotential θ.val (uscRegularization (⨆ i : S k, u i.val)) := by
    obtain ⟨i, hi⟩ := hSne k
    let : Nonempty (S k) := ⟨⟨i, hi⟩⟩
    exact native_usc_iSup_of_le (fun i : S k => hu i.val) (fun i x => hC i.val x)
  have hlower (k : ℕ) : v ≤ uscRegularization (⨆ i : S k, u i.val) := by
    apply le_of_chart_weak_limit_eventually_le hu hv (hg k) hlim
    filter_upwards [hS k] with i hi
    intro x
    have hs : u i x ≤ (⨆ j : S k, u j.val) x := by
      simp only [iSup_apply]
      exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
    exact hs.trans (le_uscRegularization _ x)
  exact ⟨S, hS, hSne, hantiS, hg, hantiW, le_antisymm hupper (le_iInf hlower)⟩

/-- The actual positive-part integral proof now works on the original arbitrary filter.
Only the newly constructed genuine event sequence uses dominated convergence. -/
theorem native_weighted_abs_of_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal))
    (e : ComplexChart n M) (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) :
    Tendsto (fun i => ∫ z, φ z *
      |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume) l (𝓝 0) := by
  obtain ⟨S, hS, _hSne, _hantiS, hg, hantiW, heq⟩ :=
    native_exists_genuine_events hu hv hlim hC
  have hgap := fun (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)) (hφ : ∀ z, 0 ≤ φ z) =>
    NaturalWeightedThetaPshMonotoneGaps.tendsto_native_weighted_gap_of_antitone_iInf
      hg hv hantiW heq e φ hφ
  let W (k : ℕ) : M → EReal := uscRegularization (⨆ i : S k, u i.val)
  have hvlower (k : ℕ) : v ≤ W k := by
    rw [← heq]
    exact iInf_le _ k
  have hui (i : ι) : Integrable
      (fun z => φ z * (chartFunction (u i) e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hvi : Integrable (fun z => φ z * (chartFunction v e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hv.quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  let F (i : ι) (z : ComplexModel n) : ℝ := φ z *
    ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)
  let P (i : ι) (z : ComplexModel n) : ℝ := max (F i z) 0
  let G (k : ℕ) (z : ComplexModel n) : ℝ := φ z *
    ((chartFunction (W k) e z).toReal - (chartFunction v e z).toReal)
  have hFi (i : ι) : Integrable (F i) volume :=
    ((hui i).sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (u i) e z).toReal - φ z * (chartFunction v e z).toReal = _
      dsimp only [F]
      ring))
  have hPi (i : ι) : Integrable (P i) volume := by
    have hz : Integrable (fun _ : ComplexModel n => (0 : ℝ)) volume := by simp
    exact (hFi i).sup hz
  have hGi (k : ℕ) : Integrable (G k) volume := by
    have hwi : Integrable (fun z => φ z * (chartFunction (W k) e z).toReal) volume := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
          ((hg k).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
    exact (hwi.sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (W k) e z).toReal - φ z * (chartFunction v e z).toReal = _
      dsimp only [G]
      ring))
  have hdom (k : ℕ) (i : ι) (hi : i ∈ S k) : P i ≤ᵐ[volume] G k := by
    have hraw : u i ≤ W k := by
      intro x
      have hsup : u i x ≤ (⨆ j : S k, u j.val) x := by
        simp only [iSup_apply]
        exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
      exact hsup.trans (le_uscRegularization _ x)
    have hgood : ∀ᵐ z ∂volume.restrict e.val.target,
        (chartFunction (u i) e z ≠ ⊤ ∧ chartFunction (u i) e z ≠ ⊥) ∧
        (chartFunction v e z ≠ ⊤ ∧ chartFunction v e z ≠ ⊥) ∧
        (chartFunction (W k) e z ≠ ⊤ ∧ chartFunction (W k) e z ≠ ⊥) := by
      filter_upwards [(hu i).quasiPshPotential.ae_finite_chart e,
        hv.quasiPshPotential.ae_finite_chart e, (hg k).quasiPshPotential.ae_finite_chart e]
        with z huz hvz hwz
      exact ⟨huz, hvz, hwz⟩
    have hgood' := (ae_restrict_iff' e.val.open_target.measurableSet).mp hgood
    filter_upwards [hgood'] with z hz
    by_cases hzt : z ∈ e.val.target
    · obtain ⟨huz, hvz, hwz⟩ := hz hzt
      have hreal : (chartFunction (u i) e z).toReal ≤ (chartFunction (W k) e z).toReal :=
        EReal.toReal_le_toReal (hraw (e.val.symm z)) huz.2 hwz.1
      have hlow : (chartFunction v e z).toReal ≤ (chartFunction (W k) e z).toReal :=
        EReal.toReal_le_toReal (hvlower k (e.val.symm z)) hvz.2 hwz.1
      exact max_le (mul_le_mul_of_nonneg_left (sub_le_sub_right hreal _) (hφ z))
        (mul_nonneg (hφ z) (sub_nonneg.mpr hlow))
    · have hzero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzt (φ.tsupport_subset h))
      simp [P, F, G, hzero]
  have hPnonneg (i : ι) : 0 ≤ ∫ z, P i z ∂volume :=
    integral_nonneg (fun z => le_max_right _ _)
  have hPlim : Tendsto (fun i => ∫ z, P i z ∂volume) l (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall (fun i => ha.trans_le (hPnonneg i))
    · intro b hb
      obtain ⟨k, hk⟩ := ((hgap e φ hφ).eventually (Iio_mem_nhds hb)).exists
      filter_upwards [hS k] with i hi
      exact (integral_mono_ae (hPi i) (hGi k) (hdom k i hi)).trans_lt hk
  have hFread (i : ι) : (∫ z, F i z ∂volume) =
      (∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) -
        ∫ z, φ z * (chartFunction v e z).toReal ∂volume := by
    dsimp only [F]
    simp_rw [mul_sub]
    exact integral_sub (hui i) hvi
  have hFlim : Tendsto (fun i => ∫ z, F i z ∂volume) l (𝓝 0) := by
    have ht := (hlim e φ).sub
      (tendsto_const_nhds (x := ∫ z, φ z * (chartFunction v e z).toReal ∂volume))
    simpa only [← hFread, sub_self] using ht
  have hrealIdentity (t : ℝ) : |t| = 2 * max t 0 - t := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, abs_of_nonneg ht]
      ring
    · rw [max_eq_right ht, abs_of_nonpos ht]
      ring
  have hAbsRead (i : ι) : (∫ z, |F i z| ∂volume) =
      2 * (∫ z, P i z ∂volume) - ∫ z, F i z ∂volume := by
    simp_rw [hrealIdentity]
    change (∫ z, 2 * P i z - F i z ∂volume) = _
    rw [integral_sub ((hPi i).const_mul 2) (hFi i), integral_const_mul]
  have hAbsLim : Tendsto (fun i => ∫ z, |F i z| ∂volume) l (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (2 : ℝ))).mul hPlim).sub hFlim
    simpa only [← hAbsRead, mul_zero, sub_zero] using ht
  have hfunction : (fun i => ∫ z, |F i z| ∂volume) =
      fun i => ∫ z, φ z *
        |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume := by
    funext i
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      dsimp only [F]
      rw [abs_mul, abs_of_nonneg (hφ z)])
  rw [hfunction] at hAbsLim
  exact hAbsLim


/-- All original compact-chart canonical errors tend to zero along the unchanged filter. -/
theorem native_manifoldL1_of_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n) u l v := by
  intro e K hK hKe
  let Ω : Opens (ComplexModel n) := ⟨e.val.target, e.val.open_target⟩
  obtain ⟨φ, hφ, hφK⟩ := exists_nonneg_testFunction_one_le_on_compact (Ω := Ω) hK hKe
  have hAbs := native_weighted_abs_of_weak_tests hu hv hlim hC e φ hφ
  have hui (i : ι) : Integrable
      (fun z => φ z * (chartFunction (u i) e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hvi : Integrable (fun z => φ z * (chartFunction v e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hv.quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hFi (i : ι) : Integrable
      (fun z => φ z * ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)) volume :=
    ((hui i).sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (u i) e z).toReal - φ z * (chartFunction v e z).toReal = _
      ring))
  have hWi (i : ι) : Integrable
      (fun z => φ z * |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) volume :=
    (hFi i).abs.congr (Eventually.of_forall (fun z => by
      change |φ z * ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)| = _
      rw [abs_mul, abs_of_nonneg (hφ z)]))
  have hbound (i : ι) : chartL1EDistance (u i) v e K ≤
      ENNReal.ofReal (∫ z, φ z *
        |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume) := by
    rw [chartL1EDistance]
    calc
      (∫⁻ z in K, canonicalERealAbsDiff (chartFunction (u i) e z) (chartFunction v e z) ∂volume)
          = ∫⁻ z in K, ENNReal.ofReal
            |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hKe
          ((hu i).quasiPshPotential.ae_finite_chart e),
          ae_restrict_of_ae_restrict_of_subset hKe (hv.quasiPshPotential.ae_finite_chart e)]
          with z huz hvz
        simpa only [EReal.coe_toReal huz.1 huz.2, EReal.coe_toReal hvz.1 hvz.2] using
          canonicalERealAbsDiff_coe_coe (chartFunction (u i) e z).toReal
            (chartFunction v e z).toReal
      _ ≤ ∫⁻ z in K, ENNReal.ofReal (φ z *
          |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
        exact ENNReal.ofReal_le_ofReal
          (le_mul_of_one_le_left (abs_nonneg _) (hφK z hz))
      _ ≤ ∫⁻ z, ENNReal.ofReal (φ z *
          |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal|) ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (hWi i)
        (Eventually.of_forall (fun z => mul_nonneg (hφ z) (abs_nonneg _)))).symm
  have hupper : Tendsto (fun i => ENNReal.ofReal (∫ z, φ z *
      |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hAbs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound



section AllFilterBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open Metric NaturalPshHartogsBallEstimate

private theorem allFilter_eventually_le_on_ball
    {I : Type*} {F : Filter I} {u : I → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, PlurisubharmonicOn (u j) U) (hv : PlurisubharmonicOn v U)
    (hU : IsPreconnected U) (hne : ∀ j, ∃ a ∈ U, u j a ≠ ⊥)
    (hvne : ∃ a ∈ U, v a ≠ ⊥)
    (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) {r A δ : ℝ}
    (hr : 0 < r) (hK : closedBall x (3 * r) ⊆ U)
    (hA : ∀ z ∈ closedBall x (3 * r), v z ≤ (A : EReal))
    (hlim : Tendsto (fun j => ∫⁻ z in closedBall x (3 * r),
      canonicalERealAbsDiff (u j z) (v z) ∂μ) F (𝓝 0))
    (hδ : 0 < δ) :
    ∀ᶠ j in F, ∀ y ∈ ball x r, u j y ≤ ((A + δ : ℝ) : EReal) := by
  let K : Set E := closedBall x (3 * r)
  have hcompact : IsCompact K := isCompact_closedBall x (3 * r)
  have hintu (j : I) : IntegrableOn (fun z => (u j z).toReal) K μ :=
    ((hu j).locallyIntegrableOn_toReal μ hU (hne j)).integrableOn_compact_subset hK hcompact
  have hintv : IntegrableOn (fun z => (v z).toReal) K μ :=
    (hv.locallyIntegrableOn_toReal μ hU hvne).integrableOn_compact_subset hK hcompact
  have hfinu (j : I) : ∀ᵐ z ∂μ.restrict K, u j z ≠ ⊤ ∧ u j z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hK ((hu j).ae_finite μ hU (hne j))
  have hfinv : ∀ᵐ z ∂μ.restrict K, v z ≠ ⊤ ∧ v z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hK (hv.ae_finite μ hU hvne)
  let err : I → ℝ := fun j => ∫ z in K, |(u j z).toReal - (v z).toReal| ∂μ
  have herr (j : I) : err j = (∫⁻ z in K, canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal := by
    dsimp only [err]
    have hi : IntegrableOn (fun z => |(u j z).toReal - (v z).toReal|) K μ := by
      exact (hintu j |>.sub hintv |>.abs)
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun z => |(u j z).toReal - (v z).toReal|)
      (Eventually.of_forall fun _ => abs_nonneg _) hi.aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfinu j, hfinv] with z hz₁ hz₂
    rw [← EReal.coe_toReal hz₁.1 hz₁.2, ← EReal.coe_toReal hz₂.1 hz₂.2,
      canonicalERealAbsDiff_coe_coe]
    simp only [EReal.toReal_coe]
  have herrlim : Tendsto err F (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have h' : Tendsto (fun j => (∫⁻ z in K,
        canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal) F (𝓝 0) := by
      change Tendsto (fun j => (∫⁻ z in K,
        canonicalERealAbsDiff (u j z) (v z) ∂μ).toReal) F (𝓝 (ENNReal.toReal 0)) at h
      simpa only [ENNReal.toReal_zero] using h
    exact h'.congr (fun j => (herr j).symm)
  let m : ℝ := (μ (ball (0 : E) r)).toReal
  have hm : 0 < m :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  have hsmall : ∀ᶠ j in F, err j < δ * m :=
    herrlim.eventually (gt_mem_nhds (mul_pos hδ hm))
  filter_upwards [hsmall] with j hj
  intro y hy
  have hclosed : closedBall y r ⊆ K := by
    intro z hz
    apply mem_closedBall.mpr
    have hzy : dist z y ≤ r := mem_closedBall.mp hz
    have hyx : dist y x < r := mem_ball.mp hy
    have htri := dist_triangle z y x
    linarith
  have hball : ball y r ⊆ K := ball_subset_closedBall.trans hclosed
  have hmass : μ (ball y r) = μ (ball (0 : E) r) := by
    simpa using (lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) y r).symm
  have hlocalA : ∀ᵐ z ∂μ.restrict (ball y r), (v z).toReal ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae_restrict_of_subset hball hfinv] with z hz hzf
    have h := hA z (hball hz)
    rw [← EReal.coe_toReal hzf.1 hzf.2, EReal.coe_le_coe_iff] at h
    exact h
  have hbound := le_real_bound_add_l1_ball_error (hu j).discPshOn μ y hr
    (hclosed.trans hK) (hintv.mono_set hball) hlocalA
  have herror : (∫ z in ball y r, |(u j z).toReal - (v z).toReal| ∂μ) ≤ err j := by
    exact setIntegral_mono_set (hintu j |>.sub hintv |>.abs)
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hball)
  refine hbound.trans (EReal.coe_le_coe_iff.mpr ?_)
  rw [hmass]
  change A + _ / m ≤ A + δ
  exact add_le_add le_rfl ((div_le_iff₀ hm).mpr (herror.trans hj.le))

end AllFilterBall

open Metric

theorem native_allFilter_eventually_locally_le
    {I : Type*} {F : Filter I} {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ.val (u j)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u F v)
    (x : M) {a : ℝ} (ha : v x < (a : EReal)) :
    ∃ V : Set M, V ∈ 𝓝 x ∧ ∀ᶠ j in F, ∀ y ∈ V, u j y ≤ (a : EReal) := by
  obtain ⟨b, hvb, hba⟩ := EReal.exists_rat_btwn_of_lt ha
  have hbaR : (b : ℝ) < a := EReal.coe_lt_coe_iff.mp hba
  let δ : ℝ := (a - (b : ℝ)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpv⟩ := hv.1 e z hz
  let corrected (f : M → EReal) : ComplexModel n → EReal :=
    fun y => chartFunction f e y + (ρ y : EReal)
  let A : ℝ := (b : ℝ) + ρ z
  have htest : corrected v z < (A : EReal) := by
    have hraw : chartFunction v e z < ((b : ℝ) : EReal) := by
      simpa only [chartFunction, z, e.val.left_inv hx] using hvb
    simpa only [corrected, A, EReal.coe_add] using EReal.add_lt_add_right_coe hraw (ρ z)
  have hupper : ∀ᶠ y in 𝓝 z, corrected v y < (A : EReal) := by
    have h := hpv.upperSemicontinuousOn z hzW (A : EReal) htest
    rw [nhdsWithin_eq_nhds.mpr (hρ.1.mem_nhds hzW)] at h
    exact h
  have hρcont : ContinuousAt ρ z :=
    ((hρ.2.2.1 z hzW).contDiffAt (hρ.1.mem_nhds hzW)).continuousAt
  have hρlow : ∀ᶠ y in 𝓝 z, ρ z - δ < ρ y :=
    hρcont.eventually (lt_mem_nhds (sub_lt_self _ hδ))
  have hnhds : {y | y ∈ W ∧ corrected v y < (A : EReal) ∧ ρ z - δ < ρ y} ∈ 𝓝 z := by
    filter_upwards [hρ.1.mem_nhds hzW, hupper, hρlow] with y hyW hyA hyρ
    exact ⟨hyW, hyA, hyρ⟩
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhds_iff.mp hnhds
  let U : Set (ComplexModel n) := ball z ε
  let r : ℝ := ε / 4
  let K : Set (ComplexModel n) := closedBall z (3 * r)
  have hr : 0 < r := by dsimp [r]; positivity
  have hKU : K ⊆ U := closedBall_subset_ball (by dsimp [r]; linarith)
  have hUW : U ⊆ W := fun y hy => (hlocal hy).1
  have hUt : U ⊆ e.val.target := hUW.trans hρ.2.1
  have hKt : K ⊆ e.val.target := hKU.trans hUt
  have hcpsh (f : M → EReal) (hf : IsThetaPshPotential θ.val f) :
      PlurisubharmonicOn (corrected f) U :=
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      hf.1 e hρ).mono hUW
  have hne (f : M → EReal) (hf : IsThetaPshPotential θ.val f) :
      ∃ y ∈ U, corrected f y ≠ ⊥ := by
    obtain ⟨y, hyU, hy⟩ := hf.2.exists_chart_ne_bot e isOpen_ball hUt (mem_ball_self hε)
    exact ⟨y, hyU, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot (ρ y)⟩⟩
  have hcorrL1 : Tendsto (fun j => ∫⁻ y in K,
      canonicalERealAbsDiff (corrected (u j) y) (corrected v y) ∂volume) F (𝓝 0) := by
    have h := hlim e K (isCompact_closedBall z (3 * r)) hKt
    simpa only [chartL1EDistance, corrected, FirstPass.canonicalERealAbsDiff_add_coe] using h
  have hlocalBound : ∀ᶠ j in F, ∀ y ∈ ball z r,
      corrected (u j) y ≤ ((A + δ : ℝ) : EReal) :=
    allFilter_eventually_le_on_ball
      (fun j => hcpsh (u j) (hu j)) (hcpsh v hv) (convex_ball z ε).isPreconnected
      (fun j => hne (u j) (hu j)) (hne v hv) volume z hr hKU
      (fun y hy => (hlocal (hKU hy)).2.1.le) hcorrL1 hδ
  let V : Set M := e.val.source ∩ e.val ⁻¹' ball z r
  have hVopen : IsOpen V := e.val.isOpen_inter_preimage isOpen_ball
  have hxV : x ∈ V := ⟨hx, mem_ball_self hr⟩
  refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
  filter_upwards [hlocalBound] with j hj
  intro y hy
  have hyU : e.val y ∈ U := (ball_subset_ball (by dsimp [r]; linarith)) hy.2
  have hρy := (hlocal hyU).2.2
  have hbound := hj (e.val y) hy.2
  change u j (e.val.symm (e.val y)) + (ρ (e.val y) : EReal) ≤
    ((A + δ : ℝ) : EReal) at hbound
  rw [e.val.left_inv hy.1] at hbound
  have htarget : ((A + δ : ℝ) : EReal) ≤ (a : EReal) + (ρ (e.val y) : EReal) := by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    dsimp only [A, δ] at hρy ⊢
    linarith
  exact (EReal.addLECancellable_coe (ρ (e.val y))).add_le_add_iff_right.mp
    (hbound.trans htarget)


variable [CompactSpace M] [Nonempty M]

/-- Compact nested actual zero-superlevel sets preserve normalization for ANY original index type. -/
theorem native_sup_zero_of_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hsup : ∀ i, (⨆ x, u i x) = 0)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume))) :
    (⨆ x, v x) = 0 := by
  have hle (i : ι) (x : M) : u i x ≤ 0 := hsup i ▸ le_iSup (u i) x
  obtain ⟨S, _hS, hSne, _hantiS, hg, hantiW, heq⟩ :=
    native_exists_genuine_events hu hv hlim
      (C := 0) (fun i x => by simpa using hle i x)
  let W (k : ℕ) : M → EReal := uscRegularization (⨆ i : S k, u i.val)
  have hWle (k : ℕ) : W k ≤ fun _ => (0 : EReal) := by
    have hsupLe : (⨆ i : S k, u i.val) ≤ fun _ : M => (0 : EReal) := by
      intro x
      simp only [iSup_apply]
      exact iSup_le (fun i => hle i.val x)
    simpa only [uscRegularization_const] using uscRegularization_mono hsupLe
  have hvle (x : M) : v x ≤ 0 := by
    have h := congrFun heq x
    simp only [iInf_apply] at h
    rw [← h]
    exact (iInf_le (fun k => W k x) 0).trans (hWle 0 x)
  let Z (k : ℕ) : Set M := (W k) ⁻¹' Ici 0
  have hZclosed (k : ℕ) : IsClosed (Z k) :=
    (hg k).1.quasiPlurisubharmonic.upperSemicontinuous.isClosed_preimage 0
  have hZne (k : ℕ) : (Z k).Nonempty := by
    obtain ⟨i, hi⟩ := hSne k
    obtain ⟨x, hx⟩ := exists_eq_zero_of_sup_eq_zero (hu i) (hsup i)
    refine ⟨x, ?_⟩
    change 0 ≤ W k x
    rw [← hx]
    have hsupRead : u i x ≤ (⨆ j : S k, u j.val) x := by
      simp only [iSup_apply]
      exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
    exact hsupRead.trans (le_uscRegularization _ x)
  have hZsucc (k : ℕ) : Z (k + 1) ⊆ Z k := by
    intro x hx
    exact hx.trans (hantiW (Nat.le_succ k) x)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    Z hZsucc hZne (hZclosed 0).isCompact hZclosed
  have hxv : 0 ≤ v x := by
    have h := congrFun heq x
    simp only [iInf_apply] at h
    rw [← h]
    exact le_iInf (fun k => mem_iInter.mp hx k)
  have hxzero : v x = 0 := le_antisymm (hvle x) hxv
  apply le_antisymm (iSup_le hvle)
  rw [← hxzero]
  exact le_iSup v x



open ThetaPshL1Topology

/-- The global supremum of every genuine potential is a finite attained real number. -/
theorem native_exists_real_sup {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ c : ℝ, (⨆ x, u x) = (c : EReal) ∧ ∃ x, u x = (c : EReal) := by
  obtain ⟨c, hc, x, hx⟩ := DivisorialDomination.exists_eq_max_of_isThetaPshPotential hu
  refine ⟨c, le_antisymm (iSup_le hc) ?_, x, hx⟩
  rw [← hx]
  exact le_iSup u x

/-- Real supremum on the ENTIRE genuine class; finiteness is proved above. -/
def nativeSup (u : ThetaPshL1 θ.val) : ℝ := (⨆ x, u.val x).toReal

@[simp] theorem nativeSup_coe (u : ThetaPshL1 θ.val) :
    (nativeSup u : EReal) = ⨆ x, u.val x := by
  obtain ⟨c, hc, _⟩ := native_exists_real_sup u.property
  simp only [nativeSup, hc, EReal.toReal_coe]

theorem native_le_sup (u : ThetaPshL1 θ.val) (x : M) : u.val x ≤ (nativeSup u : EReal) := by
  rw [nativeSup_coe]
  exact le_iSup u.val x

theorem native_attains_sup (u : ThetaPshL1 θ.val) : ∃ x, u.val x = (nativeSup u : EReal) := by
  obtain ⟨c, hc, x, hx⟩ := native_exists_real_sup u.property
  exact ⟨x, by rw [nativeSup_coe, hc, hx]⟩

/-- Literal addition of a finite constant in the original potential class. -/
def nativeAdd (u : ThetaPshL1 θ.val) (c : ℝ) : ThetaPshL1 θ.val :=
  ⟨fun x => u.val x + (c : EReal), u.property.add_const c⟩

@[simp] theorem nativeSup_add (u : ThetaPshL1 θ.val) (c : ℝ) :
    nativeSup (nativeAdd u c) = nativeSup u + c := by
  apply EReal.coe_injective
  rw [nativeSup_coe, EReal.coe_add]
  apply le_antisymm
  · exact iSup_le (fun x => add_le_add (native_le_sup u x) le_rfl)
  · obtain ⟨x, hx⟩ := native_attains_sup u
    rw [← hx]
    exact le_iSup (nativeAdd u c).val x

/-- Actual finite normalization, including all pole values. -/
def nativeNormalize (u : ThetaPshL1 θ.val) : ThetaPshL1 θ.val :=
  nativeAdd u (-nativeSup u)

@[simp] theorem nativeSup_normalize (u : ThetaPshL1 θ.val) :
    nativeSup (nativeNormalize u) = 0 := by simp [nativeNormalize]

omit [CompactSpace M] [Nonempty M] in
@[simp] theorem native_normalize_reconstruct (u : ThetaPshL1 θ.val) :
    nativeAdd (nativeNormalize u) (nativeSup u) = u := by
  apply Subtype.ext
  funext x
  change u.val x + ((-nativeSup u : ℝ) : EReal) + (nativeSup u : EReal) = u.val x
  rw [add_assoc, ← EReal.coe_add]
  simp


omit [CompactSpace M] [Nonempty M] in
/-- A finite constant upper bound survives actual canonical L1 convergence
along ANY nontrivial original filter. Only a newly selected error sequence
is countable; it is not claimed cofinal in the original filter. -/
theorem native_le_const_of_L1 {I : Type*} {F : Filter I} [NeBot F]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u F v) {a : ℝ}
    (hle : ∀ᶠ i in F, ∀ x, u i x ≤ (a : EReal)) : ∀ x, v x ≤ (a : EReal) := by
  intro x
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpv⟩ := hv.1 e z hz
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 z hzW
  let K : Set (ComplexModel n) := closedBall z (ε / 2)
  let O : Set (ComplexModel n) := ball z (ε / 2)
  have hKW : K ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hεW
  have hOW : O ⊆ W := ball_subset_closedBall.trans hKW
  have hKt : K ⊆ e.val.target := hKW.trans hρ.2.1
  let err (i : I) := chartL1EDistance (u i) v e K
  have he : Tendsto err F (𝓝 0) := hlim e K (isCompact_closedBall _ _) hKt
  have hex (k : ℕ) : ∃ i, (∀ y, u i y ≤ (a : EReal)) ∧
      err i < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by positivity
    exact (hle.and (he.eventually (gt_mem_nhds hpos))).exists
  choose t ht using hex
  have htlim : Tendsto (fun k => err (t k)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => zero_le) (fun k => (ht k).2.le)
  have hfinite (f : M → EReal) (hf : IsThetaPshPotential θ.val f) :
      ∀ᵐ y ∂volume.restrict K, chartFunction f e y ≠ ⊤ ∧ chartFunction f e y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKt (hf.quasiPshPotential.ae_finite_chart e)
  obtain ⟨ns, _, hconv⟩ := exists_strictMono_tendsto_ae_eReal_of_lintegral_canonicalERealAbsDiff
    (fun k => (hu (t k)).quasiPshPotential.aemeasurable_chart_restrict e hKt)
    (hv.quasiPshPotential.aemeasurable_chart_restrict e hKt)
    (fun k => hfinite _ (hu (t k))) (hfinite _ hv) htlim
  have haeK : ∀ᵐ y ∂volume.restrict K, chartFunction v e y ≤ (a : EReal) := by
    filter_upwards [hconv] with y hy
    exact le_of_tendsto_of_tendsto hy tendsto_const_nhds
      (Eventually.of_forall (fun k => (ht (ns k)).1 (e.val.symm y)))
  have haeO : ∀ᵐ y ∂volume.restrict O,
      chartFunction v e y + (ρ y : EReal) ≤ ((a + ρ y : ℝ) : EReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall haeK]
      with y hy
    simpa only [EReal.coe_add] using add_le_add hy (le_refl (ρ y : EReal))
  have hcont : ContinuousOn (fun y => ((a + ρ y : ℝ) : EReal)) O :=
    continuous_coe_real_ereal.comp_continuousOn (continuousOn_const.add (hρ.2.2.1.continuousOn.mono hOW))
  have hpoint := (hpv.mono hOW).le_of_ae_le isOpen_ball hcont.upperSemicontinuousOn volume
    haeO z (mem_ball_self (half_pos hε))
  rw [EReal.coe_add] at hpoint
  have hraw := (EReal.addLECancellable_coe (ρ z)).add_le_add_iff_right.mp hpoint
  simpa only [chartFunction, z, e.val.left_inv hx] using hraw

/-- The complete global upper event follows from actual local Hartogs events
and one finite neighborhood cover of the compact manifold. -/
theorem native_eventually_sup_le_of_L1 {I : Type*} {F : Filter I}
    {u : I → ThetaPshL1 θ.val} {v : ThetaPshL1 θ.val}
    (hlim : Tendsto u F (𝓝 v)) {b : ℝ} (hb : nativeSup v < b) :
    ∀ᶠ i in F, nativeSup (u i) ≤ b := by
  have hl := tendsto_iff_manifoldL1LocallyTendsto.mp hlim
  have hlocal (x : M) : ∃ V : Set M, V ∈ 𝓝 x ∧
      ∀ᶠ i in F, ∀ y ∈ V, (u i).val y ≤ (b : EReal) :=
    native_allFilter_eventually_locally_le (fun i => (u i).property) v.property hl x
      ((native_le_sup v x).trans_lt (EReal.coe_lt_coe_iff.mpr hb))
  choose V hV hbound using hlocal
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover V hV
  have hevent : ∀ᶠ i in F, ∀ x ∈ t, ∀ y ∈ V x, (u i).val y ≤ (b : EReal) :=
    (eventually_all_finset t).mpr (fun x _ => hbound x)
  filter_upwards [hevent] with i hi
  apply EReal.coe_le_coe_iff.mp
  rw [nativeSup_coe]
  apply iSup_le
  intro y
  have hy : y ∈ ⋃ x ∈ t, V x := by rw [ht]; trivial
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp hy
  exact hi x hx y hy

/-- The real global supremum is continuous on the ENTIRE genuine class
for its full chart-Lp topology, with all original filters retained. -/
theorem native_continuous_sup : Continuous (nativeSup (θ := θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_contra hbad
    have hfreq : ∃ᶠ u : ThetaPshL1 θ.val in 𝓝 v, nativeSup u ≤ a := by
      simpa only [Filter.Frequently, not_le] using hbad
    let F := 𝓝 v ⊓ 𝓟 {u : ThetaPshL1 θ.val | nativeSup u ≤ a}
    have : NeBot F := by
      exact (Filter.frequently_iff_neBot).mp hfreq
    have hlim : Tendsto (id : ThetaPshL1 θ.val → ThetaPshL1 θ.val) F (𝓝 v) :=
      tendsto_id.mono_left inf_le_left
    have hdom : ∀ᶠ u : ThetaPshL1 θ.val in F, ∀ x, u.val x ≤ (a : EReal) := by
      filter_upwards [show ∀ᶠ u : ThetaPshL1 θ.val in F, nativeSup u ≤ a from
        mem_of_superset (show {u : ThetaPshL1 θ.val | nativeSup u ≤ a} ∈ F from
          Filter.mem_inf_of_right (by simp)) (fun _ h => h)] with u hu x
      exact (native_le_sup u x).trans (EReal.coe_le_coe hu)
    have hvle := native_le_const_of_L1 (fun u : ThetaPshL1 θ.val => u.property) v.property
      (tendsto_iff_manifoldL1LocallyTendsto.mp hlim) hdom
    have hsup : nativeSup v ≤ a := EReal.coe_le_coe_iff.mp (by
      rw [nativeSup_coe]
      exact iSup_le hvle)
    exact (not_le_of_gt ha) hsup
  · intro b hb
    obtain ⟨c, hvc, hcb⟩ := exists_between hb
    exact (native_eventually_sup_le_of_L1 tendsto_id hvc).mono (fun u hu => hu.trans_lt hcb)


variable [ConnectedSpace M]

/-- Every ultrafilter of sup-normalized genuine potentials has a genuine
normalized limit in the full chart-Lp topology; original index type unrestricted. -/
theorem native_normalized_ultrafilter_limit {I : Type*} (U : Ultrafilter I)
    (u : I → ThetaPshL1 θ.val) (hnorm : ∀ i, nativeSup (u i) = 0) :
    ∃ v : ThetaPshL1 θ.val, nativeSup v = 0 ∧ Tendsto u (U : Filter I) (𝓝 v) := by
  have hs (i : I) : (⨆ x, (u i).val x) = 0 := by
    rw [← nativeSup_coe, hnorm i]
    rfl
  have hle (i : I) (x : M) : (u i).val x ≤ 0 := hs i ▸ le_iSup (u i).val x
  have hz (i : I) : ∃ x, 0 ≤ (u i).val x := by
    obtain ⟨x, hx⟩ := exists_eq_zero_of_sup_eq_zero (u i).property (hs i)
    exact ⟨x, hx.ge⟩
  obtain ⟨v, hv, hweak⟩ :=
    NaturalThetaPshWeakLimitRealization.exists_genuine_weak_limit_of_normalized
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) U
      (fun i => (u i).val) (fun i => (u i).property) hle hz
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · have hsup := native_sup_zero_of_weak_tests (fun i => (u i).property) hv hs hweak
    simp only [nativeSup, hsup, EReal.toReal_zero]
  · apply tendsto_iff_manifoldL1LocallyTendsto.mpr
    exact native_manifoldL1_of_weak_tests (fun i => (u i).property) hv hweak
      (C := 0) (fun i x => by simpa using hle i x)

/-- The whole finite-sup strip is compact for the actual chart-Lp topology.
The proof uses arbitrary ultrafilters and a scalar compact interval. -/
theorem native_isCompact_sup_strip (a b : ℝ) :
    IsCompact {u : ThetaPshL1 θ.val | a ≤ nativeSup u ∧ nativeSup u ≤ b} := by
  let S := {u : ThetaPshL1 θ.val // a ≤ nativeSup u ∧ nativeSup u ≤ b}
  have hcompact : IsCompact (univ : Set S) := by
    apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro U _
    let c : S → ℝ := fun u => nativeSup u.val
    have hIcc : Icc a b ∈ Ultrafilter.map c U := by
      apply Ultrafilter.mem_map.mpr
      exact Filter.Eventually.of_forall (fun u => u.property)
    obtain ⟨d, hd, hUd⟩ := isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map c U) hIcc
    have hcd : Tendsto c (U : Filter S) (𝓝 d) := by
      exact hUd
    obtain ⟨w, hw, hUw⟩ := native_normalized_ultrafilter_limit U
      (fun u : S => nativeNormalize u.val) (fun u => nativeSup_normalize u.val)
    let v : ThetaPshL1 θ.val := nativeAdd w d
    have hv : a ≤ nativeSup v ∧ nativeSup v ≤ b := by
      simpa only [v, nativeSup_add, hw, zero_add] using (show a ≤ d ∧ d ≤ b from hd)
    have hlim : Tendsto (fun u : S => u.val) (U : Filter S) (𝓝 v) := by
      apply tendsto_iff_manifoldL1LocallyTendsto.mpr
      have ht := (tendsto_iff_manifoldL1LocallyTendsto.mp hUw).add_tendsto_const hcd
      have heq : (fun u : S => fun x => (nativeNormalize u.val).val x + (c u : EReal)) =
          fun u : S => u.val.val := by
        funext u
        exact congrArg Subtype.val (native_normalize_reconstruct u.val)
      simpa only [heq, v, nativeAdd] using ht
    refine ⟨⟨v, hv⟩, mem_univ _, ?_⟩
    have ht : Tendsto (id : S → S) (U : Filter S) (𝓝 (⟨v, hv⟩ : S)) := by
      exact tendsto_subtype_rng.mpr hlim
    exact Filter.tendsto_id'.mp ht
  have himage := hcompact.image (continuous_subtype_val : Continuous (fun u : S => u.val))
  have heq : (fun u : S => u.val) '' (univ : Set S) =
      {u : ThetaPshL1 θ.val | a ≤ nativeSup u ∧ nativeSup u ≤ b} := by
    ext u
    constructor
    · rintro ⟨v, _, rfl⟩
      exact v.property
    · intro hu
      exact ⟨⟨u, hu⟩, mem_univ _, rfl⟩
  rwa [heq] at himage



omit [Nonempty M] in
/-- Full original chart-local L1 convergence of arbitrary directed decreasing
nets. Local smooth-potential balls cover each actual compact chart set. -/
theorem native_decreasing_net_L1 {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → M → EReal} (hu : ∀ i, IsThetaPshPotential θ.val (u i))
    (hanti : ∀ x, Antitone (fun i => u i x)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ x, u i x) :
    IsThetaPshPotential θ.val (fun x => ⨅ i, u i x) ∧
      ManifoldL1LocallyTendsto (n := n) u atTop (fun x => ⨅ i, u i x) ∧
      Tendsto (fun i => ⨆ x, u i x) atTop (𝓝 (⨆ x, ⨅ i, u i x)) := by
  obtain ⟨hv, hsup⟩ := SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    hu hanti a ha
  refine ⟨hv, ?_, hsup⟩
  intro e K hK hKt
  let v : M → EReal := fun x => ⨅ i, u i x
  let error (i : I) (z : ComplexModel n) :=
    canonicalERealAbsDiff (chartFunction (u i) e z) (chartFunction v e z)
  change Tendsto (fun i => ∫⁻ z in K, error i z) atTop (𝓝 0)
  refine hK.induction_on (p := fun S => Tendsto (fun i => ∫⁻ z in S, error i z) atTop (𝓝 0))
    ?_ ?_ ?_ ?_
  · simp only [setLIntegral_empty]
    exact tendsto_const_nhds
  · intro A B hAB hB
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
      (fun _ => zero_le) (fun i => lintegral_mono_set hAB)
  · intro A B hA hB
    have hh : Tendsto (fun i => (∫⁻ z in A, error i z) + ∫⁻ z in B, error i z)
        atTop (𝓝 0) := by simpa only [add_zero] using hA.add hB
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _ => zero_le) (fun i => lintegral_union_le (error i) A B)
  · intro z hzK
    obtain ⟨W, ρ, hzW, hρ, _⟩ := hv.1 e z (hKt hzK)
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hρ.1 z hzW
    let B : Set (ComplexModel n) := closedBall z (r / 2)
    have hBr : B ⊆ ball z r := closedBall_subset_ball (half_lt_self hr)
    have hBt : B ⊆ e.val.target := hBr.trans (hrW.trans hρ.2.1)
    have hreal := SGPT.PSH.tendsto_theta_chartLocalL1_iInf_of_compact_antitone_iSup_lower_bound
      hu hanti a ha e (hρ.mono isOpen_ball hrW) (convex_ball z r).isPreconnected
      (nonempty_ball.mpr hr) volume (isCompact_closedBall z (r / 2)) hBr
    have heq (i : I) : (∫⁻ y in B, error i y) = ENNReal.ofReal
        (∫ y in B, ‖(chartFunction (u i) e y).toReal - (chartFunction v e y).toReal‖) := by
      have hi := ((hu i).quasiPshPotential.integrableOn_chart_toReal e
        (isCompact_closedBall z (r / 2)) hBt).sub
        (hv.quasiPshPotential.integrableOn_chart_toReal e (isCompact_closedBall z (r / 2)) hBt)
      have hread := ofReal_integral_eq_lintegral_ofReal hi.norm (Eventually.of_forall (fun y => norm_nonneg _))
      simp only [Pi.sub_apply] at hread
      change (∫⁻ y in B, error i y) = _
      rw [show ENNReal.ofReal (∫ y in B, ‖(chartFunction (u i) e y).toReal - (chartFunction v e y).toReal‖) =
        ∫⁻ y in B, ENNReal.ofReal ‖(chartFunction (u i) e y).toReal - (chartFunction v e y).toReal‖ from hread]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hBt ((hu i).quasiPshPotential.ae_finite_chart e),
        ae_restrict_of_ae_restrict_of_subset hBt (hv.quasiPshPotential.ae_finite_chart e)] with y huy hvy
      dsimp only [error]
      rw [← EReal.coe_toReal huy.1 huy.2, ← EReal.coe_toReal hvy.1 hvy.2,
        canonicalERealAbsDiff_coe_coe]
      simp only [EReal.toReal_coe, Real.norm_eq_abs]
    refine ⟨B, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds z (half_pos hr)), ?_⟩
    have ht := ENNReal.tendsto_ofReal hreal
    have ht' : Tendsto (fun i => ENNReal.ofReal
        (∫ y in B, ‖(chartFunction (u i) e y).toReal - (chartFunction v e y).toReal‖)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, v, B] using ht
    exact ht'.congr (fun i => (heq i).symm)


section SourcePolar
open OpensRestrictionMeasure
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- A genuine original theta-PSH function supplies actual local PSH pole witnesses. -/
theorem source_poles_locallyPluripolar {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) : A.LocallyPluripolar {y | u y = ⊥} := by
  intro x
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
  refine ⟨U, hg.1, hxU, fun y => u y + (g y : EReal), hu.2 U g hg, ?_⟩
  intro y hy
  exact EReal.add_eq_bot_iff.mpr (Or.inl hy.1)

/-- Actual theta-PSH supremum discrepancy is locally pluripolar without
any Kähler hypothesis on the original manifold. -/
theorem source_theta_sup_exceptional {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm A} {u : I → X → EReal}
    (hu : ∀ i, A.IsThetaPSH θ (u i)) {C : ℝ}
    (hC : ∀ i x, u i x ≤ (C : EReal)) :
    A.LocallyPluripolar {x | (⨆ i, u i x) < SGPT.PSH.uscSup u x} := by
  apply A.locallyPluripolar_of_in_chart
  intro i z hz
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ ((A.chart i).symm z)
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  let σ := g ∘ (A.chart i).symm
  let f := fun j y => A.coordinate (u j) i y + (σ y : EReal)
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
  have hzD : z ∈ D := ⟨hz, hxU⟩
  have hp (j : I) : PlurisubharmonicOn (f j) D := ((hu j).2 U g hg).chartPlurisubharmonic i
  have hb := locallyBounded_corrected_family_of_majorant upperSemicontinuous_const
    (fun _ => EReal.coe_ne_top C) hC hg.1 hg.2.1 i
  have hmodel := SGPT.PSH.SupremumPluripolar.locallyPluripolarOn_sup_exceptional hD f hp hb
  apply locallyPluripolarAt_of_inter_subset (hmodel z hzD) (hD.mem_nhds hzD)
  intro y hy
  have hs : (fun y => ⨆ j, f j y) =
      (fun y => (⨆ j, A.coordinate (u j) i y) + (σ y : EReal)) := by
    funext y
    exact iSup_add_coe (fun j => A.coordinate (u j) i y) (σ y)
  have hσ : ContinuousAt σ y :=
    (((hg.2.1 i) y hy.2).contDiffAt (hD.mem_nhds hy.2)).continuousAt
  have hreg : SGPT.PSH.uscSup f y =
      SGPT.PSH.uscSup u ((A.chart i).symm y) + (σ y : EReal) := by
    unfold SGPT.PSH.uscSup
    rw [hs, uscRegularization_add_coe_continuousAt_apply _ hσ]
    change SGPT.PSH.uscSup (fun j => A.coordinate (u j) i) y + (σ y : EReal) = _
    rw [A.uscSup_coordinateFamily u i hy.2.1]
    rfl
  change (⨆ j, f j y) < SGPT.PSH.uscSup f y
  rw [congrFun hs y, hreg]
  exact EReal.add_lt_add_right_coe hy.1.2 (σ y)
end SourcePolar

section OriginalAtlas
variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [CompactSpace X] [ConnectedSpace X]

/-- Whole corrected compactness clause, for the original arbitrary-dimension
atlas, original closed tensor and ENTIRE original class with its full L1 topology. -/
theorem source_isCompact_sup_strip (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (a b : ℝ) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    IsCompact {u : A.SourceAtlasThetaPotentialL1 θ |
      a ≤ (⨆ y, u.val y).toReal ∧ (⨆ y, u.val y).toReal ≤ b} := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  let h := A.sourceConnectedThetaL1Homeomorph x θ
  have hc := native_isCompact_sup_strip (θ := A.sourceConnectedNativeForm x θ) a b
  have ht := hc.image h.symm.continuous
  have heq : h.symm '' {u | a ≤ nativeSup u ∧ nativeSup u ≤ b} =
      {u : A.SourceAtlasThetaPotentialL1 θ |
        a ≤ (⨆ y, u.val y).toReal ∧ (⨆ y, u.val y).toReal ≤ b} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hu
      exact ⟨h u, hu, h.symm_apply_apply u⟩
  rwa [heq] at ht

/-- Whole corrected continuity clause on the ENTIRE original source class. -/
theorem source_continuous_sup (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    Continuous (fun u : A.SourceAtlasThetaPotentialL1 θ => (⨆ y, u.val y).toReal) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  exact native_continuous_sup.comp (A.sourceConnectedThetaL1Homeomorph x θ).continuous

/-- Whole corrected decreasing-NET corollary: literal original infimum,
actual source theta-PSH, all original chart errors and original global sup. -/
theorem source_decreasing_net {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (A : VariableComplexAtlas X) (x : X) (θ : AtlasClosedRealOneOneForm A)
    {u : I → X → EReal} (hu : ∀ i, A.IsThetaPSH θ (u i))
    (hanti : ∀ y, Antitone (fun i => u i y)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ y, u i y) :
    A.IsThetaPSH θ (fun y => ⨅ i, u i y) ∧
      A.SourceAtlasCanonicalL1Tendsto u atTop (fun y => ⨅ i, u i y) ∧
      Tendsto (fun i => ⨆ y, u i y) atTop (𝓝 (⨆ y, ⨅ i, u i y)) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  have hn (i : I) := (A.sourceConnected_isThetaPSH_iff x θ (u i)).mp (hu i)
  obtain ⟨hv, hl, hs⟩ := native_decreasing_net_L1 (θ := A.sourceConnectedNativeForm x θ)
    hn hanti a ha
  exact ⟨(A.sourceConnected_isThetaPSH_iff x θ _).mpr hv,
    (A.sourceConnected_manifoldL1_iff x u atTop _).mp hl, hs⟩

/-- A bound on a nonpluripolar subset internally forces one uniform finite
global sup bound for the ENTIRE original theta-PSH class. -/
theorem source_nonpluripolar_uniform_sup (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (K : Set X) (hK : A.NonPluripolar K) (C₀ : ℝ) :
    ∃ C₁ : ℝ, ∀ u : A.SourceAtlasThetaPotentialL1 θ,
      (∀ y ∈ K, u.val y ≤ (C₀ : EReal)) → (⨆ y, u.val y).toReal ≤ C₁ := by
  classical
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let E := A.sourceConnectedThetaL1EquivNative x θ
  let Θ := A.sourceConnectedNativeForm x θ
  by_contra hbad
  push Not at hbad
  have hex (j : ℕ) : ∃ u : A.SourceAtlasThetaPotentialL1 θ,
      (∀ y ∈ K, u.val y ≤ (C₀ : EReal)) ∧ C₀ + (j : ℝ) + 1 < nativeSup (E u) :=
    hbad (C₀ + (j : ℝ) + 1)
  choose u huK huc using hex
  let w (j : ℕ) := nativeNormalize (E (u j))
  have hwg (j : ℕ) : IsThetaPshPotential Θ.val (w j).val := (w j).property
  have hwzero (j : ℕ) : (⨆ y, (w j).val y) = 0 := by
    rw [← nativeSup_coe, nativeSup_normalize]
    rfl
  have hwle (j : ℕ) (y : X) : (w j).val y ≤ 0 := hwzero j ▸ le_iSup (w j).val y
  have hwK (j : ℕ) (y : X) (hy : y ∈ K) : (w j).val y ≤ ((-(j : ℝ) : ℝ) : EReal) := by
    change (u j).val y + ((-nativeSup (E (u j)) : ℝ) : EReal) ≤ _
    have hh := add_le_add (huK j y hy) (le_refl ((-nativeSup (E (u j)) : ℝ) : EReal))
    apply hh.trans
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith [huc j]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hnorm (j : ℕ) : ∃ y, 0 ≤ (w j).val y := by
    obtain ⟨y, hy⟩ := exists_eq_zero_of_sup_eq_zero (hwg j) (hwzero j)
    exact ⟨y, hy.ge⟩
  obtain ⟨v, hv, hweak⟩ :=
    NaturalThetaPshWeakLimitRealization.exists_genuine_weak_limit_of_normalized
      (LocalPotentials.closedRealOneOne_hasLocalPotentials Θ) U
      (fun j => (w j).val) hwg hwle hnorm
  obtain ⟨S, hS, _, _, _, _, _⟩ := native_exists_genuine_events hwg hv hweak
    (C := 0) (fun j y => by simpa using hwle j y)
  let T (k : ℕ) : Set ℕ := S k ∩ Ici k
  have hT (k : ℕ) : T k ∈ (U : Filter ℕ) :=
    inter_mem (hS k) (hU (Ici_mem_atTop k))
  have hTne (k : ℕ) : (T k).Nonempty := Filter.nonempty_of_mem (hT k)
  let V (k : ℕ) : X → EReal := uscRegularization (⨆ j : T k, (w j.val).val)
  have hVg (k : ℕ) : IsThetaPshPotential Θ.val (V k) := by
    let : Nonempty (T k) := (hTne k).to_subtype
    exact native_usc_iSup_of_le (fun j => hwg j.val)
      (C := 0) (fun j y => by simpa using hwle j.val y)
  have hvV (k : ℕ) : v ≤ V k := by
    apply le_of_chart_weak_limit_eventually_le hwg hv (hVg k) hweak
    filter_upwards [hT k] with j hj
    intro y
    have hraw : (w j).val y ≤ (⨆ l : T k, (w l.val).val) y := by
      simp only [iSup_apply]
      exact le_iSup (fun l : T k => (w l.val).val y) ⟨j, hj⟩
    exact hraw.trans (le_uscRegularization _ y)
  let Z (k : ℕ) : Set X := {y | (⨆ j : T k, (w j.val).val y) < V k y}
  have hZ (k : ℕ) : A.LocallyPluripolar (Z k) := by
    let : Nonempty (T k) := (hTne k).to_subtype
    have hs (j : T k) : A.IsThetaPSH θ (w j.val).val :=
      (A.sourceConnected_isThetaPSH_iff x θ _).mpr (hwg j.val)
    have hh := source_theta_sup_exceptional hs (C := 0)
      (fun j y => by simpa using hwle j.val y)
    simpa only [sourceUscSup_eq_native, Z, V, iSup_apply] using hh
  have hvsource : A.IsThetaPSH θ v := (A.sourceConnected_isThetaPSH_iff x θ v).mpr hv
  let P : ℕ → Set X := fun k => if k = 0 then {y | v y = ⊥} else Z (k - 1)
  have hP (k : ℕ) : A.LocallyPluripolar (P k) := by
    by_cases hk : k = 0
    · simpa only [P, if_pos hk] using source_poles_locallyPluripolar hvsource
    · simpa only [P, if_neg hk] using hZ (k - 1)
  apply hK
  apply (VariableComplexAtlas.LocallyPluripolar.iUnion hP).mono
  intro y hy
  by_cases hex : ∃ k, y ∈ Z k
  · obtain ⟨k, hk⟩ := hex
    apply mem_iUnion.mpr
    refine ⟨k + 1, ?_⟩
    simpa only [P, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel] using hk
  · have hyZ (k : ℕ) : y ∉ Z k := fun h => hex ⟨k, h⟩
    have hbelow (k : ℕ) : v y ≤ ((-(k : ℝ) : ℝ) : EReal) := by
      have hno : V k y ≤ ⨆ j : T k, (w j.val).val y := le_of_not_gt (hyZ k)
      apply (hvV k y).trans (hno.trans (iSup_le (fun j => ?_)))
      exact (hwK j.val y hy).trans (EReal.coe_le_coe (neg_le_neg (by exact_mod_cast j.property.2)))
    have hybot : v y = ⊥ := by
      apply (EReal.eq_bot_iff_forall_lt _).mpr
      intro c
      obtain ⟨k, hk⟩ := exists_nat_gt (-c)
      exact (hbelow k).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    exact mem_iUnion.mpr ⟨0, by change v y = ⊥; exact hybot⟩

/-- Whole relative compactness clause of the corrected nonpluripolar remark,
with the actual closure in the entire original chart-L1 potential class. -/
theorem source_nonpluripolar_isCompact_closure (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (K : Set X) (hK : A.NonPluripolar K) (a b : ℝ) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    IsCompact (closure {u : A.SourceAtlasThetaPotentialL1 θ |
      (a : EReal) ≤ ⨆ y : K, u.val y.val ∧ (⨆ y : K, u.val y.val) ≤ (b : EReal)}) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  obtain ⟨B, hB⟩ := source_nonpluripolar_uniform_sup A x θ K hK b
  let T := {u : A.SourceAtlasThetaPotentialL1 θ |
    a ≤ (⨆ y, u.val y).toReal ∧ (⨆ y, u.val y).toReal ≤ max a B}
  have hTcompact : IsCompact T := source_isCompact_sup_strip A x θ a (max a B)
  have hTclosed : IsClosed T := isClosed_Icc.preimage (source_continuous_sup A x θ)
  have hsub : {u : A.SourceAtlasThetaPotentialL1 θ |
      (a : EReal) ≤ ⨆ y : K, u.val y.val ∧ (⨆ y : K, u.val y.val) ≤ (b : EReal)} ⊆ T := by
    intro u hu
    have hupper : ∀ y ∈ K, u.val y ≤ (b : EReal) := by
      intro y hy
      exact (le_iSup (fun z : K => u.val z.val) ⟨y, hy⟩).trans hu.2
    have hlower : (a : EReal) ≤ ⨆ y, u.val y :=
      hu.1.trans (iSup_le (fun y : K => le_iSup u.val y.val))
    have hn : (⨆ y, u.val y) =
        (nativeSup (A.sourceConnectedThetaL1EquivNative x θ u) : EReal) :=
      (nativeSup_coe (A.sourceConnectedThetaL1EquivNative x θ u)).symm
    refine ⟨?_, (hB u hupper).trans (le_max_right a B)⟩
    rw [hn, EReal.coe_le_coe_iff] at hlower
    exact hlower
  exact hTcompact.of_isClosed_subset isClosed_closure (closure_minimal hsub hTclosed)


/-- Nonpluripolarity internally makes every actual restricted supremum finite,
so its real interpretation never collapses a pole or an infinite value. -/
theorem source_nonpluripolar_supOn_real (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (K : Set X) (hK : A.NonPluripolar K)
    (u : A.SourceAtlasThetaPotentialL1 θ) :
    ∃ c : ℝ, (⨆ y : K, u.val y.val) = (c : EReal) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  have hu := (A.sourceConnected_isThetaPSH_iff x θ u.val).mp u.property
  obtain ⟨c, hc, _⟩ := native_exists_real_sup hu
  have hupper : (⨆ y : K, u.val y.val) ≤ (c : EReal) := by
    rw [← hc]
    exact iSup_le (fun y : K => le_iSup u.val y.val)
  have htop : (⨆ y : K, u.val y.val) ≠ ⊤ := ne_of_lt (hupper.trans_lt (EReal.coe_lt_top c))
  have hbot : (⨆ y : K, u.val y.val) ≠ ⊥ := by
    intro hb
    apply hK
    apply (source_poles_locallyPluripolar u.property).mono
    intro y hy
    change u.val y = ⊥
    apply le_bot_iff.mp
    rw [← hb]
    exact le_iSup (fun z : K => u.val z.val) ⟨y, hy⟩
  exact ⟨(⨆ y : K, u.val y.val).toReal, (EReal.coe_toReal htop hbot).symm⟩

/-- Literal real-sup formulation of the whole relatively compact source set. -/
theorem source_nonpluripolar_real_isCompact_closure (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (K : Set X) (hK : A.NonPluripolar K) (a b : ℝ) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    IsCompact (closure {u : A.SourceAtlasThetaPotentialL1 θ |
      a ≤ (⨆ y : K, u.val y.val).toReal ∧ (⨆ y : K, u.val y.val).toReal ≤ b}) := by
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  have heq : {u : A.SourceAtlasThetaPotentialL1 θ |
      a ≤ (⨆ y : K, u.val y.val).toReal ∧ (⨆ y : K, u.val y.val).toReal ≤ b} =
      {u : A.SourceAtlasThetaPotentialL1 θ |
      (a : EReal) ≤ ⨆ y : K, u.val y.val ∧ (⨆ y : K, u.val y.val) ≤ (b : EReal)} := by
    ext u
    obtain ⟨c, hc⟩ := source_nonpluripolar_supOn_real A x θ K hK u
    simp only [mem_ofPred_eq, hc, EReal.toReal_coe, EReal.coe_le_coe_iff]
  rw [heq]
  exact source_nonpluripolar_isCompact_closure A x θ K hK a b

/-- The corollary also gives literal topological convergence in the whole
original source class and ordinary REAL supremum convergence. -/
theorem source_decreasing_net_topological {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (A : VariableComplexAtlas X) (x : X) (θ : AtlasClosedRealOneOneForm A)
    (u : I → A.SourceAtlasThetaPotentialL1 θ)
    (hanti : ∀ y, Antitone (fun i => (u i).val y)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ y, (u i).val y) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    ∃ v : A.SourceAtlasThetaPotentialL1 θ, v.val = (fun y => ⨅ i, (u i).val y) ∧
      Tendsto u atTop (𝓝 v) ∧
      Tendsto (fun i => (⨆ y, (u i).val y).toReal) atTop (𝓝 (⨆ y, v.val y).toReal) := by
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  obtain ⟨hv, hl, _⟩ := source_decreasing_net A x θ (fun i => (u i).property) hanti a ha
  let v : A.SourceAtlasThetaPotentialL1 θ := ⟨fun y => ⨅ i, (u i).val y, hv⟩
  have ht : Tendsto u atTop (𝓝 v) := (A.sourceAtlasThetaPotentialL1_tendsto_iff x θ u v).mpr hl
  exact ⟨v, rfl, ht, (source_continuous_sup A x θ).continuousAt.tendsto.comp ht⟩

end OriginalAtlas

end SGPT.PSH.ConnectedThetaPSHCompactness
