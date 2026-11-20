import SGPT.Okounkov.TranscendentalWNEnvelopeContact
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables for measures of top forms along holomorphic parametrizations (WN-CONV6)

Blueprint `tok-wn-conv6:inner` (chapter `claude-tok-wn-conv6`), the step "transport the integral
chart by chart"; standard.

Let `M` be a compact complex manifold of dimension `N` with a Kähler background `w`, `Φ` a smooth
top-degree form, `U ⊆ ℂᴺ` open and `φ : U → M` continuous, injective and holomorphic in every
atlas chart.  For a measurable `K ⊆ U`,

`(Φ)₊(φ(K)) = ∫_K (φ^*Φ)₊ dλ`   (`topFormMeasure_image`),

where `φ^*Φ` at `y` is read in the chart at `φ(y)` (`coordPullback`; the density does not depend on
the chart, `topDensity_coordPullback_eq`).  The proof covers `M` by countably many charts,
partitions `K` accordingly, and on each piece combines the chart formula of `topFormMeasure`
(`topFormMeasure_image_eq`, WN-ENV), Mathlib's change of variables
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) and the Jacobian law of top densities; the
real Jacobian of a holomorphic map is `|det_ℂ|² ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.ChangeVar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The pullback of a form along `φ : ℂᴺ → M` at `y`, read in the chart `f`. -/
def chartPull {p : ℕ} (Φ : SmoothRealForm N M p) (φ : ComplexModel N → M) (f : ComplexChart N M)
    (y : ComplexModel N) : (ComplexModel N) [⋀^Fin p]→L[ℝ] ℝ :=
  (Φ.coeff f (f.val (φ y))).compContinuousLinearMap (fderiv ℝ (fun y' => f.val (φ y')) y)

/-- The pullback of a form along `φ : ℂᴺ → M` at `y`, read in the preferred chart at `φ(y)`. -/
def coordPullback {p : ℕ} (Φ : SmoothRealForm N M p) (φ : ComplexModel N → M)
    (y : ComplexModel N) : (ComplexModel N) [⋀^Fin p]→L[ℝ] ℝ :=
  chartPull Φ φ (complexChartAt (n := N) (φ y)) y

/-- **Chart independence** of the pullback. -/
theorem chartPull_eq {p : ℕ} (Φ : SmoothRealForm N M p) {φ : ComplexModel N → M}
    {y : ComplexModel N} (hφ : ContinuousAt φ y) {f f' : ComplexChart N M}
    (hf : φ y ∈ f.val.source) (hf' : φ y ∈ f'.val.source)
    (hd : DifferentiableAt ℝ (fun y' => f.val (φ y')) y) :
    chartPull Φ φ f y = chartPull Φ φ f' y := by
  set z := f.val (φ y) with hz
  have hzT : z ∈ (chartTransition f f').source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
    exact ⟨f.val.map_source hf, by rw [hz, f.val.left_inv hf]; exact hf'⟩
  have hTz : chartTransition f f' z = f'.val (φ y) := by
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hz,
      f.val.left_inv hf]
  have hT : DifferentiableAt ℝ (chartTransition f f') z :=
    ((RegularPatchNeighborhood.differentiableOn_chartTransition f f' z hzT).differentiableAt
      ((chartTransition f f').open_source.mem_nhds hzT)).restrictScalars ℝ
  have hev : (fun y' => f'.val (φ y')) =ᶠ[𝓝 y]
      fun y' => chartTransition f f' (f.val (φ y')) := by
    filter_upwards [hφ.eventually (f.val.open_source.mem_nhds hf),
      hφ.eventually (f'.val.open_source.mem_nhds hf')] with y' h1 h2
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv h1]
  have hchain : fderiv ℝ (fun y' => f'.val (φ y')) y =
      (fderiv ℝ (chartTransition f f') z).comp (fderiv ℝ (fun y' => f.val (φ y')) y) := by
    rw [hev.fderiv_eq]
    exact fderiv_comp y hT hd
  unfold chartPull
  rw [hchain, IntegrationCurrent.coeff_eq_compContinuousLinearMap Φ hzT, hTz]
  ext v
  rfl

theorem topDensity_chartPull {φ : ComplexModel N → M} (Φ : SmoothRealForm N M (2 * N))
    (f : ComplexChart N M) (y : ComplexModel N) :
    topDensity (chartPull Φ φ f y) =
      LinearMap.det (fderiv ℝ (fun y' => f.val (φ y')) y : ComplexModel N →ₗ[ℝ] ComplexModel N) *
        topDensity (Φ.coeff f (f.val (φ y))) :=
  topDensity_compContinuousLinearMap _ _

theorem det_nonneg_of_differentiableAt_complex {g : ComplexModel N → ComplexModel N}
    {y : ComplexModel N} (hg : DifferentiableAt ℂ g y) :
    0 ≤ LinearMap.det (fderiv ℝ g y : ComplexModel N →ₗ[ℝ] ComplexModel N) := by
  rw [hg.fderiv_restrictScalars ℝ]
  have h := DivisorialChangeOfVariables.det_restrictScalars_eq_normSq (fderiv ℂ g y)
  rw [ContinuousLinearMap.det] at h
  rw [h]
  exact Complex.normSq_nonneg _

/-- **The coordinate density is continuous** on `U` (Jacobian law in a fixed chart near each point). -/
theorem continuousOn_topDensity_coordPullback (Φ : SmoothRealForm N M (2 * N))
    {U : Set (ComplexModel N)} (hU : IsOpen U) {φ : ComplexModel N → M} (hφc : ContinuousOn φ U)
    (hφd : ∀ (f : ComplexChart N M), ∀ y ∈ U, φ y ∈ f.val.source →
      ContDiffAt ℂ ∞ (fun y' => f.val (φ y')) y) :
    ContinuousOn (fun y => topDensity (coordPullback Φ φ y)) U := by
  intro y₀ hy₀
  set f := complexChartAt (n := N) (φ y₀)
  have hf₀ : φ y₀ ∈ f.val.source := mem_complexChartAt_source _
  have hV : U ∩ φ ⁻¹' f.val.source ∈ 𝓝 y₀ :=
    (hφc.isOpen_inter_preimage hU f.val.open_source).mem_nhds ⟨hy₀, hf₀⟩
  have hcont0 : ContinuousAt φ y₀ := hφc.continuousAt (hU.mem_nhds hy₀)
  -- in the fixed chart `f` near `y₀`
  have heq : (fun y => topDensity (coordPullback Φ φ y)) =ᶠ[𝓝 y₀]
      fun y => LinearMap.det (fderiv ℝ (fun y' => f.val (φ y')) y :
          ComplexModel N →ₗ[ℝ] ComplexModel N) * topDensity (Φ.coeff f (f.val (φ y))) := by
    filter_upwards [hV, eventually_eventually_nhds.mpr hV] with y hy hy'
    rw [coordPullback, chartPull_eq Φ (hφc.continuousAt (hU.mem_nhds hy.1))
      (mem_complexChartAt_source (φ y)) hy.2
      (((hφd _ y hy.1 (mem_complexChartAt_source (φ y))).differentiableAt (by simp)).restrictScalars ℝ),
      topDensity_chartPull]
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.congr ?_ heq.symm
  have hcd := hφd f y₀ hy₀ hf₀
  have hder : ContinuousAt (fun y => fderiv ℝ (fun y' => f.val (φ y')) y) y₀ := by
    have h1 := (hcd.restrict_scalars ℝ).fderiv_right (m := 0) (by simp)
    exact h1.continuousAt
  refine ((ContinuousLinearMap.continuous_det.continuousAt).comp hder).mul ?_
  have hz : f.val (φ y₀) ∈ f.val.target := f.val.map_source hf₀
  have hfc : ContinuousAt (fun y => f.val (φ y)) y₀ :=
    (f.val.continuousAt hf₀).comp hcont0
  have h2 : ContinuousAt (fun y => Φ.coeff f (f.val (φ y))) y₀ :=
    ContinuousAt.comp (f := fun y => f.val (φ y)) (x := y₀)
      ((Φ.smooth f).continuousOn.continuousAt (f.val.open_target.mem_nhds hz)) hfc
  exact continuous_topDensity.continuousAt.comp h2

section Measure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Change of variables on one chart piece.** -/
theorem topFormMeasure_image_of_subset_chart (w : KahlerBackground N M) (Φ : SmoothRealForm N M (2 * N))
    {U : Set (ComplexModel N)} (hU : IsOpen U) {φ : ComplexModel N → M}
    (hφc : ContinuousOn φ U)
    (hφd : ∀ (f : ComplexChart N M), ∀ y ∈ U, φ y ∈ f.val.source →
      DifferentiableAt ℂ (fun y' => f.val (φ y')) y)
    (hinj : InjOn φ U) (f : ComplexChart N M) {K : Set (ComplexModel N)} (hK : MeasurableSet K)
    (hKU : K ⊆ U) (hKf : ∀ y ∈ K, φ y ∈ f.val.source) :
    topFormMeasure w Φ (φ '' K) = ∫⁻ y in K, ENNReal.ofReal (topDensity (coordPullback Φ φ y)) := by
  set g : ComplexModel N → ComplexModel N := fun y => f.val (φ y) with hg
  have hgd : ∀ y ∈ K, HasFDerivWithinAt g (fderiv ℝ g y) K y := fun y hy =>
    ((hφd f y (hKU hy) (hKf y hy)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hginj : InjOn g K := fun a ha b hb hab =>
    hinj (hKU ha) (hKU hb) (f.val.injOn (hKf a ha) (hKf b hb) hab)
  have himK : g '' K ⊆ f.val.target := by
    rintro _ ⟨y, hy, rfl⟩; exact f.val.map_source (hKf y hy)
  have himg : φ '' K = f.val.symm '' (g '' K) := by
    rw [image_image]
    refine image_congr fun y hy => ?_
    exact (f.val.left_inv (hKf y hy)).symm
  rw [himg, topFormMeasure_image_eq w Φ f (measurable_image_of_fderivWithin hK hgd hginj) himK,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hgd hginj]
  refine setLIntegral_congr_fun hK fun y hy => ?_
  have hdet := det_nonneg_of_differentiableAt_complex (hφd f y (hKU hy) (hKf y hy))
  have hcont : ContinuousAt φ y := hφc.continuousAt (hU.mem_nhds (hKU hy))
  rw [coordPullback, ← chartPull_eq Φ hcont (hKf y hy) (mem_complexChartAt_source (φ y))
      ((hφd f y (hKU hy) (hKf y hy)).restrictScalars ℝ), topDensity_chartPull,
    ContinuousLinearMap.det, abs_of_nonneg hdet, ← ENNReal.ofReal_mul hdet]

/-- **Change of variables for top-form measures** along an injective holomorphic
parametrization `φ : U → M`. -/
theorem topFormMeasure_image (w : KahlerBackground N M) (Φ : SmoothRealForm N M (2 * N))
    {U : Set (ComplexModel N)} (hU : IsOpen U) {φ : ComplexModel N → M}
    (hφc : ContinuousOn φ U)
    (hφd : ∀ (f : ComplexChart N M), ∀ y ∈ U, φ y ∈ f.val.source →
      DifferentiableAt ℂ (fun y' => f.val (φ y')) y)
    (hinj : InjOn φ U) {K : Set (ComplexModel N)} (hK : MeasurableSet K) (hKU : K ⊆ U) :
    topFormMeasure w Φ (φ '' K) = ∫⁻ y in K, ENNReal.ofReal (topDensity (coordPullback Φ φ y)) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : K = ∅ := by
      ext y; simp only [mem_empty_iff_false, iff_false]; intro hy
      exact (IsEmpty.false (φ y)).elim
    subst this; simp
  -- a countable atlas
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : M => (complexChartAt (n := N) x).val.source) fun x => (complexChartAt x).val.open_source
  have hTcov : (⋃ x ∈ T, (complexChartAt (n := N) x).val.source) = univ := by
    rw [hTU]; exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h] at hTcov
    simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hTcov
    obtain ⟨x⟩ := hM
    exact (eq_empty_iff_forall_notMem.mp hTcov.symm x) (mem_univ x)
  obtain ⟨xs, rfl⟩ := hTc.exists_eq_range hTne
  set f : ℕ → ComplexChart N M := fun j => complexChartAt (n := N) (xs j) with hf
  -- the pieces
  set S : ℕ → Set (ComplexModel N) := fun j => K ∩ (U ∩ φ ⁻¹' (f j).val.source) with hS
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    hK.inter (hφc.isOpen_inter_preimage hU (f j).val.open_source).measurableSet
  have hSU : (⋃ j, S j) = K := by
    ext y; simp only [mem_iUnion, hS, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨j, hy, -⟩; exact hy
    · intro hy
      have : φ y ∈ ⋃ x ∈ range xs, (complexChartAt (n := N) x).val.source := by
        rw [hTcov]; exact mem_univ _
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := mem_iUnion₂.mp this
      exact ⟨j, hy, hKU hy, hj⟩
  set P := disjointed S with hP
  have hPm : ∀ j, MeasurableSet (P j) := MeasurableSet.disjointed hSm
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed S
  have hPU : (⋃ j, P j) = K := by rw [hP, iUnion_disjointed, hSU]
  have hPS : ∀ j, P j ⊆ S j := disjointed_subset S
  have hPK : ∀ j, P j ⊆ K := fun j y hy => (hPS j hy).1
  have hPf : ∀ j, ∀ y ∈ P j, φ y ∈ (f j).val.source := fun j y hy => (hPS j hy).2.2
  -- images
  have himg : φ '' K = ⋃ j, φ '' P j := by rw [← hPU, image_iUnion]
  have himgm : ∀ j, MeasurableSet (φ '' P j) := by
    intro j
    set g : ComplexModel N → ComplexModel N := fun y => (f j).val (φ y)
    have hgd : ∀ y ∈ P j, HasFDerivWithinAt g (fderiv ℝ g y) (P j) y := fun y hy =>
      ((hφd (f j) y (hKU (hPK j hy)) (hPf j y hy)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hginj : InjOn g (P j) := fun a ha b hb hab =>
      hinj (hKU (hPK j ha)) (hKU (hPK j hb)) ((f j).val.injOn (hPf j a ha) (hPf j b hb) hab)
    have h1 : φ '' P j = (f j).val.symm '' (g '' P j) := by
      rw [image_image]
      exact image_congr fun y hy => ((f j).val.left_inv (hPf j y hy)).symm
    rw [h1]
    exact SmoothMixedMeasureDensity.measurableSet_chartSymm_image (f j) (measurable_image_of_fderivWithin (hPm j) hgd hginj)
      (by rintro _ ⟨y, hy, rfl⟩; exact (f j).val.map_source (hPf j y hy))
  have himgd : Pairwise (Function.onFun Disjoint fun j => φ '' P j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have := hinj (hKU (hPK j hb)) (hKU (hPK i ha)) hab
    subst this
    exact disjoint_left.mp (hPd hij) ha hb
  rw [himg, measure_iUnion himgd himgm, ← hPU, lintegral_iUnion hPm hPd]
  refine tsum_congr fun j => ?_
  exact topFormMeasure_image_of_subset_chart w Φ hU hφc hφd hinj (f j) (hPm j)
    ((hPK j).trans hKU) (hPf j)

omit [CompactSpace M] in
/-- Images of measurable subsets of `U` are measurable. -/
theorem measurableSet_image {U : Set (ComplexModel N)} (hU : IsOpen U) {φ : ComplexModel N → M}
    (hφc : ContinuousOn φ U)
    (hφd : ∀ (f : ComplexChart N M), ∀ y ∈ U, φ y ∈ f.val.source →
      DifferentiableAt ℂ (fun y' => f.val (φ y')) y)
    (hinj : InjOn φ U) {K : Set (ComplexModel N)} (hK : MeasurableSet K) (hKU : K ⊆ U) :
    MeasurableSet (φ '' K) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : φ '' K = ∅ := by
      ext x; exact (IsEmpty.false x).elim
    rw [this]; exact MeasurableSet.empty
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : M => (complexChartAt (n := N) x).val.source) fun x => (complexChartAt x).val.open_source
  have hcov : ∀ x : M, ∃ t ∈ T, x ∈ (complexChartAt (n := N) t).val.source := by
    intro x
    have : x ∈ ⋃ i ∈ T, (complexChartAt (n := N) i).val.source := by
      rw [hTU]; exact mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩
    simpa using this
  have hK' : K = ⋃ t ∈ T, K ∩ (U ∩ φ ⁻¹' (complexChartAt (n := N) t).val.source) := by
    ext y; simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_prop]
    constructor
    · intro hy
      obtain ⟨t, ht, hyt⟩ := hcov (φ y)
      exact ⟨t, ht, hy, hKU hy, hyt⟩
    · rintro ⟨t, -, hy, -⟩; exact hy
  rw [hK', image_iUnion₂]
  refine MeasurableSet.biUnion hTc fun t _ => ?_
  set f := complexChartAt (n := N) t
  set P := K ∩ (U ∩ φ ⁻¹' f.val.source)
  have hPm : MeasurableSet P := hK.inter (hφc.isOpen_inter_preimage hU f.val.open_source).measurableSet
  set g : ComplexModel N → ComplexModel N := fun y => f.val (φ y)
  have hgd : ∀ y ∈ P, HasFDerivWithinAt g (fderiv ℝ g y) P y := fun y hy =>
    ((hφd f y hy.2.1 hy.2.2).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hginj : InjOn g P := fun a ha b hb hab =>
    hinj ha.2.1 hb.2.1 (f.val.injOn ha.2.2 hb.2.2 hab)
  have h1 : φ '' P = f.val.symm '' (g '' P) := by
    rw [image_image]
    exact image_congr fun y hy => (f.val.left_inv hy.2.2).symm
  rw [h1]
  exact SmoothMixedMeasureDensity.measurableSet_chartSymm_image f
    (measurable_image_of_fderivWithin hPm hgd hginj)
    (by rintro _ ⟨y, hy, rfl⟩; exact f.val.map_source hy.2.2)

end Measure

end SGPT.Okounkov.TranscendentalWN.ChangeVar
