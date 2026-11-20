import SGPT.Foundations.Analysis.Pending.SkodaElMirEstimate
import SGPT.Foundations.Analysis.Pending.LogCutoffLevi
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false

/-!
# Skoda--El Mir for a linearly flattened closed set; the diagonal of `X × X`

Let `Δ` be a closed subset of a compact Kähler manifold `M` which, near each of its points, is the
zero set of a `ℂ`-linear map in a chart (`IsLinearlyFlat`; the diagonal of `X × X` in the product
charts, `isLinearlyFlat_diagonal`).  For a closed positive current `T` of bidimension `(k+1, k+1)`
the restrictions `𝟙_{M \ Δ} T` and `𝟙_Δ T` (`CurrentRestriction.restrictCurrent`) are closed
(`isClosedCurrent_restrictCurrent_compl`, `isClosedCurrent_restrictCurrent`;
`demailly-cadg:III.2.3`/`III.2.4` for the complete pluripolar set `Δ = {log ‖Y‖² = -∞}`).

Proof.  Closedness of the positive current `𝟙_{M \ Δ} T` is tested locally with closed
semipositive slots (`ClosedCurrentLocalTests.isClosedCurrent_of_local`).  Near a point of `Δ`
take the flattening chart, `f` supported in `{‖Y‖² < 1}`, a chart bump `h₁ = 1` near `supp f` and
the plurisubharmonic log cut-offs `vᵢ = χ₂ · ρ(log ‖Y‖²/(i+1) + 1)` (`LogCutoffLevi`); near a
point off `Δ` take `vᵢ = 1` and `h₁` supported off `Δ`.  In both cases
`SkodaElMirEstimate.restrictCurrent_closedTestForm_eq_zero` gives
`𝟙_{M \ Δ} T (Π₁₁ d(f dg) ∧ β) = 0`.  Then `𝟙_Δ T = T - 𝟙_{M \ Δ} T`.

This is step B4.3 of the TN.4 plan for Boucksom's criterion (`bou:skoda-elmir-submanifold`): with B4.4 (the support theorem) it
gives `Θ ≥ λ [Δ]` for the closed weak limits `Θ` of bou02 4.10/4.12.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SkodaElMirSubmanifold

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents ClosedCurrentLocalTests
  CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms SkodaElMirEstimate
  CurrentRestriction LogCutoffLevi

section Flat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A set that is, near each of its points, the zero set of a `ℂ`-linear map read in a chart. -/
def IsLinearlyFlat (Δ : Set M) : Prop :=
  ∀ x ∈ Δ, ∃ e : ComplexChart n M, x ∈ e.val.source ∧
    ∃ (c : ℕ) (Y : ComplexModel n →L[ℂ] ComplexModel c),
      ∀ p ∈ e.val.source, p ∈ Δ ↔ Y (e.val p) = 0

/-- A smooth cut-off equal to `1` near a compact subset of an open set and supported in it. -/
theorem exists_cutoff {O : Set (ComplexModel n)} (hO : IsOpen O) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧ ∀ᶠ z in 𝓝ˢ K, χ z = 1 := by
  obtain ⟨χ, h1, hr⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := (⟨O, hO⟩ : TopologicalSpace.Opens (ComplexModel n))) hK hKO
  exact ⟨χ, χ.contDiff, χ.hasCompactSupport, χ.tsupport_subset, fun z => (hr z).1,
    fun z => (hr z).2, h1⟩

omit [IsComplexManifold n M] in
/-- Points where a chart bump does not vanish lie in the chart domain, over the support. -/
theorem chartExtend_ne_zero {e : ComplexChart n M} {χ : ComplexModel n → ℝ} {x : M}
    (hx : chartExtend e χ x ≠ 0) : x ∈ e.val.source ∧ e.val x ∈ tsupport χ := by
  by_cases hxs : x ∈ e.val.source
  · rw [chartExtend_of_mem hxs] at hx
    exact ⟨hxs, subset_tsupport _ hx⟩
  · exact absurd (chartExtend_of_notMem hxs) hx

end Flat

section Assembly

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {k : ℕ}
  {T : ProductCurrent n M (k + 1)}

omit [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The common set-up: a chart bump equal to `1` near the support of `f`. -/
theorem exists_chart_bump (e : ComplexChart n M) {O : Set (ComplexModel n)} (hO : IsOpen O)
    (hOt : O ⊆ e.val.target) {f : M → ℝ} (hfO : tsupport f ⊆ e.val.symm '' O)
    (hfc : IsCompact (tsupport f)) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
      ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, chartExtend e χ y = 1 := by
  have hfs : tsupport f ⊆ e.val.source := hfO.trans (image_symm_subset_source hOt)
  have hKc : IsCompact (e.val '' tsupport f) := hfc.image_of_continuousOn (e.val.continuousOn.mono hfs)
  have hKO : e.val '' tsupport f ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hfO hp
    rw [e.val.right_inv (hOt hz)]
    exact hz
  obtain ⟨χ, hχ, hχc, hχO, hχ0, hχ1, hχK⟩ := exists_cutoff hO hKc hKO
  refine ⟨χ, hχ, hχc, hχO, hχ0, hχ1, fun x hx => ?_⟩
  have hxs : x ∈ e.val.source := hfs hx
  have hev : ∀ᶠ z in 𝓝 (e.val x), χ z = 1 :=
    hχK.filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ hx))
  have hc : ContinuousAt e.val x := e.val.continuousAt hxs
  filter_upwards [hc.eventually hev, e.val.open_source.mem_nhds hxs] with y hy hys
  rw [chartExtend_of_mem hys, hy]

/-- **Near a point off `Δ`.** -/
theorem local_vanishing_of_notMem (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (hΔ : IsClosed Δ) (x : M) :
    ∃ (e : ComplexChart n M) (O : Set (ComplexModel n)), IsOpen O ∧ O ⊆ e.val.target ∧
      (x ∉ Δ → x ∈ e.val.symm '' O) ∧
      ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
        tsupport f ⊆ e.val.symm '' O → IsCompact (tsupport f) →
          ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
            restrictCurrent w T hT Δᶜ (closedTestForm f g hf hg k β) = 0 := by
  set e := complexChartAt (n := n) x
  set O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' Δᶜ
  have hO : IsOpen O := e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target
    hΔ.isOpen_compl
  have hOt : O ⊆ e.val.target := inter_subset_left
  refine ⟨e, O, hO, hOt, fun hx => ⟨e.val x, ⟨e.val.map_source (mem_complexChartAt_source x), ?_⟩,
    e.val.left_inv (mem_complexChartAt_source x)⟩, ?_⟩
  · show e.val.symm (e.val x) ∈ Δᶜ
    rw [e.val.left_inv (mem_complexChartAt_source x)]
    exact hx
  intro f g hf hg hfO hfc β hβ
  obtain ⟨χ, hχ, hχc, hχO, hχ0, hχ1, hχf⟩ := exists_chart_bump e hO hOt hfO hfc
  have hOΔ : ∀ y, chartExtend e χ y ≠ 0 → y ∈ Δᶜ := fun y hy => by
    obtain ⟨hys, hyχ⟩ := chartExtend_ne_zero hy
    have := (hχO hyχ).2
    rwa [mem_preimage, e.val.left_inv hys] at this
  refine restrictCurrent_closedTestForm_eq_zero w hT hTc hβ hΔ.isOpen_compl.measurableSet hf hg e
    hχ hχc (hχO.trans hOt) hχ0 hχ1 hχf (v := fun _ _ => 1) (fun _ => chartSmooth_const 1)
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) ?_ ?_ ?_
  · intro i e' z hz _ u
    rw [ddcForm_coeff, GlobalPotentialTransforms.smoothDDC_const]
    simp
  · intro y hy
    rw [indicator_of_mem (hOΔ y hy), elMirCutoff_one]
    exact tendsto_const_nhds
  · intro y _
    rw [deriv_elMirCutoff_one]
    exact tendsto_const_nhds

/-- **Near a point of `Δ`**, in a flattening chart. -/
theorem local_vanishing_of_mem (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (e : ComplexChart n M) {c : ℕ}
    (Y : ComplexModel n →L[ℂ] ComplexModel c) (hY : ∀ p ∈ e.val.source, p ∈ Δ ↔ Y (e.val p) = 0)
    (hΔm : MeasurableSet Δ) :
    ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
      tsupport f ⊆ e.val.symm '' (e.val.target ∩ {z | ‖Y z‖ ^ 2 < 1}) → IsCompact (tsupport f) →
        ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
          restrictCurrent w T hT Δᶜ (closedTestForm f g hf hg k β) = 0 := by
  intro f g hf hg hfO hfc β hβ
  set O : Set (ComplexModel n) := e.val.target ∩ {z | ‖Y z‖ ^ 2 < 1} with hO_def
  have hO : IsOpen O := e.val.open_target.inter
    (isOpen_lt (contDiff_normSq_comp Y).continuous continuous_const)
  have hOt : O ⊆ e.val.target := inter_subset_left
  obtain ⟨χ, hχ, hχc, hχO, hχ0, hχ1, hχf⟩ := exists_chart_bump e hO hOt hfO hfc
  -- the second cut-off, equal to one near the support of `χ`
  obtain ⟨χ₂, hχ₂, hχ₂c, hχ₂O, hχ₂0, hχ₂1, hχ₂K⟩ := exists_cutoff hO hχc (hχO)
  set V : ℕ → ComplexModel n → ℝ := fun i z => χ₂ z * logCutoff Y i z with hV_def
  have hVd : ∀ i, ContDiff ℝ ∞ (V i) := fun i => hχ₂.mul (contDiff_logCutoff Y i)
  have hVc : ∀ i, HasCompactSupport (V i) := fun i => hχ₂c.mul_right
  have hVt : ∀ i, tsupport (V i) ⊆ e.val.target := fun i =>
    tsupport_mul_subset_left.trans (hχ₂O.trans hOt)
  set v : ℕ → M → ℝ := fun i => chartExtend e (V i) with hv_def
  have hv : ∀ i, ChartSmooth (n := n) (v i) := fun i =>
    chartSmooth_chartExtend e (hVd i) (hVc i) (hVt i)
  have hV0 : ∀ i z, 0 ≤ V i z := fun i z => mul_nonneg (hχ₂0 z) (logCutoff_nonneg Y i z)
  have hV1 : ∀ i z, V i z ≤ 1 := fun i z => by
    by_cases hz : χ₂ z = 0
    · simp [hV_def, hz]
    · have hzO : z ∈ O := hχ₂O (subset_tsupport _ hz)
      have h1 := logCutoff_le_one Y i hzO.2
      have h0 := logCutoff_nonneg Y i z
      calc V i z = χ₂ z * logCutoff Y i z := rfl
        _ ≤ 1 * 1 := mul_le_mul (hχ₂1 z) h1 h0 zero_le_one
        _ = 1 := one_mul 1
  -- near the support of `χ`, `vᵢ` is the log cut-off
  have hloc : ∀ i {z : ComplexModel n}, z ∈ tsupport χ →
      (fun y => v i (e.val.symm y)) =ᶠ[𝓝 z] logCutoff Y i := by
    intro i z hz
    have hev : ∀ᶠ y in 𝓝 z, χ₂ y = 1 := hχ₂K.filter_mono (nhds_le_nhdsSet hz)
    filter_upwards [chartExtend_eventuallyEq (β := V i) (hχO.trans hOt hz), hev] with y hy hy2
    change chartExtend e (V i) (e.val.symm y) = _
    rw [hy, hV_def]
    simp [hy2]
  have hval : ∀ i {y : M}, chartExtend e χ y ≠ 0 → v i y = logCutoff Y i (e.val y) := by
    intro i y hy
    obtain ⟨hys, hyχ⟩ := chartExtend_ne_zero hy
    have := (hloc i hyχ).self_of_nhds
    simpa [e.val.left_inv hys] using this
  -- the limits at a point where `h₁ ≠ 0`
  have hlim : ∀ {y : M}, chartExtend e χ y ≠ 0 →
      (y ∈ Δ ∧ ∀ i, v i y = 0) ∨ (y ∉ Δ ∧ Tendsto (fun i => v i y) atTop (𝓝 1)) := by
    intro y hy
    obtain ⟨hys, -⟩ := chartExtend_ne_zero hy
    by_cases hyΔ : y ∈ Δ
    · left
      refine ⟨hyΔ, fun i => ?_⟩
      rw [hval i hy, logCutoff_of_eq_zero Y i ((hY y hys).mp hyΔ)]
    · right
      refine ⟨hyΔ, ?_⟩
      have hYy : Y (e.val y) ≠ 0 := fun h0 => hyΔ ((hY y hys).mpr h0)
      exact (tendsto_logCutoff Y hYy).congr fun i => (hval i hy).symm
  refine restrictCurrent_closedTestForm_eq_zero w hT hTc hβ hΔm.compl hf hg e
    hχ hχc (hχO.trans hOt) hχ0 hχ1 hχf (v := v) hv
    (fun i y => chartExtend_nonneg (hV0 i) y) (fun i y => chartExtend_le_one (hV1 i) y) ?_ ?_ ?_
  · -- plurisubharmonicity where `h₁ ≠ 0`
    intro i e' z hz hx u
    obtain ⟨hps, hpχ⟩ := chartExtend_ne_zero hx
    have hzs : z ∈ (chartTransition e' e).source := ⟨hz, hps⟩
    rw [KahlerDomination.lineValue_compatible _ e' e hzs u]
    set ze := chartTransition e' e z
    have hze : ze = e.val (e'.val.symm z) := rfl
    rw [ddcForm_coeff, smoothDDC_congr (hloc i (hze ▸ hpχ))]
    exact smoothDDC_logCutoff_nonneg Y i (hχO (hze ▸ hpχ)).2 _
  · -- `θ(vᵢ) → 𝟙_{M \ Δ}`
    intro y hy
    rcases hlim hy with ⟨hyΔ, h0⟩ | ⟨hyΔ, h1⟩
    · rw [indicator_of_notMem (not_not.mpr hyΔ)]
      simp only [h0, elMirCutoff_zero]
      exact tendsto_const_nhds
    · rw [indicator_of_mem hyΔ, ← elMirCutoff_one]
      exact (contDiff_elMirCutoff.continuous.tendsto 1).comp h1
  · -- `θ'(vᵢ) → 0` on the support of `f`
    intro y hfy
    have hy : chartExtend e χ y ≠ 0 := by
      rw [(hχf y (subset_tsupport _ hfy)).self_of_nhds]
      exact one_ne_zero
    rcases hlim hy with ⟨-, h0⟩ | ⟨-, h1⟩
    · simp only [h0, deriv_elMirCutoff_zero]
      exact tendsto_const_nhds
    · rw [← deriv_elMirCutoff_one]
      exact (continuous_deriv_elMirCutoff.tendsto 1).comp h1

/-- **Skoda--El Mir for a linearly flat closed set**: `𝟙_{M \ Δ} T` is closed. -/
theorem isClosedCurrent_restrictCurrent_compl (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (hΔ : IsClosed Δ) (hflat : IsLinearlyFlat (n := n) Δ) :
    IsClosedCurrent (restrictCurrent w T hT Δᶜ) := by
  classical
  have hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
        tsupport f ⊆ U → IsCompact (tsupport f) →
          ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
            restrictCurrent w T hT Δᶜ (closedTestForm f g hf hg k β) = 0 := by
    intro x
    by_cases hx : x ∈ Δ
    · obtain ⟨e, hxe, c, Y, hY⟩ := hflat x hx
      set O : Set (ComplexModel n) := e.val.target ∩ {z | ‖Y z‖ ^ 2 < 1}
      have hO : IsOpen O := e.val.open_target.inter
        (isOpen_lt (contDiff_normSq_comp Y).continuous continuous_const)
      have hOt : O ⊆ e.val.target := inter_subset_left
      refine ⟨e.val.symm '' O, ?_, ⟨e.val x, ⟨e.val.map_source hxe, ?_⟩, e.val.left_inv hxe⟩,
        local_vanishing_of_mem w hT hTc e Y hY hΔ.measurableSet⟩
      · rw [e.val.symm_image_eq_source_inter_preimage hOt]
        exact e.val.isOpen_inter_preimage hO
      · show ‖Y (e.val x)‖ ^ 2 < 1
        rw [(hY x hxe).mp hx, norm_zero]
        norm_num
    · obtain ⟨e, O, hO, hOt, hxO, hvan⟩ := local_vanishing_of_notMem w hT hTc hΔ x
      refine ⟨e.val.symm '' O, ?_, hxO hx, hvan⟩
      rw [e.val.symm_image_eq_source_inter_preimage hOt]
      exact e.val.isOpen_inter_preimage hO
  choose U hUo hxU hU using hloc
  exact isClosedCurrent_of_local w (isPositive_restrictCurrent w T hT Δᶜ) U hUo hxU hU

/-- **Skoda--El Mir for a linearly flat closed set**: `𝟙_Δ T` is closed. -/
theorem isClosedCurrent_restrictCurrent (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (hΔ : IsClosed Δ) (hflat : IsLinearlyFlat (n := n) Δ) :
    IsClosedCurrent (restrictCurrent w T hT Δ) := by
  have h := restrictCurrent_add_compl w T hT hΔ.measurableSet
  have : restrictCurrent w T hT Δ = T - restrictCurrent w T hT Δᶜ := eq_sub_of_add_eq h
  rw [this]
  exact hTc.sub (isClosedCurrent_restrictCurrent_compl w hT hTc hΔ hflat)

end Assembly

/-! ### The diagonal of `X × X` -/

section Diagonal

open scoped ProductComplexManifold
open ProductComplexManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `L(u, u') ↦ u' - u`, whose kernel is the diagonal in a product chart. -/
def diagDifference (n : ℕ) : ComplexModel (n + n) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n) -
    ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap

omit [IsComplexManifold n X] in
/-- **The diagonal is linearly flat**: in the product chart at `(p, p)` it is the kernel of
`L(u, u') ↦ u' - u`. -/
theorem isLinearlyFlat_diagonal :
    IsLinearlyFlat (n := n + n) (M := X × X) (Set.diagonal X) := by
  rintro ⟨p, q⟩ (h : p = q)
  subst h
  set e := complexChartAt (n := n + n) ((p, p) : X × X)
  set a := chartAt (ComplexModel n) p
  have he : e.val = prodChart a a := rfl
  refine ⟨e, mem_complexChartAt_source _, n, diagDifference n, fun y hy => ?_⟩
  rw [he, prodChart_source] at hy
  rw [he]
  simp only [diagDifference, ContinuousLinearMap.coe_comp, Function.comp_apply,
    prodChart_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', sub_eq_zero,
    Set.mem_diagonal_iff]
  exact ⟨fun h => by rw [h], fun h => a.injOn hy.1 hy.2 h.symm⟩

variable [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)] {k : ℕ}
  {T : ProductCurrent (n + n) (X × X) (k + 1)}

/-- **Skoda--El Mir on the diagonal of `X × X`** (`bou:skoda-elmir-submanifold` for `Δ`): for a
closed positive current `T` on `X × X`, `𝟙_Δ T` and `𝟙_{X × X \ Δ} T` are closed. -/
theorem isClosedCurrent_restrictCurrent_diagonal (w : KahlerBackground (n + n) (X × X))
    (hT : IsPositive T) (hTc : IsClosedCurrent T) :
    IsClosedCurrent (restrictCurrent w T hT (Set.diagonal X)) ∧
      IsClosedCurrent (restrictCurrent w T hT (Set.diagonal X)ᶜ) :=
  ⟨isClosedCurrent_restrictCurrent w hT hTc isClosed_diagonal isLinearlyFlat_diagonal,
    isClosedCurrent_restrictCurrent_compl w hT hTc isClosed_diagonal isLinearlyFlat_diagonal⟩

end Diagonal

end SGPT.Foundations.Analysis.Pending.SkodaElMirSubmanifold
