import SGPT.Foundations.Analysis.Pending.SlotTestForms

set_option autoImplicit false

/-!
# Integration by parts against a closed positive current on a compact manifold

For a closed positive current `T` of bidimension `(k + 1, k + 1)` on a compact complex manifold
`M`, closed real `(1,1)`-forms `β₀, …, β_{k-1}` and chart-smooth functions `h`, `u`,

`T (h ddᶜu ∧ β) = T (u ddᶜh ∧ β)`   (`slotForm_ibp_of_compact`).

`SlotTestForms.slotForm_ibp` proves this when `h` has compact support in one chart.  In general,
a chart-smooth partition of unity `(χ_a)` subordinate to the chart domains
(`ChartPartition.exists_chartSmooth_partitionOfUnity`) splits `h = ∑ₐ χ_a h`, each `χ_a h` is the
extension by zero of a smooth function with compact support in one chart target, and both sides
are additive in `h` (only the coefficients at chart points matter,
`SlotTestForms.apply_slotForm_congr'`; `ddᶜ` is additive on chart targets).

This is the integration by parts used by TN-CLASSICAL for the identity
`R_ε = m_ε b + ddᶜ v_ε` on the Levi test forms (B6 step (i-1), `M = X × X`, `h = (φ ∘ e) ∘ p₁` not
supported in one chart of `X × X`); statement agreed on I-0831.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SlotFormCompactIBP

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  PositiveProductCurrents ClosedProductCurrents SmoothDDCForm ChartPartition SlotTestForms
  ClosedCurrentLocalTests

/-- `ddᶜ` of a finite sum of functions smooth on an open set is the sum of the `ddᶜ`s. -/
theorem smoothDDC_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) {g : ι → ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) U)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => ∑ i ∈ s, g i y) z = ∑ i ∈ s, smoothDDC (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [smoothDDC_add hU (hg a (Finset.mem_insert_self a s))
      (ContDiffOn.sum fun i hi => hg i (Finset.mem_insert_of_mem hi)) hz,
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- A function smooth on an open set containing its topological support is smooth. -/
theorem contDiff_of_contDiffOn_of_tsupport_subset {n : ℕ} {V : Set (ComplexModel n)}
    (hV : IsOpen V) {a : ComplexModel n → ℝ} (ha : ContDiffOn ℝ ∞ a V) (haV : tsupport a ⊆ V) :
    ContDiff ℝ ∞ a := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact ha.contDiffAt (hV.mem_nhds hx)
  · have hx' : x ∉ tsupport a := fun h => hx (haV h)
    have hev : a =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hx'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq hev

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A chart-supported function is an extension by zero.**  If `f` is chart-smooth and its
topological support is a compact subset of the domain of the chart `e`, then `f` is the extension
by zero of a smooth function with compact support in `e.target`. -/
theorem exists_eq_chartExtend {f : M → ℝ} (hf : ChartSmooth (n := n) f) (e : ComplexChart n M)
    (hfc : IsCompact (tsupport f)) (hfe : tsupport f ⊆ e.val.source) :
    ∃ G : ComplexModel n → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ e.val.target ∧ chartExtend e G = f := by
  classical
  set K : Set (ComplexModel n) := e.val '' tsupport f with hK_def
  have hKc : IsCompact K := hfc.image_of_continuousOn (e.val.continuousOn.mono hfe)
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.val.map_source (hfe hx)
  set G : ComplexModel n → ℝ := e.val.target.indicator fun z => f (e.val.symm z) with hG_def
  have hGK : tsupport G ⊆ K := by
    refine closure_minimal (fun z hz => ?_) hKc.isClosed
    have hzt : z ∈ e.val.target := by
      by_contra hzt
      exact hz (indicator_of_notMem hzt _)
    have hfz : f (e.val.symm z) ≠ 0 := by
      intro h0
      exact hz (by rw [hG_def, indicator_of_mem hzt, h0])
    exact ⟨e.val.symm z, subset_tsupport _ hfz, e.val.right_inv hzt⟩
  have hGt : tsupport G ⊆ e.val.target := hGK.trans hKt
  have hGon : ContDiffOn ℝ ∞ G e.val.target :=
    (hf e).congr fun z hz => indicator_of_mem hz _
  refine ⟨G, contDiff_of_contDiffOn_of_tsupport_subset e.val.open_target hGon hGt,
    hKc.of_isClosed_subset (isClosed_tsupport _) hGK, hGt, funext fun x => ?_⟩
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx, hG_def, indicator_of_mem (e.val.map_source hx), e.val.left_inv hx]
  · rw [chartExtend_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport fun h => hx (hfe h)).symm

/-- `slotForm_ibp` for a chart-smooth `h` with compact support in one chart domain. -/
theorem slotForm_ibp_of_tsupport_subset {k : ℕ} {T : ProductCurrent n M (k + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) (β : Fin k → ClosedRealOneOneForm n M)
    {f u : M → ℝ} (hf : ChartSmooth (n := n) f) (hu : ChartSmooth (n := n) u)
    (e : ComplexChart n M) (hfc : IsCompact (tsupport f)) (hfe : tsupport f ⊆ e.val.source) :
    T (slotForm (smulFun f hf (ddcForm u hu)) k β) =
      T (slotForm (smulFun u hu (ddcForm f hf)) k β) := by
  obtain ⟨G, hGd, hGc, hGt, hGf⟩ := exists_eq_chartExtend hf e hfc hfe
  have key : ∀ (f' : M → ℝ) (hf' : ChartSmooth (n := n) f'), f' = f →
      T (slotForm (smulFun f' hf' (ddcForm u hu)) k β) =
        T (slotForm (smulFun u hu (ddcForm f' hf')) k β) →
      T (slotForm (smulFun f hf (ddcForm u hu)) k β) =
        T (slotForm (smulFun u hu (ddcForm f hf)) k β) := by
    intro f' hf' hff' H
    subst hff'
    exact H
  exact key _ _ hGf (slotForm_ibp hT hTc β e hGd hGc hGt hu)

/-- **Integration by parts against a closed positive current on a compact manifold**:
`T (h ddᶜu ∧ β) = T (u ddᶜh ∧ β)` for all chart-smooth `h`, `u`. -/
theorem slotForm_ibp_of_compact [CompactSpace M] {k : ℕ} {T : ProductCurrent n M (k + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T)
    (β : Fin k → ClosedRealOneOneForm n M) {h u : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hu : ChartSmooth (n := n) u) :
    T (slotForm (smulFun h hh (ddcForm u hu)) k β) =
      T (slotForm (smulFun u hu (ddcForm h hh)) k β) := by
  classical
  -- a chart-smooth partition of unity subordinate to the chart domains
  obtain ⟨m, χ, idx, hχs, -, hχsupp, hχc, hχ1⟩ := exists_chartSmooth_partitionOfUnity (n := n)
    (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
      (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
    (fun x => ⟨x, mem_complexChartAt_source x⟩)
  set g : Fin m → M → ℝ := fun a x => χ a x * h x with hg_def
  have hg : ∀ a, ChartSmooth (n := n) (g a) := fun a e => (hχs a e).mul (hh e)
  have hsum : ∀ x, h x = ∑ a, g a x := fun x => by
    rw [hg_def]
    simp only
    rw [← Finset.sum_mul, hχ1, one_mul]
  -- each piece has compact support in one chart domain
  have hpiece : ∀ a, T (slotForm (smulFun (g a) (hg a) (ddcForm u hu)) k β) =
      T (slotForm (smulFun u hu (ddcForm (g a) (hg a))) k β) := by
    intro a
    have hga : tsupport (g a) ⊆ tsupport (χ a) :=
      closure_mono fun x hx => by
        by_contra h0
        exact hx (by rw [hg_def]; simp only; rw [Function.notMem_support.mp h0, zero_mul])
    exact slotForm_ibp_of_tsupport_subset hT hTc β (hg a) hu (complexChartAt (n := n) (idx a))
      ((hχc a).of_isClosed_subset (isClosed_tsupport _) hga) (hga.trans (hχsupp a))
  -- additivity of the left side in `h`
  have hL : T (slotForm (smulFun h hh (ddcForm u hu)) k β) =
      ∑ a, T (slotForm (smulFun (g a) (hg a) (ddcForm u hu)) k β) := by
    rw [apply_slotForm_congr' hT β (γ' := ∑ a, smulFun (g a) (hg a) (ddcForm u hu))
      fun e z _ => by rw [coeff_sum, smulFun_coeff, hsum, Finset.sum_smul]; rfl,
      slotForm_sum, map_sum]
  -- additivity of the right side in `h` (on chart targets)
  have hR : T (slotForm (smulFun u hu (ddcForm h hh)) k β) =
      ∑ a, T (slotForm (smulFun u hu (ddcForm (g a) (hg a))) k β) := by
    rw [apply_slotForm_congr' hT β (γ' := ∑ a, smulFun u hu (ddcForm (g a) (hg a)))
      fun e z hz => ?_, slotForm_sum, map_sum]
    have hfun : (fun y => h (e.val.symm y)) = fun y => ∑ a, g a (e.val.symm y) :=
      funext fun y => hsum _
    rw [coeff_sum, smulFun_coeff, ddcForm_coeff, hfun,
      smoothDDC_finset_sum Finset.univ e.val.open_target (fun a _ => hg a e) hz, Finset.smul_sum]
    rfl
  rw [hL, hR]
  exact Finset.sum_congr rfl fun a _ => hpiece a

end SGPT.Foundations.Analysis.Pending.SlotFormCompactIBP
