import SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain
import Mathlib.Data.Set.Card.Arithmetic

set_option autoImplicit false

/-!
# From a sheet bound on the chart germ to a sheet bound on the subvariety

`Pending.AdaptedProjectionGerm.exists_adaptedProjection` asks for a direction `B`,
a neighbourhood `U` of a point `x` of a subvariety `V` of a manifold, a base set
`Δ` and a sheet number `N`, with at most `N` points of `U ∩ V` over almost every
value of `B ∘ e`, `e` the preferred chart at `x`.  The local analytic geometry of
the project speaks instead about a germ at `0 ∈ ℂⁿ`: the chart germ
`Pending.AnalyticDescendingChain.chartGerm V.carrier x`, which is `e(V)`
translated so that `e(x)` sits at the origin.

This module is the passage between the two, and it changes nothing about the
direction: `exists_adaptedProjection_of_chartGermSheetBound` takes `B` as given
and returns the same `B`, so a germ-level bound with a PRESCRIBED direction — as
in `Pending.IrreducibleGermSheetBound.exists_germSheetBound_near` — yields the
manifold statement with the same prescription.

Two elementary facts do all the work.  The chart is injective on its source, so a
fibre upstairs injects into a fibre of the germ; and the translation by `B(e x)`
in the target is measure-preserving, so the null set of exceptional values is
carried across unchanged.  `exists_sheetBound_iUnion` adds the finite unions,
which is what the decomposition of a germ into its irreducible components needs:
the neighbourhoods intersect, the base sets union, the sheet numbers add.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ChartGermSheetBound

open FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain

variable {n : ℕ}

/-- The conclusion of a sheet bound for a subset `A` of `ℂⁿ` in the direction
`B`, near `0`: a neighbourhood, a finite-volume base set carrying the image, and
one integer bounding the fibre over almost every value. -/
def GermSheetBound {d : ℕ} (A : Set (ComplexModel n))
    (B : ComplexModel n →L[ℂ] ComplexModel d) : Prop :=
  ∃ (U : Set (ComplexModel n)) (Δ : Set (ComplexModel d)) (N : ℕ),
    IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
      MeasurableSet Δ ∧ volume Δ ≠ ⊤ ∧
      (∀ z ∈ A ∩ U, B z ∈ Δ) ∧
      ∀ᵐ y : ComplexModel d, (A ∩ U ∩ B ⁻¹' {y}).encard ≤ (N : ℕ∞)

/-- A sheet bound is inherited by a smaller set. -/
theorem GermSheetBound.mono {d : ℕ} {A A' : Set (ComplexModel n)}
    {B : ComplexModel n →L[ℂ] ComplexModel d} (h : GermSheetBound A B) (hA : A' ⊆ A) :
    GermSheetBound A' B := by
  obtain ⟨U, Δ, N, hU, h0, hΔ, hΔt, hmaps, hfib⟩ := h
  refine ⟨U, Δ, N, hU, h0, hΔ, hΔt, fun z hz => hmaps z ⟨hA hz.1, hz.2⟩, hfib.mono fun y hy => ?_⟩
  exact le_trans (Set.encard_mono (Set.inter_subset_inter_left _
    (Set.inter_subset_inter_left _ hA))) hy

/-- A sheet bound only sees the germ: two sets agreeing near `0` have the same
sheet bounds. -/
theorem GermSheetBound.congr {d : ℕ} {A A' : Set (ComplexModel n)}
    {B : ComplexModel n →L[ℂ] ComplexModel d} (h : GermSheetBound A' B)
    (hAA : A =ᶠ[𝓝 0] A') : GermSheetBound A B := by
  obtain ⟨U, Δ, N, hU, h0, hΔ, hΔt, hmaps, hfib⟩ := h
  obtain ⟨W, hWmem, hWopen, h0W⟩ := mem_nhds_iff.1 hAA
  have hAW : ∀ z ∈ W, (z ∈ A ↔ z ∈ A') := fun z hz => iff_of_eq (hWmem hz)
  refine ⟨U ∩ W, Δ, N, hU.inter hWopen, ⟨h0, h0W⟩, hΔ, hΔt, ?_, hfib.mono fun y hy => ?_⟩
  · rintro z ⟨hzA, hzU, hzW⟩
    exact hmaps z ⟨(hAW z hzW).1 hzA, hzU⟩
  · refine le_trans (Set.encard_mono ?_) hy
    rintro z ⟨⟨hzA, hzU, hzW⟩, hzy⟩
    exact ⟨⟨(hAW z hzW).1 hzA, hzU⟩, hzy⟩

/-- **A finite union of sheet bounds in ONE direction is a sheet bound.**  The
neighbourhoods intersect, the base sets union, the sheet numbers add; the fibre
of a union is the union of the fibres. -/
theorem exists_sheetBound_iUnion {d r : ℕ} {B : ComplexModel n →L[ℂ] ComplexModel d}
    {A : Fin r → Set (ComplexModel n)} (h : ∀ i, GermSheetBound (A i) B) :
    GermSheetBound (⋃ i, A i) B := by
  classical
  choose U Δ N hU h0 hΔ hΔt hmaps hfib using h
  refine ⟨⋂ i, U i, ⋃ i, Δ i, ∑ i, N i, isOpen_iInter_of_finite hU,
    Set.mem_iInter.2 h0, MeasurableSet.iUnion hΔ, ?_, ?_, ?_⟩
  · refine ne_top_of_le_ne_top ?_ (measure_iUnion_fintype_le volume Δ)
    exact ENNReal.sum_ne_top.2 fun i _ => hΔt i
  · rintro z ⟨hzA, hzU⟩
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hzA
    exact Set.mem_iUnion.2 ⟨i, hmaps i z ⟨hzi, Set.mem_iInter.1 hzU i⟩⟩
  · have hall : ∀ᵐ y : ComplexModel d, ∀ i, (A i ∩ U i ∩ B ⁻¹' {y}).encard ≤ (N i : ℕ∞) :=
      (ae_all_iff).2 hfib
    refine hall.mono fun y hy => ?_
    have hsub : (⋃ i, A i) ∩ (⋂ i, U i) ∩ B ⁻¹' {y} ⊆
        ⋃ i, A i ∩ U i ∩ B ⁻¹' {y} := by
      rintro z ⟨⟨hzA, hzU⟩, hzy⟩
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hzA
      exact Set.mem_iUnion.2 ⟨i, ⟨hzi, Set.mem_iInter.1 hzU i⟩, hzy⟩
    calc ((⋃ i, A i) ∩ (⋂ i, U i) ∩ B ⁻¹' {y}).encard
        ≤ (⋃ i, A i ∩ U i ∩ B ⁻¹' {y}).encard := Set.encard_mono hsub
      _ ≤ ∑ i, (A i ∩ U i ∩ B ⁻¹' {y}).encard := Set.encard_iUnion_le_of_fintype _
      _ ≤ ∑ i, (N i : ℕ∞) := Finset.sum_le_sum fun i _ => hy i
      _ = ((∑ i, N i : ℕ) : ℕ∞) := by push_cast; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The manifold form of a chart-germ sheet bound, PROVED.**  If the chart germ
of `V` at `x` has a sheet bound in the direction `B`, then so does `V` itself
near `x`, in the shape `Pending.AdaptedProjectionGerm.exists_adaptedProjection`
asks for, with the SAME `B`.

The chart is injective on its source, so `z ↦ e z - e x` maps a fibre of `B ∘ e`
over `y` injectively into the germ fibre over `y - B(e x)`; and translation by
`B(e x)` preserves Lebesgue measure, so the null set of exceptional values comes
across unchanged. -/
theorem exists_adaptedProjection_of_chartGermSheetBound
    (V : ClosedIrreducibleAnalyticSubvariety n M) (x : M)
    {B : ComplexModel n →L[ℂ] ComplexModel V.dim}
    (h : GermSheetBound (chartGerm (n := n) V.carrier x) B) :
    ∃ (U : Set M) (Δ : Set (ComplexModel V.dim)) (N : ℕ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ (complexChartAt (n := n) x).val.source ∧
        MeasurableSet Δ ∧ volume Δ ≠ ⊤ ∧
        (∀ z ∈ U ∩ V.carrier, B ((complexChartAt (n := n) x).val z) ∈ Δ) ∧
        (∀ᵐ y : ComplexModel V.dim,
          {z | z ∈ U ∩ V.carrier ∧ B ((complexChartAt (n := n) x).val z) = y}.encard
            ≤ (N : ℕ∞)) := by
  classical
  obtain ⟨U₀, Δ₀, N, hU₀, h0U₀, hΔ₀, hΔ₀t, hmaps, hfib⟩ := h
  set e := (complexChartAt (n := n) x).val with he
  set c : ComplexModel V.dim := B (e x) with hc
  -- the neighbourhood upstairs
  set U : Set M := e.source ∩ e ⁻¹' {v : ComplexModel n | v - e x ∈ U₀} with hU
  have hshiftopen : IsOpen {v : ComplexModel n | v - e x ∈ U₀} :=
    hU₀.preimage (continuous_id.sub continuous_const)
  have hUopen : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source hshiftopen
  -- the germ point attached to a point of `U ∩ V`
  have hgerm : ∀ z ∈ U ∩ V.carrier,
      e z - e x ∈ chartGerm (n := n) V.carrier x ∩ U₀ ∧ B (e z) - c = B (e z - e x) := by
    rintro z ⟨⟨hzs, hzU⟩, hzV⟩
    have hsum : e z - e x + e x = e z := sub_add_cancel _ _
    refine ⟨⟨⟨?_, ?_⟩, hzU⟩, by rw [hc, ← map_sub]⟩
    · rw [hsum]; exact e.map_source hzs
    · show e.symm (e z - e x + e x) ∈ V.carrier
      rw [hsum, e.left_inv hzs]
      exact hzV
  refine ⟨U, (fun w : ComplexModel V.dim => w - c) ⁻¹' Δ₀, N, hUopen,
    ⟨mem_complexChartAt_source x, by simpa using h0U₀⟩, Set.inter_subset_left,
    hΔ₀.preimage (measurable_id.sub_const c), ?_, ?_, ?_⟩
  · have hpre : (fun w : ComplexModel V.dim => w - c) ⁻¹' Δ₀
        = (fun w : ComplexModel V.dim => w + (-c)) ⁻¹' Δ₀ := by
      ext w; simp [sub_eq_add_neg]
    rw [hpre, measure_preimage_add_right volume (-c) Δ₀]
    exact hΔ₀t
  · intro z hz
    obtain ⟨hmem, hsub⟩ := hgerm z hz
    show B (e z) - c ∈ Δ₀
    rw [hsub]
    exact hmaps _ hmem
  · -- the almost-everywhere clause, transported by the measure-preserving shift
    have hshift : ∀ᵐ y : ComplexModel V.dim,
        (chartGerm (n := n) V.carrier x ∩ U₀ ∩ B ⁻¹' {y - c}).encard ≤ (N : ℕ∞) := by
      rw [← map_sub_right_ae (volume : Measure (ComplexModel V.dim)) c] at hfib
      exact hfib
    refine hshift.mono fun y hy => ?_
    set S := {z | z ∈ U ∩ V.carrier ∧ B (e z) = y} with hS
    have hinj : Set.InjOn (fun z => e z - e x) S := fun z₁ hz₁ z₂ hz₂ hEq =>
      e.injOn hz₁.1.1.1 hz₂.1.1.1 (sub_left_inj.1 hEq)
    have himg : (fun z => e z - e x) '' S ⊆
        chartGerm (n := n) V.carrier x ∩ U₀ ∩ B ⁻¹' {y - c} := by
      rintro w ⟨z, hz, rfl⟩
      obtain ⟨hmem, hsub⟩ := hgerm z hz.1
      exact ⟨hmem, by rw [Set.mem_preimage, Set.mem_singleton_iff, ← hsub, hz.2]⟩
    calc S.encard = ((fun z => e z - e x) '' S).encard := (hinj.encard_image).symm
      _ ≤ (chartGerm (n := n) V.carrier x ∩ U₀ ∩ B ⁻¹' {y - c}).encard := Set.encard_mono himg
      _ ≤ (N : ℕ∞) := hy

end SGPT.Foundations.Analysis.Pending.ChartGermSheetBound
