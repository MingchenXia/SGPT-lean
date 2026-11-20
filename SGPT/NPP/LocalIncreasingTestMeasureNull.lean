import SGPT.NPP.LocalIncreasingDeficit
import SGPT.NPP.LocalIncreasingUpperGaps
import SGPT.NPP.CapacityConvergenceLocalSource
import SGPT.Foundations.Analysis.Pending.ThetaCapacityChart

/-!
Actual bounded global test measures vanish on original increasing deficits
inside a genuine original chart. Local potentials and their bounds are
ordinary geometric chart data; no capacity-null or measure-null conclusion
is an input. The later compact-cover consumer produces these local data
from the original two closed backgrounds. Plan: compact-lower-gap.tex.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.LocalIncreasingCapacityDraft

open Set Filter MeasureTheory TopologicalSpace
open Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual local PSH approximation and genuine relative-capacity theorem
annihilate every bounded original global test measure on its true deficit. -/
theorem bounded_test_measure_deficit_eq_zero_on_chart
    (ω : KahlerBackground n M)
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hDU : ∀ z ∈ (D : Set (ComplexModel n)), e.val.symm z ∈ (U : Set M))
    (ρ η : ComplexModel n → ℝ)
    (hρ : IsSmoothLocalPotential (atlasClosedFormToNative α).val e D ρ)
    (hη : IsSmoothLocalPotential ω.form.val e D η)
    (hae : ∀ᵐ z, z ∈ (D : Set (ComplexModel n)) →
      Tendsto (fun j => u j (e.val.symm z)) atTop (𝓝 (v (e.val.symm z))))
    {w : M → EReal} (hw : IsThetaPshPotential ω.form.val w)
    {c d L : ℝ} (hcd : c ≤ d) (hL0 : 0 ≤ L)
    (hwb : ∀ x, (c : EReal) ≤ w x ∧ w x ≤ (d : EReal))
    (hηb : ∀ z ∈ (D : Set (ComplexModel n)), |η z| ≤ L)
    (E : Set M)
    (hE : E ⊆ (ThetaCapacityChart.diagSlotChart ω.form e D hη.2.1 η hη).source)
    (hgap : ∀ x ∈ E, (⨆ j, u j x) < v x) :
    diagonalPotentialMeasure ω.form w hw E = 0 := by
  let a : ℕ → ComplexModel n → EReal := fun j z => u j (e.val.symm z) + (ρ z : EReal)
  let b : ComplexModel n → EReal := fun z => v (e.val.symm z) + (ρ z : EReal)
  have ha : ∀ j, PlurisubharmonicOn (a j) D := fun j =>
    CapacityConvergence.plurisubharmonicOn_chart_of_isThetaPSHOn (hu j) e hDU hρ
  have hb : PlurisubharmonicOn b D :=
    CapacityConvergence.plurisubharmonicOn_chart_of_isThetaPSHOn hv e hDU hρ
  have ham : ∀ z ∈ (D : Set (ComplexModel n)), Monotone fun j => a j z := by
    intro z hz i j hij
    exact add_le_add (hm _ (hDU z hz) hij) le_rfl
  have hat : ∀ᵐ z, z ∈ (D : Set (ComplexModel n)) →
      Tendsto (fun j => a j z) atTop (𝓝 (b z)) := by
    filter_upwards [hae] with z hz hzD
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (ρ z)))
      (Or.inr (EReal.coe_ne_top (ρ z)))).tendsto.comp
        ((hz hzD).prodMk_nhds tendsto_const_nhds)
  have hzero := relCapacity_deficit_eq_zero_of_monotone_ae
    (D := D) (O := D) le_rfl ha hb ham hat
  have himage : e.val '' E ⊆ {z | z ∈ D ∧ (⨆ j, a j z) < b z} := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : x ∈ e.val.source := (hE hx).1
    have hxD : e.val x ∈ D := (hE hx).2
    refine ⟨hxD, ?_⟩
    change (⨆ j, u j (e.val.symm (e.val x)) + (ρ (e.val x) : EReal)) <
      v (e.val.symm (e.val x)) + (ρ (e.val x) : EReal)
    rw [e.val.left_inv hxS, ← NegligibleSetNotCharged.iSup_add_coe]
    exact EReal.add_lt_add_right_coe (hgap x hx) _
  have hrel : relCapacity D (e.val '' E) = 0 :=
    le_antisymm ((relCapacity_mono himage).trans_eq hzero) bot_le
  have hbound := ThetaCapacityChart.diagonalPotentialMeasure_le_relCapacity
    hw e D hη.2.1 η hη hcd hL0 hwb hηb E hE
  rw [hrel, mul_zero] at hbound
  exact le_antisymm hbound bot_le

/-- Actual simultaneous local-potential data for the PSH background and
capacity background. No nullness or convergence conclusion is stored. -/
structure CommonLocalCapacityChart
    (ω : KahlerBackground n M) (α : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) (x : M) where
  chart : ComplexChart n M
  domain : Opens (ComplexModel n)
  alphaPotential : ComplexModel n → ℝ
  omegaPotential : ComplexModel n → ℝ
  alpha_valid : IsSmoothLocalPotential (atlasClosedFormToNative α).val chart domain alphaPotential
  omega_valid : IsSmoothLocalPotential ω.form.val chart domain omegaPotential
  source_mem : x ∈ chart.val.source
  coordinate_mem : chart.val x ∈ domain
  domain_inside : ∀ z ∈ (domain : Set (ComplexModel n)), chart.val.symm z ∈ (U : Set M)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  omega_bounded : ∀ z ∈ (domain : Set (ComplexModel n)), |omegaPotential z| ≤ bound

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The two original closed backgrounds internally produce the common
chart geometry, including a genuine bounded local Kähler potential. -/
theorem nonempty_commonLocalCapacityChart
    (ω : KahlerBackground n M) (α : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {x : M} (hx : x ∈ (U : Set M)) :
    Nonempty (CommonLocalCapacityChart ω α U x) := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  let z : ComplexModel n := e.val x
  have hzt : z ∈ e.val.target := e.val.map_source hxs
  obtain ⟨A, ρ, hzA, hρ⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative α) e z hzt
  obtain ⟨B, η, hzB, hη⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials ω.form e z hzt
  have hzU : z ∈ e.val.target ∩ e.val.symm ⁻¹' (U : Set M) := by
    refine ⟨hzt, ?_⟩
    simpa only [z, mem_preimage, e.val.left_inv hxs] using hx
  have hnb : A ∩ B ∩ (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)) ∈ 𝓝 z :=
    inter_mem (inter_mem (hρ.1.mem_nhds hzA) (hη.1.mem_nhds hzB))
      ((e.val.isOpen_inter_preimage_symm U.isOpen).mem_nhds hzU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnb
  let D : Opens (ComplexModel n) := ⟨ball z (r / 2), isOpen_ball⟩
  have hclosed : closedBall z (r / 2) ⊆ ball z r := closedBall_subset_ball (by linarith)
  have hDsmall : (D : Set (ComplexModel n)) ⊆ ball z r :=
    ball_subset_closedBall.trans hclosed
  have hDA : (D : Set (ComplexModel n)) ⊆ A := fun y hy => (hball (hDsmall hy)).1.1
  have hDB : (D : Set (ComplexModel n)) ⊆ B := fun y hy => (hball (hDsmall hy)).1.2
  obtain ⟨L, hL⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
    (hη.2.2.1.continuousOn.mono (fun y hy => (hball (hclosed hy)).1.2))
  have hL0 : 0 ≤ L := (norm_nonneg (η z)).trans
    (hL z (mem_closedBall_self (by linarith)))
  exact ⟨⟨e, D, ρ, η, hρ.mono isOpen_ball hDA, hη.mono isOpen_ball hDB,
    hxs, mem_ball_self (by linarith),
    fun y hy => (hball (hDsmall hy)).2.2, L, hL0,
    fun y hy => by simpa only [Real.norm_eq_abs] using hL y (ball_subset_closedBall hy)⟩⟩

/-- The true original increasing deficit is null on every compact core for
every actual bounded global Kähler-PSH measure. All chart data are produced. -/
theorem bounded_test_measure_compact_deficit_eq_zero
    (ω : KahlerBackground n M)
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (hae : NetChartTendstoAEOn (n := n) U u v)
    {w : M → EReal} (hw : IsThetaPshPotential ω.form.val w) (hwb : IsBoundedPotential w)
    {C : Set M} (hC : IsCompact C) (hCU : C ⊆ U)
    (hgap : ∀ x ∈ C, (⨆ j, u j x) < v x) :
    diagonalPotentialMeasure ω.form w hw C = 0 := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact measure_empty
  obtain ⟨c, d, hwbd⟩ := hwb
  obtain ⟨x₀, hx₀⟩ := hCne
  have hcd : c ≤ d := EReal.coe_le_coe_iff.mp ((hwbd x₀).1.trans (hwbd x₀).2)
  have hlocal : ∀ x : C, ∃ N : Set M, IsOpen N ∧ x.1 ∈ N ∧
      diagonalPotentialMeasure ω.form w hw (C ∩ N) = 0 := by
    intro x
    let P := Classical.choice (nonempty_commonLocalCapacityChart ω α U (hCU x.2))
    let N := (ThetaCapacityChart.diagSlotChart ω.form P.chart P.domain
      P.omega_valid.2.1 P.omegaPotential P.omega_valid).source
    refine ⟨N, N.isOpen, ⟨P.source_mem, P.coordinate_mem⟩, ?_⟩
    have hDom : IsOpen (P.chart.val.target ∩ P.chart.val.symm ⁻¹' (U : Set M)) :=
      P.chart.val.isOpen_inter_preimage_symm U.isOpen
    have hAE := hae P.chart
    rw [ae_restrict_iff' hDom.measurableSet] at hAE
    have hat : ∀ᵐ z, z ∈ (P.domain : Set (ComplexModel n)) →
        Tendsto (fun j => u j (P.chart.val.symm z)) atTop
          (𝓝 (v (P.chart.val.symm z))) := by
      filter_upwards [hAE] with z hz hzD
      exact hz ⟨P.alpha_valid.2.1 hzD, P.domain_inside z hzD⟩
    exact bounded_test_measure_deficit_eq_zero_on_chart ω α U hu hv hm
      P.chart P.domain P.domain_inside P.alphaPotential P.omegaPotential
      P.alpha_valid P.omega_valid hat hw hcd P.bound_nonneg hwbd P.omega_bounded
      (C ∩ N) inter_subset_right (fun y hy => hgap y hy.1)
  choose N hNo hxN hNzero using hlocal
  obtain ⟨t, htcover⟩ := hC.elim_nhds_subcover' (fun x hx => N ⟨x, hx⟩)
    (fun x hx => (hNo ⟨x, hx⟩).mem_nhds (hxN ⟨x, hx⟩))
  have hsub : C ⊆ ⋃ x : t, C ∩ N x.1 := by
    intro y hy
    obtain ⟨x, hxt, hyN⟩ := mem_iUnion₂.mp (htcover hy)
    exact mem_iUnion.mpr ⟨⟨x, hxt⟩, hy, hyN⟩
  exact measure_mono_null hsub (measure_iUnion_null fun x : t => hNzero x.1)

end SGPT.NPP.LocalIncreasingCapacityDraft
