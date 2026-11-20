import SGPT.Checks.Comparison.TraceInfimumSliceLimit
import SGPT.NAPotential.TraceResNATrace

/-! The ORIGINAL actual trace cutoff of the ORIGINAL actual NA infimum.
Blueprint: `trace-na-decreasing-limit.tex`. Endpoint convergence is produced
from actual whole-target generic readers, never assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition
open scoped Topology ENNReal

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The actual original intrinsic NA order transfers actual traceability
of the SAME slice along the SAME target map, across original backgrounds. -/
theorem sliceTraceable_of_naOrder {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (h : SourceNAPOrder Γ Δ) (ι : V → M) (κ : SourceKahlerForm n M) {s : ℝ}
    (hs : SliceTraceable ι Γ κ s) : SliceTraceable ι Δ κ s := by
  have hc := (sourceNAPOrder_iff_component Γ Δ κ).mp h
  refine ⟨hs.1.trans_le hc.cutoff_le, ?_⟩
  exact SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
    ((Γ.component κ).val.native_thetaPSH ⟨s,hs.1⟩)
    (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder (hc.slice_le s hs.1)) hs.2

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- A genuinely traceable lower original NA curve gives well-defined trace
of EVERY actual original upper curve. -/
theorem traceWellDefined_of_naOrder {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (h : SourceNAPOrder Γ Δ) {ι : V → M} (hwd : TraceWellDefined ι Γ) : TraceWellDefined ι Δ := by
  intro κ
  obtain ⟨s, hs⟩ := hwd κ
  exact ⟨s, fun r hr => sliceTraceable_of_naOrder h ι κ (hs r hr)⟩

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- Actual intrinsic original order makes the ACTUAL original trace cutoff
monotone; no cutoff comparison is supplied. -/
theorem traceCutoff_mono_of_naOrder {Γ : SourceNAPotential θ} {Δ : SourceNAPotential σ}
    (h : SourceNAPOrder Γ Δ) {ι : V → M} (hwd : TraceWellDefined ι Γ) (κ : SourceKahlerForm n M) :
    traceCutoff ι Γ κ ≤ traceCutoff ι Δ κ :=
  csSup_le_csSup (traceCutoff_set_bddAbove ι Δ κ) (traceCutoff_set_nonempty hwd κ)
    (fun _ hs => sliceTraceable_of_naOrder h ι κ hs)

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The ACTUAL original trace cutoff of the ACTUAL original decreasing NA
infimum is EXACTLY the infimum of the ACTUAL original member trace cutoffs.
Original dS slice limits and all positive-reader endpoint detection are internal. -/
theorem traceCutoff_decreasingInf
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    {ι : V → M} (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omega Γ ha hb))
    (κ : SourceKahlerForm n M) :
    traceCutoff ι (SourceNAPotential.decreasingInf omega Γ ha hb) κ =
      sInf (range fun i => traceCutoff ι (Γ i) κ) := by
  let D := SourceNAPotential.decreasingInf omega Γ ha hb
  let T := traceCutoff ι D κ
  let Ti : I → ℝ := fun i => traceCutoff ι (Γ i) κ
  have hle (i : I) : SourceNAPOrder D (Γ i) := SourceNAPotential.decreasingInf_le omega Γ ha hb i
  have hwdi (i : I) : TraceWellDefined ι (Γ i) := traceWellDefined_of_naOrder (hle i) hwd
  have hTlow (i : I) : T ≤ Ti i := traceCutoff_mono_of_naOrder (hle i) hwd κ
  have hbb : BddBelow (range Ti) := ⟨T, by rintro _ ⟨i,rfl⟩; exact hTlow i⟩
  have hambient : sInf (range Ti) ≤ (D.component κ).val.max := by
    change sInf (range Ti) ≤ sInf (range fun i => ((Γ i).component κ).val.max)
    apply le_csInf (range_nonempty _)
    rintro _ ⟨i,rfl⟩
    exact (csInf_le hbb ⟨i,rfl⟩).trans (traceCutoff_le_max (hwdi i) κ)
  apply le_antisymm
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨i,rfl⟩; exact hTlow i)
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hTr
    by_cases hr : r < (D.component κ).val.max
    · have hne : sourceGenericLelongNumber (n := n) ι ((D.component κ).val.potential ⟨r,hr⟩) ≠ 0 := by
        intro hzero
        have hrt : r ≤ T := le_csSup (traceCutoff_set_bddAbove ι D κ) ⟨hr,hzero⟩
        exact (not_le.mpr hTr) hrt
      have hlim := tendsto_sourceGenericLelongNumber_na_decreasingInf omega Γ ha hb κ hr ι
      have hev := hlim.eventually_const_lt (pos_iff_ne_zero.mpr hne)
      obtain ⟨i, hi⟩ := hev.exists
      have hiT : Ti i ≤ r := by
        apply le_of_not_gt
        intro hri
        have hzero := (sliceTraceable_of_lt_traceCutoff (hwdi i) κ hri).2
        exact (ne_of_gt hi) hzero
      exact (csInf_le hbb ⟨i,rfl⟩).trans hiT
    · exact hambient.trans (le_of_not_gt hr)

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- Actual member trace cutoffs form an antitone net; trace existence and
all member comparisons are produced from the original infimum data. -/
theorem traceCutoff_antitone_decreasingInf
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    {ι : V → M} (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omega Γ ha hb))
    (κ : SourceKahlerForm n M) : Antitone (fun i => traceCutoff ι (Γ i) κ) := by
  intro i j hij
  exact traceCutoff_mono_of_naOrder (ha i j hij)
    (traceWellDefined_of_naOrder (SourceNAPotential.decreasingInf_le omega Γ ha hb j) hwd) κ

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The ACTUAL original member trace cutoffs converge to the ACTUAL
original infimum trace cutoff in the ordinary real topology. -/
theorem tendsto_traceCutoff_decreasingInf
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    {ι : V → M} (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omega Γ ha hb))
    (κ : SourceKahlerForm n M) :
    Tendsto (fun i => traceCutoff ι (Γ i) κ) atTop
      (𝓝 (traceCutoff ι (SourceNAPotential.decreasingInf omega Γ ha hb) κ)) := by
  have hanti := traceCutoff_antitone_decreasingInf omega Γ ha hb hwd κ
  have hbb : BddBelow (range fun i => traceCutoff ι (Γ i) κ) :=
    ⟨traceCutoff ι (SourceNAPotential.decreasingInf omega Γ ha hb) κ,
      by rintro _ ⟨i,rfl⟩
         exact traceCutoff_mono_of_naOrder (SourceNAPotential.decreasingInf_le omega Γ ha hb i) hwd κ⟩
  rw [traceCutoff_decreasingInf omega Γ ha hb hwd κ]
  exact tendsto_atTop_ciInf hanti hbb

end SGPT.NAPotential.TraceComparison
