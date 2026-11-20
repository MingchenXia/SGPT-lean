import SGPT.NPP.LocalIncreasingUpperGaps
import SGPT.NPP.CapacityConvergenceLocalSource
import SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1

/-!
Actual local representatives and Choquet selection. USC regularization is
used on the original manifold, locally inside U; original values outside U
are never constrained or changed. The local-majorant theorem prevents them
from affecting the regularization at any interior point.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.LocalIncreasingCapacityDraft

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The actual local almost-everywhere comparison only needs an USC majorant
on the right; it need not be supplied as a PSH potential. -/
theorem local_qpsh_le_upperSemicontinuous_of_chartAELE
    {U : Opens M} {v g : M → EReal}
    (hv : IsLocalQuasiPshOn (n := n) (U : Set M) v)
    (hg : UpperSemicontinuous g)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂volume.restrict (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)),
        v (e.val.symm z) ≤ g (e.val.symm z)) :
    ∀ x ∈ (U : Set M), v x ≤ g x := by
  intro x hx
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  let D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' (U : Set M)
  have hDo : IsOpen D := e.val.isOpen_inter_preimage_symm U.isOpen
  have hzg : UpperSemicontinuousOn (fun z => g (e.val.symm z)) D :=
    (hg.upperSemicontinuousOn univ).comp (e.val.symm.continuousOn.mono inter_subset_left)
      (fun _ _ => mem_univ _)
  have hz : e.val x ∈ D := by
    refine ⟨e.val.map_source hxs, ?_⟩
    simpa only [mem_preimage, e.val.left_inv hxs] using hx
  have h := QuasiPshAlmostEverywhereComparison.le_of_ae_le (hv.1 e) hDo hzg volume
    (hae e) (e.val x) hz
  simpa only [chartFunction, e.val.left_inv hxs] using h

omit [IsComplexManifold n M] in
/-- An actual increasing local quasi-PSH net has its prescribed a.e. limit
as the regularized supremum at each interior point. No regularized-limit
identity is assumed. -/
theorem uscRegularization_iSup_eqOn_of_monotone_ae
    {U : Opens M} {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsLocalQuasiPshOn (n := n) (U : Set M) (u i))
    (hv : IsLocalQuasiPshOn (n := n) (U : Set M) v)
    (hm : ∀ x ∈ (U : Set M), Monotone fun i => u i x)
    (hae : NetChartTendstoAEOn (n := n) U u v) :
    EqOn (uscRegularization (⨆ i, u i)) v U := by
  have hle := increasing_local_le_limit hu hv hm hae
  have hupper : ∀ x ∈ (U : Set M), uscRegularization (⨆ i, u i) x ≤ v x := by
    intro x hx
    apply uscRegularization_le_of_eventually_le (hv.upperSemicontinuousAt hx)
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    simpa only [iSup_apply] using iSup_le fun i => hle i y hy
  have hlower := local_qpsh_le_upperSemicontinuous_of_chartAELE hv
    (upperSemicontinuous_uscRegularization (⨆ i, u i)) (fun e => by
      filter_upwards [hae e] with z hz
      exact le_of_tendsto' hz fun i =>
        (le_iSup (fun j => u j (e.val.symm z)) i).trans
          (by rw [← iSup_apply]; exact le_uscRegularization _ _))
  exact fun x hx => le_antisymm (hupper x hx) (hlower x hx)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Choquet supplies a sequence of actual original indices, and directedness
makes it increasing; its regularized supremum is the same original local
PSH limit. This includes arbitrary disconnected open sets. -/
theorem exists_monotone_sequence_regularized_limit
    {U : Opens M} {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsLocalQuasiPshOn (n := n) (U : Set M) (u i))
    (hv : IsLocalQuasiPshOn (n := n) (U : Set M) v)
    (hm : ∀ x ∈ (U : Set M), Monotone fun i => u i x)
    (hae : NetChartTendstoAEOn (n := n) U u v) :
    ∃ j : ℕ → I, Monotone j ∧ EqOn (uscRegularization (⨆ k, u (j k))) v U := by
  classical
  obtain ⟨s, hsF, hs⟩ := exists_seq_uscRegularization_iSup_eq (range_nonempty u)
  choose idx hidx using hsF
  obtain ⟨j, hjmono, hjdom⟩ := exists_monotone_dominating idx
  have hle := increasing_local_le_limit hu hv hm hae
  have hupper : ∀ x ∈ (U : Set M), uscRegularization (⨆ k, u (j k)) x ≤ v x := by
    intro x hx
    apply uscRegularization_le_of_eventually_le (hv.upperSemicontinuousAt hx)
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    simpa only [iSup_apply] using iSup_le fun k => hle (j k) y hy
  -- Locally, the countable Choquet subfamily is dominated by the increasing
  -- selected sequence. Arbitrary original values outside U are irrelevant.
  have hselected : ∀ x ∈ (U : Set M),
      uscRegularization (⨆ k, s k) x ≤ uscRegularization (⨆ k, u (j k)) x := by
    intro x hx
    apply uscRegularization_le_of_eventually_le
      (upperSemicontinuous_uscRegularization _ x)
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    refine (show (⨆ k, s k) y ≤ (⨆ k, u (j k)) y from ?_).trans
      (le_uscRegularization _ y)
    simp only [iSup_apply]
    apply iSup_le
    intro k
    rw [← hidx k]
    exact le_iSup_of_le k (hm y hy (hjdom k))
  have hlower := local_qpsh_le_upperSemicontinuous_of_chartAELE hv
    (upperSemicontinuous_uscRegularization (⨆ k, u (j k))) (fun e => by
      have hDo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)) :=
        e.val.isOpen_inter_preimage_symm U.isOpen
      filter_upwards [hae e, ae_restrict_mem hDo.measurableSet] with z hz hzD
      apply le_of_tendsto' hz
      intro i
      have hdom : u i (e.val.symm z) ≤ sSup (range u) (e.val.symm z) := by
        rw [sSup_apply]
        exact le_iSup_of_le ⟨u i, mem_range_self i⟩ le_rfl
      exact hdom.trans ((le_uscRegularization _ _).trans
        (by rw [← hs]; exact hselected _ hzD.2)))
  exact ⟨j, hjmono, fun x hx => le_antisymm (hupper x hx) (hlower x hx)⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A true increasing local PSH sequence with the actual regularized limit
converges Lebesgue-almost everywhere in every original restricted chart.
The local finite upper bound is produced by the actual corrected PSH limit. -/
theorem netChartTendstoAEOn_of_monotone_regularized_limit
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSHOn α (u j) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun j => u j x)
    (hle : ∀ j x, x ∈ (U : Set M) → u j x ≤ v x)
    (hreg : EqOn (uscRegularization (⨆ j, u j)) v U) :
    NetChartTendstoAEOn (n := n) U u v := by
  intro e
  apply ae_restrict_of_open_neighborhood_ae
  intro z hz
  obtain ⟨A, ρ, hzA, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials
    (atlasClosedFormToNative α) e z hz.1
  let W : Set (ComplexModel n) := A ∩ (e.val.target ∩ e.val.symm ⁻¹' (U : Set M))
  have hWo : IsOpen W := hρ.1.inter (e.val.isOpen_inter_preimage_symm U.isOpen)
  have hzW : z ∈ W := ⟨hzA, hz⟩
  have hWinside : ∀ y ∈ W, e.val.symm y ∈ (U : Set M) := fun y hy => hy.2.2
  have hρW := hρ.mono hWo (show W ⊆ A from inter_subset_left)
  let a : ℕ → ComplexModel n → EReal := fun j y => u j (e.val.symm y) + (ρ y : EReal)
  let b : ComplexModel n → EReal := fun y => v (e.val.symm y) + (ρ y : EReal)
  have ha : ∀ j, PlurisubharmonicOn (a j) W := fun j =>
    CapacityConvergence.plurisubharmonicOn_chart_of_isThetaPSHOn (hu j) e hWinside hρW
  have hb : PlurisubharmonicOn b W :=
    CapacityConvergence.plurisubharmonicOn_chart_of_isThetaPSHOn hv e hWinside hρW
  have hρc : ∀ y ∈ W, ContinuousAt ρ y := fun y hy =>
    ((hρW.2.2.1 y hy).contDiffAt (hWo.mem_nhds hy)).continuousAt
  have hsup : (⨆ j, a j) = fun y => chartFunction (⨆ j, u j) e y + (ρ y : EReal) := by
    funext y
    simp only [iSup_apply, chartFunction, a]
    exact (NegligibleSetNotCharged.iSup_add_coe (fun j => u j (e.val.symm y)) (ρ y)).symm
  have hVeq : ∀ y ∈ W, uscRegularization (⨆ j, a j) y = b y := by
    intro y hy
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hρc y hy),
      uscRegularization_chartFunction_apply _ e hy.2.1]
    change uscRegularization (⨆ j, u j) (e.val.symm y) + (ρ y : EReal) =
      v (e.val.symm y) + (ρ y : EReal)
    rw [hreg (hWinside y hy)]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, b z < (B : EReal) :=
    EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hb z hzW).ne_top) |>.imp
      fun _ h => h.1
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp
    ((hb z hzW).quasiPlurisubharmonicAt.upperSemicontinuousAt (B : EReal) hB)
  obtain ⟨S, hS, hSWV⟩ := Metric.isOpen_iff.mp (hWo.inter hVo) z ⟨hzW, hzV⟩
  have hSW : ball z S ⊆ W := fun y hy => (hSWV hy).1
  have haB : ∀ j y, y ∈ ball z S → a j y ≤ (B : EReal) := by
    intro j y hy
    have h1 : a j y ≤ b y := add_le_add (hle j (e.val.symm y) (hWinside y (hSW hy))) le_rfl
    exact h1.trans (hVsub (hSWV hy).2).le
  have ham : ∀ y ∈ W, Monotone fun j => a j y := by
    intro y hy i j hij
    exact add_le_add (hm _ (hWinside y hy) hij) le_rfl
  have hae := ae_uscRegularization_iSup_eq_on_ball
    (fun j => (ha j).discPshOn) ham volume z hS hSW haB
  refine ⟨ball z (S / 2), isOpen_ball, mem_ball_self (by linarith), ?_⟩
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with y hy hyball
  have hyW : y ∈ W := hSW (ball_subset_ball (by linarith) hyball)
  have heq : (⨆ j, u j (e.val.symm y)) = v (e.val.symm y) := by
    have hsupfun : (fun z => ⨆ j, a j z) = (⨆ j, a j) := by
      funext z
      simp only [iSup_apply]
    have hy' := hy hyball
    rw [hsupfun] at hy'
    have h := (hVeq y hyW).symm.trans hy'
    change v (e.val.symm y) + (ρ y : EReal) = ⨆ j, a j y at h
    rw [show (⨆ j, a j y) = (⨆ j, u j (e.val.symm y)) + (ρ y : EReal) from
      (NegligibleSetNotCharged.iSup_add_coe _ _).symm] at h
    exact (IncreasingThetaPshChartL1.eReal_add_coe_right_cancel h).symm
  rw [← heq]
  exact tendsto_atTop_iSup (hm _ (hWinside y hyW))

end SGPT.NPP.LocalIncreasingCapacityDraft
