import SGPT.Hodge.SourceMovingClassNetCompactness

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  _root_.SGPT.Foundations.Analysis.LocalCurrents
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
  [CompactSpace M] [ConnectedSpace M]
local notation "ClosedCur" => ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m)
local notation "cls" => bottChernClass (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m)

theorem class_eq_of_weak_class_net (ω : KahlerBackground (m+1) M)
    {ι : Type*} {l : Filter ι} [l.NeBot] (T : ι → ClosedCur) (S : ClosedCur)
    (hT : ∀ i, IsFullPositive (T i).val)
    (hweak : ∀ e η, Tendsto (fun i => (T i).val.inChart e η) l (𝓝 (S.val.inChart e η)))
    (β : RealBottChern (m+1) M)
    (hclass : Tendsto (fun i => cls (T i)) l (@nhds _ (SGPT.BDivisor.euclideanTopology _) β)) :
    cls S = β := by
  let U : Ultrafilter ι := Ultrafilter.of l
  have hU : (U : Filter ι) ≤ l := Ultrafilter.of_le _
  obtain ⟨S',-,hS'β,hS'lim⟩ :=
    SourceAugmentedNetDraft.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω U hU β T hT hclass
  have hEq : S'=S := by
    apply Subtype.ext
    apply GlobalCurrent.ext
    intro e η
    exact tendsto_nhds_unique (hS'lim e η) ((hweak e η).mono_left hU)
  rw [←hEq,hS'β]

/-- Actual whole-net weak convergence of positive currents implies ORIGINAL
cohomology convergence, without a supplied class limit or class bound. -/
theorem class_tendsto_of_weak_net (ω : KahlerBackground (m+1) M)
    {ι : Type*} {l : Filter ι} (T : ι → ClosedCur) (S : ClosedCur)
    (hT : ∀ i, IsFullPositive (T i).val)
    (hweak : ∀ e η, Tendsto (fun i => (T i).val.inChart e η) l (𝓝 (S.val.inChart e η))) :
    Tendsto (fun i => cls (T i)) l (@nhds _ (SGPT.BDivisor.euclideanTopology _) (cls S)) := by
  classical
  let _ := SGPT.Hodge.finiteDimensional_realBottChern ω
  let b := Module.finBasis ℝ (RealBottChern (m+1) M)
  rw [SGPT.Hodge.tendsto_euclideanTopology_iff_equivFun b]
  apply (Filter.tendsto_iff_ultrafilter _ l _).mpr
  intro U hU
  let a := fun i => b.equivFun (cls (T i))
  have hgraph (T' : ι → ClosedCur) (S' : ClosedCur)
      (hT' : ∀ i, IsFullPositive (T' i).val)
      (hw : ∀ e η, Tendsto (fun i => (T' i).val.inChart e η) (U : Filter ι)
        (𝓝 (S'.val.inChart e η)))
      (v : Fin (Module.finrank ℝ (RealBottChern (m+1) M)) → ℝ)
      (hv : Tendsto (fun i => b.equivFun (cls (T' i))) (U : Filter ι) (𝓝 v)) :
      b.equivFun (cls S') = v := by
    have hc : Tendsto (fun i => cls (T' i)) (U : Filter ι)
        (@nhds _ (SGPT.BDivisor.euclideanTopology _) (b.equivFun.symm v)) := by
      rw [SGPT.Hodge.tendsto_euclideanTopology_iff_equivFun b,LinearEquiv.apply_symm_apply]
      exact hv
    rw [class_eq_of_weak_class_net ω T' S' hT' hw _ hc,LinearEquiv.apply_symm_apply]
  by_cases hbdd : ∃ C : ℝ, ∀ᶠ i in (U : Filter ι), a i ∈ Metric.closedBall 0 C
  · obtain ⟨C,hC⟩ := hbdd
    obtain ⟨v,-,hv⟩ := (isCompact_closedBall (0 : Fin _ → ℝ) C).ultrafilter_le_nhds'
      (U.map a) hC
    have hav : Tendsto a (U : Filter ι) (𝓝 v) := hv
    have heq := hgraph T S hT (fun e η => (hweak e η).mono_left hU) v hav
    rw [←heq] at hav
    exact hav
  · have hnorm : Tendsto (fun i => ‖a i‖) (U : Filter ι) atTop := by
      apply tendsto_atTop.2
      intro C
      have hnot : ¬∀ᶠ i in (U : Filter ι), a i ∈ Metric.closedBall 0 C :=
        fun h => hbdd ⟨C,h⟩
      have hn : ∀ᶠ i in (U : Filter ι), a i ∉ Metric.closedBall 0 C :=
        Ultrafilter.eventually_not.mpr hnot
      filter_upwards [hn] with i hi
      exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hi)).le
    let c : ι → ℝ := fun i => ‖a i‖⁻¹
    have hc0 (i) : 0 ≤ c i := inv_nonneg.mpr (norm_nonneg _)
    have hclim : Tendsto c (U : Filter ι) (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
    have hpos : ∀ᶠ i in (U : Filter ι), 0 < ‖a i‖ := hnorm.eventually (eventually_gt_atTop 0)
    let T' : ι → ClosedCur := fun i => c i • T i
    have hT' (i) : IsFullPositive (T' i).val := by
      intro e α hα
      change 0 ≤ (c i • (T i).val).inChart e _
      rw [GlobalCurrent.inChart_smul]
      exact mul_nonneg (hc0 i) (hT i e α hα)
    have hw : ∀ e η, Tendsto (fun i => (T' i).val.inChart e η) (U : Filter ι)
        (𝓝 (((0 : ℝ) • S).val.inChart e η)) := by
      intro e η
      change Tendsto (fun i => (c i • (T i).val).inChart e η) (U : Filter ι)
        (𝓝 (((0 : ℝ) • S.val).inChart e η))
      simp only [GlobalCurrent.inChart_smul]
      exact hclim.mul ((hweak e η).mono_left hU)
    have hcls (i) : b.equivFun (cls (T' i)) = c i • a i := by
      change b.equivFun (bottChernClassLinearMap (M := M) (canonicalBasis (m+1))
        (Nat.succ_pos m) (c i • T i)) = c i • a i
      rw [map_smul,map_smul]
      rfl
    have hunit : ∀ᶠ i in (U : Filter ι), ‖b.equivFun (cls (T' i))‖ = 1 := by
      filter_upwards [hpos] with i hi
      rw [hcls,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hc0 i)]
      exact inv_mul_cancel₀ hi.ne'
    obtain ⟨v,-,hv⟩ := (isCompact_closedBall (0 : Fin _ → ℝ) 1).ultrafilter_le_nhds'
      (U.map (fun i => b.equivFun (cls (T' i))))
      (hunit.mono fun i hi => by rw [Metric.mem_closedBall,dist_zero_right,hi])
    have hav : Tendsto (fun i => b.equivFun (cls (T' i))) (U : Filter ι) (𝓝 v) := hv
    have heq := hgraph T' ((0 : ℝ) • S) hT' hw v hav
    have hzero : cls ((0 : ℝ) • S) = 0 := by
      change bottChernClassLinearMap (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m)
        ((0 : ℝ) • S) = 0
      rw [map_smul,zero_smul]
    rw [hzero,map_zero] at heq
    have hnv : ‖v‖=1 := tendsto_nhds_unique hav.norm
      (tendsto_const_nhds.congr' (hunit.mono fun i hi => hi.symm))
    rw [←heq,norm_zero] at hnv
    exact False.elim (zero_ne_one hnv)

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
