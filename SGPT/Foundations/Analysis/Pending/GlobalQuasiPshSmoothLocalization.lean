import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.GlobalPotentials

set_option autoImplicit false

/-! # Actual global smooth corrections of raw local quasi-PSH decompositions -/

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization

open FirstPass FirstPass.HolomorphicMaps ChartPartition

noncomputable section

variable {n : ℕ}

/-- Multiplication by a genuinely supported cutoff localizes actual smoothness;
outside its closed support the product is identically zero on a neighborhood. -/
theorem contDiff_mul_of_tsupport_subset {W : Set (ComplexModel n)} (hW : IsOpen W)
    {β h : ComplexModel n → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContDiffOn ℝ ∞ h W) (hs : tsupport β ⊆ W) :
    ContDiff ℝ ∞ (fun y => β y * h y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport β
  · exact hβ.contDiffAt.mul ((hh y (hs hy)).contDiffAt (hW.mem_nhds (hs hy)))
  · have heq : (fun w => β w * h w) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hy] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    have h0 : ContDiffAt ℝ ∞ (fun _ : ComplexModel n => (0 : ℝ)) y := contDiffAt_const
    exact h0.congr_of_eventuallyEq heq

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A genuine smooth germ in an actual holomorphic chart is internally cut off
and extended by zero to a function smooth in every actual holomorphic chart. -/
theorem exists_chartSmooth_germ_extension (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) {h : ComplexModel n → ℝ}
    (hh : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ h y) :
    ∃ H : M → ℝ, ChartSmooth (n := n) H ∧
      (fun y => H (e.val.symm y)) =ᶠ[𝓝 z] h := by
  obtain ⟨W, hWsub, hWo, hzW⟩ :=
    mem_nhds_iff.mp (hh.and (e.val.open_target.mem_nhds hz))
  have hWh : ContDiffOn ℝ ∞ h W := fun y hy => (hWsub hy).1.contDiffWithinAt
  have hWt : W ⊆ e.val.target := fun y hy => (hWsub hy).2
  let Ω : Opens (ComplexModel n) := ⟨W, hWo⟩
  obtain ⟨β, hβ1, _⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := Ω) isCompact_singleton (singleton_subset_iff.mpr hzW)
  rw [nhdsSet_singleton] at hβ1
  have hβh := contDiff_mul_of_tsupport_subset hWo β.contDiff hWh β.tsupport_subset
  have hβhc : IsCompact (tsupport (fun y => β y * h y)) :=
    β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
  have hβht : tsupport (fun y => β y * h y) ⊆ e.val.target :=
    tsupport_mul_subset_left.trans (β.tsupport_subset.trans hWt)
  refine ⟨chartExtend e (fun y => β y * h y),
    chartSmooth_chartExtend e hβh hβhc hβht, ?_⟩
  filter_upwards [hβ1, e.val.open_target.mem_nhds hz] with y hy hyt
  rw [chartExtend_of_mem (e.val.map_target hyt), e.val.right_inv hyt, hy, one_mul]

/-- Actual PSH germs, including negative-infinite germs, transport through the
actual holomorphic chart transition and its inverse. -/
theorem plurisubharmonicAt_chart_iff (q : M → EReal) (e f : ComplexChart n M)
    (x : M) (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    PlurisubharmonicAt (chartFunction q e) (e.val x) ↔
      PlurisubharmonicAt (chartFunction q f) (f.val x) := by
  have transport (a b : ComplexChart n M) (ha : x ∈ a.val.source)
      (hb : x ∈ b.val.source)
      (hq : PlurisubharmonicAt (chartFunction q a) (a.val x)) :
      PlurisubharmonicAt (chartFunction q b) (b.val x) := by
    let F := coordinateMap (id : M → M) b a
    let U := coordinateDomain (id : M → M) b a
    have hU : IsOpen U := coordinateDomain_isOpen contMDiff_id b a
    have hxU : b.val x ∈ U := mem_coordinateDomain hb ha
    have hqF : PlurisubharmonicAt (chartFunction q a) (F (b.val x)) := by
      simpa only [F, coordinateMap_at hb, id_eq] using hq
    have hp := HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hU
      ((coordinateMap_contDiffOn contMDiff_id b a).differentiableOn (by simp)) hxU hqF
    apply hp.congr
    filter_upwards [hU.mem_nhds hxU] with y hy
    change q (a.val.symm (a.val (b.val.symm y))) = q (b.val.symm y)
    exact congrArg q (a.val.left_inv hy.2)
  exact ⟨transport e f he hf, transport f e hf he⟩

/-- The actual local quasi-PSH decomposition internally supplies one genuine
global smooth correction making the difference locally PSH in every chart. -/
theorem exists_chartSmooth_local_psh_correction {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (x : M) :
    ∃ H : M → ℝ, ChartSmooth (n := n) H ∧
      ∃ S : Set M, IsOpen S ∧ x ∈ S ∧
        ∀ (f : ComplexChart n M) (z : ComplexModel n), z ∈ f.val.target →
          f.val.symm z ∈ S →
          PlurisubharmonicAt (chartFunction (fun y => u y - (H y : EReal)) f) z := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hzt : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨p, h, hp, hh, heq⟩ := hu e (e.val x) hzt
  obtain ⟨H, hH, hHgerm⟩ := exists_chartSmooth_germ_extension e hzt hh
  obtain ⟨V, hVo, hzV, hpV⟩ := hp
  have hVnear : ∀ᶠ y in 𝓝 (e.val x), y ∈ V := hVo.mem_nhds hzV
  have hTnear : ∀ᶠ y in 𝓝 (e.val x), y ∈ e.val.target := e.val.open_target.mem_nhds hzt
  have hnear := heq.and (hHgerm.and (hVnear.and hTnear))
  obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.mp hnear
  have hpref (y : ComplexModel n) (hy : y ∈ W) :
      PlurisubharmonicAt (chartFunction (fun a => u a - (H a : EReal)) e) y := by
    have hpy := hpV.plurisubharmonicOn hVo y (hWsub hy).2.2.1
    apply hpy.congr
    filter_upwards [hWo.mem_nhds hy] with w hw
    symm
    change chartFunction u e w - (H (e.val.symm w) : EReal) = p w
    have huw : chartFunction u e w = p w + (h w : EReal) := (hWsub hw).1
    have hHw : H (e.val.symm w) = h w := (hWsub hw).2.1
    rw [huw, hHw, EReal.add_sub_cancel_right]
  let S := e.val.source ∩ e.val ⁻¹' W
  have hS : IsOpen S := e.val.isOpen_inter_preimage hWo
  refine ⟨H, hH, S, hS, ⟨hx, hzW⟩, ?_⟩
  intro f z hz hzS
  have hyf : f.val.symm z ∈ f.val.source := f.val.map_target hz
  have hp0 := hpref (e.val (f.val.symm z)) hzS.2
  have hpf := (plurisubharmonicAt_chart_iff
    (fun y => u y - (H y : EReal)) e f (f.val.symm z) hzS.1 hyf).mp hp0
  simpa only [f.val.right_inv hz] using hpf

end

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization
