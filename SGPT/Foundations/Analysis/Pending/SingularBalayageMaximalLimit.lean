import SGPT.Foundations.Analysis.Pending.SingularBalayageDataOrder
import SGPT.Foundations.Analysis.Pending.SingularPerronBoundaryMaximality
import SGPT.Foundations.Analysis.PlurisubharmonicLimits
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

set_option autoImplicit false

/-! # Actual bounded balayages descending to an extended-real ordinary maximal PSH function -/

open Set Filter TopologicalSpace Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularBalayageMaximalLimit

open FirstPass FirstPass.MongeAmpere BedfordTaylor SingularBalayageDataOrder
  SingularPerronBoundaryMaximality

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- Genuine extended-real truncations have the original value as their exact lattice infimum, including poles. -/
theorem iInf_truncation (u : ComplexModel n → EReal) (z : ComplexModel n) :
    (⨅ j, truncation u j z) = u z := by
  refine le_antisymm ?_ (le_iInf fun j => le_max_left _ _)
  cases h : u z with
  | bot =>
    rw [le_bot_iff, iInf_eq_bot]
    intro b hb
    obtain ⟨s, hs⟩ : ∃ s : ℝ, (s : EReal) ≤ b := by
      cases b with
      | bot => exact (lt_irrefl _ hb).elim
      | top => exact ⟨0, le_top⟩
      | coe s => exact ⟨s, le_rfl⟩
    obtain ⟨j, hj⟩ := exists_nat_gt (-s)
    refine ⟨j, ?_⟩
    simp only [truncation, h, max_eq_right bot_le]
    exact (EReal.coe_lt_coe_iff.mpr (by linarith : -(j : ℝ) < s)).trans_le hs
  | top => exact le_top
  | coe s =>
    obtain ⟨j, hj⟩ := exists_nat_gt (-s)
    apply (iInf_le _ j).trans
    simpa only [truncation, h] using
      (max_le le_rfl (EReal.coe_le_coe_iff.mpr (by linarith : -(j : ℝ) ≤ s)))

/-- Actual truncation domination by its genuine scaled balayage holds on the whole actual domain. -/
theorem truncation_le_balayage (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    (j : ℕ) {z : ComplexModel n} (hz : z ∈ Ω) :
    truncation u j z ≤ (scaledPolydiskBalayage c r (truncationReal u j) z : EReal) := by
  rw [← coe_truncationReal hu j hz]
  apply EReal.coe_le_coe_iff.mpr
  by_cases hzP : z ∈ scaledPolydisk c r
  · exact le_scaledPolydiskBalayage hn (truncationReal_isLocallyBoundedPshOn hu j) hr hPΩ hzP
  · rw [scaledPolydiskBalayage_eqOn_compl hr (truncationReal u j) hzP]

/-- The genuine decreasing extended-real infimum of the actual truncation balayages is PSH on the original actual domain. -/
theorem plurisubharmonicOn_iInf_balayage (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    PlurisubharmonicOn
      (fun z => ⨅ j, (scaledPolydiskBalayage c r (truncationReal u j) z : EReal)) Ω := by
  apply DiscPshOn.plurisubharmonicOn_iInf_of_antitone Ω.isOpen
  · intro j
    exact (plurisubharmonicOn_scaledPolydiskBalayage hn
      (truncationReal_isLocallyBoundedPshOn hu j) hr hPΩ).discPshOn
  · intro z hz i j hij
    exact EReal.coe_le_coe_iff.mpr
      (scaledPolydiskBalayage_truncation_antitone hn hu hr hPΩ hz hij)

/-- Actual ordinary boundary maximality identifies the actual singular balayage infimum, without a finite lower bound. -/
theorem iInf_balayage_eq_of_boundaryMaximal (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsBoundaryMaximalPshOn (Ω : Set (ComplexModel n)) u)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {z : ComplexModel n} (hz : z ∈ Ω) :
    (⨅ j, (scaledPolydiskBalayage c r (truncationReal u j) z : EReal)) = u z := by
  let w : ComplexModel n → EReal :=
    fun x => ⨅ j, (scaledPolydiskBalayage c r (truncationReal u j) x : EReal)
  have hwpsh : PlurisubharmonicOn w Ω := plurisubharmonicOn_iInf_balayage hn hu.2.1 hr hPΩ
  have hge : ∀ x ∈ Ω, u x ≤ w x := fun x hx => le_iInf fun j =>
    (le_max_left _ _).trans (truncation_le_balayage hn hu.2.1 hr hPΩ j hx)
  have hoff : ∀ x ∈ Ω, x ∉ scaledPolydisk c r → w x = u x := by
    intro x hx hxP
    change (⨅ j, (scaledPolydiskBalayage c r (truncationReal u j) x : EReal)) = _
    simp_rw [scaledPolydiskBalayage_eqOn_compl hr _ hxP, coe_truncationReal hu.2.1 _ hx]
    exact iInf_truncation u x
  have hPo : IsOpen (scaledPolydisk c r) := by
    rw [← coe_scaledPolydiskOpens hr]
    exact (scaledPolydiskOpens c r).isOpen
  have hK : IsCompact (polydiskChart c r '' closedUnitPolydisk n) :=
    isCompact_closedUnitPolydisk.image (continuous_polydiskChart c r)
  have hclK : closure (scaledPolydisk c r) ⊆ polydiskChart c r '' closedUnitPolydisk n :=
    closure_minimal (image_mono unitPolydisk_subset_closedUnitPolydisk) hK.isClosed
  have hclΩ := hclK.trans hPΩ
  by_cases hzP : z ∈ scaledPolydisk c r
  · apply le_antisymm ?_ (hge z hz)
    exact hu.2.2 (scaledPolydisk c r) hPo
      (hK.of_isClosed_subset isClosed_closure hclK) hclΩ w
      (hwpsh.mono (subset_closure.trans hclΩ))
      (hwpsh.upperSemicontinuousOn.mono hclΩ)
      (fun x hx => (hoff x (hclΩ hx.1) (by simpa only [hPo.interior_eq] using hx.2)).le) z hzP
  · exact hoff z hz hzP

/-- The actual decreasing truncation balayages converge to the actual ordinary maximal singular potential at every point, including poles. -/
theorem tendsto_balayage_of_boundaryMaximal (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsBoundaryMaximalPshOn (Ω : Set (ComplexModel n)) u)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {z : ComplexModel n} (hz : z ∈ Ω) :
    Tendsto (fun j => (scaledPolydiskBalayage c r (truncationReal u j) z : EReal))
      atTop (𝓝 (u z)) := by
  rw [← iInf_balayage_eq_of_boundaryMaximal hn hu hr hPΩ hz]
  exact tendsto_atTop_iInf fun i j hij => EReal.coe_le_coe_iff.mpr
    (scaledPolydiskBalayage_truncation_antitone hn hu.2.1 hr hPΩ hz hij)

/-- Genuine truncation floors and actual PSH compact upper bounds make every actual real balayage locally bounded. -/
theorem isLocallyBoundedPshOn_balayage_truncation (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) (j : ℕ) :
    IsLocallyBoundedPshOn Ω (scaledPolydiskBalayage c r (truncationReal u j)) := by
  have hpsh := plurisubharmonicOn_scaledPolydiskBalayage hn
    (truncationReal_isLocallyBoundedPshOn hu j) hr hPΩ
  refine ⟨hpsh, ?_⟩
  intro z hz
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hz)
  have hclosed : closedBall z (s / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC0, hC⟩ := hpsh.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (s / 2)) hclosed
  refine ⟨⟨ball z (s / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hclosed, C + (j : ℝ), ?_⟩
  intro x hx
  have hxΩ := hclosed (ball_subset_closedBall hx)
  have hlo : -(j : ℝ) ≤ scaledPolydiskBalayage c r (truncationReal u j) x :=
    EReal.coe_le_coe_iff.mp ((truncation_lower_bound u j x).trans
      (truncation_le_balayage hn hu hr hPΩ j hxΩ))
  have hhi := EReal.coe_le_coe_iff.mp (hC x (ball_subset_closedBall hx))
  exact abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) j]⟩

end

end SGPT.Foundations.Analysis.Pending.SingularBalayageMaximalLimit
