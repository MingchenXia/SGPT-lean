import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity
import SGPT.Foundations.Analysis.LocalPshDiscControl

/-! Actual weak maximum on arbitrary compact complex-plane subsets.
Blueprint: complex-compact-maximum.tex. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.SingularMaximum

/-- A genuine compact-set maximum principle with no connectedness or
smooth-boundary premise, for the unchanged extended-real PSH function. -/
theorem le_const_on_compact_of_le_on_frontier
    {u : ℂ → EReal} {Ω K : Set ℂ} (hu : PlurisubharmonicOn u Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {C : ℝ}
    (hfront : ∀ z ∈ frontier K,u z ≤ (C : EReal)) :
    ∀ z ∈ K,u z ≤ (C : EReal) := by
  intro z hz
  by_contra hle
  have hCz : (C : EReal) < u z := lt_of_not_ge hle
  obtain ⟨p,hpK,hmax⟩ :=
    (hu.upperSemicontinuousOn.mono hKΩ).exists_isMaxOn ⟨z,hz⟩ hK
  have hpTop : u p ≠ ⊤ := (hu p (hKΩ hpK)).ne_top
  have hpBot : u p ≠ ⊥ := by
    intro h
    have hm := hCz.trans_le (hmax hz)
    rw [h] at hm
    exact (not_lt_of_ge bot_le) hm
  let B : ℝ := (u p).toReal
  have hpB : u p = (B : EReal) := (EReal.coe_toReal hpTop hpBot).symm
  have hCB : C < B := by
    rw [← EReal.coe_lt_coe_iff,← hpB]
    exact hCz.trans_le (hmax hz)
  let M : Set ℂ := K ∩ u ⁻¹' Ici (B : EReal)
  have hMc : IsCompact M :=
    (hu.upperSemicontinuousOn.mono hKΩ).isCompact_inter_preimage_Ici hK (B : EReal)
  have hMeq : ∀ q ∈ M,u q = (B : EReal) := by
    intro q hq
    exact le_antisymm ((hmax hq.1).trans_eq hpB) hq.2
  have hMinterior : M ⊆ interior K := by
    intro q hq
    by_contra hqi
    have hqfront : q ∈ frontier K := (mem_frontier_iff_notMem_interior hq.1).mpr hqi
    have h := hfront q hqfront
    rw [hMeq q hq,EReal.coe_le_coe_iff] at h
    exact (not_lt_of_ge h) hCB
  have hMo : IsOpen M := by
    apply Metric.isOpen_iff.mpr
    intro q hq
    obtain ⟨W,hW,hqW,hdisc⟩ := hu q (hKΩ hq.1)
    have hO : IsOpen (W ∩ interior K) := hW.inter isOpen_interior
    have hqO : q ∈ W ∩ interior K := ⟨hqW,hMinterior hq⟩
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hO q hqO
    have hbW : ball q r ⊆ W := fun a ha => (hball ha).1
    have hbound : ∀ a ∈ ball q r,u a ≤ (B : EReal) := by
      intro a ha
      exact (hmax (interior_subset (hball ha).2)).trans_eq hpB
    have heq := hdisc.eqOn_ball_of_le_of_eq q hbW hbound (hMeq q hq)
    refine ⟨r,hr,fun a ha => ⟨interior_subset (hball ha).2,?_⟩⟩
    exact (heq ha).ge
  have hMne : M.Nonempty := ⟨p,hpK,by simp [hpB]⟩
  have hMuniv : M = univ := (show IsClopen M from ⟨hMc.isClosed,hMo⟩).eq_univ hMne
  exact noncompact_univ ℂ (hMuniv ▸ hMc)

end SGPT.Unibranch.SingularMaximum
