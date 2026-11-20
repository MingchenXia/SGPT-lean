import SGPT.PSH.Basic
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.PlurisubharmonicPullback

/-! A genuine nontrivial ambient PSH representative, including the bottom case.
Blueprint: native-nov16-psh-pole-pullback.tex. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.NativeNov16AmbientPSHStabilization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def potential (u : E → EReal) : E × ℂ → EReal :=
  fun z => max (u z.1) (logNormSq z.2)

theorem disc {u : E → EReal} {U : Set E} (hu : DiscPshOn u U) :
    DiscPshOn (potential u) (U ×ˢ ball (0 : ℂ) 1) := by
  have hfirst : DiscPshOn (fun z : E × ℂ => u z.1) (U ×ˢ ball (0 : ℂ) 1) :=
    (hu.comp_continuousLinearMap (ContinuousLinearMap.fst ℂ E ℂ)).mono (fun _ hz => hz.1)
  have hlast : DiscPshOn (fun z : E × ℂ => logNormSq z.2) (U ×ˢ ball (0 : ℂ) 1) :=
    ((discPshOn_logNormSq (univ : Set ℂ)).comp_continuousLinearMap
      (ContinuousLinearMap.snd ℂ E ℂ)).mono (fun _ _ => mem_univ _)
  exact hfirst.max hlast

theorem psh {u : E → EReal} {U : Set E} (hu : DiscPshOn u U) (hU : U.Nonempty) :
    SGPT.PSH.PSHOn (potential u) (U ×ˢ ball (0 : ℂ) 1) := by
  obtain ⟨z,hz⟩ := hU
  refine ⟨disc hu,⟨(z,(1/2 : ℂ)),⟨hz,?_⟩,?_⟩⟩
  · norm_num [Metric.mem_ball,dist_eq_norm]
  · have hn : logNormSq (1/2 : ℂ) ≠ ⊥ :=
      (logNormSq_eq_bot_iff _).not.mpr (by norm_num)
    exact ne_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hn) (le_max_right _ _))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp] theorem zero (u : E → EReal) (z : E) : potential u (z,0)=u z := by
  simp [potential]

end SGPT.Unibranch.NativeNov16AmbientPSHStabilization
