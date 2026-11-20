import SGPT.Unibranch.NativeNov16AmbientPSHStabilization

/-! The same genuine stabilized potential on an unrestricted extra complex line.
Blueprint: native-nov16-psh-pole-pullback.tex. -/
set_option autoImplicit false
noncomputable section
open Set SGPT.Foundations.Analysis
namespace SGPT.Unibranch.NativeNov16AmbientPSHStabilization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem disc_on_product {u : E → EReal} {U : Set E} (hu : DiscPshOn u U) (D : Set ℂ) :
    DiscPshOn (potential u) (U ×ˢ D) := by
  have hfirst : DiscPshOn (fun z : E × ℂ => u z.1) (U ×ˢ D) :=
    (hu.comp_continuousLinearMap (ContinuousLinearMap.fst ℂ E ℂ)).mono (fun _ hz => hz.1)
  have hlast : DiscPshOn (fun z : E × ℂ => logNormSq z.2) (U ×ˢ D) :=
    ((discPshOn_logNormSq (univ : Set ℂ)).comp_continuousLinearMap
      (ContinuousLinearMap.snd ℂ E ℂ)).mono (fun _ _ => mem_univ _)
  exact hfirst.max hlast

theorem psh_on_product {u : E → EReal} {U : Set E} (hu : DiscPshOn u U) (hU : U.Nonempty)
    {D : Set ℂ} (hD : ∃ t ∈ D,t ≠ 0) : SGPT.PSH.PSHOn (potential u) (U ×ˢ D) := by
  obtain ⟨z,hz⟩ := hU
  obtain ⟨t,ht,ht0⟩ := hD
  refine ⟨disc_on_product hu D,⟨(z,t),⟨hz,ht⟩,?_⟩⟩
  have hn : logNormSq t ≠ ⊥ := (logNormSq_eq_bot_iff _).not.mpr ht0
  exact ne_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hn) (le_max_right _ _))

theorem psh_univ {u : E → EReal} {U : Set E} (hu : DiscPshOn u U) (hU : U.Nonempty) :
    SGPT.PSH.PSHOn (potential u) (U ×ˢ (univ : Set ℂ)) :=
  psh_on_product hu hU ⟨1,mem_univ _,one_ne_zero⟩

theorem psh_comp_equiv {u : F → EReal} {U : Set F} (hu : SGPT.PSH.PSHOn u U)
    (e : E ≃L[ℂ] F) : SGPT.PSH.PSHOn (fun x => u (e x)) (e ⁻¹' U) := by
  refine ⟨hu.disc.comp_continuousLinearMap e.toContinuousLinearMap,?_⟩
  obtain ⟨z,hz,hn⟩ := hu.nontrivial
  exact ⟨e.symm z,by simpa using hz,by simpa using hn⟩

end SGPT.Unibranch.NativeNov16AmbientPSHStabilization
