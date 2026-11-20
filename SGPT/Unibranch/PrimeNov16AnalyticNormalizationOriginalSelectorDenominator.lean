import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections

/-! Genuine common denominator plus actual entire selector equation manufacture EVERY own-branch denominator germ.
Blueprint: prime-nov16-analytic-normalization-original-selector-denominator.tex. -/
set_option autoImplicit false
noncomputable section
open TopologicalSpace CategoryTheory Opposite
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorDenominator

theorem original_selector_denominator_nonzero {X : TopCat} (S : X.Sheaf CommRingCat)
    (W V : Opens X) (hVW : V ≤ W)
    (Q e T H : (S.presheaf.obj (op W)).carrier)
    (hq : ∀ x (hx : x ∈ W),S.presheaf.germ W x hx Q ≠ 0)
    (hrel : Q*e=T*H) (he : S.presheaf.map (homOfLE hVW).op e=1) :
    ∀ x (hx : x ∈ V),S.presheaf.germ V x hx (S.presheaf.map (homOfLE hVW).op H) ≠ 0 := by
  have hprod : S.presheaf.map (homOfLE hVW).op Q=
      S.presheaf.map (homOfLE hVW).op T*S.presheaf.map (homOfLE hVW).op H := by
    have hp := congrArg (S.presheaf.map (homOfLE hVW).op) hrel
    rw [map_mul,map_mul,he,mul_one] at hp
    exact hp
  intro x hx hz
  apply hq x (hVW hx)
  calc
    S.presheaf.germ W x (hVW hx) Q=
        S.presheaf.germ V x hx (S.presheaf.map (homOfLE hVW).op Q) :=
      (S.presheaf.germ_res_apply (homOfLE hVW) x hx Q).symm
    _=S.presheaf.germ V x hx (S.presheaf.map (homOfLE hVW).op T)*
        S.presheaf.germ V x hx (S.presheaf.map (homOfLE hVW).op H) := by rw [hprod,map_mul]
    _=0 := by rw [hz,mul_zero]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorDenominator
