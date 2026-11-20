import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingDiscSubmean

set_option autoImplicit false

/-! # Actual plurisubharmonic boundary maximum pasting, retaining arbitrary pole sets -/

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH

open ERealBoundaryMaxPastingTopology ERealBoundaryMaxPastingDiscSubmean

noncomputable section

/-- Actual continuous maps transport actual boundary upper-limit inequalities to genuine inverse-image patches. -/
theorem boundaryDominatedOn_comp_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Ω D : Set Y} {v u : Y → EReal} (hboundary : BoundaryDominatedOn Ω D v u)
    {F : X → Y} (hF : Continuous F) :
    BoundaryDominatedOn (F ⁻¹' Ω) (F ⁻¹' D) (v ∘ F) (u ∘ F) := by
  intro x hx c hc
  have hxfr : F x ∈ frontier D := hF.frontier_preimage_subset D hx.2
  have hnear : ∀ᶠ y in 𝓝 (F x), y ∈ D → v y < c :=
    eventually_nhdsWithin_iff.mp (hboundary (F x) ⟨hx.1, hxfr⟩ c hc)
  exact eventually_nhdsWithin_iff.mpr (hF.continuousAt.tendsto.eventually hnear)

/-- The actual maximum-pasting operation commutes pointwise with an actual pullback. -/
theorem gluedMax_comp {X Y : Type*} (D : Set Y) (v u : Y → EReal) (F : X → Y) :
    (fun x => gluedMax D v u (F x)) = gluedMax (F ⁻¹' D) (v ∘ F) (u ∘ F) := by
  funext x
  by_cases hx : F x ∈ D <;> simp [gluedMax, hx]

/-- Actual affine complex-line pullback and genuine one-variable deficit comparison produce the complete disc-PSH criterion for boundary pasting. -/
theorem discPshOn_gluedMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ω D : Set E} {v u : E → EReal} (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u) :
    DiscPshOn (gluedMax D v u) Ω := by
  let G : E → EReal := gluedMax D v u
  refine ⟨gluedMax_ne_top (fun z hz => (hu z hz).ne_top) (fun z hz => (hv z hz).ne_top),
    upperSemicontinuousOn_gluedMax hD hu.upperSemicontinuousOn hv.upperSemicontinuousOn hboundary, ?_⟩
  intro x a r hr hK C hC
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight a
  let F : ℂ → E := fun z => x + L z
  have hF : Continuous F := continuous_const.add L.continuous
  have hDline : IsOpen (F ⁻¹' D) := hD.preimage hF
  have huline : PlurisubharmonicOn (u ∘ F) (F ⁻¹' Ω) := hu.comp_affine L x
  have hvline : PlurisubharmonicOn (v ∘ F) (F ⁻¹' D) := hv.comp_affine L x
  have hbline : BoundaryDominatedOn (F ⁻¹' Ω) (F ⁻¹' D) (v ∘ F) (u ∘ F) :=
    boundaryDominatedOn_comp_continuous hboundary hF
  have hclosed : closedBall (0 : ℂ) r ⊆ F ⁻¹' Ω := by
    intro z hz
    apply hK
    exact ⟨z, hz, by simp [F, L]⟩
  have hcompat : (fun z => G (F z)) = gluedMax (F ⁻¹' D) (v ∘ F) (u ∘ F) :=
    gluedMax_comp D v u F
  have hbound : ∀ z ∈ closedBall (0 : ℂ) r,
      gluedMax (F ⁻¹' D) (v ∘ F) (u ∘ F) z ≤ (C : EReal) := by
    intro z hz
    rw [← hcompat]
    apply hC
    exact ⟨z, hz, by simp [F, L]⟩
  have hsub := gluedMax_circleSubmean hDline huline hvline hbline hr hclosed hbound
  rw [← hcompat] at hsub
  change circleDeficit (fun z => G (x + L z)) 0 1 r C ≤
    ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - G (x + L 0)).toENNReal at hsub
  rw [circleDeficit_comp_affine G L x] at hsub
  simpa [L] using hsub

/-- Actual open-domain boundary upper-limit dominance yields genuine PSH maximum pasting, with no finite lower bound. -/
theorem plurisubharmonicOn_gluedMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ω D : Set E} {v u : E → EReal} (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u) :
    PlurisubharmonicOn (gluedMax D v u) Ω :=
  (discPshOn_gluedMax hD hu hv hboundary).plurisubharmonicOn hΩ

end

end SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH
