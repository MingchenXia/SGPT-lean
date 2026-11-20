import SGPT.PSH.ThetaRooftop
import SGPT.Toric.ProjectiveToricOrder
import SGPT.Convex.FamilyOperations

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical

/-- Pullback of every original common minorant proves the literal raw
rooftop's circle invariance, including bottom and empty families. -/
theorem projectiveCircleInvariant_thetaRooftop
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    ProjectiveCircleInvariant (thetaRooftop projectiveFSForm u v) := by
  have hle (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1)
      (p : Projectivization ℂ (Fin 2 → ℂ)) :
      thetaRooftop projectiveFSForm u v (projectiveTorusAction a p) ≤
        thetaRooftop projectiveFSForm u v p := by
    change (⨆ f : {f : Projectivization ℂ (Fin 2 → ℂ) → EReal //
        projectiveLineAtlas.IsThetaPSH projectiveFSForm f ∧ f ≤ u ∧ f ≤ v},
      f.val (projectiveTorusAction a p)) ≤ _
    apply iSup_le
    intro f
    exact le_thetaRooftop (isThetaPSH_comp_projectiveTorusAction f.property.1 ha)
      (fun q ↦ (f.property.2.1 (projectiveTorusAction a q)).trans_eq (hiu a ha q))
      (fun q ↦ (f.property.2.2 (projectiveTorusAction a q)).trans_eq (hiv a ha q)) p
  intro a ha p
  apply le_antisymm (hle a ha p)
  have hainv : ‖((a⁻¹ : ℂˣ) : ℂ)‖ = 1 := by simp [norm_inv, ha]
  have h := hle a⁻¹ hainv (projectiveTorusAction a p)
  rwa [← projectiveTorusAction_mul, inv_mul_cancel, projectiveTorusAction_one] at h

/-- The source's actual non-bottom hypothesis eliminates precisely the
adjoined bottom branch of the original rooftop class closure. -/
theorem isThetaPSH_projective_thetaRooftop
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hne : thetaRooftop projectiveFSForm u v ≠ ⊥) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm
      (thetaRooftop projectiveFSForm u v) := by
  rcases isThetaPSHOrBot_thetaRooftop (Or.inl hu) (Or.inl hv) with h | h
  · exact h
  · exact False.elim (hne h)

/-- Genuine raw-rooftop maximality and the actual projective inverse map
identify the literal corrected descent with the real convex rooftop. -/
theorem projectiveToricCorrectedDescent_thetaRooftop
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v)
    (hne : thetaRooftop projectiveFSForm u v ≠ ⊥) :
    projectiveToricCorrectedDescent (thetaRooftop projectiveFSForm u v) =
      convexInf (fun b : Bool ↦ if b then projectiveToricCorrectedDescent v
        else projectiveToricCorrectedDescent u) := by
  let R := thetaRooftop projectiveFSForm u v
  let f := fun b : Bool ↦ if b then projectiveToricCorrectedDescent v
    else projectiveToricCorrectedDescent u
  let H := convexInf f
  have hR : projectiveLineAtlas.IsThetaPSH projectiveFSForm R :=
    isThetaPSH_projective_thetaRooftop hu hv hne
  have hiR : ProjectiveCircleInvariant R := projectiveCircleInvariant_thetaRooftop hiu hiv
  have hRF := projectiveToricCorrectedDescent_mem_growthClass hR hiR
  have hUF := projectiveToricCorrectedDescent_mem_growthClass hu hiu
  have hRu : projectiveToricCorrectedDescent R ≤ projectiveToricCorrectedDescent u :=
    (projectiveToricCorrectedDescent_le_iff hR hu hiR hiu).mp
      (thetaRooftop_le_left projectiveFSForm u v)
  have hRv : projectiveToricCorrectedDescent R ≤ projectiveToricCorrectedDescent v :=
    (projectiveToricCorrectedDescent_le_iff hR hv hiR hiv).mp
      (thetaRooftop_le_right projectiveFSForm u v)
  have hRH : projectiveToricCorrectedDescent R ≤ H := by
    apply le_convexInf hRF.1.1
    intro b
    cases b
    · exact hRu
    · exact hRv
  have hHu : H ≤ projectiveToricCorrectedDescent u := convexInf_le f false
  have hHv : H ≤ projectiveToricCorrectedDescent v := convexInf_le f true
  obtain ⟨fu, hfu, hFu⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hiu
  have htop : ∀ x, H x ≠ ⊤ := by
    intro x
    exact ne_of_lt ((hHu x).trans_lt (by rw [hFu]; exact EReal.coe_lt_top (fu x)))
  have hbot : ∀ x, H x ≠ ⊥ := by
    intro x
    exact ne_of_gt ((bot_lt_iff_ne_bot.mpr (hRF.1.2.2 x)).trans_le (hRH x))
  have hreal : H = fun x ↦ ((H x).toReal : EReal) :=
    funext fun x ↦ (EReal.coe_toReal (htop x) (hbot x)).symm
  have hconv : ConvexOn ℝ univ (fun x ↦ (H x).toReal) := by
    apply isConvex_coe_iff.mp
    rw [← hreal]
    exact isConvex_convexInf f
  have hgrowth : (fun x ↦ (H x).toReal) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
    refine ⟨hconv, ?_⟩
    rw [← hreal]
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hUF.2
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, fun x ↦ (hHu x).trans (hC x)⟩
  let w := projectiveToricExtension (fun x ↦ (H x).toReal) hgrowth
  have hw := projectiveToricExtension_spec (fun x ↦ (H x).toReal) hgrowth
  have hiw : ProjectiveCircleInvariant w :=
    projectiveToricExtension_circleInvariant hgrowth hw.1 hw.2
  have hwF : projectiveToricCorrectedDescent w = H :=
    (projectiveToricCorrectedDescent_eq_of_extension hw.2).trans hreal.symm
  have hwu : w ≤ u :=
    (projectiveToricCorrectedDescent_le_iff hw.1 hu hiw hiu).mpr (by rwa [hwF])
  have hwv : w ≤ v :=
    (projectiveToricCorrectedDescent_le_iff hw.1 hv hiw hiv).mpr (by rwa [hwF])
  have hwR : w ≤ R := le_thetaRooftop hw.1 hwu hwv
  have hHR := (projectiveToricCorrectedDescent_le_iff hw.1 hR hiw hiR).mp hwR
  rw [hwF] at hHR
  exact le_antisymm hRH hHR

/-- The completed actual convex-family identity gives precisely the
maximum of the two original Legendre functions, retaining all poles. -/
theorem projectiveToricLegendre_thetaRooftop
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v)
    (hne : thetaRooftop projectiveFSForm u v ≠ ⊥) :
    projectiveToricLegendre (thetaRooftop projectiveFSForm u v) =
      fun m ↦ max (projectiveToricLegendre u m) (projectiveToricLegendre v m) := by
  unfold projectiveToricLegendre
  rw [projectiveToricCorrectedDescent_thetaRooftop hu hv hiu hiv hne,
    conjugate_convexInf]
  funext m
  simp [convexSup, iSup_bool_eq, sup_comm]

end SGPT.Toric
