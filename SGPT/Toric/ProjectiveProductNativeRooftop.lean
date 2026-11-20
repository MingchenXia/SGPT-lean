import SGPT.Toric.ProjectiveProductNativeCirclePullback
import SGPT.Toric.ProjectiveProductNativeEnergy
import SGPT.Convex.FamilyOperations
import SGPT.Foundations.Analysis.Pending.RooftopPshCriterion

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance
open scoped Topology RealInnerProductSpace

/-- Actual non-bottom of the original native rooftop manufactures a genuine
common competitor, hence native strong PSH by the existing rooftop theorem. -/
theorem isThetaPshPotential_projectiveProductRooftop {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hne : rooftop (projectiveProductFSBackground n).form u v ≠ ⊥) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (rooftop (projectiveProductFSBackground n).form u v) := by
  classical
  have hnonempty : (rooftopCompetitors (projectiveProductFSBackground n).form.val
      (fun p => min (u p) (v p))).Nonempty := by
    by_contra h
    exact hne (rooftopEnvelope_of_empty (Set.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨L, hL, hLc⟩ := hnonempty
  have hLR := le_rooftopEnvelope hL hLc
  have hLu : L ≤ u := hLR.trans (rooftop_le_left hu hv)
  have hLv : L ≤ v := hLR.trans (rooftop_le_right hu hv)
  exact (RooftopPshCriterion.rooftop_min_of_lower (projectiveProductFSBackground n).form
    hu hv hL hLu hLv).1

/-- Native rooftop maximality and genuine arbitrary-native circle pullback
manufacture original invariance of the actual non-bottom rooftop. -/
theorem projectiveProductRooftop_circleInvariant {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v)
    (hne : rooftop (projectiveProductFSBackground n).form u v ≠ ⊥) :
    ProjectiveProductCircleInvariant (rooftop (projectiveProductFSBackground n).form u v) := by
  let R := rooftop (projectiveProductFSBackground n).form u v
  have hR := isThetaPshPotential_projectiveProductRooftop hu hv hne
  have hle (a : Fin n → ℂˣ) (ha : ∀ i, ‖(a i : ℂ)‖ = 1) :
      (fun p => R (projectiveProductTorusAction n a p)) ≤ R := by
    apply (le_rooftop_iff hu hv (isThetaPshPotential_comp_projectiveProductTorusAction hR ha)).mpr
    exact ⟨fun p => (rooftop_le_left hu hv (projectiveProductTorusAction n a p)).trans_eq (hiu a ha p),
      fun p => (rooftop_le_right hu hv (projectiveProductTorusAction n a p)).trans_eq (hiv a ha p)⟩
  intro a ha p
  apply le_antisymm (hle a ha p)
  have hai : ∀ i, ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by intro i; simp [norm_inv, ha i]
  have h := hle (fun i => (a i)⁻¹) hai (projectiveProductTorusAction n a p)
  dsimp only at h
  rw [← projectiveProductTorusAction_mul] at h
  simpa only [inv_mul_cancel, projectiveProductTorusAction_one] using h

/-- The literal original native rooftop has precisely the original convex
infimum profile. Finiteness of the convex infimum is produced before readback. -/
theorem projectiveProductToricProfile_rooftop {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v)
    (hne : rooftop (projectiveProductFSBackground n).form u v ≠ ⊥) :
    (fun x => (projectiveProductToricEuclideanProfile
      (rooftop (projectiveProductFSBackground n).form u v) x : EReal)) =
      convexInf (fun b : Bool => if b then
        (fun x => (projectiveProductToricEuclideanProfile v x : EReal)) else
        (fun x => (projectiveProductToricEuclideanProfile u x : EReal))) := by
  let R := rooftop (projectiveProductFSBackground n).form u v
  let f := fun b : Bool => if b then
    (fun x => (projectiveProductToricEuclideanProfile v x : EReal)) else
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal))
  let H := convexInf f
  have hR : IsThetaPshPotential (projectiveProductFSBackground n).form.val R :=
    isThetaPshPotential_projectiveProductRooftop hu hv hne
  have hiR : ProjectiveProductCircleInvariant R := projectiveProductRooftop_circleInvariant hu hv hiu hiv hne
  have hRF := projectiveProductToricProfile_mem_growthClass hR hiR
  have hUF := projectiveProductToricProfile_mem_growthClass hu hiu
  have hRu := (projectiveProductToricProfile_le_iff hR hu hiR hiu).mp (rooftop_le_left hu hv)
  have hRv := (projectiveProductToricProfile_le_iff hR hv hiR hiv).mp (rooftop_le_right hu hv)
  have hRH : (fun x => (projectiveProductToricEuclideanProfile R x : EReal)) ≤ H := by
    apply le_convexInf hRF.1.1
    intro b
    cases b
    · exact fun x => EReal.coe_le_coe (hRu x)
    · exact fun x => EReal.coe_le_coe (hRv x)
  have hHu : H ≤ fun x => (projectiveProductToricEuclideanProfile u x : EReal) := convexInf_le f false
  have hHv : H ≤ fun x => (projectiveProductToricEuclideanProfile v x : EReal) := convexInf_le f true
  have ht (x) : H x ≠ ⊤ := ne_of_lt ((hHu x).trans_lt (EReal.coe_lt_top _))
  have hb (x) : H x ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans_le (hRH x))
  have hreal : (fun x => ((H x).toReal : EReal)) = H := funext fun x => EReal.coe_toReal (ht x) (hb x)
  have hconv : ConvexOn ℝ univ (fun x => (H x).toReal) := by
    apply isConvex_coe_iff.mp
    rw [hreal]
    exact isConvex_convexInf f
  have hgrowth : (fun x => (H x).toReal) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n) := by
    refine ⟨hconv, ?_⟩
    rw [hreal]
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hUF.2
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, fun x => (hHu x).trans (hC x)⟩
  let w := projectiveProductToricExtension (fun x => (H x).toReal)
  have hw : IsThetaPshPotential (projectiveProductFSBackground n).form.val w :=
    isThetaPshPotential_projectiveProductToricExtension hgrowth
  have hiw : ProjectiveProductCircleInvariant w := projectiveProductToricExtension_circleInvariant _
  have hwF : projectiveProductToricEuclideanProfile w = fun x => (H x).toReal :=
    projectiveProductToricEuclideanProfile_extension hconv
  have hwu : w ≤ u := by
    apply (projectiveProductToricProfile_le_iff hw hu hiw hiu).mpr
    intro x
    rw [hwF]
    have h := hHu x
    rw [← congrFun hreal x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hwv : w ≤ v := by
    apply (projectiveProductToricProfile_le_iff hw hv hiw hiv).mpr
    intro x
    rw [hwF]
    have h := hHv x
    rw [← congrFun hreal x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hwR : w ≤ R := (le_rooftop_iff hu hv hw).mpr ⟨hwu, hwv⟩
  have hHR := (projectiveProductToricProfile_le_iff hw hR hiw hiR).mp hwR
  rw [hwF] at hHR
  apply le_antisymm hRH
  intro x
  rw [← congrFun hreal x]
  exact EReal.coe_le_coe (hHR x)

/-- Existing unconditional convex-family conjugation identifies the original
extended Legendre transform of the actual native rooftop, retaining all infinities. -/
theorem projectiveProductToricLegendre_rooftop {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v)
    (hne : rooftop (projectiveProductFSBackground n).form u v ≠ ⊥) :
    projectiveProductToricLegendre (rooftop (projectiveProductFSBackground n).form u v) =
      fun m => max (projectiveProductToricLegendre u m) (projectiveProductToricLegendre v m) := by
  unfold projectiveProductToricLegendre
  rw [projectiveProductToricProfile_rooftop hu hv hiu hiv hne, conjugate_convexInf]
  funext m
  simp [convexSup, iSup_bool_eq, sup_comm]

end SGPT.Toric
