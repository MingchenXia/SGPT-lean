import SGPT.Toric.TropicalConvexity
import SGPT.Toric.ProjectiveTorusAction
import SGPT.Toric.Conjugacy
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical

/-- Literal invariance under the actual compact homogeneous circle action. -/
def ProjectiveCircleInvariant (u : Projectivization ℂ (Fin 2 → ℂ) → EReal) : Prop :=
  ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ p, u (projectiveTorusAction a p) = u p

/-- Equal genuine moduli differ by an actual unit-circle homogeneous action. -/
theorem ProjectiveCircleInvariant.eq_of_norm_eq
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal} (hu : ProjectiveCircleInvariant u)
    {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hn : ‖z‖ = ‖w‖) :
    u (OnePoint.equivProjectivization ℂ z) = u (OnePoint.equivProjectivization ℂ w) := by
  let a : ℂˣ := Units.mk0 (z / w) (div_ne_zero hz hw)
  have ha : ‖(a : ℂ)‖ = 1 := by
    change ‖z / w‖ = 1
    rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hw)]
  have h := hu a ha (OnePoint.equivProjectivization ℂ w)
  rw [projectiveTorusAction_finite] at h
  simpa only [a, Units.val_mk0, div_mul_cancel₀ _ hw] using h

/-- The original logarithmic-coordinate descent uses the actual positive section. -/
def projectiveToricDescent (u : Projectivization ℂ (Fin 2 → ℂ) → EReal)
    (x : EuclideanSpace ℝ (Fin 1)) : EReal :=
  u (OnePoint.equivProjectivization ℂ (expCoordinates x 0))

/-- Genuine circle invariance gives the exact original logarithmic pullback. -/
theorem projectiveToricDescent_tropicalization
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal} (hu : ProjectiveCircleInvariant u)
    {z : ComplexModel 1} (hz : z ∈ complexTorus 1) :
    projectiveToricDescent u (tropicalization z) =
      u (OnePoint.equivProjectivization ℂ (z 0)) := by
  have he := expCoordinates_mem_complexTorus (tropicalization z)
  have hlog := congrArg (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0)
    (tropicalization_expCoordinates (tropicalization z))
  rw [tropicalization_apply_eq_log_norm_sq, tropicalization_apply_eq_log_norm_sq] at hlog
  have hs := congrArg Real.exp hlog
  rw [Real.exp_log (pow_pos (norm_pos_iff.mpr (he 0)) 2),
    Real.exp_log (pow_pos (norm_pos_iff.mpr (hz 0)) 2)] at hs
  have hn : ‖expCoordinates (tropicalization z) 0‖ = ‖z 0‖ := by
    nlinarith [norm_nonneg (expCoordinates (tropicalization z) 0), norm_nonneg (z 0)]
  exact hu.eq_of_norm_eq (he 0) (hz 0) hn

/-- The corrected literal source convex coordinate includes the computed reference partition. -/
def projectiveToricCorrectedDescent (u : Projectivization ℂ (Fin 2 → ℂ) → EReal)
    (x : EuclideanSpace ℝ (Fin 1)) : EReal :=
  projectiveToricDescent u x + (projectiveLineLogPartition (x 0) : EReal)

/-- The descended corrected function is exactly the genuine preferred corrected chart function. -/
theorem projectiveToricCorrectedDescent_tropicalPullback
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal} (hu : ProjectiveCircleInvariant u)
    {z : ComplexModel 1} (hz : z ∈ complexTorus 1) :
    tropicalPullback (projectiveToricCorrectedDescent u) z =
      u ((projectiveModelChart false).symm z) + (projectiveFSPotential z : EReal) := by
  change projectiveToricDescent u (tropicalization z) +
    (projectiveLineLogPartition (tropicalization z 0) : EReal) = _
  rw [projectiveToricDescent_tropicalization hu hz,
    projectiveLineLogPartition_tropicalization (hz 0), ← projectiveFSPotential_eq]
  congr 1

/-- Original universal theta tests and true open-torus witnesses produce the full disc PSH input. -/
theorem pshOn_projectiveToricCorrectedDescent
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    PSHOn (tropicalPullback (projectiveToricCorrectedDescent u)) (complexTorus 1) := by
  let e := projectiveModelChart false
  have hp := hu.preferred_chart_corrected (i := false)
    contDiff_projectiveFSPotential.contDiffOn (fun _ _ ↦ rfl)
  change PlurisubharmonicOn
    (fun z ↦ u (e.symm z) + (projectiveFSPotential z : EReal)) e.target at hp
  have htarget (z : ComplexModel 1) : z ∈ e.target := by
    simp [e, projectiveModelChart, projectiveQuotientScalarChart_target]
  have hraw : PlurisubharmonicOn
      (tropicalPullback (projectiveToricCorrectedDescent u)) (complexTorus 1) := by
    intro z hz
    apply (hp z (htarget z)).congr
    filter_upwards [(isOpen_complexTorus 1).mem_nhds hz] with w hw
    exact (projectiveToricCorrectedDescent_tropicalPullback hi hw).symm
  refine ⟨hraw.discPshOn, ?_⟩
  let O := e.source ∩ e ⁻¹' complexTorus 1
  have hO : IsOpen O := e.isOpen_inter_preimage (isOpen_complexTorus 1)
  let z₀ := expCoordinates (0 : EuclideanSpace ℝ (Fin 1))
  have hz₀ : z₀ ∈ complexTorus 1 := expCoordinates_mem_complexTorus 0
  have hxO : e.symm z₀ ∈ O := by
    refine ⟨e.mapsTo_symm (htarget z₀), ?_⟩
    change e (e.symm z₀) ∈ complexTorus 1
    rwa [e.right_inv (htarget z₀)]
  obtain ⟨p, hpO, hfin⟩ := hu.locallyNondegenerate (e.symm z₀) (mem_univ _) O hO hxO
  refine ⟨e p, hpO.2.2, ?_⟩
  rw [projectiveToricCorrectedDescent_tropicalPullback hi hpO.2.2]
  change u (e.symm (e p)) + (projectiveFSPotential (e p) : EReal) ≠ ⊥
  rw [e.left_inv hpO.2.1]
  intro hb
  rcases EReal.add_eq_bot_iff.mp hb with hb | hb
  · exact hfin hb
  · exact EReal.coe_ne_bot _ hb

/-- Actual invariant original theta-PSH potentials produce finite real convex logarithmic functions. -/
theorem exists_real_convex_projectiveToricCorrectedDescent
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, ConvexOn ℝ univ f ∧
      projectiveToricCorrectedDescent u = fun x ↦ (f x : EReal) :=
  exists_real_convex_of_pshOn_tropicalPullback (pshOn_projectiveToricCorrectedDescent hu hi)

/-- Actual quotient compactness and genuine upper semicontinuity produce a global finite bound. -/
theorem exists_upper_bound_projectiveThetaPSH
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    ∃ C : ℝ, ∀ p, u p ≤ (C : EReal) := by
  let : CompactSpace (Projectivization ℂ (Fin 2 → ℂ)) := projectiveLineHomeomorph.compactSpace
  let : Nonempty (Projectivization ℂ (Fin 2 → ℂ)) := ⟨OnePoint.equivProjectivization ℂ (0 : ℂ)⟩
  exact exists_real_upper_bound_of_upperSemicontinuous hu.upperSemicontinuous hu.1

/-- The original compact theta potential gives its true finite comparison with the reference partition. -/
theorem projectiveToricCorrectedDescent_le_partition
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    ∃ C : ℝ, ∀ x, projectiveToricCorrectedDescent u x ≤
      ((projectiveLineLogPartition (x 0) + C : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_projectiveThetaPSH hu
  refine ⟨C, fun x ↦ ?_⟩
  have h := add_le_add_right (hC (OnePoint.equivProjectivization ℂ (expCoordinates x 0)))
    (projectiveLineLogPartition (x 0) : EReal)
  simpa only [projectiveToricCorrectedDescent, projectiveToricDescent,
    ← EReal.coe_add, add_comm] using h

/-- The genuine two-term logarithmic bound reuses the actual finite-sum producer. -/
theorem projectiveLineLogPartition_le_max (x : ℝ) :
    projectiveLineLogPartition x ≤ max 0 x + Real.log 2 := by
  have h := SGPT.Convex.logSumExp_le_of_bound (fun b : Bool ↦ if b then x else 0)
    (r := max 0 x) (by intro b; cases b; exact le_max_left _ _; exact le_max_right _ _)
  simpa [SGPT.Convex.logSumExp, Fintype.sum_bool, projectiveLineLogPartition, add_comm] using h

/-- The original descended convex coordinate has its actual interval-support growth bound. -/
theorem projectiveToricCorrectedDescent_le_max
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    ∃ C : ℝ, ∀ x, projectiveToricCorrectedDescent u x ≤
      ((max 0 (x 0) + C : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := projectiveToricCorrectedDescent_le_partition hu
  refine ⟨Real.log 2 + C, fun x ↦ ?_⟩
  have hb : projectiveLineLogPartition (x 0) + C ≤ max 0 (x 0) + (Real.log 2 + C) := by
    linarith [projectiveLineLogPartition_le_max (x 0)]
  exact (hC x).trans (by exact_mod_cast hb)

/-- The original projective-line moment interval in the actual one-dimensional real coordinates. -/
def projectiveMomentInterval : Set (EuclideanSpace ℝ (Fin 1)) :=
  {m | 0 ≤ m 0 ∧ m 0 ≤ 1}

/-- Its actual dual support is exactly the original maximum of the two endpoint costs. -/
theorem support_projectiveMomentInterval (x : EuclideanSpace ℝ (Fin 1)) :
    SGPT.Convex.support (innerₗ (EuclideanSpace ℝ (Fin 1))).flip projectiveMomentInterval x =
      ((max (0 : ℝ) (x 0) : ℝ) : EReal) := by
  have he (m : EuclideanSpace ℝ (Fin 1)) :
      (innerₗ (EuclideanSpace ℝ (Fin 1))).flip m x = m 0 * x 0 := by
    simp [innerₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  apply le_antisymm
  · apply iSup_le
    intro m
    have hm : 0 ≤ m.val 0 ∧ m.val 0 ≤ 1 := m.property
    have h : m.val 0 * x 0 ≤ max 0 (x 0) := by
      by_cases hx : 0 ≤ x 0
      · rw [max_eq_right hx]
        nlinarith [hm.1, hm.2]
      · rw [max_eq_left (le_of_not_ge hx)]
        exact mul_nonpos_of_nonneg_of_nonpos hm.1 (le_of_not_ge hx)
    change ((innerₗ (EuclideanSpace ℝ (Fin 1))).flip m.val x : EReal) ≤ _
    rw [he]
    exact EReal.coe_le_coe_iff.mpr h
  · by_cases hx : 0 ≤ x 0
    · rw [max_eq_right hx]
      let m : projectiveMomentInterval := ⟨WithLp.toLp 2 (fun _ ↦ (1 : ℝ)), by simp [projectiveMomentInterval]⟩
      have h := le_iSup (fun p : projectiveMomentInterval ↦
        ((innerₗ (EuclideanSpace ℝ (Fin 1))).flip p.val x : EReal)) m
      have hm : m.val 0 = 1 := rfl
      have hcost : (innerₗ (EuclideanSpace ℝ (Fin 1))).flip m.val x = x 0 := by
        rw [he, hm, one_mul]
      rw [hcost] at h
      exact h
    · rw [max_eq_left (le_of_not_ge hx)]
      let m : projectiveMomentInterval := ⟨0, by simp [projectiveMomentInterval]⟩
      have h := le_iSup (fun p : projectiveMomentInterval ↦
        ((innerₗ (EuclideanSpace ℝ (Fin 1))).flip p.val x : EReal)) m
      have hm : m.val 0 = 0 := rfl
      have hcost : (innerₗ (EuclideanSpace ℝ (Fin 1))).flip m.val x = 0 := by
        rw [he, hm, zero_mul]
      rw [hcost, EReal.coe_zero] at h
      exact h

/-- The original invariant theta potential produces an actual member of the book's proper support-growth class. -/
theorem projectiveToricCorrectedDescent_mem_growthClass
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricCorrectedDescent u ∈ SGPT.Convex.GrowthClass
      (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
  obtain ⟨f, hf, heq⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact SGPT.Convex.isProper_coe_of_convexOn hf
  · obtain ⟨C, hC⟩ := projectiveToricCorrectedDescent_le_max hu
    apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x ↦ ?_⟩
    rw [support_projectiveMomentInterval, ← EReal.coe_add]
    exact hC x

end SGPT.Toric
