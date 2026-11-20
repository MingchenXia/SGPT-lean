import SGPT.Trace.OptimalNativeNormalBackground
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Global exhaustion on the actual full native pencil over an open disc

No supplied pseudoconvexity. Properness is relative to the original open
disc, and every original common base-locus point is retained.
Blueprint: work/sgpt-resume-20261114/bert-e2-disc-exhaustion/blueprint/bert-e2-disc-exhaustion.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniDiscExhaustion
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.BertiniNormalMetric
open SGPT.Trace.TwistedL2
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalBackground
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini

/-- The original actual open parameter disc. -/
def parameterDisc (ρ : ℝ) : TopologicalSpace.Opens (ComplexModel 1) :=
  ⟨ball 0 ρ, isOpen_ball⟩

/-- Proper holomorphic maps to the actual open disc produce a literal
GLOBAL smooth PSH exhaustion, with original compact sublevels. -/
theorem actual_global_disc_exhaustion {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {ρ : ℝ} (hρ : 0 < ρ)
    {g : Y → parameterDisc ρ}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g) (hgp : IsProperMap g) :
    ChartSmooth (n := n) (fun y => ballExhaustion 0 ρ (g y).val) ∧
    (∀ (c : ComplexChart n Y) (z : ComplexModel n), z ∈ c.val.target → ∀ v : ComplexModel n,
      0 ≤ leviForm (fun w => ballExhaustion 0 ρ (g (c.val.symm w)).val) z v) ∧
    ∀ t : ℝ, IsCompact {y | ballExhaustion 0 ρ (g y).val ≤ t} := by
  let F : Y → ComplexModel 1 := fun y => (g y).val
  have hF := (OpensRestriction.contMDiff_val (parameterDisc ρ)).comp hg
  let d := complexChartAt (n := 1) (0 : ComplexModel 1)
  have hdom (c : ComplexChart n Y) : c.val.target ⊆ coordinateDomain F c d := by
    intro z hz
    exact ⟨hz, Set.mem_univ _⟩
  have hmaps (c : ComplexChart n Y) : MapsTo (fun w => F (c.val.symm w)) c.val.target (ball 0 ρ) :=
    fun w _ => (g (c.val.symm w)).property
  have hsm : ChartSmooth (n := n) (fun y => ballExhaustion 0 ρ (g y).val) := by
    intro c
    exact (contDiffOn_ballExhaustion 0 ρ).comp
      ((coordinateMap_contDiffOn_real hF c d).mono (hdom c)) (hmaps c)
  have hpsh (c : ComplexChart n Y) : PlurisubharmonicOn
      (fun w => (ballExhaustion 0 ρ (g (c.val.symm w)).val : EReal)) c.val.target := by
    have hfc : DifferentiableOn ℂ (fun w => F (c.val.symm w)) c.val.target :=
      ((coordinateMap_contDiffOn hF c d).differentiableOn (by simp)).mono (hdom c)
    exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic c.val.open_target hfc (hmaps c)
      (plurisubharmonicOn_of_convexOn isOpen_ball (convexOn_ballExhaustion 0 ρ)
        (contDiffOn_ballExhaustion 0 ρ).continuousOn)
  refine ⟨hsm, fun c z hz v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
    (U := ⟨c.val.target, c.val.open_target⟩) (hsm c) (hpsh c) hz v, ?_⟩
  have hc : Continuous (fun y => ballExhaustion 0 ρ (g y).val) := continuous_of_chartSmooth' hsm
  intro t
  by_cases ht : 0 < t
  · let s := Real.sqrt (max (ρ ^ 2 - t⁻¹) 0)
    have hsr : s < ρ := by
      rw [show s = Real.sqrt (max (ρ ^ 2 - t⁻¹) 0) from rfl, Real.sqrt_lt' hρ]
      exact max_lt (by linarith [inv_pos.mpr ht]) (by positivity)
    let K : Set (parameterDisc ρ) := {u | u.val ∈ closedBall (0 : ComplexModel 1) s}
    have hKc : IsCompact K := by
      apply Subtype.isCompact_iff.mpr
      have himage : (Subtype.val : parameterDisc ρ → ComplexModel 1) '' K = closedBall 0 s := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact hu
        · intro hz
          exact ⟨⟨z, closedBall_subset_ball hsr hz⟩, hz, rfl⟩
      rw [himage]
      exact isCompact_closedBall 0 s
    have hpK := hgp.isCompact_preimage hKc
    have hset : {y | ballExhaustion 0 ρ (g y).val ≤ t} =
        g ⁻¹' K ∩ (fun y => ballExhaustion 0 ρ (g y).val) ⁻¹' Iic t := by
      ext y
      constructor
      · intro hyt
        refine ⟨?_, hyt⟩
        have hpos := ballExhaustion_pos (g y).property
        have h1 : t⁻¹ ≤ ρ ^ 2 - ‖(g y).val - 0‖ ^ 2 := by
          have h := (inv_le_inv₀ ht hpos).mpr hyt
          simpa only [ballExhaustion, inv_inv] using h
        change (g y).val ∈ closedBall (0 : ComplexModel 1) s
        rw [mem_closedBall, dist_eq_norm]
        exact Real.le_sqrt_of_sq_le (le_max_of_le_left (by linarith))
      · exact fun hy => hy.2
    rw [hset]
    exact hpK.inter_right (isClosed_Iic.preimage hc)
  · convert isCompact_empty
    ext y
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_le_of_lt (not_lt.mp ht) (ballExhaustion_pos (g y).property)

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)

/-- Literal original full incidence over the actual open disc: no supplied
exhaustion, no deleted pencil base locus. -/
theorem actual_pencil_disc_exhaustion [CompactSpace X] {ρ : ℝ} (hρ : 0 < ρ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
    haveI := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
    ChartSmooth (n := n) (fun q : familyIncidence p i a v (parameterDisc ρ) =>
      ballExhaustion 0 ρ q.val.1.val) ∧
    (∀ (c : ComplexChart n (familyIncidence p i a v (parameterDisc ρ))) (z : ComplexModel n),
      z ∈ c.val.target → ∀ w : ComplexModel n,
      0 ≤ leviForm (fun y => ballExhaustion 0 ρ (c.val.symm y).val.1.val) z w) ∧
    ∀ t : ℝ, IsCompact {q : familyIncidence p i a v (parameterDisc ρ) |
      ballExhaustion 0 ρ q.val.1.val ≤ t} := by
  let := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
  have := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
  exact actual_global_disc_exhaustion hρ
    (contMDiff_familyProjection p i a v (parameterDisc ρ) hp hsm)
    (isProperMap_familyProjection p i a v (parameterDisc ρ) hp)

omit [TopologicalSpace X] in
theorem actual_pencil_normal_radius_lt_one {ρ : ℝ} (hρ : 0 < ρ)
    (q : familyIncidence p i a v (parameterDisc ρ)) :
    nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q < 1 := by
  have hnorm : ‖q.val.1.val‖ < ρ := by
    have hq := q.val.1.property
    change q.val.1.val ∈ ball (0 : ComplexModel 1) ρ at hq
    simpa only [mem_ball, dist_zero_right] using hq
  have hcoord : ‖q.val.1.val 0‖ < ρ := (PiLp.norm_apply_le q.val.1.val (0 : Fin 1)).trans_lt hnorm
  have hnonneg : 0 ≤ ‖q.val.1.val 0‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hlt : ‖q.val.1.val 0‖ / ρ < 1 := (div_lt_one hρ).mpr hcoord
  change ‖q.val.1.val 0 / (ρ : ℂ)‖ ^ 2 < 1
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

end SGPT.Trace.BertiniDiscExhaustion
