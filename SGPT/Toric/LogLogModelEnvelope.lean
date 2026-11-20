import SGPT.Toric.ProjectiveLogLog
import SGPT.PSH.ThetaRooftop

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Literal ALL original theta-PSH competitors below zero with the source
additive singularity comparison. Empty families are retained. -/
def sourceSingularityCompetitors (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :=
  {v : X → EReal // A.IsThetaPSH θ v ∧ v ≤ 0 ∧ SGPT.PSH.SingularityLE v u}

/-- Actual neighborhood upper regularization of the literal competitor supremum. -/
def sourceSingularityEnvelope (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    X → EReal :=
  uscSup (fun v : sourceSingularityCompetitors θ u ↦ v.1)

theorem sourceSingularityEnvelope_le_zero (θ : AtlasClosedRealOneOneForm A)
    (u : X → EReal) : sourceSingularityEnvelope θ u ≤ 0 :=
  uscRegularization_le (continuous_const.upperSemicontinuous)
    (fun x ↦ iSup_le fun v ↦ v.2.2.1 x)

theorem le_sourceSingularityEnvelope {θ : AtlasClosedRealOneOneForm A}
    {u v : X → EReal} (hv : A.IsThetaPSH θ v) (hv0 : v ≤ 0)
    (hvu : SGPT.PSH.SingularityLE v u) : v ≤ sourceSingularityEnvelope θ u := by
  intro x
  change v x ≤ uscRegularization
    (fun y ↦ ⨆ t : sourceSingularityCompetitors θ u, t.1 y) x
  exact (le_iSup (fun t : sourceSingularityCompetitors θ u ↦ t.1 x)
    ⟨v, hv, hv0, hvu⟩).trans (le_uscRegularization
      (fun y ↦ ⨆ t : sourceSingularityCompetitors θ u, t.1 y) x)

theorem upperSemicontinuous_sourceSingularityEnvelope
    (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    UpperSemicontinuous (sourceSingularityEnvelope θ u) :=
  upperSemicontinuous_uscRegularization _

theorem isThetaPSH_sourceSingularityEnvelope_of_nonempty
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hn : Nonempty (sourceSingularityCompetitors θ u)) :
    A.IsThetaPSH θ (sourceSingularityEnvelope θ u) := by
  let := hn
  exact isThetaPSH_uscSup_of_majorant (w := fun _ ↦ (0 : EReal)) (fun v ↦ v.2.1)
    continuous_const.upperSemicontinuous (fun _ ↦ EReal.coe_ne_top (0 : ℝ))
    (fun v ↦ v.2.2.1)

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- Actual entropy conjugation already gives convexity of the finite partition. -/
theorem convexOn_projectiveLineLogPartition :
    ConvexOn ℝ univ projectiveLineLogPartition := by
  apply isConvex_coe_iff.mp
  have he : conjugate scalarPairing projectiveLineEntropy =
      fun x ↦ (projectiveLineLogPartition x : EReal) :=
    funext conjugate_projectiveLineEntropy
  rw [← he]
  exact isConvex_conjugate _ _

/-- Independently defined finite convex candidate profiles. -/
def logLogModelProfile (a x : ℝ) : ℝ :=
  a * x + (1 - a) * projectiveLineLogPartition x

theorem convexOn_logLogModelProfile {a : ℝ} (_ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ConvexOn ℝ univ (logLogModelProfile a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hL := convexOn_projectiveLineLogPartition.2 (mem_univ x) (mem_univ y) hs ht hst
  change projectiveLineLogPartition (s * x + t * y) ≤
    s * projectiveLineLogPartition x + t * projectiveLineLogPartition y at hL
  change logLogModelProfile a (s * x + t * y) ≤
    s * logLogModelProfile a x + t * logLogModelProfile a y
  unfold logLogModelProfile
  have h := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr ha1)
  nlinarith

theorem logLogModelProfile_le_partition {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    logLogModelProfile a x ≤ projectiveLineLogPartition x := by
  have hx := (le_max_right (0 : ℝ) x).trans (max_le_projectiveLineLogPartition x)
  have h := mul_le_mul_of_nonneg_left hx ha
  unfold logLogModelProfile
  nlinarith

theorem logLogModelProfile_le_support_add_log_two {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (x : ℝ) :
    logLogModelProfile a x ≤ max 0 x + Real.log 2 := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) x) ha
  have h2 := mul_le_mul_of_nonneg_left (projectiveLineLogPartition_le_max x)
    (sub_nonneg.mpr ha1)
  have h3 := mul_nonneg ha (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  unfold logLogModelProfile
  nlinarith

/-- A genuine finite global comparison constant, manufactured from log tangency. -/
def logLogModelComparisonConstant (a : ℝ) : ℝ :=
  max (-Real.log a - 1 + (1 - a) * Real.log 2)
    ((1 - a) * (logLogLambda + Real.log 2) - 2)

theorem logLogModelProfile_le_logLog_add {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (x : ℝ) :
    logLogModelProfile a x ≤ logLogProfile x + logLogModelComparisonConstant a := by
  have hell : 0 < logLogLambda := lt_trans (by norm_num) logLogLambda_gt_two
  have h1 : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  by_cases hx : x ≤ -logLogLambda
  · have ht : 0 < -x := by linarith
    have hlog := Real.log_le_sub_one_of_pos (mul_pos ha ht)
    rw [Real.log_mul ha.ne' ht.ne'] at hlog
    have hL : projectiveLineLogPartition x ≤ Real.log 2 := by
      have hmax : max (0 : ℝ) x = 0 := max_eq_left (by linarith)
      simpa only [hmax, zero_add] using projectiveLineLogPartition_le_max x
    have hLp := mul_le_mul_of_nonneg_left hL h1
    have hC := le_max_left (-Real.log a - 1 + (1 - a) * Real.log 2)
      ((1 - a) * (logLogLambda + Real.log 2) - 2)
    simp only [logLogProfile, if_pos hx, logLogModelProfile,
      logLogModelComparisonConstant]
    nlinarith
  · have hL : projectiveLineLogPartition x - x ≤ logLogLambda + Real.log 2 := by
      by_cases hx0 : 0 ≤ x
      · have hmax : max (0 : ℝ) x = x := max_eq_right hx0
        have hp := projectiveLineLogPartition_le_max x
        rw [hmax] at hp
        linarith
      · have hmax : max (0 : ℝ) x = 0 := max_eq_left (le_of_not_ge hx0)
        have hp := projectiveLineLogPartition_le_max x
        rw [hmax] at hp
        linarith
    have hLp := mul_le_mul_of_nonneg_left hL h1
    have hC := le_max_right (-Real.log a - 1 + (1 - a) * Real.log 2)
      ((1 - a) * (logLogLambda + Real.log 2) - 2)
    simp only [logLogProfile, if_neg hx, logLogModelProfile,
      logLogModelComparisonConstant]
    nlinarith

/-- The true one-coordinate realization of the manufactured finite candidates. -/
def logLogModelEuclideanProfile (a : ℝ) (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  logLogModelProfile a (x 0)

theorem logLogModelEuclideanProfile_mem_realGrowthClass {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    logLogModelEuclideanProfile a ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
  refine ⟨?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ s t hs ht hst
    simpa only [logLogModelEuclideanProfile, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      using (convexOn_logLogModelProfile ha ha1).2 (mem_univ (x 0))
        (mem_univ (y 0)) hs ht hst
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨Real.log 2, fun x ↦ ?_⟩
    rw [support_projectiveMomentInterval, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (logLogModelProfile_le_support_add_log_two ha ha1 (x 0))

/-- Genuine original theta-PSH inverse of the actual finite convex growth function. -/
def projectiveLogLogModelCandidate (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Projectivization ℂ (Fin 2 → ℂ) → EReal :=
  projectiveToricExtension (logLogModelEuclideanProfile a)
    (logLogModelEuclideanProfile_mem_realGrowthClass ha.le ha1)

theorem isThetaPSH_projectiveLogLogModelCandidate {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (projectiveLogLogModelCandidate a ha ha1) :=
  (projectiveToricExtension_spec _ (logLogModelEuclideanProfile_mem_realGrowthClass ha.le ha1)).1

theorem projectiveLogLogModelCandidate_offPotential {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    EqOn (projectiveLogLogModelCandidate a ha ha1)
      (projectiveToricOffPotential (logLogModelEuclideanProfile a)) projectiveToricBoundaryᶜ :=
  (projectiveToricExtension_spec _ (logLogModelEuclideanProfile_mem_realGrowthClass ha.le ha1)).2

/-- Actual torus values are finite and equal the printed scaled X0 cost. -/
theorem projectiveLogLogModelCandidate_off_value {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    projectiveLogLogModelCandidate a ha ha1 p =
      ((a * (tropicalization (projectiveModelChart false p) 0 -
        projectiveFSPotential (projectiveModelChart false p)) : ℝ) : EReal) := by
  rw [projectiveLogLogModelCandidate_offPotential ha ha1 hp]
  let z := projectiveModelChart false p
  have hz := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
  have hpart := projectiveLineLogPartition_tropicalization (hz 0)
  rw [← projectiveFSPotential_eq] at hpart
  change ((logLogModelProfile a (tropicalization z 0) - projectiveFSPotential z : ℝ) : EReal) = _
  congr 1
  unfold logLogModelProfile
  rw [hpart]
  ring

theorem projectiveLogLogModelCandidate_eq_scaled_section_off {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) {p : Projectivization ℂ (Fin 2 → ℂ)}
    (hp : p ∉ projectiveToricBoundary) :
    projectiveLogLogModelCandidate a ha ha1 p = (a : EReal) * projectiveLogSingularity p := by
  rw [projectiveLogLogModelCandidate_off_value ha ha1 hp, projectiveLogSingularity_offPotential hp]
  change ((a * (tropicalization (projectiveModelChart false p) 0 -
    projectiveFSPotential (projectiveModelChart false p)) : ℝ) : EReal) =
    (a : EReal) * ((tropicalization (projectiveModelChart false p) 0 -
      projectiveFSPotential (projectiveModelChart false p) : ℝ) : EReal)
  exact (EReal.coe_mul _ _).symm

/-- True bottom-filled analytic regularization supplies the global zero bound,
including both original projective boundary points. -/
theorem projectiveLogLogModelCandidate_le_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    projectiveLogLogModelCandidate a ha ha1 ≤ 0 := by
  intro p
  rw [projectiveThetaPSH_eq_analyticExtension (isThetaPSH_projectiveLogLogModelCandidate ha ha1)]
  apply uscRegularization_le_of_eventually_le
    (g := fun _ ↦ (0 : EReal)) continuous_const.continuousAt.upperSemicontinuousAt
  exact Eventually.of_forall fun q ↦ by
    by_cases hq : q ∈ projectiveToricBoundary
    · simp [hq]
    · simp only [if_neg hq]
      rw [projectiveLogLogModelCandidate_offPotential ha ha1 hq]
      let z := projectiveModelChart false q
      have hz := projectiveFiniteCoordinate_mem_torus_of_off_boundary hq
      have hpart := logLogModelProfile_le_partition ha.le (tropicalization z 0)
      rw [projectiveLineLogPartition_tropicalization (hz 0), ← projectiveFSPotential_eq] at hpart
      change ((logLogModelProfile a (tropicalization z 0) - projectiveFSPotential z : ℝ) : EReal) ≤ 0
      exact EReal.coe_le_coe (sub_nonpos.mpr hpart)

/-- Manufactured real comparison transfers through actual pole-inclusive filling. -/
theorem projectiveLogLogModelCandidate_singularityLE {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    SingularityLE (projectiveLogLogModelCandidate a ha ha1) projectiveLogLogPotential := by
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨logLogModelComparisonConstant a,
    projectiveThetaPSH_le_add_of_le_off (isThetaPSH_projectiveLogLogModelCandidate ha ha1)
      isThetaPSH_projectiveLogLogPotential (logLogModelComparisonConstant a) ?_⟩
  intro p hp
  rw [projectiveLogLogModelCandidate_offPotential ha ha1 hp, projectiveLogLogPotential_offPotential hp]
  change ((logLogModelProfile a (tropicalization (projectiveModelChart false p) 0) -
    projectiveFSPotential (projectiveModelChart false p) : ℝ) : EReal) ≤
    ((logLogProfile (tropicalization (projectiveModelChart false p) 0) -
      projectiveFSPotential (projectiveModelChart false p) : ℝ) : EReal) +
      (logLogModelComparisonConstant a : EReal)
  rw [← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr (by
    linarith [logLogModelProfile_le_logLog_add ha ha1
      (tropicalization (projectiveModelChart false p) 0)])

/-- Genuine competitors at every positive integer scale. -/
def logLogModelScale (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem logLogModelScale_pos (k : ℕ) : 0 < logLogModelScale k := by
  unfold logLogModelScale
  positivity

theorem logLogModelScale_le_one (k : ℕ) : logLogModelScale k ≤ 1 := by
  unfold logLogModelScale
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem tendsto_projectiveLogLogModelCandidate_off
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    Tendsto (fun k ↦ projectiveLogLogModelCandidate (logLogModelScale k)
      (logLogModelScale_pos k) (logLogModelScale_le_one k) p) atTop (𝓝 0) := by
  have hreal : Tendsto (fun k : ℕ ↦ logLogModelScale k *
      (tropicalization (projectiveModelChart false p) 0 -
        projectiveFSPotential (projectiveModelChart false p))) atTop (𝓝 0) := by
    simpa only [logLogModelScale, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
        (tropicalization (projectiveModelChart false p) 0 -
          projectiveFSPotential (projectiveModelChart false p))
  have hE : Tendsto (fun k : ℕ ↦ ((logLogModelScale k *
      (tropicalization (projectiveModelChart false p) 0 -
        projectiveFSPotential (projectiveModelChart false p)) : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := EReal.tendsto_coe.mpr hreal
  simpa only [Function.comp_apply, EReal.coe_zero,
    projectiveLogLogModelCandidate_off_value _ _ hp] using hE

theorem sourceSingularityEnvelope_logLog_nonneg_off
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    0 ≤ sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential p := by
  apply le_of_tendsto (tendsto_projectiveLogLogModelCandidate_off hp)
  exact Eventually.of_forall fun k ↦ le_sourceSingularityEnvelope
    (isThetaPSH_projectiveLogLogModelCandidate (logLogModelScale_pos k) (logLogModelScale_le_one k))
    (projectiveLogLogModelCandidate_le_zero (logLogModelScale_pos k) (logLogModelScale_le_one k))
    (projectiveLogLogModelCandidate_singularityLE (logLogModelScale_pos k) (logLogModelScale_le_one k)) p

/-- The literal original model envelope is zero on the WHOLE quotient P1.
No nonpluripolar mass assertion is an input. -/
theorem sourceSingularityEnvelope_projectiveLogLog_eq_zero :
    sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential = 0 := by
  apply le_antisymm (sourceSingularityEnvelope_le_zero _ _)
  have hd : Dense (projectiveToricBoundaryᶜ) :=
    interior_eq_empty_iff_dense_compl.mp interior_projectiveToricBoundary
  have hs : projectiveToricBoundaryᶜ ⊆
      {p | 0 ≤ sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential p} :=
    fun _ hp ↦ sourceSingularityEnvelope_logLog_nonneg_off hp
  have hc : IsClosed
      {p | 0 ≤ sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential p} :=
    (upperSemicontinuous_sourceSingularityEnvelope _ _).isClosed_preimage 0
  intro p
  exact closure_minimal hs hc (hd p)

theorem sourceSingularityCompetitors_logLog_nonempty :
    Nonempty (sourceSingularityCompetitors projectiveFSForm projectiveLogLogPotential) :=
  ⟨⟨projectiveLogLogModelCandidate (logLogModelScale 0)
      (logLogModelScale_pos 0) (logLogModelScale_le_one 0),
    isThetaPSH_projectiveLogLogModelCandidate (logLogModelScale_pos 0) (logLogModelScale_le_one 0),
    projectiveLogLogModelCandidate_le_zero (logLogModelScale_pos 0) (logLogModelScale_le_one 0),
    projectiveLogLogModelCandidate_singularityLE (logLogModelScale_pos 0) (logLogModelScale_le_one 0)⟩⟩

theorem isThetaPSH_sourceSingularityEnvelope_logLog :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm
      (sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential) :=
  isThetaPSH_sourceSingularityEnvelope_of_nonempty sourceSingularityCompetitors_logLog_nonempty

/-- The original pole makes the claimed difference of singularity types actual. -/
theorem not_singularityEquiv_projectiveLogLog_envelope :
    ¬ SingularityEquiv projectiveLogLogPotential
      (sourceSingularityEnvelope projectiveFSForm projectiveLogLogPotential) := by
  intro h
  have hrev := (singularityEquiv_iff _ _).mp h |>.2
  rw [sourceSingularityEnvelope_projectiveLogLog_eq_zero] at hrev
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hrev
  have h0 := hC projectiveOrigin
  simp [projectiveLogLogPotential_origin] at h0

end SGPT.Toric
