import SGPT.Toric.ProjectiveProductNativeEnergy
import SGPT.Convex.ConjugateTruncationLimit

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology ENNReal RealInnerProductSpace

/-- The actual product native zero is a genuine model, with its produced positive n! mass. -/
theorem isModelPotential_projectiveProductZero (n : ℕ) :
    IsModelPotential (projectiveProductFSBackground n).form
      (fun _ : projectiveProductSpace n => (0 : EReal)) := by
  have h0 := isThetaPshPotential_projectiveProductZero n
  have hm : DiagonalMass.diagonalPotentialMass (projectiveProductFSBackground n).form
      (fun _ : projectiveProductSpace n => (0 : EReal)) h0 = (n.factorial : ENNReal) :=
    projectiveProductZeroMixedMeasure_univ n
  refine ⟨h0, ?_, ?_⟩
  · exact le_antisymm (self_le_singularityEnvelope h0 le_rfl)
      (singularityEnvelope_le_zero _ _)
  · rw [hm]
    exact_mod_cast Nat.factorial_pos n

/-- Literal original lower floors preserve source poles until taking their actual maximum. -/
def projectiveProductToricTruncation {n : ℕ} (u : projectiveProductSpace n → EReal)
    (j : ℕ) (p : projectiveProductSpace n) : EReal := max (u p) ((-(j : ℝ) : ℝ) : EReal)

private theorem truncation_eq_native {n : ℕ} (u : projectiveProductSpace n → EReal) (j : ℕ) :
    projectiveProductToricTruncation u j = MongeAmpereEnergyDecreasing.truncation
      (fun _ : projectiveProductSpace n => (0 : EReal)) u j := by
  funext p
  simp only [MongeAmpereEnergyDecreasing.truncation, projectiveProductToricTruncation,
    zero_sub, ← EReal.coe_neg]

/-- Actual native maxima and the genuine finite lower floor manufacture strong native PSH. -/
theorem isThetaPshPotential_projectiveProductToricTruncation {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (j : ℕ) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (projectiveProductToricTruncation u j) := by
  have hc := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const
    (isThetaPshPotential_projectiveProductZero n).1 (j : ℝ)
  have hmax := BoundedGlobalProduct.ThetaPlurisubharmonic.max hu.1 hc
  refine ⟨?_, BoundedPotentialSmoothingOfAlgebraicApproximation.locallyNondegenerate_of_coe_le
    (fun p => le_max_right (u p) ((-(j : ℝ) : ℝ) : EReal))⟩
  change ThetaPlurisubharmonic (projectiveProductFSBackground n).form.val
    (fun p => max (u p) ((-(j : ℝ) : ℝ) : EReal))
  simpa only [zero_sub, ← EReal.coe_neg] using hmax

/-- The actual source normalization supplies true finite original bounds at every point. -/
theorem isBoundedPotential_projectiveProductToricTruncation {n : ℕ}
    {u : projectiveProductSpace n → EReal} (hle : u ≤ fun _ => (0 : EReal)) (j : ℕ) :
    IsBoundedPotential (projectiveProductToricTruncation u j) := by
  refine ⟨-(j : ℝ), 0, fun p => ⟨le_max_right _ _, ?_⟩⟩
  apply max_le (hle p)
  exact EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg j))

/-- Actual original homogeneous circle invariance preserves the native lower floor. -/
theorem projectiveProductCircleInvariant_truncation {n : ℕ}
    {u : projectiveProductSpace n → EReal} (hi : ProjectiveProductCircleInvariant u) (j : ℕ) :
    ProjectiveProductCircleInvariant (projectiveProductToricTruncation u j) := by
  intro a ha p
  simp only [projectiveProductToricTruncation, hi a ha p]

/-- The actual native floors decrease at every original source point. -/
theorem projectiveProductToricTruncation_antitone {n : ℕ}
    (u : projectiveProductSpace n → EReal) (p : projectiveProductSpace n) :
    Antitone (fun j => projectiveProductToricTruncation u j p) := by
  simp_rw [truncation_eq_native]
  exact MongeAmpereEnergyDecreasing.truncation_antitone _ _ p

/-- Genuine native truncations converge at every original point, including source poles. -/
theorem tendsto_projectiveProductToricTruncation {n : ℕ}
    (u : projectiveProductSpace n → EReal) (p : projectiveProductSpace n) :
    Tendsto (fun j => projectiveProductToricTruncation u j p) atTop (𝓝 (u p)) := by
  simp_rw [truncation_eq_native]
  exact MongeAmpereEnergyDecreasing.tendsto_truncation ⟨0, 0, fun _ => by simp⟩ p

/-- The actual finite correction commutes with the source maximum before real conversion. -/
theorem projectiveProductToricCorrectedDescent_truncation {n : ℕ}
    (u : projectiveProductSpace n → EReal) (j : ℕ) :
    projectiveProductToricCorrectedDescent (projectiveProductToricTruncation u j) = fun x =>
      max (projectiveProductToricCorrectedDescent u x)
        (projectiveProductToricCorrectedDescent (fun _ : projectiveProductSpace n => (0 : EReal)) x -
          ((j : ℝ) : EReal)) := by
  funext x
  let p := (projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)
  let r := projectiveProductReferenceProfile n x
  have he : ((-(j : ℝ) : ℝ) : EReal) + (r : EReal) = (r : EReal) - ((j : ℝ) : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    ring
  change max (u p) ((-(j : ℝ) : ℝ) : EReal) + (r : EReal) =
    max (u p + (r : EReal)) ((0 + (r : EReal)) - ((j : ℝ) : EReal))
  rw [zero_add]
  by_cases h : u p ≤ ((-(j : ℝ) : ℝ) : EReal)
  · rw [max_eq_right h, max_eq_right (by rw [← he]; exact add_le_add h le_rfl)]
    exact he
  · have h' := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (by rw [← he]; exact add_le_add h' le_rfl)]

private theorem profile_coe_eq {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) =
      projectiveProductToricCorrectedDescent u := by
  funext x
  have hf := finite_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi) x
  exact EReal.coe_toReal hf.1 hf.2

/-- Manufactured actual source finiteness gives the literal real reference-floor profile. -/
theorem projectiveProductToricEuclideanProfile_truncation {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (j : ℕ) :
    projectiveProductToricEuclideanProfile (projectiveProductToricTruncation u j) =
      realLowerTruncation (projectiveProductToricEuclideanProfile u)
        (projectiveProductToricEuclideanProfile (fun _ : projectiveProductSpace n => (0 : EReal))) j := by
  funext x
  unfold projectiveProductToricEuclideanProfile
  rw [projectiveProductToricCorrectedDescent_truncation]
  dsimp only
  rw [← congrFun (profile_coe_eq hu hi) x,
    ← congrFun (profile_coe_eq (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl)) x,
    ← EReal.coe_sub]
  change (max (projectiveProductToricEuclideanProfile u x : EReal)
      ((projectiveProductToricEuclideanProfile (fun _ : projectiveProductSpace n => (0 : EReal)) x -
        j : ℝ) : EReal)).toReal =
    max (projectiveProductToricEuclideanProfile u x)
      (projectiveProductToricEuclideanProfile (fun _ : projectiveProductSpace n => (0 : EReal)) x - j)
  by_cases h : projectiveProductToricEuclideanProfile u x ≤
      projectiveProductToricEuclideanProfile (fun _ : projectiveProductSpace n => (0 : EReal)) x - j
  · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe, max_eq_right h]
  · have h' := le_of_not_ge h
    rw [max_eq_left (EReal.coe_le_coe_iff.mpr h'), EReal.toReal_coe, max_eq_left h']

/-- Actual real lower floors reverse to genuine extended conjugate monotonicity. -/
theorem projectiveProductToricLegendre_truncation_mono {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    Monotone (fun j => projectiveProductToricLegendre (projectiveProductToricTruncation u j)) := by
  unfold projectiveProductToricLegendre
  simp_rw [projectiveProductToricEuclideanProfile_truncation hu hi]
  exact conjugate_realLowerTruncation_mono _ _

/-- True conjugation of the actual pointwise floor-infimum retains every infinite value. -/
theorem projectiveProductToricLegendre_eq_iSup_truncation {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    projectiveProductToricLegendre u = fun m =>
      ⨆ j : ℕ, projectiveProductToricLegendre (projectiveProductToricTruncation u j) m := by
  unfold projectiveProductToricLegendre
  simp_rw [projectiveProductToricEuclideanProfile_truncation hu hi]
  exact conjugate_eq_iSup_realLowerTruncation _ _

/-- Genuine source-native profile floors manufacture actual extended-gap MCT on the real cube. -/
theorem projectiveProductToricLegendre_gap_lintegral_eq_iSup_truncation {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (∫⁻ m in euclideanUnitCube n, (projectiveProductToricLegendre u m -
      projectiveProductToricLegendre (fun _ : projectiveProductSpace n => (0 : EReal)) m).toENNReal) =
      ⨆ j : ℕ, ∫⁻ m in euclideanUnitCube n,
        (projectiveProductToricLegendre (projectiveProductToricTruncation u j) m -
          projectiveProductToricLegendre (fun _ : projectiveProductSpace n => (0 : EReal)) m).toENNReal := by
  unfold projectiveProductToricLegendre
  simp_rw [projectiveProductToricEuclideanProfile_truncation hu hi]
  exact lintegral_conjugate_gap_eq_iSup_realLowerTruncation volume
    (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n) (convex_euclideanUnitCube n) _ _
    (projectiveProductToricProfile_mem_boundedGrowthClass
      (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl) ⟨0, 0, fun _ => by simp⟩)

end SGPT.Toric
