import SGPT.Convex.UnitCubeSupport
import SGPT.Convex.GrowthSum
import SGPT.Toric.ProjectiveProductToricProfile
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology RealInnerProductSpace
/-- The produced actual product Kähler form manufactures genuine native PSH of zero. -/
theorem isThetaPshPotential_projectiveProductZero (n : ℕ) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (fun _ : projectiveProductSpace n => (0 : EReal)) :=
  (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (projectiveProductFSBackground n).isSemipositive

private theorem product_zero_profile (n : ℕ) :
    projectiveProductToricEuclideanProfile (fun _ : projectiveProductSpace n => (0 : EReal)) =
      projectiveProductReferenceProfile n := by
  funext x
  simp [projectiveProductToricEuclideanProfile, projectiveProductToricCorrectedDescent,
    projectiveProductToricDescent]

private theorem proper_real_profile {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ univ f) : IsProper (fun x => (f x : EReal)) :=
  ⟨isConvex_coe_iff.mpr hf, ⟨0, EReal.coe_lt_top _⟩, fun x => EReal.coe_ne_bot (f x)⟩

private theorem closed_real_profile {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ univ f) : IsClosedConvex (fun x => (f x : EReal)) :=
  isClosedConvex_of_isProper_full_domain (proper_real_profile hf)
    (by ext x; simp [effectiveDomain])

private theorem reference_upper (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    projectiveProductReferenceProfile n x ≤ (∑ i : Fin n, max 0 (x i)) + n * Real.log 2 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    projectiveLineLogPartition_le_max (x i))
  simpa only [projectiveProductReferenceProfile, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

private theorem reference_lower (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n, max 0 (x i) ≤ projectiveProductReferenceProfile n x :=
  Finset.sum_le_sum (fun i _ => max_le_projectiveLineLogPartition (x i))

/-- Actual source partition inequalities supply both original support comparisons. -/
theorem projectiveProductReferenceProfile_boundedGrowthClass (n : ℕ) :
    (fun x => (projectiveProductReferenceProfile n x : EReal)) ∈
      BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n) := by
  have hc := projectiveProductToricEuclideanProfile_convex
    (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl)
  rw [product_zero_profile] at hc
  refine ⟨closed_real_profile hc, ?_, ?_⟩
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨n * Real.log 2, fun x => ?_⟩
    rw [support_euclideanUnitCube, ← EReal.coe_add]
    exact EReal.coe_le_coe (reference_upper n x)
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨0, fun x => ?_⟩
    rw [support_euclideanUnitCube, EReal.coe_zero, add_zero]
    exact EReal.coe_le_coe (reference_lower n x)

private theorem product_profile_coe {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (x : EuclideanSpace ℝ (Fin n)) :
    (projectiveProductToricEuclideanProfile u x : EReal) =
      u ((projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)) +
        (projectiveProductReferenceProfile n x : EReal) := by
  have h := projectiveProductToricEuclideanProfile_corrected hu hi (expCoordinates_mem_complexTorus x)
  have hρ := projectiveProductReferenceProfile_tropicalization (expCoordinates_mem_complexTorus x)
  change u ((projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)) +
    (projectiveProductFSPotential n (expCoordinates x) : EReal) =
    (projectiveProductToricEuclideanProfile u (tropicalization (expCoordinates x)) : EReal) at h
  rw [tropicalization_expCoordinates] at h hρ
  rw [← hρ] at h
  exact h.symm

/-- Genuine original compact native upper bounds produce original support growth,
retaining possible source poles. -/
theorem projectiveProductToricProfile_mem_growthClass {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈
      GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n) := by
  let : Nonempty (projectiveProductSpace n) :=
    ⟨(projectiveProductCoordinates n).symm (fun _ => projectiveOrigin)⟩
  obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
  refine ⟨proper_real_profile (projectiveProductToricEuclideanProfile_convex hu hi), ?_⟩
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨n * Real.log 2 + C, fun x => ?_⟩
  have h : u ((projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)) +
      (projectiveProductReferenceProfile n x : EReal) ≤
      (C : EReal) + (projectiveProductReferenceProfile n x : EReal) :=
    add_le_add (hC _) le_rfl
  rw [← product_profile_coe hu hi x, ← EReal.coe_add] at h
  rw [support_euclideanUnitCube, ← EReal.coe_add]
  exact h.trans (EReal.coe_le_coe (by linarith [reference_upper n x]))

/-- Genuine original two-sided finite EReal boundedness produces the original
bounded-growth class without any finite-real surrogate at poles. -/
theorem projectiveProductToricProfile_mem_boundedGrowthClass {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hb : IsBoundedPotential u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) ∈
      BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n) := by
  refine ⟨closed_real_profile (projectiveProductToricEuclideanProfile_convex hu hi),
    (projectiveProductToricProfile_mem_growthClass hu hi).2, ?_⟩
  obtain ⟨A, _B, hAB⟩ := hb
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨-A, fun x => ?_⟩
  have h : (A : EReal) + (projectiveProductReferenceProfile n x : EReal) ≤
      u ((projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)) +
        (projectiveProductReferenceProfile n x : EReal) :=
    add_le_add (hAB _).1 le_rfl
  rw [← EReal.coe_add, ← product_profile_coe hu hi x] at h
  have h' : (((A + projectiveProductReferenceProfile n x : ℝ) : EReal) + ((-A : ℝ) : EReal)) ≤
      (projectiveProductToricEuclideanProfile u x : EReal) + ((-A : ℝ) : EReal) :=
    add_le_add h le_rfl
  rw [← EReal.coe_add] at h'
  have hlow : (projectiveProductReferenceProfile n x : EReal) ≤
      (projectiveProductToricEuclideanProfile u x : EReal) + ((-A : ℝ) : EReal) := by
    convert h' using 1
    congr 1
    ring
  rw [support_euclideanUnitCube]
  exact (EReal.coe_le_coe (reference_lower n x)).trans hlow

/-- True original reference support growth proves the actual entire finite
Legendre domain and its literal Newton closure, including the empty-tuple cube. -/
theorem projectiveProductReferenceProfile_NewtonBody (n : ℕ) :
    convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x => (projectiveProductReferenceProfile n x : EReal))) = euclideanUnitCube n := by
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  let f := fun x => (projectiveProductReferenceProfile n x : EReal)
  have hb := projectiveProductReferenceProfile_boundedGrowthClass n
  have hp := isProper_of_mem_boundedGrowthClass B (isCompact_euclideanUnitCube n)
    (nonempty_euclideanUnitCube n) hb
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    (isCompact_euclideanUnitCube n) (convex_euclideanUnitCube n) hb
  have hdom : effectiveDomain (conjugate B f) = euclideanUnitCube n := by
    ext m
    constructor
    · intro h
      by_contra hm
      have he := conjugate_eq_top_of_singularityLE_support B
        (isCompact_euclideanUnitCube n) (convex_euclideanUnitCube n) hp hb.2.1 hm
      change conjugate B f m < ⊤ at h
      rw [he] at h
      exact (lt_irrefl _ h)
    · intro hm
      exact ((hab m hm).2).trans_lt (EReal.coe_lt_top b)
  change closure (effectiveDomain (conjugate B f)) = _
  rw [hdom, (isCompact_euclideanUnitCube n).isClosed.closure_eq]

/-- The actual original native product FS reference NP total is n!, with no
rank-one scalar or assumed reference mass normalization. -/
theorem projectiveProductZeroMixedMeasure_univ (n : ℕ) :
    GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form)
      (fun _ => fun _ : projectiveProductSpace n => (0 : EReal))
      (fun _ => (isThetaPshPotential_projectiveProductZero n).1) univ = (n.factorial : ENNReal) := by
  rw [projectiveProductMixedMeasure_univ_eq_NewtonBody
    (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl)]
  simp only [product_zero_profile, projectiveProductReferenceProfile_NewtonBody,
    volume_euclideanUnitCube, mul_one]

end SGPT.Toric
