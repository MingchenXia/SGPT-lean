import SGPT.Foundations.Analysis.Pending.RankDegeneracy
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Foundations.Analysis.FirstPass.BlowupSequences

set_option autoImplicit false

/-!
# The differential exceptional locus is analytic

The whole smooth source has its full coordinate tangent space.  Its preferred
chart rank is exactly the range dimension of the manifold derivative.  The
rank-degeneracy theorem therefore gives analyticity of the intrinsic locus of
non-bijective differential, without properness or an exceptional witness.
-/

open Set Module
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.HolomorphicIntrinsicExceptionalAnalytic

open FirstPass FirstPass.BlowupSequences AnalyticDimensionBasics RankDegeneracy

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The actual non-bijective-differential locus of a holomorphic map between
manifolds of the same complex dimension is analytic in every dimension. -/
theorem isComplexAnalyticSubset_exceptionalLocus {g : Y → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    IsComplexAnalyticSubset (n := n) (exceptionalLocus n g) := by
  have hreg (y : Y) : RegularAtDim (n := n) (univ : Set Y) y n :=
    AnalyticIrreducibleComponents.regularAtDim_univ y
  have hdim : IsPureDim (n := n) (univ : Set Y) n :=
    fun y k hy => RegularPointDimension.eq_of_regularAtDim hy (hreg y)
  have heq : rankDegeneracyLocus n n g (univ : Set Y) n n = exceptionalLocus n g := by
    ext y
    have ht : tangentSpaceIn (complexChartAt (n := n) y) (univ : Set Y) y = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa only [finrank_euclideanSpace_fin] using
        finrank_tangentSpaceIn_of_regularAtDim (complexChartAt (n := n) y)
          (mem_complexChartAt_source y) (hreg y)
    have hd : chartDeriv (complexChartAt (n := n) y) (complexChartAt (n := n) (g y)) g y =
        mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y := by
      rw [((hg y).mdifferentiableAt (by simp)).mfderiv]
      simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
      rfl
    let D : ComplexModel n →ₗ[ℂ] ComplexModel n :=
      { toFun := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y
        map_add' := (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y).map_add
        map_smul' := (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y).map_smul }
    have hr : rankAt (n := n) (n' := n) g (univ : Set Y) y = finrank ℂ (LinearMap.range D) := by
      unfold rankAt rankIn
      rw [ht, hd, Submodule.map_top]
      rfl
    simp only [rankDegeneracyLocus, mem_union, mem_sdiff, mem_univ, mem_regularLocus,
      hreg y, not_true_eq_false, and_false, false_or, mem_ofPred_eq, true_and,
      exceptionalLocus, hr]
    constructor
    · intro hlt hbij
      have htop : LinearMap.range D = ⊤ := LinearMap.range_eq_top.mpr hbij.2
      have hsame : finrank ℂ (LinearMap.range D) = n := by
        rw [htop, finrank_top, finrank_euclideanSpace_fin]
      omega
    · intro hnot
      by_contra hlt
      have htop : LinearMap.range D = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hle := Submodule.finrank_le (LinearMap.range D)
        simp only [finrank_euclideanSpace_fin] at hle ⊢
        omega
      have hsurj : Function.Surjective D := LinearMap.range_eq_top.mp htop
      exact hnot ⟨(LinearMap.injective_iff_surjective (f := D)).mpr hsurj, hsurj⟩
  rw [← heq]
  exact isComplexAnalyticSubset_rankDegeneracyLocus isComplexAnalyticSubset_univ hdim
    (hg.mdifferentiable (by simp)) n

end SGPT.Foundations.Analysis.Pending.HolomorphicIntrinsicExceptionalAnalytic
