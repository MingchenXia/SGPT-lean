import SGPT.NAPotential.ProjectiveGraphRelationCore
import SGPT.Projective.Basic
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import Mathlib.Analysis.Analytic.Polynomial

/-!
# The actual full-relation projective zero locus is analytic

Finite homogeneous equations are presented in the original projective affine
charts, with polynomial generators obtained by normalized homogeneous lifts.
No analyticity certificate is an input. Noetherianity supplies finite actual
homogeneous generators of the full relation ideal of an actual vector.

Blueprint: `projective-graph-analytic-zero.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAnalyticZero

open MvPolynomial Set Filter
open ProjectiveGraphRelations ProjectiveGraphRelationCore
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N r : ℕ}

/-- The zero locus uses the actual projective representatives, with homogeneous invariance proved below. -/
def finiteZeroLocus (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ) : Set (ComplexProjectiveSpace N) :=
  {x | ∀ i, MvPolynomial.eval x.rep (P i) = 0}

/-- Homogeneity makes vanishing independent of the actual nonzero homogeneous lift. -/
theorem eval_rep_eq_zero_iff {p : MvPolynomial (Fin (N + 1)) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (x : ComplexProjectiveSpace N)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (hx : x = mk v hv) :
    MvPolynomial.eval x.rep p = 0 ↔ MvPolynomial.eval v p = 0 := by
  obtain ⟨c, hc, hrep⟩ := rep_smul x hv hx
  have hscale : MvPolynomial.eval (c • v) p = c ^ n * MvPolynomial.eval v p := by
    change eval₂Hom (RingHom.id ℂ) (fun i => c * v i) p =
      c ^ n * eval₂Hom (RingHom.id ℂ) v p
    exact eval₂Hom_scale_of_isHomogeneous hp (RingHom.id ℂ) v c
  rw [hrep, hscale, mul_eq_zero, or_iff_right (pow_ne_zero n hc)]

/-- The affine equations are actual polynomial substitutions in the normalized lift. -/
theorem differentiable_affinePolynomial (j : Fin (N + 1))
    (p : MvPolynomial (Fin (N + 1)) ℂ) :
    Differentiable ℂ (fun z : ComplexModel N => MvPolynomial.eval (affineLift j z) p) :=
  (differentiableOn_univ.mp (AnalyticOnNhd.eval_mvPolynomial p).differentiableOn).comp
    (differentiable_affineLift j)

/-- Actual finite homogeneous equations give a presentation in every original projective chart. -/
theorem isComplexAnalyticSubset_finiteZeroLocus
    (P : Fin r → MvPolynomial (Fin (N + 1)) ℂ)
    (hP : ∀ i, ∃ n : ℕ, (P i).IsHomogeneous n) :
    IsComplexAnalyticSubset (n := N) (finiteZeroLocus P) := by
  intro x
  let j := chartIndex x
  refine ⟨{
    generatorCount := r
    generator := fun i z => MvPolynomial.eval (affineLift j z) (P i)
    coordinateNeighborhood := univ
    isOpen_coordinateNeighborhood := isOpen_univ
    center_mem_coordinateNeighborhood := mem_univ _
    coordinateNeighborhood_subset_target := by
      change univ ⊆ (affineChart j).target
      rw [affineChart_target]
    generator_holomorphic := fun i => (differentiable_affinePolynomial j (P i)).differentiableOn
    zeroLocus := ?_ }⟩
  intro y hy _
  change y ∈ (affineChart j).source at hy
  have hyMk : y = mk (affineLift j (affineChart j y)) (affineLift_ne_zero j _) :=
    ((affineChart j).left_inv hy).symm
  change (∀ i, MvPolynomial.eval y.rep (P i) = 0) ↔
    ∀ i, MvPolynomial.eval (affineLift j (affineChart j y)) (P i) = 0
  apply forall_congr'
  intro i
  obtain ⟨n, hn⟩ := hP i
  exact eval_rep_eq_zero_iff hn y _ (affineLift_ne_zero j _) hyMk

/-- Vanishing of every actual member of an original homogeneous ideal. -/
def idealZeroLocus (J : Ideal (MvPolynomial (Fin (N + 1)) ℂ)) :
    Set (ComplexProjectiveSpace N) :=
  {x | ∀ p ∈ J, MvPolynomial.eval x.rep p = 0}

/-- Noetherianity makes the full original homogeneous-ideal zero locus analytic. -/
theorem isComplexAnalyticSubset_idealZeroLocus
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) ℂ)) :
    IsComplexAnalyticSubset (n := N) (idealZeroLocus J.toIdeal) := by
  classical
  obtain ⟨F, hF, hspan⟩ := exists_finite_homogeneous_generators J
  let P : Fin F.card → MvPolynomial (Fin (N + 1)) ℂ := fun i => (F.equivFin.symm i).val
  have hP : ∀ i, ∃ n : ℕ, (P i).IsHomogeneous n := fun i =>
    (hF _ (F.equivFin.symm i).property).1
  have hset : idealZeroLocus J.toIdeal = finiteZeroLocus P := by
    ext x
    constructor
    · intro hx i
      exact hx _ (hF _ (F.equivFin.symm i).property).2
    · intro hx p hp
      have hle : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval x.rep) := by
        rw [← hspan]
        apply Ideal.span_le.mpr
        intro q hq
        change MvPolynomial.eval x.rep q = 0
        have h := hx (F.equivFin ⟨q, hq⟩)
        simpa only [P, Equiv.symm_apply_apply] using h
      exact hle hp
  rw [hset]
  exact isComplexAnalyticSubset_finiteZeroLocus P hP

variable {K : Type*} [CommRing K] [Algebra ℂ K]

/-- The actual full homogeneous relation zero locus of an actual coordinate vector. -/
def relationZeroLocus (v : Fin (N + 1) → K) : Set (ComplexProjectiveSpace N) :=
  idealZeroLocus (relationCore (A := ℂ) v).toIdeal

/-- **Actual full-relation projective zero locus**, with analyticity produced by finite equations. -/
theorem isComplexAnalyticSubset_relationZeroLocus (v : Fin (N + 1) → K) :
    IsComplexAnalyticSubset (n := N) (relationZeroLocus v) :=
  isComplexAnalyticSubset_idealZeroLocus (relationCore (A := ℂ) v)

theorem isClosed_relationZeroLocus (v : Fin (N + 1) → K) : IsClosed (relationZeroLocus v) :=
  (isComplexAnalyticSubset_relationZeroLocus v).isClosed

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphAnalyticZero
