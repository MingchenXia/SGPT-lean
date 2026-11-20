import SGPT.NAPotential.ProjectiveGraphSegre
import SGPT.NAPotential.ProjectiveGraphSegreEquations

/-!
# Finite bihomogeneous equations on the original ambient product

The finite actual Segre relations of the original embedding and rational functions
are pulled back by the actual polynomial substitution `Z_(j,i) ↦ X_j Y_i`.
The resulting finite equations retain both original degrees and rational
vanishing, and their exact common zero set is the actual `globalRelationGraph`.

Blueprint: `projective-graph-bihomogeneous.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphBihomogeneous

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.ChowBl SGPT.GAGA.H0S SGPT.Okounkov
open ProjectiveGraphSegre ProjectiveGraphSegreEquations ProjectiveGraphAnalyticZero
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance bihomogeneousGraphTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance bihomogeneousGraphCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance bihomogeneousGraphManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (E : ClosedProjectiveEmbedding f)

/-- The actual original product-coordinate polynomial associated with a Segre equation. -/
def segreEquation (p : MvPolynomial (Fin (segreDim E.ambientDimension s + 1)) ℂ) :
    MvPolynomial (Sum (Fin (E.ambientDimension + 1)) (Fin (s + 1))) ℂ :=
  segreSubstitution (segreIdx E.ambientDimension s) p

/-- The actual homogeneous representatives in the two original projective factors. -/
def productPointCoordinates (z : graphAmbient f m s) :
    Sum (Fin (E.ambientDimension + 1)) (Fin (s + 1)) → ℂ :=
  Sum.elim (projectivePoint f E (m + 1) z.1).rep z.2.rep

theorem eval_segreEquation (p : MvPolynomial (Fin (segreDim E.ambientDimension s + 1)) ℂ)
    (z : graphAmbient f m s) :
    MvPolynomial.eval (productPointCoordinates E z) (segreEquation E p) =
      MvPolynomial.eval (segreVec (projectivePoint f E (m + 1) z.1).rep z.2.rep) p := by
  change aeval (Sum.elim (projectivePoint f E (m + 1) z.1).rep z.2.rep)
    (segreSubstitution (segreIdx E.ambientDimension s) p) =
      aeval (segreVector (segreIdx E.ambientDimension s)
        (projectivePoint f E (m + 1) z.1).rep z.2.rep) p
  exact aeval_segreSubstitution _ _ _ _

theorem homogeneous_equation_iff {p : MvPolynomial (Fin (segreDim E.ambientDimension s + 1)) ℂ}
    {n : ℕ} (hp : p.IsHomogeneous n) (z : graphAmbient f m s) :
    MvPolynomial.eval (segreAmbientMap E z).rep p = 0 ↔
      MvPolynomial.eval (productPointCoordinates E z) (segreEquation E p) = 0 := by
  have hne := segreVec_ne_zero (projectivePoint f E (m + 1) z.1).rep_ne_zero z.2.rep_ne_zero
  have hpoint : segreAmbientMap E z =
      mk (segreVec (projectivePoint f E (m + 1) z.1).rep z.2.rep) hne := pmk_eq_mk hne
  rw [eval_segreEquation]
  exact eval_rep_eq_zero_iff hp _ _ hne hpoint

variable [IsIntegral X]

/-- The actual original rational product coordinates associated with `E` and `b`. -/
def rationalProductCoordinates (b : Fin s → X.functionField) :
    Sum (Fin (E.ambientDimension + 1)) (Fin (s + 1)) → X.functionField :=
  Sum.elim (genericCoordinates E) (Fin.cons (1 : X.functionField) b)

/-- Finite actual bihomogeneous equations cut out the exact original ambient relation set. -/
theorem exists_finite_bihomogeneous_equations (b : Fin s → X.functionField) :
    letI := schemeFunctionFieldAlgebra f
    ∃ Q : Finset (MvPolynomial (Sum (Fin (E.ambientDimension + 1)) (Fin (s + 1))) ℂ),
      (∀ q ∈ Q, ∃ n : ℕ,
        q.IsWeightedHomogeneous (leftWeight (I := Fin (E.ambientDimension + 1)) (J := Fin (s + 1))) n ∧
        q.IsWeightedHomogeneous (rightWeight (I := Fin (E.ambientDimension + 1)) (J := Fin (s + 1))) n ∧
        aeval (rationalProductCoordinates E b) q = 0) ∧
      ∀ z : graphAmbient f m s, z ∈ globalRelationGraph (m := m) E b ↔
        ∀ q ∈ Q, MvPolynomial.eval (productPointCoordinates E z) q = 0 := by
  classical
  let := schemeFunctionFieldAlgebra f
  obtain ⟨F, hF, hset⟩ := exists_finite_globalRelationEquations (m := m) E b
  refine ⟨F.image (segreEquation E), ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨n, hn, hzero⟩ := hF p hp
    refine ⟨n, segreSubstitution_left hn _, segreSubstitution_right hn _, ?_⟩
    rw [rationalProductCoordinates, segreEquation, aeval_segreSubstitution]
    exact hzero
  · intro z
    rw [hset]
    constructor
    · intro hz q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨n, hn, _⟩ := hF p hp
      exact (homogeneous_equation_iff E hn z).mp (hz p hp)
    · intro hz p hp
      obtain ⟨n, hn, _⟩ := hF p hp
      exact (homogeneous_equation_iff E hn z).mpr (hz _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphBihomogeneous
