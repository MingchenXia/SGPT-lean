import SGPT.NAPotential.ProjectiveGraphRegularOpen
import SGPT.NAPotential.ProjectiveGraphSeparation

/-!
# The full global relation set is the actual graph over an original open

Every numerator and denominator is produced from the original affine presentation;
column relations eliminate extra fibres, including the putative `Y₀=0` fibre.
Blueprint: `projective-graph-uniqueness.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphUniqueness

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Okounkov
open ProjectiveGraphRelations ProjectiveGraphRelationCore ProjectiveGraphAnalyticZero
open ProjectiveGraphSegre ProjectiveGraphMembership ProjectiveGraphRegularOpen
open ProjectiveGraphSeparation ProjectiveGraphSegreEquations
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Full homogeneous-ideal vanishing retains every actual nonzero lift, including nonhomogeneous ideal elements. -/
theorem eval_lift_of_mem_idealZeroLocus {N : ℕ}
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) ℂ))
    (x : ComplexProjectiveSpace N) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0)
    (hx : x = mk v hv) (hz : x ∈ idealZeroLocus J.toIdeal)
    (p : MvPolynomial (Fin (N + 1)) ℂ) (hp : p ∈ J.toIdeal) :
    MvPolynomial.eval v p = 0 := by
  obtain ⟨F, hF, hspan⟩ := exists_finite_homogeneous_generators J
  have hle : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [← hspan]
    apply Ideal.span_le.mpr
    intro q hq
    obtain ⟨⟨n, hn⟩, hmem⟩ := hF q hq
    exact (eval_rep_eq_zero_iff hn x v hv hx).mp (hz q hmem)
  exact hle hp

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance uniquenessTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance uniquenessCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance uniquenessManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **Actual global graph producer over a genuine original regular open**: membership and uniqueness,
with no supplied graph, inverse, analyticity, or order certificate. -/
theorem exists_regularGraph_unique (b : Fin s → X.functionField) :
    ∃ (V : X.Opens) (hV : genericPoint X ∈ V)
      (_hVU : V ≤ coordOpen E (genericCoordinateIndex E)) (r : Fin s → Γ(X, V)),
      (∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i) ∧
      (∀ x ∉ graphBase f V, graphMap (m := m) E r x ∈ globalRelationGraph (m := m) E b) ∧
      ∀ z ∈ globalRelationGraph (m := m) E b, z.1 ∉ graphBase f V →
        z = graphMap (m := m) E r z.1 := by
  let := schemeFunctionFieldAlgebra f
  classical
  obtain ⟨V, hV, hVU, r, d, a, hr, hfrac, hvalues⟩ := exists_regular_fraction_open (m := m) E b
  refine ⟨V, hV, hVU, r, hr, ?_, ?_⟩
  · intro x hx
    apply graphMap_mem_globalRelationGraph (m := m) E V hV hVU b r hr x
    simpa only [mem_graphBase, not_not] using hx
  · intro z hz hx
    have hxV : schemeComplexPointImage f z.1 ∈ V := by
      simpa only [mem_graphBase, not_not] using hx
    let c := genericCoordinates E
    let w : Fin (s + 1) → X.functionField := Fin.cons 1 b
    let q := homCoords f E (m + 1) (genericCoordinateIndex E) z.1
    let u := graphLift (m := m) E r z.1
    have hq : q (genericCoordinateIndex E) = 1 :=
      homCoords_self f E (m + 1) (genericCoordinateIndex E) (hVU hxV)
    have hq0 : q ≠ 0 := homCoords_ne_zero f E (m + 1) (genericCoordinateIndex E) (hVU hxV)
    have hpoint : segreAmbientMap E z = mk (segreVec q z.2.rep) (segreVec_ne_zero hq0 z.2.rep_ne_zero) := by
      change segreMap (projectivePoint f E (m + 1) z.1) z.2 = _
      rw [projectivePoint_eq f E (m + 1) (genericCoordinateIndex E) (hVU hxV)]
      simpa only [mk_rep] using ProjectiveGraphSegre.segreMap_mk hq0 z.2.rep_ne_zero
    have hzfull : ∀ p ∈ (relationCore (A := ℂ) (segreVector (segreIdx E.ambientDimension s) c w)).toIdeal,
        aeval (segreVector (segreIdx E.ambientDimension s) q z.2.rep) p = 0 := by
      intro p hp
      exact eval_lift_of_mem_idealZeroLocus (relationCore (A := ℂ) (rationalSegreCoordinates E b))
        (segreAmbientMap E z) (segreVec q z.2.rep) (segreVec_ne_zero hq0 z.2.rep_ne_zero)
        hpoint hz p hp
    have hrep (l : Fin (s + 1)) : ∃ (n : ℕ) (D A : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ),
        D.IsHomogeneous n ∧ A.IsHomogeneous n ∧
        aeval c D * w l = aeval c A * w 0 ∧ aeval q D ≠ 0 ∧ aeval q A = aeval q D * u l := by
      refine Fin.cases ?_ (fun i => ?_) l
      · refine ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp [u, graphLift]
      · let n := max (d i).totalDegree (a i).totalDegree
        let D := baseHomogenize (genericCoordinateIndex E) n (d i)
        let A := baseHomogenize (genericCoordinateIndex E) n (a i)
        have hD : D.IsHomogeneous n := baseHomogenize_isHomogeneous _ _ _ (le_max_left _ _)
        have hA : A.IsHomogeneous n := baseHomogenize_isHomogeneous _ _ _ (le_max_right _ _)
        have hDc : aeval c D = aeval (fun k => c ((genericCoordinateIndex E).succAbove k)) (d i) :=
          aeval_baseHomogenize _ _ _ c (genericCoordinates_self E)
        have hAc : aeval c A = aeval (fun k => c ((genericCoordinateIndex E).succAbove k)) (a i) :=
          aeval_baseHomogenize _ _ _ c (genericCoordinates_self E)
        have hDq : aeval q D = MvPolynomial.eval (fun k => q ((genericCoordinateIndex E).succAbove k)) (d i) :=
          aeval_baseHomogenize _ _ _ q hq
        have hAq : aeval q A = MvPolynomial.eval (fun k => q ((genericCoordinateIndex E).succAbove k)) (a i) :=
          aeval_baseHomogenize _ _ _ q hq
        refine ⟨n, D, A, hD, hA, ?_, ?_, ?_⟩
        · rw [hDc, hAc]
          simpa only [w, Fin.cons_succ, Fin.cons_zero, mul_one] using hfrac i
        · rw [hDq]
          exact (hvalues z.1 hxV i).1
        · rw [hAq, hDq]
          exact (hvalues z.1 hxV i).2
    obtain ⟨_hy0, hy⟩ := coordinates_of_fullRelations (segreIdx E.ambientDimension s)
      (genericCoordinateIndex E) 0 c w q z.2.rep u (by rw [hq]; exact one_ne_zero)
      z.2.rep_ne_zero hzfull hrep
    apply Prod.ext
    · rfl
    · change z.2 = mk u (graphLift_ne_zero (m := m) E r z.1)
      rw [← mk_rep z.2]
      exact (mk_eq_mk_iff _ _).mpr ⟨z.2.rep 0, hy.symm⟩

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphUniqueness
