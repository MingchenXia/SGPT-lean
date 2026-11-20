import SGPT.Unibranch.UnibAnSpace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
open SGPT.Unibranch SGPT.Foundations.Schemes
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

variable {N : ℕ} {I J : Ideal (MvPolynomial (Fin N) ℂ)}

/-- The reduced carriers of nested ideals are included in the opposite direction. -/
theorem polynomialZeroSet_subset_of_le (hIJ : I ≤ J) :
    polynomialZeroSet J ⊆ polynomialZeroSet I :=
  fun _ h p hp => h p (hIJ hp)

/-- The closed analytic model is included via its actual quotient sheaf map.
On the ambient manifold this is induced by the identity. -/
def closedChartInclusion (hIJ : I ≤ J) :
    actualSubspaceLocallyRingedSpace (n := N) (polynomialZeroSet J) ⟶
      actualSubspaceLocallyRingedSpace (n := N) (polynomialZeroSet I) :=
  actualSubspaceMap (n := N) (m := N) (f := id) contMDiff_id
    (fun _ hx => polynomialZeroSet_subset_of_le hIJ hx)

theorem closedChartInclusion_point (hIJ : I ≤ J) :
    closedChartInclusion hIJ ≫ subspacePointMap (n := N) (polynomialZeroSet I) =
      subspacePointMap (n := N) (polynomialZeroSet J) :=
  actualSubspaceMap_point (n := N) (m := N) (f := id) contMDiff_id
    (fun _ hx => polynomialZeroSet_subset_of_le hIJ hx)

/-- The comparison uses the same point evaluation precomposed with the
literal algebraic quotient map. -/
theorem pointEval_closedChartInclusion (hIJ : I ≤ J) (x : polynomialZeroSet J) :
    pointEval ((closedChartInclusion hIJ).base x) =
      (pointEval x).comp (Ideal.Quotient.factor hIJ) := by
  refine RingHom.ext fun (a : MvPolynomial (Fin N) ℂ ⧸ I) => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.comp_apply, Ideal.Quotient.factor_mk, pointEval_mk, pointEval_mk] <;> rfl

/-- The same sheaf-theoretic comparison commutes with the literal Spec maps
of complex evaluations into the target affine chart. -/
theorem closedChartInclusion_spec (hIJ : I ≤ J) (x : polynomialZeroSet J) :
    Spec.map (CommRingCat.ofHom (pointEval ((closedChartInclusion hIJ).base x))) =
      Spec.map (CommRingCat.ofHom (pointEval x)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) := by
  rw [pointEval_closedChartInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end

end SGPT.Unibranch.UnibAn
