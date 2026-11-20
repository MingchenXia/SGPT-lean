import SGPT.NAPotential.ProjectiveGraphSegre
import SGPT.NAPotential.ProjectiveGraphMembership
import SGPT.NAPotential.ProjectiveGraphScaling
import SGPT.NAPotential.ProjectiveGraphSegreEquations

/-!
# The same original graph relations in every nonempty original coordinate chart

Changing the actual original normalized ratio vector scales the actual Segre
vector by the original nonzero frame transition. Its full homogeneous ideal is
therefore exactly unchanged; the chart can be chosen to contain the divisor centre.
Blueprint: `projective-graph-centred-charts.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphCoordinateCharts

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphSegre ProjectiveGraphMembership ProjectiveGraphScaling
open ProjectiveGraphRelationCore ProjectiveGraphSegreEquations

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {s : ℕ}

/-- Every genuine nonempty original coordinate chart contains the actual original generic point. -/
theorem generic_mem_coordOpen (j : Fin (E.ambientDimension + 1)) (hU : Nonempty (coordOpen E j)) :
    genericPoint X ∈ coordOpen E j :=
  ((genericPoint_spec X).mem_open_set_iff (coordOpen E j).isOpen).mpr (by simpa using hU)

/-- The actual original coordinate ratios, evaluated at the actual generic point in the chosen original chart. -/
def chartGenericCoordinates (j : Fin (E.ambientDimension + 1)) (hU : Nonempty (coordOpen E j)) :
    Fin (E.ambientDimension + 1) → X.functionField :=
  fun k => X.presheaf.germ (coordOpen E j) (genericPoint X) (generic_mem_coordOpen E j hU) (ratio E j k)

@[simp]
theorem chartGenericCoordinates_self (j : Fin (E.ambientDimension + 1)) (hU : Nonempty (coordOpen E j)) :
    chartGenericCoordinates E j hU j = 1 := by
  simp [chartGenericCoordinates, ratio_self]

theorem chartGenericCoordinates_genericIndex (hU : Nonempty (coordOpen E (genericCoordinateIndex E))) :
    chartGenericCoordinates E (genericCoordinateIndex E) hU = genericCoordinates E := rfl

/-- The actual original frame transition scales the actual generic coordinate vector by a nonzero original rational function. -/
theorem chartGenericCoordinates_transition
    (i j : Fin (E.ambientDimension + 1)) (hi : Nonempty (coordOpen E i)) (hj : Nonempty (coordOpen E j)) :
    ∃ t : X.functionField, t ≠ 0 ∧
      chartGenericCoordinates E j hj = fun k => t * chartGenericCoordinates E i hi k := by
  let W : X.Opens := coordOpen E i ⊓ coordOpen E j
  have hW : genericPoint X ∈ W := ⟨generic_mem_coordOpen E i hi, generic_mem_coordOpen E j hj⟩
  let t := X.presheaf.germ W (genericPoint X) hW (frameTr E i j)
  have heq (k : Fin (E.ambientDimension + 1)) :
      chartGenericCoordinates E j hj k = t * chartGenericCoordinates E i hi k := by
    have h := congrArg (fun a : Γ(X, W) => X.presheaf.germ W (genericPoint X) hW a)
      (ratio_transition E i j k)
    rw [map_mul] at h
    change X.presheaf.germ W (genericPoint X) hW
      (X.presheaf.map (homOfLE (inf_le_right : W ≤ coordOpen E j)).op (ratio E j k)) =
        t * X.presheaf.germ W (genericPoint X) hW
          (X.presheaf.map (homOfLE (inf_le_left : W ≤ coordOpen E i)).op (ratio E i k)) at h
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at h
    exact h
  refine ⟨t, ?_, funext heq⟩
  intro ht
  have h := heq j
  simp [ht] at h

/-- The actual rational Segre vector in an arbitrary genuine nonempty original coordinate chart. -/
def chartRationalSegreCoordinates (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (b : Fin s → X.functionField) :
    Fin (segreDim E.ambientDimension s + 1) → X.functionField :=
  segreVector (segreIdx E.ambientDimension s) (chartGenericCoordinates E j hU) (Fin.cons 1 b)

/-- **The same full original global relation ideal**, even when the chosen chart changes to contain the original divisor centre. -/
theorem relationCore_chartRationalSegre (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (b : Fin s → X.functionField) :
    letI := schemeFunctionFieldAlgebra f
    relationCore (A := ℂ) (chartRationalSegreCoordinates E j hU b) =
      relationCore (A := ℂ) (rationalSegreCoordinates E b) := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨t, ht, heq⟩ := chartGenericCoordinates_transition E (genericCoordinateIndex E) j
    ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩ hU
  have hvec : chartRationalSegreCoordinates E j hU b = fun k => t * rationalSegreCoordinates E b k := by
    funext k
    change chartGenericCoordinates E j hU (segreIdx E.ambientDimension s k).1 *
      (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField) (segreIdx E.ambientDimension s k).2 = _
    rw [heq]
    change (t * genericCoordinates E (segreIdx E.ambientDimension s k).1) * _ = _
    exact mul_assoc _ _ _
  rw [hvec]
  exact relationCore_scale _ ht

/-- Actual generic evaluation of the original affine presentation in the chosen original chart. -/
theorem generic_affinePresentation (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (p : MvPolynomial (Fin E.ambientDimension) ℂ) :
    letI := schemeFunctionFieldAlgebra f
    X.presheaf.germ (coordOpen E j) (genericPoint X) (generic_mem_coordOpen E j hU)
      (affinePresentation f E j p) = aeval (fun k => chartGenericCoordinates E j hU (j.succAbove k)) p := by
  let := schemeFunctionFieldAlgebra f
  let := hU
  have h : (X.germToFunctionField (coordOpen E j)).hom.comp (affinePresentation f E j) =
      eval₂Hom (algebraMap ℂ X.functionField) (fun k => chartGenericCoordinates E j hU (j.succAbove k)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C]
      rw [affinePresentation_C]
      exact DFunLike.congr_fun (functionField_sectionConstants (f := f) (coordOpen E j)) c
    · intro k
      rw [RingHom.comp_apply, affinePresentation_X f E, MvPolynomial.eval₂Hom_X']
      rfl
  exact (DFunLike.congr_fun h p).trans (aeval_eq_eval₂Hom _ p).symm

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphCoordinateCharts
