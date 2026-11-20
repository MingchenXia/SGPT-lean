import SGPT.NAPotential.ProjectiveGraphMembership

/-!
# Original affine numerator and denominator polynomials

The actual original coordinate chart is affine. Its genuine fraction-field map
and its actual surjective affine presentation produce polynomial numerators and
denominators of the original rational functions, without a representation certificate.
Blueprint: `projective-graph-regular-fractions.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularFractions

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.NAPotential.FSPos SGPT.Okounkov
open ProjectiveGraphSegre ProjectiveGraphMembership
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {s : ℕ}

/-- Taking the original generic germ of the original affine presentation is actual polynomial evaluation. -/
theorem generic_affinePresentation (p : MvPolynomial (Fin E.ambientDimension) ℂ) :
    letI := schemeFunctionFieldAlgebra f
    X.presheaf.germ (coordOpen E (genericCoordinateIndex E)) (genericPoint X)
      (genericCoordinateIndex_mem E) (affinePresentation f E (genericCoordinateIndex E) p) =
        aeval (fun a => genericCoordinates E ((genericCoordinateIndex E).succAbove a)) p := by
  let := schemeFunctionFieldAlgebra f
  let U := coordOpen E (genericCoordinateIndex E)
  let : Nonempty U := ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩
  have h : (X.germToFunctionField U).hom.comp (affinePresentation f E (genericCoordinateIndex E)) =
      eval₂Hom (algebraMap ℂ X.functionField)
        (fun a => genericCoordinates E ((genericCoordinateIndex E).succAbove a)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C]
      rw [affinePresentation_C]
      exact DFunLike.congr_fun (functionField_sectionConstants (f := f) U) c
    · intro a
      rw [RingHom.comp_apply, affinePresentation_X f E, MvPolynomial.eval₂Hom_X']
      rfl
  exact (DFunLike.congr_fun h p).trans (aeval_eq_eval₂Hom _ p).symm

/-- Actual original rational functions have actual original affine-coordinate numerator and denominator polynomials. -/
theorem exists_affine_fraction_polynomials (b : Fin s → X.functionField) :
    letI := schemeFunctionFieldAlgebra f
    ∃ d a : Fin s → MvPolynomial (Fin E.ambientDimension) ℂ,
      ∀ i, aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) (d i) ≠ 0 ∧
        aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) (d i) * b i =
          aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) (a i) := by
  let := schemeFunctionFieldAlgebra f
  let U := coordOpen E (genericCoordinateIndex E)
  let : Nonempty U := ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen X U (isAffineOpen_coordOpen E _)
  have hrep (i : Fin s) : ∃ d a : MvPolynomial (Fin E.ambientDimension) ℂ,
      aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) d ≠ 0 ∧
      aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) d * b i =
        aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) a := by
    obtain ⟨a', d', hd', hfrac⟩ := IsFractionRing.div_surjective Γ(X, U) (b i)
    obtain ⟨a, ha⟩ := affinePresentation_surjective f E (genericCoordinateIndex E) a'
    obtain ⟨d, hd⟩ := affinePresentation_surjective f E (genericCoordinateIndex E) d'
    have hden : algebraMap Γ(X, U) X.functionField d' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd'
    have heval (p : MvPolynomial (Fin E.ambientDimension) ℂ) :
        aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) p =
          algebraMap Γ(X, U) X.functionField (affinePresentation f E (genericCoordinateIndex E) p) :=
      (generic_affinePresentation E p).symm
    refine ⟨d, a, ?_, ?_⟩
    · rw [heval, hd]
      exact hden
    · rw [heval, heval, ha, hd]
      exact (mul_comm _ _).trans ((div_eq_iff hden).mp hfrac).symm
  choose d a h using hrep
  exact ⟨d, a, h⟩

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularFractions
