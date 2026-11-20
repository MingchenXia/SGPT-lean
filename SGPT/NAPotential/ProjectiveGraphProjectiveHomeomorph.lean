import SGPT.NAPotential.ProjectiveGraphProjectiveReadback
import SGPT.Toric.NativeProjectivePointComparison

/-!
# The actual original native projective-point map is a homeomorphism

Blueprint: `projective-graph-projective-homeomorph.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphProjectiveReadback ProjectiveGraphProjectivePoint
open SGPT.Foundations.Analysis.FirstPass
attribute [local instance] SGPT.Toric.monomialProjectiveTopology

local instance nativeTopology (N : ℕ) : TopologicalSpace (SchemeComplexPoint
    (polynomialProjStructureMap ℂ N)) := schemeAnalyticPointTopology _

/-- The original native polynomial projective points and ORIGINAL book projective space are homeomorphic. -/
def originalProjectiveHomeomorph (N : ℕ) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ N) ≃ₜ ComplexProjectiveSpace N :=
  (SGPT.Toric.nativeProjectivePointHomeomorph N).symm

/-- **The actual homeomorphism is precisely the ORIGINAL projectivePoint of the identity embedding**. -/
theorem originalProjectiveHomeomorph_apply (N : ℕ)
    (q : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :
    originalProjectiveHomeomorph N q =
      projectivePoint (polynomialProjStructureMap ℂ N) (identityEmbedding N) N q := by
  obtain ⟨v, rfl⟩ := polynomialProjNonzeroVectorPoint_surjective N q
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate N v.val v.property
  rw [polynomialProjNonzeroVectorPoint_eq_chart N v i hi,
    nativeVectorPoint_projectivePoint N i v.val v.property hi]
  change (SGPT.Toric.nativeProjectivePointHomeomorph N).symm
    (polynomialProjVectorChartPoint N i v.val) = mk v.val v.property
  rw [← polynomialProjNonzeroVectorPoint_eq_chart N v i hi,
    ← SGPT.Toric.nativeProjectivePointHomeomorph_mk N v]
  exact (SGPT.Toric.nativeProjectivePointHomeomorph N).symm_apply_apply _

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
