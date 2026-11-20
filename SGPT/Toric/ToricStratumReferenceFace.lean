import SGPT.Toric.ToricStratumVolumeGeometry

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Pointwise Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual reference ample face, translated by its genuine original
containing-vertex Cartier datum into the ACTUAL original annihilator. -/
def toricStratumReferenceFace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Set (toricStratumRealSpace (polytopeToricRay γ hs v '' J)) :=
  toricStratumTranslatedFace (polytopeToricAmpleDivisor γ hs) v J
    (toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) (polytopeToricMomentPolytope γ)

/-- The genuine reference ample face is compact in the ACTUAL original
annihilator, independently of all potentials and trace operations. -/
theorem isCompact_toricStratumReferenceFace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    IsCompact (toricStratumReferenceFace (hs := hs) v J) := by
  apply isCompact_toricStratumTranslatedFace v J _
    (isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J)
    (by rw [toricDivisorPolytope_ampleDivisor])
  exact isCompact_polytopeToricMomentPolytope γ

/-- The genuine reference ample face is convex in the SAME actual space. -/
theorem convex_toricStratumReferenceFace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Convex ℝ (toricStratumReferenceFace (hs := hs) v J) := by
  apply convex_toricStratumTranslatedFace v J _
    (isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J)
    (by rw [toricDivisorPolytope_ampleDivisor])
  exact convex_polytopeToricMomentPolytope γ

/-- The genuine containing vertex supplies the origin in the translated
reference face, including the full cone and ambient dimension zero. -/
theorem zero_mem_toricStratumReferenceFace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (0 : toricStratumRealSpace (polytopeToricRay γ hs v '' J)) ∈
      toricStratumReferenceFace (hs := hs) v J := by
  unfold toricStratumReferenceFace
  rw [toricStratumTranslatedFace_eq_preimage v J _
    (isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J)
    (by rw [toricDivisorPolytope_ampleDivisor])]
  change 0 + latticeVector (toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) ∈
    polytopeToricMomentPolytope γ
  rw [zero_add, toricCartierDatum_ampleDivisor, ←toricDivisorPolytope_ampleDivisor]
  exact latticeVector_vertex_mem_ampleDivisorPolytope γ hs v

end SGPT.Toric
