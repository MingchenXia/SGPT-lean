import SGPT.NAPotential.ProjectiveGraphProjectivePoint
import SGPT.Foundations.Schemes.PolynomialProjectiveCoordinatePullback

/-!
# The original projective-point map reads actual native homogeneous coordinates

Blueprint: `projective-graph-projective-point.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveReadback

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphNativeReadback ProjectiveGraphProjectivePoint ProjectiveGraphPointEvaluation
open SGPT.Foundations.Analysis.FirstPass
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual native projective coordinate-section pullback is the same actual open-chart pullback. -/
theorem coordinateRegularPullback_eq (N : ℕ) (i : Fin (N + 1))
    (h : (⊤ : (Spec (.of (polynomialProjCoordinateRing ℂ N i))).Opens) ≤
      polynomialProjCoordinateImmersion ℂ N i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N i) :
    (polynomialProjCoordinateImmersion ℂ N i).appLE (polynomialProjCoordinateOpen ℂ N i) ⊤ h =
      polynomialProjCoordinateRegularPullback ℂ N i := by
  let U := polynomialProjCoordinateOpen ℂ N i
  let e := polynomialProjCoordinateSchemeIso ℂ N i
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  have he : e.inv.appLE ⊤ ⊤ (by simp) = e.inv.appTop := by
    simp [Scheme.Hom.appLE]
  change (e.inv ≫ U.ι).appLE U ⊤ h = _
  have hcomp := Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ U.ι_preimage_self.ge (by simp)
  rw [hι, he] at hcomp
  exact hcomp.symm


/-- Every actual native vector-point original regular ratio has its literal original coordinate value. -/
theorem nativeVectorPoint_ratio (N : ℕ) (i k : Fin (N + 1))
    (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0) :
    schemeOpenRegularFunction (polynomialProjStructureMap ℂ N) N (identityEmbedding N)
      (coordOpen (identityEmbedding N) i) (ratio (identityEmbedding N) i k)
        (polynomialProjVectorChartPoint N i v) = v k / v i := by
  let fP := polynomialProjStructureMap ℂ N
  let c := polynomialProjComplexAffineChart N i
  let := affinePointFieldAlgebra (c.map ≫ fP)
  let := affineSchemePointTopologyOfStructure (c.map ≫ fP)
  let z := (affineSchemePointHomeomorphOfStructure (c.map ≫ fP)).symm
    (polynomialProjVectorChartInheritedPoint N i v)
  have hc : Set.range c.map ⊆ polynomialProjCoordinateOpen ℂ N i := by
    rintro _ ⟨x, rfl⟩
    change (polynomialProjCoordinateOpen ℂ N i).ι
      ((polynomialProjCoordinateSchemeIso ℂ N i).inv x) ∈ polynomialProjCoordinateOpen ℂ N i
    exact ((polynomialProjCoordinateSchemeIso ℂ N i).inv x).property
  have hp : schemeComplexPointImage fP (complexAffineChartPointMap fP c z) ∈
      polynomialProjCoordinateOpen ℂ N i := by
    rw [schemeComplexPointImage_chart]
    exact hc ⟨_, rfl⟩
  have hcoef : schemeAffineSectionCoefficient c (polynomialProjCoordinateOpen ℂ N i) hc
      (polynomialProjCoordinateRegularRatio ℂ N i k) = polynomialProjCoordinateRatio ℂ N i k := by
    change (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing ℂ N i))).hom
      ((polynomialProjCoordinateImmersion ℂ N i).appLE (polynomialProjCoordinateOpen ℂ N i) ⊤ _
        (polynomialProjCoordinateRegularRatio ℂ N i k)) = _
    rw [coordinateRegularPullback_eq, polynomialProjCoordinateRegularPullback_ratio]
    simp only [affineCoordinateMap]
    exact Iso.inv_hom_id_apply _ _
  have hs := schemeAffineOriginalRegularStalk_section fP c z
    (polynomialProjCoordinateOpen ℂ N i) hc (polynomialProjCoordinateRegularRatio ℂ N i k)
  rw [hcoef] at hs
  have he := schemeComplexPointStalkEval_affine fP c z (polynomialProjCoordinateRatio ℂ N i k)
  rw [hs] at he
  have hvalue := canonical_value_original fP N (identityEmbedding N)
    (polynomialProjCoordinateOpen ℂ N i) (polynomialProjCoordinateRegularRatio ℂ N i k)
      (complexAffineChartPointMap fP c z) hp
  rw [hvalue] at he
  have hz : affineSchemePointHomeomorphOfStructure (c.map ≫ fP) z =
      polynomialProjVectorChartInheritedPoint N i v :=
    (affineSchemePointHomeomorphOfStructure (c.map ≫ fP)).apply_symm_apply _
  rw [hz] at he
  exact he.trans (polynomialProjVectorChartAlgebraPoint_ratio N i k v hi)


/-- Actual nonzero homogeneous coordinate puts the SAME native vector point in its original coordinate chart. -/
theorem nativeVectorPoint_mem (N : ℕ) (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0) :
    schemeComplexPointImage (polynomialProjStructureMap ℂ N) (polynomialProjVectorChartPoint N i v) ∈
      coordOpen (identityEmbedding N) i := by
  change MvPolynomial.X i ∉ (schemeComplexPointImage (polynomialProjStructureMap ℂ N)
    (polynomialProjVectorChartPoint N i v)).asHomogeneousIdeal
  intro h
  have hz := (polynomialProjVectorChartPoint_mem_homogeneous_positive N i v hi 1 one_pos
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)).mp h
  exact hi (by simpa only [MvPolynomial.eval_X] using hz)

/-- **The actual native vector point has exactly its original projective class** in the unchanged book manifold. -/
theorem nativeVectorPoint_projectivePoint (N : ℕ) (i : Fin (N + 1))
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (hi : v i ≠ 0) :
    projectivePoint (polynomialProjStructureMap ℂ N) (identityEmbedding N) N
      (polynomialProjVectorChartPoint N i v) = mk v hv := by
  rw [projectivePoint_eq (polynomialProjStructureMap ℂ N) (identityEmbedding N) N i
    (nativeVectorPoint_mem N i v hi)]
  apply (mk_eq_mk_iff _ hv).mpr
  refine ⟨(v i)⁻¹, ?_⟩
  funext k
  change (v i)⁻¹ * v k = schemeOpenRegularFunction (polynomialProjStructureMap ℂ N) N
    (identityEmbedding N) (coordOpen (identityEmbedding N) i) (ratio (identityEmbedding N) i k)
      (polynomialProjVectorChartPoint N i v)
  rw [nativeVectorPoint_ratio N i k v hi]
  rw [div_eq_mul_inv, mul_comm]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveReadback
