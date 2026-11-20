import SGPT.Projective.SourceHyperplaneBundle
import SGPT.Projective.SourceFiniteSectionMap
import SGPT.Toric.PointBlowupGeometry

/-! Genuine native simplex coordinate sections, including every boundary and N=0. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set Filter
open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff BigOperators

/-- Every original simplex vertex is an actual lattice point of its original
hyperplane Cartier divisor, without a positive-dimension assumption. -/
def sourceSimplexCoordinateLatticePoint (N : ℕ) (i : Fin (N+1)) :
    toricLatticePoints (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N))) :=
  ⟨simplexGenerator N (finSuccEquiv N i), by
    change latticeVector (simplexGenerator N (finSuccEquiv N i)) ∈
      toricDivisorPolytope (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N)))
    rw [simplexHyperplaneDivisor_eq_ample]
    exact latticeVector_vertex_mem_ampleDivisorPolytope (simplexGenerator N)
      (simplex_edgeSmooth (N := N)) (simplexVertex (finSuccEquiv N i))⟩

/-- All original Cartier data are present in the actual coordinate family. -/
theorem sourceSimplexCoordinateLatticePoint_containsDatum (N : ℕ)
    (v : latticePolytopeVertices (simplexGenerator N)) :
    ∃ i : Fin (N+1), (sourceSimplexCoordinateLatticePoint N i).val =
      toricCartierDatum (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N))) v := by
  obtain ⟨o, ho⟩ := exists_generator_eq_of_mem_vertices v
  have hv : v = simplexVertex o := Subtype.ext ho.symm
  refine ⟨(finSuccEquiv N).symm o, ?_⟩
  rw [hv, toricCartierDatum_simplexHyperplaneDivisor]
  simp only [sourceSimplexCoordinateLatticePoint, Equiv.apply_symm_apply]

/-- An actual original native full holomorphic coordinate section. -/
def sourceSimplexCoordinateNativeSection (N : ℕ) (i : Fin (N+1)) :
    HolomorphicSections (n := N)
      (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N)).Fiber :=
  toricNativeSectionOfToric (sourceSimplexHyperplaneMetric N)
    (originalMonomialSection (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N)))
      (sourceSimplexCoordinateLatticePoint N i))

/-- Literal coefficient in EVERY original vertex frame, including boundary. -/
theorem sourceSimplexCoordinateNativeSection_coefficient (N : ℕ) (i : Fin (N+1))
    (v : latticePolytopeVertices (simplexGenerator N))
    {p : PolytopeToricVariety (simplexGenerator N) (simplex_edgeSmooth (N := N))}
    (hp : p ∈ (originalPolytopeNativeModelChart (simplexGenerator N)
      (simplex_edgeSmooth (N := N)) v).source) :
    ((toricNativeLineTrivialization (sourceSimplexHyperplaneMetric N) v)
      ⟨p, sourceSimplexCoordinateNativeSection N i p⟩).2 =
      toricMonomial (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N))) v
        (sourceSimplexCoordinateLatticePoint N i).val
        (originalPolytopeNativeModelChart (simplexGenerator N) (simplex_edgeSmooth (N := N)) v p) := by
  change ((toricNativeLineTrivialization (sourceSimplexHyperplaneMetric N) v)
    ⟨p, toricOriginalSectionNativeValue (sourceSimplexHyperplaneMetric N)
      (originalMonomialSection _ (sourceSimplexCoordinateLatticePoint N i)) p⟩).2 = _
  rw [toricOriginalSectionNativeValue_coefficient _ _ v hp,
    originalMonomialSection_coefficient]

/-- The actual coordinate family genuinely generates EVERY original fiber.
The coefficient one in an internally chosen vertex chart proves generation. -/
theorem sourceSimplexCoordinateNativeSection_generating (N : ℕ) :
    ∀ p : PolytopeToricVariety (simplexGenerator N) (simplex_edgeSmooth (N := N)),
      ∃ i : Fin (N+1), sourceSimplexCoordinateNativeSection N i p ≠ 0 := by
  intro p
  obtain ⟨v, hp⟩ := originalPolytopeNativeModelChart_cover (simplexGenerator N)
    (simplex_edgeSmooth (N := N)) p
  obtain ⟨i, hi⟩ := sourceSimplexCoordinateLatticePoint_containsDatum N v
  have hOne : ((toricNativeLineTrivialization (sourceSimplexHyperplaneMetric N) v)
      ⟨p, sourceSimplexCoordinateNativeSection N i p⟩).2 = 1 := by
    rw [sourceSimplexCoordinateNativeSection_coefficient N i v hp]
    simp only [hi, toricMonomial, sub_self, Int.toNat_zero, pow_zero, Finset.prod_const_one]
  refine ⟨i, ?_⟩
  intro hz
  let e := toricNativeLineTrivialization (sourceSimplexHyperplaneMetric N) v
  have he : p ∈ e.baseSet := hp
  have hZero : (e ⟨p, (0 : ToricNativeLineFiber (sourceSimplexHyperplaneMetric N) p)⟩).2 = 0 :=
    (e.linearEquivAt ℂ p he).map_zero
  rw [hz] at hOne
  exact one_ne_zero (hOne.symm.trans hZero)

/-- The ACTUAL native family map reads the actual original Cartier monomial
map, in every original vertex chart. -/
theorem sourceSimplexCoordinateNativeSection_projectiveMap_eq_monomial (N : ℕ)
    (p : PolytopeToricVariety (simplexGenerator N) (simplex_edgeSmooth (N := N))) :
    sourceNativeFiniteSectionProjectiveMap
      (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
      (sourceSimplexCoordinateNativeSection N) (sourceSimplexCoordinateNativeSection_generating N) p =
      originalMonomialProjectiveMap (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N)))
        (sourceSimplexCoordinateLatticePoint N) (sourceSimplexCoordinateLatticePoint_containsDatum N) p := by
  obtain ⟨v, hp⟩ := originalPolytopeNativeModelChart_cover (simplexGenerator N)
    (simplex_edgeSmooth (N := N)) p
  rw [sourceNativeFiniteSectionProjectiveMap_frame _ _ _
    (toricNativeLineAtlasFrame (sourceSimplexHyperplaneMetric N) v) p hp,
    originalMonomialProjectiveMap_eq_chart _ _ _ v hp]
  apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  simp only [one_smul]
  exact (sourceSimplexCoordinateNativeSection_coefficient N i v hp).symm

/-- The SAME original native full-section coordinate map is exactly the
established genuine simplex/projective biholomorphism at EVERY original
point. Boundary equality follows from the existing genuine dense torus. -/
theorem sourceSimplexCoordinateNativeSection_projectiveMap_eq_simplex (N : ℕ)
    (p : PolytopeToricVariety (simplexGenerator N) (simplex_edgeSmooth (N := N))) :
    sourceNativeFiniteSectionProjectiveMap
      (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
      (sourceSimplexCoordinateNativeSection N) (sourceSimplexCoordinateNativeSection_generating N) p =
      simplexProjectiveHomeomorph (simplex_edgeSmooth (N := N)) p := by
  rw [sourceSimplexCoordinateNativeSection_projectiveMap_eq_monomial]
  let D := simplexHyperplaneDivisor (simplex_edgeSmooth (N := N))
  let G := originalMonomialProjectiveMap D (sourceSimplexCoordinateLatticePoint N)
    (sourceSimplexCoordinateLatticePoint_containsDatum N)
  have hG : Continuous G := (contMDiff_originalMonomialProjectiveMap D
    (sourceSimplexCoordinateLatticePoint N) (sourceSimplexCoordinateLatticePoint_containsDatum N)).continuous
  have hall := toricCartier_eqOn_of_denseTorus Set.univ isOpen_univ G
    (simplexProjectiveHomeomorph (simplex_edgeSmooth (N := N))) hG.continuousOn
    (simplexProjectiveHomeomorph (simplex_edgeSmooth (N := N))).continuous.continuousOn (by
      intro a _ha
      dsimp only [G]
      rw [originalMonomialProjectiveMap_torus, simplexProjectiveHomeomorph_embedding]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (latticeCharacter (simplexGenerator N none) a : ℂ) = 1
        simp [simplexGenerator_none, latticeCharacter]
      · change (latticeCharacter (simplexGenerator N (some j)) a : ℂ) = a j
        simp [simplexGenerator_some, latticeCharacter, Pi.single_apply])
  exact hall (Set.mem_univ p)

end SGPT.Bergman.NativeKodairaPullback
