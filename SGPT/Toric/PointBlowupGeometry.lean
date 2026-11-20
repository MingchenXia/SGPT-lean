import SGPT.Toric.NativePhysicalLineBundle
import SGPT.Projective.Maps
import SGPT.Toric.Toric4Okounkov
import Mathlib.Topology.Homeomorph.Lemmas
import SGPT.Toric.Toric4Projective
import Lean.Elab.Command

section PointBlowupCanonicalFragment001
/- BEGIN OriginalMonomialProjectiveMapDraft; original source SHA256 60aea249cd4569c24dc4c5911115d63f1c39f5e2d6db827f16f60229b006aa5e -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators


variable {n r : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original character section, with membership manufactured by
its original divisor-polytope condition. -/
def originalMonomialSection (D : ToricDivisor γ hs) (m : toricLatticePoints D) :
    toricSections D :=
  ⟨fun a => (latticeCharacter m.val a : ℂ), latticeCharacter_mem_toricSections D m.property⟩

/-- Uniqueness on the actual dense coordinate torus identifies the existing
original entire section coefficient with its actual polynomial monomial. -/
theorem originalMonomialSection_coefficient (D : ToricDivisor γ hs)
    (m : toricLatticePoints D) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (originalMonomialSection D m) v = toricMonomial D v m.val := by
  apply toricSectionCoeff_unique D v
    (differentiable_toricOriginalSectionCoeff _ v).continuous
    (differentiable_toricMonomial D v m.val).continuous
  · exact toricOriginalSectionCoeff_torus _ v
  · exact latticeCharacter_eq_toricMonomial D m.property v

/-- Entire-overlap compatibility on the SAME original manifold, including
its boundary. No overlap compatibility certificate is an input. -/
theorem originalMonomial_transition (D : ToricDivisor γ hs)
    (m : toricLatticePoints D) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricMonomial D w m.val (originalPolytopeNativeModelChart γ hs w p) =
      toricCartierTransition D v w p *
        toricMonomial D v m.val (originalPolytopeNativeModelChart γ hs v p) := by
  have h := toricOriginalSectionCoeff_transition (originalMonomialSection D m) v w hv hw
  simpa only [originalMonomialSection_coefficient] using h

/-- The actual vector of original section coefficients in a vertex frame. -/
def originalMonomialVector (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (v : latticePolytopeVertices γ) (z : ComplexModel n) : Fin (r + 1) → ℂ :=
  fun i => toricMonomial D v (m i).val z

/-- A Cartier datum present in the actual system gives the constant one in
that entire chart, so basepoint freeness is a conclusion. -/
theorem originalMonomialVector_ne_zero (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (hdatum : ∀ v, ∃ i, (m i).val = toricCartierDatum D v)
    (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    originalMonomialVector D m v z ≠ 0 := by
  obtain ⟨i, hi⟩ := hdatum v
  intro h
  have hc := congrFun h i
  simp only [originalMonomialVector, hi, toricMonomial, sub_self, Int.toNat_zero,
    pow_zero, Finset.prod_const_one, Pi.zero_apply] at hc
  exact one_ne_zero hc

/-- A genuine map on the SAME original projective orbit closure. Its
preferred chart is an internal choice from the existing original cover. -/
def originalMonomialProjectiveMap (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (hdatum : ∀ v, ∃ i, (m i).val = toricCartierDatum D v)
    (p : PolytopeToricVariety γ hs) : SGPT.Projective.ComplexProjectiveSpace r :=
  let v := toricNativePreferredVertex γ hs p
  SGPT.Projective.ComplexProjectiveSpace.mk (originalMonomialVector D m v (originalPolytopeNativeModelChart γ hs v p))
    (originalMonomialVector_ne_zero D m hdatum v _)

/-- The global map has the literal polynomial lift in EVERY original chart;
all choices disappear from this conclusion. -/
theorem originalMonomialProjectiveMap_eq_chart (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (hdatum : ∀ v, ∃ i, (m i).val = toricCartierDatum D v)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    originalMonomialProjectiveMap D m hdatum p =
      SGPT.Projective.ComplexProjectiveSpace.mk (originalMonomialVector D m v (originalPolytopeNativeModelChart γ hs v p))
        (originalMonomialVector_ne_zero D m hdatum v _) := by
  let w := toricNativePreferredVertex γ hs p
  have hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source :=
    toricNativePreferredVertex_mem p
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨toricCartierTransition D v w p, ?_⟩
  funext i
  exact (originalMonomial_transition D (m i) v w hv hw).symm

/-- Existing projective holomorphic-lift geometry proves holomorphy of the
actual glued map, with no incoming holomorphic map or model identification. -/
theorem contMDiff_originalMonomialProjectiveMap (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (hdatum : ∀ v, ∃ i, (m i).val = toricCartierDatum D v) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel r) ∞
      (originalMonomialProjectiveMap D m hdatum) := by
  intro p
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  have hmem : originalPolytopeNativeModelChart γ hs v ∈
      atlas (ComplexModel n) (PolytopeToricVariety γ hs) := ⟨v, rfl⟩
  have hchart : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : PolytopeToricVariety γ hs => originalPolytopeNativeModelChart γ hs v q) p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas
      (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) hmem) hv
  have hdiff : Differentiable ℂ (originalMonomialVector D m v) := by
    apply differentiable_pi.mpr
    intro i
    exact differentiable_toricMonomial D v (m i).val
  have hsmooth : ContDiff ℂ ∞ (originalMonomialVector D m v) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex hdiff.differentiableOn isOpen_univ)
  apply SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_of_lift (hsmooth.contMDiff.contMDiffAt.comp p hchart)
    (originalMonomialVector_ne_zero D m hdatum v _)
  filter_upwards [(originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds hv] with q hq
  exact ⟨originalMonomialVector_ne_zero D m hdatum v _,
    originalMonomialProjectiveMap_eq_chart D m hdatum v hq⟩

/-- No homogeneous character vector vanishes at a genuine original torus
point; even a one-coordinate target retains this conclusion. -/
theorem originalCharacterVector_ne_zero (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D) (a : Fin n → ℂˣ) :
    (fun i => (latticeCharacter (m i).val a : ℂ)) ≠ 0 := by
  intro h
  exact Units.ne_zero _ (congrFun h 0)

/-- The SAME original dense torus sees exactly the expected original
character map, with the common Cartier frame scalar cancelled internally. -/
theorem originalMonomialProjectiveMap_torus (D : ToricDivisor γ hs)
    (m : Fin (r + 1) → toricLatticePoints D)
    (hdatum : ∀ v, ∃ i, (m i).val = toricCartierDatum D v)
    (a : Fin n → ℂˣ) :
    originalMonomialProjectiveMap D m hdatum (polytopeToricEmbedding γ hs a) =
      SGPT.Projective.ComplexProjectiveSpace.mk (fun i => (latticeCharacter (m i).val a : ℂ))
        (originalCharacterVector_ne_zero D m a) := by
  let p := polytopeToricEmbedding γ hs a
  let v := toricNativePreferredVertex γ hs p
  have hv := toricNativePreferredVertex_mem p
  rw [originalMonomialProjectiveMap_eq_chart D m hdatum v hv]
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨(latticeCharacter (toricCartierDatum D v) a : ℂ)⁻¹, ?_⟩
  funext i
  change (latticeCharacter (toricCartierDatum D v) a : ℂ)⁻¹ *
    (latticeCharacter (m i).val a : ℂ) = _
  rw [latticeCharacter_eq_toricMonomial D (m i).property v a]
  field_simp
  rfl

end SGPT.Toric.BlowdownDraft

end
/- END OriginalMonomialProjectiveMapDraft -/
end PointBlowupCanonicalFragment001

section PointBlowupCanonicalFragment002
/- BEGIN OriginalBlowdownMapDraft; original source SHA256 e52c25342433bff029ee3f5df4f49f2b00c2f37e40fd18da202935bdba51987e -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Exactly the three source hyperplane monomials 1, χe1, χe2. -/
def blowdownExponent : Fin 3 → Fin 2 → ℤ := ![![0, 0], ![1, 0], ![0, 1]]

theorem blowdownExponent_mem (i : Fin 3) :
    blowdownExponent i ∈ toricLatticePoints (blowupHyperplaneDivisor hs) := by
  change latticeVector (blowdownExponent i) ∈ toricDivisorPolytope _
  rw [toricDivisorPolytope_blowupHyperplaneDivisor]
  fin_cases i <;> norm_num [blowdownExponent, latticeVector, SGPT.AlmostSemigroup.Counting.integerCast]

/-- The three actual sections of H are manufactured from the source data. -/
def blowdownLatticePoint (i : Fin 3) : toricLatticePoints (blowupHyperplaneDivisor hs) :=
  ⟨blowdownExponent i, blowdownExponent_mem hs i⟩

/-- ALL actual original vertices have a Cartier datum in this exact system;
there is no incoming basepoint-free certificate or missing chart. -/
theorem blowdownDatum_occurs (v : latticePolytopeVertices blowupGenerator) :
    ∃ i, (blowdownLatticePoint hs i).val = toricCartierDatum (blowupHyperplaneDivisor hs) v := by
  obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
  have hv : v = blowupVertex k := Subtype.ext hk.symm
  subst v
  obtain ⟨h0, h3, h1, h2⟩ := toricCartierDatum_blowupHyperplaneDivisor hs
  fin_cases k
  · exact ⟨0, h0.symm⟩
  · exact ⟨1, h1.symm⟩
  · exact ⟨2, h2.symm⟩
  · exact ⟨0, h3.symm⟩

/-- The ACTUAL global blowdown map on the original X_P', with its original
native topology and complex atlas. No model identification is supplied. -/
def originalBlowdown : PolytopeToricVariety blowupGenerator hs →
    SGPT.Projective.ComplexProjectiveSpace 2 :=
  originalMonomialProjectiveMap (blowupHyperplaneDivisor hs) (blowdownLatticePoint hs)
    (blowdownDatum_occurs hs)

theorem contMDiff_originalBlowdown :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalBlowdown hs) :=
  contMDiff_originalMonomialProjectiveMap _ _ _

/-- Original primitive edge bases determine the coordinate permutation;
the choice is internal, and all actual charts and points are unchanged. -/
def blowupOriginalPermutation (k : Fin 4) : Equiv.Perm (Fin 2) :=
  (exists_perm_originalPolytopeNativeBasis_eq hs (blowupVertex k)
    (blowup_isVertexConeBasis k)).choose

theorem blowupOriginalPermutation_basis (k : Fin 4) (j : Fin 2) :
    originalPolytopeNativeBasis blowupGenerator hs (blowupVertex k) j =
      blowupBasis k (blowupOriginalPermutation hs k j) :=
  (exists_perm_originalPolytopeNativeBasis_eq hs (blowupVertex k)
    (blowup_isVertexConeBasis k)).choose_spec j

/-- Literal original coordinates reindexed by the derived source basis. -/
def blowupOriginalCoordinates (k : Fin 4) (z : Fin 2 → ℂ) : ComplexModel 2 :=
  modelPoint (fun j => z (blowupOriginalPermutation hs k j))

/-- A whole affine parametrization of the SAME original vertex open. -/
def blowupOriginalChartPoint (k : Fin 4) (z : Fin 2 → ℂ) :
    PolytopeToricVariety blowupGenerator hs :=
  (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).symm
    (blowupOriginalCoordinates hs k z)

theorem blowupOriginalChartPoint_mem (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈
      (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source := by
  apply (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).map_target
  rw [originalPolytopeNativeModelChart_target]
  exact mem_univ _

theorem blowupOriginalChartPoint_coordinate (k : Fin 4) (z : Fin 2 → ℂ) :
    originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)
      (blowupOriginalChartPoint hs k z) = blowupOriginalCoordinates hs k z := by
  apply (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).right_inv
  rw [originalPolytopeNativeModelChart_target]
  exact mem_univ _

/-- The four actual whole-affine parametrizations cover the original space. -/
theorem blowupOriginalChartPoint_cover (p : PolytopeToricVariety blowupGenerator hs) :
    ∃ k z, blowupOriginalChartPoint hs k z = p := by
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover blowupGenerator hs p
  obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
  have hvk : v = blowupVertex k := Subtype.ext hk.symm
  subst v
  refine ⟨k, fun j => originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p
    ((blowupOriginalPermutation hs k).symm j), ?_⟩
  have hcoord : blowupOriginalCoordinates hs k
      (fun j => originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p
        ((blowupOriginalPermutation hs k).symm j)) =
      originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p := by
    ext j
    simp [blowupOriginalCoordinates, modelPoint_apply]
  unfold blowupOriginalChartPoint
  rw [hcoord]
  exact (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).left_inv hv

/-- Reindexing the internally derived basis yields the actual expected
monomial polynomial, proved rather than assumed for the original chart. -/
theorem blowupMonomial_ordered (D : ToricDivisor blowupGenerator hs)
    (k : Fin 4) (m : Fin 2 → ℤ) (z : Fin 2 → ℂ) :
    toricMonomial D (blowupVertex k) m (blowupOriginalCoordinates hs k z) =
      ∏ j : Fin 2, z j ^ (intPairing m (vertexConeRay (blowupBasis k) j) -
        intPairing (toricCartierDatum D (blowupVertex k))
          (vertexConeRay (blowupBasis k) j)).toNat := by
  unfold toricMonomial
  simp only [blowupOriginalCoordinates, modelPoint_apply,
    polytopeToricRayGenerator_eq_vertexConeRay hs (blowupVertex k)
      (blowupOriginalPermutation_basis hs k)]
  exact Equiv.prod_comp (blowupOriginalPermutation hs k) (fun j : Fin 2 =>
    z j ^ (intPairing m (vertexConeRay (blowupBasis k) j) -
      intPairing (toricCartierDatum D (blowupVertex k)) (vertexConeRay (blowupBasis k) j)).toNat)

/-- Expected coordinate order: the four source bases are respectively
((1,0),(-1,1)), ((-1,1),(-1,0)), ((0,-1),(1,-1)), ((1,-1),(0,1)). -/
def blowdownChartVector (k : Fin 4) (z : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![![1, z 0, z 0 * z 1], ![z 1, 1, z 0], ![z 0, z 1, 1],
    ![1, z 0 * z 1, z 1]] k

theorem blowdownOriginalVector (k : Fin 4) (z : Fin 2 → ℂ) :
    originalMonomialVector (blowupHyperplaneDivisor hs) (blowdownLatticePoint hs)
      (blowupVertex k) (blowupOriginalCoordinates hs k z) = blowdownChartVector k z := by
  obtain ⟨h0, h3, h1, h2⟩ := toricCartierDatum_blowupHyperplaneDivisor hs
  have hdatum (j : Fin 4) : toricCartierDatum (blowupHyperplaneDivisor hs) (blowupVertex j) =
      (![![0, 0], ![1, 0], ![0, 1], ![0, 0]] : Fin 4 → Fin 2 → ℤ) j := by
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  funext i
  change toricMonomial _ _ (blowdownExponent i) _ = _
  rw [blowupMonomial_ordered, hdatum k]
  fin_cases k <;> fin_cases i <;>
    simp [blowdownChartVector, blowdownExponent, blowupBasis,
      vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one,
      Fin.prod_univ_two, intPairing, Fin.sum_univ_two]

theorem blowdownChartVector_ne_zero (k : Fin 4) (z : Fin 2 → ℂ) :
    blowdownChartVector k z ≠ 0 := by
  fin_cases k
  · intro h
    have hc := congrFun h 0
    simp [blowdownChartVector] at hc
  · intro h
    have hc := congrFun h 1
    simp [blowdownChartVector] at hc
  · intro h
    have hc := congrFun h 2
    simp [blowdownChartVector] at hc
  · intro h
    have hc := congrFun h 0
    simp [blowdownChartVector] at hc

/-- All four blowdown formulas hold on the ACTUAL original chart points,
including the exceptional divisor and every other boundary point. -/
theorem originalBlowdown_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    originalBlowdown hs (blowupOriginalChartPoint hs k z) =
      SGPT.Projective.ComplexProjectiveSpace.mk (blowdownChartVector k z)
        (blowdownChartVector_ne_zero k z) := by
  unfold originalBlowdown
  rw [originalMonomialProjectiveMap_eq_chart _ _ _ (blowupVertex k)
    (blowupOriginalChartPoint_mem hs k z), blowupOriginalChartPoint_coordinate]
  congr 1
  exact blowdownOriginalVector hs k z

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowdownMapDraft -/
end PointBlowupCanonicalFragment002

section PointBlowupCanonicalFragment003
/- BEGIN OriginalBlowupDirectionDraft; original source SHA256 d912ddcf9c15117a4e6f5aa17d1b48f0f616416a1758a15c44c185a0156b6a55 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual source divisor H-E whose two sections recover the blowup
direction; all original boundary data are retained. -/
def blowupDirectionCoeff (u : Fin 2 → ℤ) : ℤ :=
  if u = blowupRay4 then 1 else if u = blowupRay7 then -1 else 0

def blowupDirectionDivisor : ToricDivisor blowupGenerator hs :=
  toricDivisorOfCoeff hs blowupDirectionCoeff

def blowupDirectionDatum : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![1, 0], ![0, 1], ![0, 1]]

/-- The two distinct Cartier data are proved from the actual original
cone pairings, without prescribing an outgoing direction map. -/
theorem blowupDirection_cartierDatum (k : Fin 4) :
    toricCartierDatum (blowupDirectionDivisor hs) (blowupVertex k) = blowupDirectionDatum k := by
  apply toricCartierDatum_ofCoeff blowupDirectionCoeff (blowupVertex k)
    (blowup_isVertexConeBasis k)
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [blowupDirectionDatum, blowupBasis, vertexConeRay_lattice2Basis_zero,
      vertexConeRay_lattice2Basis_one, blowupDirectionCoeff,
      blowupRay4, blowupRay5, blowupRay6, blowupRay7, intPairing, Fin.sum_univ_two]

def blowupDirectionExponent : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![0, 1]]

theorem blowupDirectionExponent_mem (i : Fin 2) :
    blowupDirectionExponent i ∈ toricLatticePoints (blowupDirectionDivisor hs) := by
  change latticeVector (blowupDirectionExponent i) ∈ toricDivisorPolytope _
  rw [blowupDirectionDivisor, blowup_toricDivisorPolytope]
  fin_cases i <;> norm_num [blowupDirectionExponent, latticeVector,
    SGPT.AlmostSemigroup.Counting.integerCast, blowupDirectionCoeff,
    blowupRay4, blowupRay5, blowupRay6, blowupRay7]

def blowupDirectionLatticePoint (i : Fin 2) : toricLatticePoints (blowupDirectionDivisor hs) :=
  ⟨blowupDirectionExponent i, blowupDirectionExponent_mem hs i⟩

theorem blowupDirectionDatum_occurs (v : latticePolytopeVertices blowupGenerator) :
    ∃ i, (blowupDirectionLatticePoint hs i).val = toricCartierDatum (blowupDirectionDivisor hs) v := by
  obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
  have hv : v = blowupVertex k := Subtype.ext hk.symm
  subst v
  rw [blowupDirection_cartierDatum]
  fin_cases k
  · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩

/-- A genuine global holomorphic map on the original X_P′, recovering the
projective direction even on the entire exceptional fibre. -/
def originalBlowupDirection : PolytopeToricVariety blowupGenerator hs →
    SGPT.Projective.ComplexProjectiveSpace 1 :=
  originalMonomialProjectiveMap (blowupDirectionDivisor hs) (blowupDirectionLatticePoint hs)
    (blowupDirectionDatum_occurs hs)

theorem contMDiff_originalBlowupDirection :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 1) ∞ (originalBlowupDirection hs) :=
  contMDiff_originalMonomialProjectiveMap _ _ _

def blowupDirectionChartVector (k : Fin 4) (z : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![![1, z 1], ![1, z 0], ![z 1, 1], ![z 0, 1]] k

theorem blowupDirectionOriginalVector (k : Fin 4) (z : Fin 2 → ℂ) :
    originalMonomialVector (blowupDirectionDivisor hs) (blowupDirectionLatticePoint hs)
      (blowupVertex k) (blowupOriginalCoordinates hs k z) = blowupDirectionChartVector k z := by
  funext i
  change toricMonomial _ _ (blowupDirectionExponent i) _ = _
  rw [blowupMonomial_ordered, blowupDirection_cartierDatum]
  fin_cases k <;> fin_cases i <;>
    simp [blowupDirectionDatum, blowupDirectionChartVector, blowupDirectionExponent,
      blowupBasis, vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one,
      Fin.prod_univ_two, intPairing, Fin.sum_univ_two]

theorem blowupDirectionChartVector_ne_zero (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupDirectionChartVector k z ≠ 0 := by
  fin_cases k
  · intro h
    have hc := congrFun h 0
    simp [blowupDirectionChartVector] at hc
  · intro h
    have hc := congrFun h 0
    simp [blowupDirectionChartVector] at hc
  · intro h
    have hc := congrFun h 1
    simp [blowupDirectionChartVector] at hc
  · intro h
    have hc := congrFun h 1
    simp [blowupDirectionChartVector] at hc

/-- All four actual direction formulas in the SAME original vertex charts. -/
theorem originalBlowupDirection_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    originalBlowupDirection hs (blowupOriginalChartPoint hs k z) =
      SGPT.Projective.ComplexProjectiveSpace.mk (blowupDirectionChartVector k z)
        (blowupDirectionChartVector_ne_zero k z) := by
  unfold originalBlowupDirection
  rw [originalMonomialProjectiveMap_eq_chart _ _ _ (blowupVertex k)
    (blowupOriginalChartPoint_mem hs k z), blowupOriginalChartPoint_coordinate]
  congr 1
  exact blowupDirectionOriginalVector hs k z

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowupDirectionDraft -/
end PointBlowupCanonicalFragment003

section PointBlowupCanonicalFragment004
/- BEGIN OriginalBlowdownDivisorsDraft; original source SHA256 9253dc7282bcf47d31095aa7b6b3e43ecf46089f1a5c2198eb46691eec67be46 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The same original toric ray σ7, rather than an independently supplied
exceptional subset. -/
def blowupExceptionalRay : PolytopeToricRays blowupGenerator hs :=
  ⟨blowupRay7, by rw [blowup_rays hs]; simp⟩

def blowupStrictLineRay : PolytopeToricRays blowupGenerator hs :=
  ⟨blowupRay5, by rw [blowup_rays hs]; simp⟩

/-- Every actual prime-divisor incidence, in source-ordered coordinates. -/
theorem originalPrimeDivisor_chart (ρ : PolytopeToricRays blowupGenerator hs)
    (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈ toricPrimeDivisor ρ ↔
      ∃ j, vertexConeRay (blowupBasis k) j = ρ.val ∧ z j = 0 := by
  rw [mem_toricPrimeDivisor_iff (blowupOriginalChartPoint_mem hs k z) ρ,
    blowupOriginalChartPoint_coordinate]
  constructor
  · rintro ⟨j, hj, hz⟩
    refine ⟨blowupOriginalPermutation hs k j, ?_, hz⟩
    exact (polytopeToricRayGenerator_eq_vertexConeRay hs (blowupVertex k)
      (blowupOriginalPermutation_basis hs k) j).symm.trans hj
  · rintro ⟨j, hj, hz⟩
    refine ⟨(blowupOriginalPermutation hs k).symm j, ?_, ?_⟩
    · rw [polytopeToricRayGenerator_eq_vertexConeRay hs (blowupVertex k)
        (blowupOriginalPermutation_basis hs k), Equiv.apply_symm_apply]
      exact hj
    · simpa only [blowupOriginalCoordinates, modelPoint_apply, Equiv.apply_symm_apply] using hz

/-- All actual boundary equations of σ7 in the original four charts. -/
theorem exceptionalRay_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈ toricPrimeDivisor (blowupExceptionalRay hs) ↔
      (![z 0 = 0, False, False, z 1 = 0] : Fin 4 → Prop) k := by
  rw [originalPrimeDivisor_chart]
  fin_cases k <;> norm_num [Fin.exists_fin_two, blowupBasis, blowupExceptionalRay,
    vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one, blowupRay7]

/-- All actual boundary equations of σ5 in the original four charts. -/
theorem strictLineRay_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈ toricPrimeDivisor (blowupStrictLineRay hs) ↔
      (![False, False, z 1 = 0, z 0 = 0] : Fin 4 → Prop) k := by
  rw [originalPrimeDivisor_chart]
  fin_cases k <;> norm_num [Fin.exists_fin_two, blowupBasis, blowupStrictLineRay,
    vertexConeRay_lattice2Basis_zero, vertexConeRay_lattice2Basis_one, blowupRay5]

/-- The literal book point [1:0:0]. -/
def blowdownOrigin : SGPT.Projective.ComplexProjectiveSpace 2 :=
  SGPT.Projective.ComplexProjectiveSpace.mk (![1, 0, 0] : Fin 3 → ℂ)
    (by intro h; have hc := congrFun h 0; simp at hc)

theorem projective_mk_eq_blowdownOrigin_iff (X : Fin 3 → ℂ) (hX : X ≠ 0) :
    SGPT.Projective.ComplexProjectiveSpace.mk X hX = blowdownOrigin ↔ X 1 = 0 ∧ X 2 = 0 := by
  rw [blowdownOrigin, SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨by simpa using (congrFun hc 1).symm, by simpa using (congrFun hc 2).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨X 0, ?_⟩
    funext i
    fin_cases i <;> simp [h1, h2]

/-- The actual fibre of the genuine global blowdown at the literal book
origin is EXACTLY the existing original toric prime divisor σ7. -/
theorem originalBlowdown_fibre_origin :
    {p : PolytopeToricVariety blowupGenerator hs | originalBlowdown hs p = blowdownOrigin} =
      toricPrimeDivisor (blowupExceptionalRay hs) := by
  ext p
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  change originalBlowdown hs (blowupOriginalChartPoint hs k z) = blowdownOrigin ↔ _
  rw [originalBlowdown_chart, projective_mk_eq_blowdownOrigin_iff, exceptionalRay_chart]
  fin_cases k <;> simp [blowdownChartVector, mul_eq_zero] <;> aesop

/-- Vanishing of a homogeneous coordinate is independent of the chosen
representative, retaining arbitrary nonzero vectors. -/
theorem projective_rep_mk_eq_zero_iff {N : ℕ} (X : Fin (N + 1) → ℂ)
    (hX : X ≠ 0) (i : Fin (N + 1)) :
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX).rep i = 0 ↔ X i = 0 := by
  obtain ⟨c, hc, hrep⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX) hX rfl
  rw [hrep, Pi.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc]

/-- The SAME original whole-affine parametrization is continuous. -/
theorem continuous_blowupOriginalChartPoint (k : Fin 4) :
    Continuous (blowupOriginalChartPoint hs k) := by
  have hinv : Continuous (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).symm :=
    continuousOn_univ.mp (by
      have hc : ContinuousOn
          (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).symm
          (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).target :=
        (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).symm.continuousOn
      rwa [originalPolytopeNativeModelChart_target] at hc)
  exact hinv.comp (continuous_modelPoint.comp (continuous_pi fun j =>
    continuous_apply (blowupOriginalPermutation hs k j)))

/-- The exact open line printed by the source, pulled back under the actual
map. The strict transform below is its actual topological closure. -/
def originalSourceLineLift : Set (PolytopeToricVariety blowupGenerator hs) :=
  {p | (originalBlowdown hs p).rep 1 = 0 ∧
    (originalBlowdown hs p).rep 0 ≠ 0 ∧ (originalBlowdown hs p).rep 2 ≠ 0}

theorem originalSourceLineLift_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupOriginalChartPoint hs k z ∈ originalSourceLineLift hs ↔
      (![False, False, z 1 = 0 ∧ z 0 ≠ 0, z 0 = 0 ∧ z 1 ≠ 0] : Fin 4 → Prop) k := by
  change (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep 1 = 0 ∧
    (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep 0 ≠ 0 ∧
    (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep 2 ≠ 0 ↔ _
  have hc (i : Fin 3) :
      (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep i = 0 ↔
        blowdownChartVector k z i = 0 := by
    rw [originalBlowdown_chart]
    exact projective_rep_mk_eq_zero_iff _ _ i
  apply (and_congr (hc 1) (and_congr (not_congr (hc 0)) (not_congr (hc 2)))).trans
  fin_cases k <;> simp [blowdownChartVector, mul_eq_zero] <;> aesop

/-- The book's strict transform of {X1=0, X0X2≠0} is the actual existing
original ray divisor σ5; density at BOTH removed endpoints is proved. -/
theorem originalSourceLine_strictTransform :
    closure (originalSourceLineLift hs) = toricPrimeDivisor (blowupStrictLineRay hs) := by
  apply Subset.antisymm
  · apply (isClosed_toricPrimeDivisor (blowupStrictLineRay hs)).closure_subset_iff.mpr
    intro p hp
    obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
    rw [originalSourceLineLift_chart] at hp
    rw [strictLineRay_chart]
    fin_cases k
    · exact hp.elim
    · exact hp.elim
    · exact hp.1
    · exact hp.1
  · intro p hp
    obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
    rw [strictLineRay_chart] at hp
    fin_cases k
    · exact hp.elim
    · exact hp.elim
    · have hz : z 1 = 0 := hp
      let f : ℂ → PolytopeToricVariety blowupGenerator hs :=
        fun t => blowupOriginalChartPoint hs 2 ![t, 0]
      have hf : Continuous f := (continuous_blowupOriginalChartPoint hs 2).comp (by
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop)
      have hd : z 0 ∈ closure ({(0 : ℂ)}ᶜ) := dense_compl_singleton 0 (z 0)
      have hclosure := mem_closure_image hf.continuousAt hd
      have hsub : f '' ({(0 : ℂ)}ᶜ) ⊆ originalSourceLineLift hs := by
        rintro q ⟨t, ht, rfl⟩
        rw [originalSourceLineLift_chart]
        exact ⟨rfl, ht⟩
      have heq : f (z 0) = blowupOriginalChartPoint hs 2 z := by
        change blowupOriginalChartPoint hs 2 ![z 0, 0] = _
        apply congrArg (blowupOriginalChartPoint hs 2)
        funext i
        fin_cases i <;> simp [hz]
      rw [heq] at hclosure
      exact closure_mono hsub hclosure
    · have hz : z 0 = 0 := hp
      let f : ℂ → PolytopeToricVariety blowupGenerator hs :=
        fun t => blowupOriginalChartPoint hs 3 ![0, t]
      have hf : Continuous f := (continuous_blowupOriginalChartPoint hs 3).comp (by
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop)
      have hd : z 1 ∈ closure ({(0 : ℂ)}ᶜ) := dense_compl_singleton 0 (z 1)
      have hclosure := mem_closure_image hf.continuousAt hd
      have hsub : f '' ({(0 : ℂ)}ᶜ) ⊆ originalSourceLineLift hs := by
        rintro q ⟨t, ht, rfl⟩
        rw [originalSourceLineLift_chart]
        exact ⟨rfl, ht⟩
      have heq : f (z 1) = blowupOriginalChartPoint hs 3 z := by
        change blowupOriginalChartPoint hs 3 ![0, z 1] = _
        apply congrArg (blowupOriginalChartPoint hs 3)
        funext i
        fin_cases i <;> simp [hz]
      rw [heq] at hclosure
      exact closure_mono hsub hclosure

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowdownDivisorsDraft -/
end PointBlowupCanonicalFragment004

section PointBlowupCanonicalFragment005
/- BEGIN OriginalBlowupIncidenceDraft; original source SHA256 69baaff4940507fc876932c0bab12c45535d867fe01c95bb4a251c60c826cf55 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators

/-- The LITERAL classical point-blowup incidence subset of P²×P¹. -/
def blowupIncidenceSet : Set (SGPT.Projective.ComplexProjectiveSpace 2 ×
    SGPT.Projective.ComplexProjectiveSpace 1) :=
  {q | q.1.rep 1 * q.2.rep 1 = q.1.rep 2 * q.2.rep 0}

/-- Both arbitrary nonzero representatives yield the SAME actual incidence
equation; the chosen quotient representatives impose no extra condition. -/
theorem blowupIncidence_mk_iff (X : Fin 3 → ℂ) (hX : X ≠ 0)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) :
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX,
      SGPT.Projective.ComplexProjectiveSpace.mk u hu) ∈ blowupIncidenceSet ↔
      X 1 * u 1 = X 2 * u 0 := by
  obtain ⟨c, hc, hrepX⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX) hX rfl
  obtain ⟨d, hd, hrepu⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (SGPT.Projective.ComplexProjectiveSpace.mk u hu) hu rfl
  change (SGPT.Projective.ComplexProjectiveSpace.mk X hX).rep 1 *
      (SGPT.Projective.ComplexProjectiveSpace.mk u hu).rep 1 =
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX).rep 2 *
      (SGPT.Projective.ComplexProjectiveSpace.mk u hu).rep 0 ↔ _
  rw [hrepX, hrepu]
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : (c * X 1) * (d * u 1) = (c * X 2) * (d * u 0) ↔
      (c * d) * (X 1 * u 1) = (c * d) * (X 2 * u 0) := by ring_nf
  rw [heq]
  exact ⟨mul_left_cancel₀ (mul_ne_zero hc hd), congrArg (fun x : ℂ => (c * d) * x)⟩

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The genuine original maps land in the literal incidence subset on ALL
points, including the entire exceptional fibre and both remaining boundaries. -/
theorem originalBlowup_lands_incidence (p : PolytopeToricVariety blowupGenerator hs) :
    (originalBlowdown hs p, originalBlowupDirection hs p) ∈ blowupIncidenceSet := by
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  rw [originalBlowdown_chart, originalBlowupDirection_chart, blowupIncidence_mk_iff]
  fin_cases k <;> simp [blowdownChartVector, blowupDirectionChartVector, mul_comm]

/-- An actual global map from the SAME original toric carrier to the actual
classical incidence space; neither a model identification nor output witness
is an input. -/
def originalBlowupIncidenceMap (p : PolytopeToricVariety blowupGenerator hs) :
    blowupIncidenceSet :=
  ⟨(originalBlowdown hs p, originalBlowupDirection hs p), originalBlowup_lands_incidence hs p⟩

theorem continuous_originalBlowupIncidenceMap : Continuous (originalBlowupIncidenceMap hs) :=
  ((contMDiff_originalBlowdown hs).continuous.prodMk
    (contMDiff_originalBlowupDirection hs).continuous).subtype_mk _

/-- Every literal incidence pair has an actual preimage in an internally
selected ORIGINAL affine chart. All centre and projective boundary cases
are retained, with no model-surjectivity certificate. -/
theorem exists_originalBlowup_incidence_preimage (X : Fin 3 → ℂ) (hX : X ≠ 0)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) (hinc : X 1 * u 1 = X 2 * u 0) :
    ∃ p : PolytopeToricVariety blowupGenerator hs,
      originalBlowdown hs p = SGPT.Projective.ComplexProjectiveSpace.mk X hX ∧
      originalBlowupDirection hs p = SGPT.Projective.ComplexProjectiveSpace.mk u hu := by
  by_cases h1 : X 1 = 0
  · by_cases h2 : X 2 = 0
    · have h0 : X 0 ≠ 0 := by
        intro h0
        apply hX
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      by_cases hu0 : u 0 = 0
      · have hu1 : u 1 ≠ 0 := by
          intro hu1
          apply hu
          funext i
          fin_cases i <;> simp [hu0, hu1]
        refine ⟨blowupOriginalChartPoint hs 3 ![0, 0], ?_, ?_⟩
        · rw [originalBlowdown_chart]
          apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
          refine ⟨(X 0)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [blowdownChartVector, Pi.smul_apply, smul_eq_mul, h0, h1, h2]
        · rw [originalBlowupDirection_chart]
          apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
          refine ⟨(u 1)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [blowupDirectionChartVector, Pi.smul_apply, smul_eq_mul, hu0, hu1]
      · refine ⟨blowupOriginalChartPoint hs 0 ![0, u 1 / u 0], ?_, ?_⟩
        · rw [originalBlowdown_chart]
          apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
          refine ⟨(X 0)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [blowdownChartVector, Pi.smul_apply, smul_eq_mul, h0, h1, h2]
        · rw [originalBlowupDirection_chart]
          apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
          refine ⟨(u 0)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [blowupDirectionChartVector, Pi.smul_apply, smul_eq_mul,
            hu0, div_eq_mul_inv, mul_comm]
    · have hu1 : u 1 ≠ 0 := by
        intro hu1
        have hu0 : u 0 = 0 := (mul_eq_zero.mp (by simpa [hu1] using hinc.symm)).resolve_left h2
        exact hu (by funext i; fin_cases i <;> simp [hu0, hu1])
      refine ⟨blowupOriginalChartPoint hs 2 ![X 0 / X 2, X 1 / X 2], ?_, ?_⟩
      · rw [originalBlowdown_chart]
        apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
        refine ⟨(X 2)⁻¹, ?_⟩
        funext i
        fin_cases i <;> simp [blowdownChartVector, Pi.smul_apply, smul_eq_mul,
          h2, div_eq_mul_inv, mul_comm]
      · rw [originalBlowupDirection_chart]
        apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
        refine ⟨(u 1)⁻¹, ?_⟩
        funext i
        fin_cases i
        · change (u 1)⁻¹ * u 0 = X 1 / X 2
          field_simp
          linear_combination -hinc
        · simp [blowupDirectionChartVector, Pi.smul_apply, smul_eq_mul, hu1]
  · have hu0 : u 0 ≠ 0 := by
      intro hu0
      have hu1 : u 1 = 0 := (mul_eq_zero.mp (by simpa [hu0] using hinc)).resolve_left h1
      exact hu (by funext i; fin_cases i <;> simp [hu0, hu1])
    refine ⟨blowupOriginalChartPoint hs 1 ![X 2 / X 1, X 0 / X 1], ?_, ?_⟩
    · rw [originalBlowdown_chart]
      apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      refine ⟨(X 1)⁻¹, ?_⟩
      funext i
      fin_cases i <;> simp [blowdownChartVector, Pi.smul_apply, smul_eq_mul,
        h1, div_eq_mul_inv, mul_comm]
    · rw [originalBlowupDirection_chart]
      apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      refine ⟨(u 0)⁻¹, ?_⟩
      funext i
      fin_cases i
      · simp [blowupDirectionChartVector, Pi.smul_apply, smul_eq_mul, hu0]
      · change (u 0)⁻¹ * u 1 = X 2 / X 1
        field_simp
        linear_combination hinc

/-- Genuine surjectivity to the actual classical incidence set. -/
theorem originalBlowupIncidenceMap_surjective :
    Function.Surjective (originalBlowupIncidenceMap hs) := by
  rintro ⟨⟨p, q⟩, hq⟩
  have hinc : p.rep 1 * q.rep 1 = p.rep 2 * q.rep 0 := hq
  obtain ⟨x, hp, hq⟩ := exists_originalBlowup_incidence_preimage hs
    p.rep p.rep_ne_zero q.rep q.rep_ne_zero hinc
  refine ⟨x, Subtype.ext ?_⟩
  change (originalBlowdown hs x, originalBlowupDirection hs x) = (p, q)
  exact Prod.ext (hp.trans (SGPT.Projective.ComplexProjectiveSpace.mk_rep p))
    (hq.trans (SGPT.Projective.ComplexProjectiveSpace.mk_rep q))

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowupIncidenceDraft -/
end PointBlowupCanonicalFragment005

section PointBlowupCanonicalFragment006
/- BEGIN OriginalBlowupReconstructionDraft; original source SHA256 d72727cff7d7aed1ae580c27557e73cbdaa3ae8f31863469aefa93be8a4dd8f3 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators

/-- The actual full original homogeneous index has exactly these five
possible exponents, proved from the original vertex cone inequalities. -/
theorem blowupLatticePoint_cases (m : Fin 2 → ℤ)
    (hm : m ∈ latticePolytopeIntegerPoints blowupGenerator) :
    m = ![1, 0] ∨ m = ![2, 0] ∨ m = ![1, 1] ∨ m = ![0, 2] ∨ m = ![0, 1] := by
  have h00 := (blowup_isVertexConeBasis 0).coord_nonneg hm 0
  have h01 := (blowup_isVertexConeBasis 0).coord_nonneg hm 1
  have h20 := (blowup_isVertexConeBasis 2).coord_nonneg hm 0
  have h21 := (blowup_isVertexConeBasis 2).coord_nonneg hm 1
  simp [vertexConeCoord_integerCast, blowupBasis, lattice2Basis_repr, blowupGenerator]
    at h00 h01 h20 h21
  norm_cast at h00 h01 h20 h21
  simp only [Matrix.vecHead, Matrix.vecTail] at h00 h01 h20 h21
  dsimp only [Function.comp] at h00 h01 h20 h21
  change 0 ≤ m 0 - 1 + m 1 at h00
  change 0 ≤ m 1 at h01
  change ((m 0 + m 1 : ℤ) : ℝ) ≤ (2 : ℝ) at h20
  have hupper : m 0 + m 1 ≤ (2 : ℤ) := by exact_mod_cast h20
  have hcases : (m 0 = 1 ∧ m 1 = 0) ∨ (m 0 = 2 ∧ m 1 = 0) ∨
      (m 0 = 1 ∧ m 1 = 1) ∨ (m 0 = 0 ∧ m 1 = 2) ∨ (m 0 = 0 ∧ m 1 = 1) := by omega
  have heq (a b : ℤ) : (m 0 = a ∧ m 1 = b) ↔ m = ![a, b] := by
    constructor
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> simp [h0, h1]
    · intro h
      subst m
      simp
  simpa only [heq] using hcases

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The SAME original normalized homogeneous vector, retaining the full
internally manufactured lattice-point enumeration and its actual basis. -/
def blowupNativeChartVector (k : Fin 4) (z : Fin 2 → ℂ) :
    Fin (originalPolytopeFullIndexSize blowupGenerator + 1) → ℂ :=
  originalPolytopeNativeVector blowupGenerator hs (blowupVertex k)
    (fun j => z (blowupOriginalPermutation hs k j))

theorem blowupNativeChartVector_ne_zero (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupNativeChartVector hs k z ≠ 0 := originalPolytopeNativeVector_ne_zero _ _ _ _

/-- The SAME original chart point has exactly this original projective
representative, with no replacement of the model or object identity. -/
theorem blowupOriginalChartPoint_val (k : Fin 4) (z : Fin 2 → ℂ) :
    (blowupOriginalChartPoint hs k z).val =
      Projectivization.mk ℂ (blowupNativeChartVector hs k z)
        (blowupNativeChartVector_ne_zero hs k z) := by
  change ((originalPolytopeNativePiChart blowupGenerator hs (blowupVertex k)).symm
    (fun j => z (blowupOriginalPermutation hs k j))).val = _
  exact originalPolytopeNativePiChart_symm_val _ _ _ _

/-- Actual primitive basis ordering determines every full original
homogeneous coordinate, rather than only the four vertex coordinates. -/
theorem blowupNativeChartVector_ordered (k : Fin 4) (z : Fin 2 → ℂ)
    (i : Fin (originalPolytopeFullIndexSize blowupGenerator + 1)) :
    blowupNativeChartVector hs k z i = ∏ j : Fin 2,
      z j ^ ((blowupBasis k).repr
        (originalPolytopeFullExponents blowupGenerator i - blowupGenerator k) j).toNat := by
  have hv : originalPolytopeFullExponents blowupGenerator
      (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) = blowupGenerator k :=
    latticePolytopeExponentFamily_vertexIndex blowupGenerator
      (originalPolytopeFullEnumeration blowupGenerator) (blowupVertex k)
  unfold blowupNativeChartVector originalPolytopeNativeVector monomialVertexVector monomialVertexExponent
  rw [hv]
  simp only [basis_repr_eq_intPairing hs (blowupVertex k),
    polytopeToricRayGenerator_eq_vertexConeRay hs (blowupVertex k)
      (blowupOriginalPermutation_basis hs k), intPairing_vertexConeRay]
  exact Equiv.prod_comp (blowupOriginalPermutation hs k) (fun j : Fin 2 =>
    z j ^ ((blowupBasis k).repr
      (originalPolytopeFullExponents blowupGenerator i - blowupGenerator k) j).toNat)

/-- Bilinear reconstruction in the literal exponent-labelled original
homogeneous coordinates. It is independent of enumeration order. -/
def blowupReconstructionCoefficient (m : Fin 2 → ℤ) (X : Fin 3 → ℂ) (u : Fin 2 → ℂ) : ℂ :=
  if m = ![1, 0] then X 0 * u 0 else
  if m = ![2, 0] then X 1 * u 0 else
  if m = ![1, 1] then X 1 * u 1 else
  if m = ![0, 2] then X 2 * u 1 else X 0 * u 1

def blowupReconstructionVector (X : Fin 3 → ℂ) (u : Fin 2 → ℂ) :
    Fin (originalPolytopeFullIndexSize blowupGenerator + 1) → ℂ :=
  fun i => blowupReconstructionCoefficient (originalPolytopeFullExponents blowupGenerator i) X u

/-- Arbitrary independent homogeneous rescalings multiply ALL reconstructed
original coordinates by the same scalar, proved before projectivization. -/
theorem blowupReconstructionVector_smul (X : Fin 3 → ℂ) (u : Fin 2 → ℂ) (c d : ℂ) :
    blowupReconstructionVector (c • X) (d • u) = (c * d) • blowupReconstructionVector X u := by
  funext i
  change blowupReconstructionCoefficient (originalPolytopeFullExponents blowupGenerator i)
    (c • X) (d • u) = (c * d) *
      blowupReconstructionCoefficient (originalPolytopeFullExponents blowupGenerator i) X u
  unfold blowupReconstructionCoefficient
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring

/-- Both actual original projective maps reconstruct the FULL SAME original
normalized homogeneous vector in each whole original affine chart. -/
theorem blowupReconstructionVector_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupReconstructionVector (blowdownChartVector k z) (blowupDirectionChartVector k z) =
      blowupNativeChartVector hs k z := by
  funext i
  rw [blowupNativeChartVector_ordered]
  change blowupReconstructionCoefficient (originalPolytopeFullExponents blowupGenerator i)
    (blowdownChartVector k z) (blowupDirectionChartVector k z) = _
  have hm := blowupLatticePoint_cases (originalPolytopeFullExponents blowupGenerator i)
    (originalPolytopeFullExponents_mem i)
  rcases hm with h | h | h | h | h <;> rw [h] <;> fin_cases k <;>
    simp [blowupReconstructionCoefficient, blowdownChartVector, blowupDirectionChartVector,
      blowupBasis, blowupGenerator, lattice2Basis_repr, Fin.prod_univ_two] <;> ring

/-- Reconstruction from arbitrary chosen representatives of the actual
images differs from the SAME original representative by a nonzero scalar. -/
theorem blowupReconstructionVector_original_reps (k : Fin 4) (z : Fin 2 → ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧
      blowupReconstructionVector
        (originalBlowdown hs (blowupOriginalChartPoint hs k z)).rep
        (originalBlowupDirection hs (blowupOriginalChartPoint hs k z)).rep =
          c • blowupNativeChartVector hs k z := by
  obtain ⟨c, hc, hX⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (originalBlowdown hs (blowupOriginalChartPoint hs k z))
    (blowdownChartVector_ne_zero k z) (originalBlowdown_chart hs k z)
  obtain ⟨d, hd, hu⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (originalBlowupDirection hs (blowupOriginalChartPoint hs k z))
    (blowupDirectionChartVector_ne_zero k z) (originalBlowupDirection_chart hs k z)
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  rw [hX, hu, blowupReconstructionVector_smul, blowupReconstructionVector_chart]

/-- Equality of the literal incidence pair forces equality of actual
original projective points, retaining all boundary cases. -/
theorem originalBlowup_pair_injective {p q : PolytopeToricVariety blowupGenerator hs}
    (hπ : originalBlowdown hs p = originalBlowdown hs q)
    (hρ : originalBlowupDirection hs p = originalBlowupDirection hs q) : p = q := by
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  obtain ⟨l, w, rfl⟩ := blowupOriginalChartPoint_cover hs q
  obtain ⟨c, hc, hpc⟩ := blowupReconstructionVector_original_reps hs k z
  obtain ⟨d, hd, hqd⟩ := blowupReconstructionVector_original_reps hs l w
  have hvec : c • blowupNativeChartVector hs k z = d • blowupNativeChartVector hs l w := by
    rw [← hpc, ← hqd, hπ, hρ]
  apply Subtype.ext
  rw [blowupOriginalChartPoint_val, blowupOriginalChartPoint_val]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨c⁻¹ * d, ?_⟩
  have hcancel := congrArg (fun v => c⁻¹ • v) hvec
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hcancel.symm

/-- The actual map to the literal incidence variety is genuinely injective. -/
theorem originalBlowupIncidenceMap_injective :
    Function.Injective (originalBlowupIncidenceMap hs) := by
  intro p q h
  exact originalBlowup_pair_injective hs (congrArg (fun x => x.val.1) h)
    (congrArg (fun x => x.val.2) h)

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowupReconstructionDraft -/
end PointBlowupCanonicalFragment006

section PointBlowupCanonicalFragment007
/- BEGIN OriginalIncidenceHomeomorphDraft; original source SHA256 b4fc76e29f3f2176cd060d82088fc5a76003a9bca732a8942d86ee155d6f1f4c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual equivalence is manufactured from the two independently proved
pointwise geometry producers; no identification certificate is incoming. -/
def originalBlowupIncidenceEquiv : PolytopeToricVariety blowupGenerator hs ≃ blowupIncidenceSet :=
  Equiv.ofBijective (originalBlowupIncidenceMap hs)
    ⟨originalBlowupIncidenceMap_injective hs, originalBlowupIncidenceMap_surjective hs⟩

/-- Compactness and the unchanged Hausdorff subspace topology prove the
actual incidence identification is a genuine homeomorphism. -/
def originalBlowupIncidenceHomeomorph :
    PolytopeToricVariety blowupGenerator hs ≃ₜ blowupIncidenceSet :=
  Continuous.homeoOfEquivCompactToT2 (f := originalBlowupIncidenceEquiv hs)
    (continuous_originalBlowupIncidenceMap hs)

/-- The first component of the genuine identification is the actual global
holomorphic map previously produced from the H sections. -/
theorem originalBlowupIncidenceHomeomorph_projection (p : PolytopeToricVariety blowupGenerator hs) :
    (originalBlowupIncidenceHomeomorph hs p).val.1 = originalBlowdown hs p := rfl

theorem originalBlowupIncidenceHomeomorph_direction (p : PolytopeToricVariety blowupGenerator hs) :
    (originalBlowupIncidenceHomeomorph hs p).val.2 = originalBlowupDirection hs p := rfl

/-- The literal flag point in the actual σ1′ original chart. -/
def blowupOriginalFlagPoint : PolytopeToricVariety blowupGenerator hs :=
  blowupOriginalChartPoint hs 3 0

/-- The actual original strict-transform divisor and actual exceptional
fibre meet at precisely the source's flag point, with no extra point at
another original affine chart. -/
theorem originalStrictLine_inter_exceptional :
    toricPrimeDivisor (blowupStrictLineRay hs) ∩ toricPrimeDivisor (blowupExceptionalRay hs) =
      {blowupOriginalFlagPoint hs} := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
    rw [mem_inter_iff, strictLineRay_chart, exceptionalRay_chart] at hp
    change blowupOriginalChartPoint hs k z = blowupOriginalFlagPoint hs
    fin_cases k
    · exact hp.1.elim
    · exact hp.1.elim
    · exact hp.2.elim
    · apply congrArg (blowupOriginalChartPoint hs 3)
      funext i
      fin_cases i
      · exact hp.1
      · exact hp.2
  · intro p hp
    have hp' : p = blowupOriginalFlagPoint hs := hp
    subst p
    change blowupOriginalChartPoint hs 3 0 ∈ toricPrimeDivisor (blowupStrictLineRay hs) ∧
      blowupOriginalChartPoint hs 3 0 ∈ toricPrimeDivisor (blowupExceptionalRay hs)
    exact ⟨(strictLineRay_chart hs 3 0).mpr rfl, (exceptionalRay_chart hs 3 0).mpr rfl⟩

/-- The ACTUAL strict transform and ACTUAL exceptional fibre realize exactly
the source's singleton second flag member. -/
theorem originalSourceLine_flag_point :
    closure (originalSourceLineLift hs) ∩
      {p : PolytopeToricVariety blowupGenerator hs | originalBlowdown hs p = blowdownOrigin} =
        {blowupOriginalFlagPoint hs} := by
  rw [originalSourceLine_strictTransform, originalBlowdown_fibre_origin,
    originalStrictLine_inter_exceptional]

end SGPT.Toric.BlowdownDraft

end
/- END OriginalIncidenceHomeomorphDraft -/
end PointBlowupCanonicalFragment007

section PointBlowupCanonicalFragment008
/- BEGIN OriginalIncidenceNaturalOpensDraft; original source SHA256 cdee5eb61fa378789d9cefdc3288de6b47593ac6100a5d9bb8b4944d4f1ac938 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- The four literal classical incidence coordinate opens, in the order
of the ACTUAL original source vertices. -/
def incidenceProjectivePivot : Fin 4 → Fin 3 := ![0, 1, 2, 0]
def incidenceDirectionPivot : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def blowupIncidenceNaturalOpen (k : Fin 4) : Set blowupIncidenceSet :=
  {q | q.val.1.rep (incidenceProjectivePivot k) ≠ 0 ∧
    q.val.2.rep (incidenceDirectionPivot k) ≠ 0}

theorem isOpen_blowupIncidenceNaturalOpen (k : Fin 4) : IsOpen (blowupIncidenceNaturalOpen k) := by
  have heq : blowupIncidenceNaturalOpen k =
      (fun q : blowupIncidenceSet => q.val.1) ⁻¹'
        (SGPT.Projective.ComplexProjectiveSpace.affineChart (incidenceProjectivePivot k)).source ∩
      (fun q : blowupIncidenceSet => q.val.2) ⁻¹'
        (SGPT.Projective.ComplexProjectiveSpace.affineChart (incidenceDirectionPivot k)).source := by
    ext q
    simp only [blowupIncidenceNaturalOpen, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_source_iff]
  rw [heq]
  exact ((SGPT.Projective.ComplexProjectiveSpace.affineChart
    (incidenceProjectivePivot k)).open_source.preimage (continuous_fst.comp continuous_subtype_val)).inter
      ((SGPT.Projective.ComplexProjectiveSpace.affineChart
        (incidenceDirectionPivot k)).open_source.preimage (continuous_snd.comp continuous_subtype_val))

/-- The source vertex coordinate is the corresponding literal projective
incidence pivot product, in the SAME full original exponent enumeration. -/
theorem blowupReconstructionVector_vertex (k : Fin 4) (X : Fin 3 → ℂ) (u : Fin 2 → ℂ) :
    blowupReconstructionVector X u
      (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) =
        X (incidenceProjectivePivot k) * u (incidenceDirectionPivot k) := by
  have hv : originalPolytopeFullExponents blowupGenerator
      (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) = blowupGenerator k :=
    latticePolytopeExponentFamily_vertexIndex blowupGenerator
      (originalPolytopeFullEnumeration blowupGenerator) (blowupVertex k)
  change blowupReconstructionCoefficient
    (originalPolytopeFullExponents blowupGenerator
      (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k))) X u = _
  rw [hv]
  fin_cases k <;> simp [blowupReconstructionCoefficient, blowupGenerator,
    incidenceProjectivePivot, incidenceDirectionPivot]

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- EXACT identification of every original vertex source with the actual
standard incidence affine open. No target/source dictionary is incoming. -/
theorem originalChart_source_iff_incidenceOpen (k : Fin 4)
    (p : PolytopeToricVariety blowupGenerator hs) :
    p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source ↔
      originalBlowupIncidenceHomeomorph hs p ∈ blowupIncidenceNaturalOpen k := by
  obtain ⟨l, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  have hsource : blowupOriginalChartPoint hs l z ∈
      (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source ↔
        blowupNativeChartVector hs l z
          (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) ≠ 0 := by
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativePiChart_mem_source_iff blowupGenerator hs (blowupVertex k)
      (blowupOriginalChartPoint hs l z) (blowupNativeChartVector hs l z)
      (blowupNativeChartVector_ne_zero hs l z) (blowupOriginalChartPoint_val hs l z)
  rw [hsource]
  obtain ⟨c, hc, hR⟩ := blowupReconstructionVector_original_reps hs l z
  have hi := congrFun hR (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k))
  rw [blowupReconstructionVector_vertex] at hi
  change blowupNativeChartVector hs l z
      (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) ≠ 0 ↔
    (originalBlowdown hs (blowupOriginalChartPoint hs l z)).rep (incidenceProjectivePivot k) ≠ 0 ∧
    (originalBlowupDirection hs (blowupOriginalChartPoint hs l z)).rep (incidenceDirectionPivot k) ≠ 0
  change (originalBlowdown hs (blowupOriginalChartPoint hs l z)).rep (incidenceProjectivePivot k) *
      (originalBlowupDirection hs (blowupOriginalChartPoint hs l z)).rep (incidenceDirectionPivot k) =
        c * blowupNativeChartVector hs l z
          (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) at hi
  calc
    _ ↔ c * blowupNativeChartVector hs l z
        (originalPolytopeNativeVertexIndex blowupGenerator (blowupVertex k)) ≠ 0 := by simp [hc]
    _ ↔ (originalBlowdown hs (blowupOriginalChartPoint hs l z)).rep (incidenceProjectivePivot k) *
        (originalBlowupDirection hs (blowupOriginalChartPoint hs l z)).rep
          (incidenceDirectionPivot k) ≠ 0 := by rw [hi]
    _ ↔ _ := mul_ne_zero_iff

/-- The four actual classical incidence opens cover the actual incidence
set, derived from the original geometric cover and genuine surjectivity. -/
theorem blowupIncidenceNaturalOpen_cover (hs : latticePolytopeEdgeSmooth blowupGenerator)
    (q : blowupIncidenceSet) :
    ∃ k, q ∈ blowupIncidenceNaturalOpen k := by
  obtain ⟨p, rfl⟩ := (originalBlowupIncidenceHomeomorph hs).surjective q
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  exact ⟨k, (originalChart_source_iff_incidenceOpen hs k _).mp (blowupOriginalChartPoint_mem hs k z)⟩

/-- Genuine native charts on the LITERAL incidence subset with its unchanged
product-subspace topology. Their sources are identified with the explicit
classical affine opens below, rather than prescribed as a certificate. -/
def blowupIncidenceNativeChart (v : latticePolytopeVertices blowupGenerator) :
    OpenPartialHomeomorph blowupIncidenceSet (ComplexModel 2) :=
  (originalBlowupIncidenceHomeomorph hs).symm.toOpenPartialHomeomorph.trans
    (originalPolytopeNativeModelChart blowupGenerator hs v)

theorem blowupIncidenceNativeChart_target (v : latticePolytopeVertices blowupGenerator) :
    (blowupIncidenceNativeChart hs v).target = univ := by
  simp [blowupIncidenceNativeChart, originalPolytopeNativeModelChart_target]

/-- Every original vertex open is EXACTLY the natural incidence open. -/
theorem blowupIncidenceNativeChart_source (k : Fin 4) :
    (blowupIncidenceNativeChart hs (blowupVertex k)).source = blowupIncidenceNaturalOpen k := by
  ext q
  change (True ∧ (originalBlowupIncidenceHomeomorph hs).symm q ∈
    (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source) ↔ _
  simp only [true_and]
  have h := originalChart_source_iff_incidenceOpen hs k ((originalBlowupIncidenceHomeomorph hs).symm q)
  simpa only [Homeomorph.apply_symm_apply] using h

theorem blowupIncidenceNativeChart_cover (q : blowupIncidenceSet) :
    ∃ v, q ∈ (blowupIncidenceNativeChart hs v).source := by
  obtain ⟨k, hk⟩ := blowupIncidenceNaturalOpen_cover hs q
  exact ⟨blowupVertex k, by rwa [blowupIncidenceNativeChart_source]⟩

/-- Inverse charts have the ACTUAL original global maps as their literal
projective components; thus their affine formulas are already polynomial. -/
theorem blowupIncidenceNativeChart_symm (v : latticePolytopeVertices blowupGenerator)
    (z : ComplexModel 2) :
    (blowupIncidenceNativeChart hs v).symm z = originalBlowupIncidenceHomeomorph hs
      ((originalPolytopeNativeModelChart blowupGenerator hs v).symm z) := rfl

end SGPT.Toric.BlowdownDraft

end
/- END OriginalIncidenceNaturalOpensDraft -/
end PointBlowupCanonicalFragment008

section PointBlowupCanonicalFragment009
/- BEGIN OriginalIncidenceAnalyticManifoldDraft; original source SHA256 49c384d1672318ef6e58630c41896a163bc4a324c96fdc94096967e0bd496e8c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The ACTUAL literal incidence subset, in its unchanged subspace topology,
with precisely the whole-affine native vertex charts whose explicit natural
classical sources were derived in OriginalIncidenceNaturalOpensDraft. -/
@[instance_reducible]
def blowupIncidenceNativeChartedSpace : ChartedSpace (ComplexModel 2) blowupIncidenceSet where
  atlas := range (blowupIncidenceNativeChart hs)
  chartAt q := blowupIncidenceNativeChart hs (blowupIncidenceNativeChart_cover hs q).choose
  mem_chart_source q := (blowupIncidenceNativeChart_cover hs q).choose_spec
  chart_mem_atlas q := ⟨(blowupIncidenceNativeChart_cover hs q).choose, rfl⟩

/-- Literal source/target transitions coincide with the SAME original toric
transitions, because the genuine two inverse homeomorphisms cancel. -/
theorem blowupIncidenceNativeTransition_eq (v w : latticePolytopeVertices blowupGenerator) :
    (blowupIncidenceNativeChart hs v).symm.trans (blowupIncidenceNativeChart hs w) =
      originalPolytopeNativeModelTransition blowupGenerator hs v w := by
  ext z <;> simp [blowupIncidenceNativeChart, originalPolytopeNativeModelTransition]

/-- The natural classical incidence chart atlas gives a genuine complex
manifold, by the existing genuine original analytic overlap producer. -/
theorem blowupIncidenceNativeIsManifold (r : ℕ∞ω) :
    letI := blowupIncidenceNativeChartedSpace hs
    IsManifold 𝓘(ℂ, ComplexModel 2) r blowupIncidenceSet := by
  let := blowupIncidenceNativeChartedSpace hs
  apply isManifold_of_contDiffOn 𝓘(ℂ, ComplexModel 2) r blowupIncidenceSet
  intro e f he hf
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hf
  have h := contDiffOn_originalPolytopeNativeModelTransition blowupGenerator hs v w r
  rw [← blowupIncidenceNativeTransition_eq] at h
  simpa only [mfld_simps] using h

theorem blowupIncidenceNativeIsComplexManifold :
    letI := blowupIncidenceNativeChartedSpace hs
    IsComplexManifold 2 blowupIncidenceSet := by
  let := blowupIncidenceNativeChartedSpace hs
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := inferInstance
    toIsManifold := blowupIncidenceNativeIsManifold hs ∞ }

/-- The actual original identification is holomorphic in the genuine
literal incidence complex structure, proved in corresponding native charts. -/
theorem contMDiff_originalBlowupIncidenceHomeomorph :
    letI := blowupIncidenceNativeChartedSpace hs
    letI := blowupIncidenceNativeIsComplexManifold hs
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞
      (originalBlowupIncidenceHomeomorph hs) := by
  let := blowupIncidenceNativeChartedSpace hs
  let := blowupIncidenceNativeIsComplexManifold hs
  intro p
  let v := toricNativePreferredVertex blowupGenerator hs p
  let cs : OpenPartialHomeomorph (PolytopeToricVariety blowupGenerator hs) (ComplexModel 2) :=
    originalPolytopeNativeModelChart blowupGenerator hs v
  let ct := blowupIncidenceNativeChart hs v
  have hv : p ∈ cs.source := toricNativePreferredVertex_mem p
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ cs p :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := PolytopeToricVariety blowupGenerator hs)
        (show cs ∈ atlas (ComplexModel 2) (PolytopeToricVariety blowupGenerator hs) from ⟨v, rfl⟩)) hv
  have hct : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ ct.symm (cs p) :=
    (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := blowupIncidenceSet) (show ct ∈ atlas (ComplexModel 2) blowupIncidenceSet from ⟨v, rfl⟩))).contMDiffAt
          (by rw [blowupIncidenceNativeChart_target]; exact Filter.univ_mem)
  apply (hct.comp p hcs).congr_of_eventuallyEq
  filter_upwards [cs.open_source.mem_nhds hv] with q hq
  change originalBlowupIncidenceHomeomorph hs q =
    originalBlowupIncidenceHomeomorph hs (cs.symm (cs q))
  exact congrArg (originalBlowupIncidenceHomeomorph hs) (cs.left_inv hq).symm

/-- The genuine inverse identification is also holomorphic, retaining all
incidence boundary points and actual chart domains. -/
theorem contMDiff_originalBlowupIncidenceHomeomorph_symm :
    letI := blowupIncidenceNativeChartedSpace hs
    letI := blowupIncidenceNativeIsComplexManifold hs
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞
      (originalBlowupIncidenceHomeomorph hs).symm := by
  let := blowupIncidenceNativeChartedSpace hs
  let := blowupIncidenceNativeIsComplexManifold hs
  intro q
  obtain ⟨v, hv⟩ := blowupIncidenceNativeChart_cover hs q
  let cs : OpenPartialHomeomorph (PolytopeToricVariety blowupGenerator hs) (ComplexModel 2) :=
    originalPolytopeNativeModelChart blowupGenerator hs v
  let ct := blowupIncidenceNativeChart hs v
  have hct : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ ct q :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := blowupIncidenceSet) (show ct ∈ atlas (ComplexModel 2) blowupIncidenceSet from ⟨v, rfl⟩)) hv
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ cs.symm (ct q) :=
    (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := PolytopeToricVariety blowupGenerator hs)
        (show cs ∈ atlas (ComplexModel 2) (PolytopeToricVariety blowupGenerator hs) from ⟨v, rfl⟩))).contMDiffAt
          (by change cs.target ∈ 𝓝 (ct q)
              rw [show cs.target = univ from originalPolytopeNativeModelChart_target _ _ _]
              exact Filter.univ_mem)
  apply (hcs.comp q hct).congr_of_eventuallyEq
  filter_upwards [ct.open_source.mem_nhds hv] with u hu
  change (originalBlowupIncidenceHomeomorph hs).symm u = cs.symm (cs ((originalBlowupIncidenceHomeomorph hs).symm u))
  exact (cs.left_inv hu.2).symm

/-- The genuine literal incidence complex manifold maps holomorphically to
the ambient projective product through its ACTUAL subtype inclusion. -/
theorem contMDiff_blowupIncidence_inclusion :
    letI := blowupIncidenceNativeChartedSpace hs
    letI := blowupIncidenceNativeIsComplexManifold hs
    ContMDiff 𝓘(ℂ, ComplexModel 2) ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ComplexModel 1))) ∞
      (fun q : blowupIncidenceSet => q.val) := by
  let := blowupIncidenceNativeChartedSpace hs
  let := blowupIncidenceNativeIsComplexManifold hs
  have h := ((contMDiff_originalBlowdown hs).prodMk (contMDiff_originalBlowupDirection hs)).comp
    (contMDiff_originalBlowupIncidenceHomeomorph_symm hs)
  convert h using 1
  funext q
  exact (congrArg Subtype.val ((originalBlowupIncidenceHomeomorph hs).apply_symm_apply q)).symm

end SGPT.Toric.BlowdownDraft

end
/- END OriginalIncidenceAnalyticManifoldDraft -/
end PointBlowupCanonicalFragment009

section PointBlowupCanonicalFragment010
/- BEGIN OriginalIncidenceRatioChartsDraft; original source SHA256 10eb47156678caa0c13e09968af1046f5dc04b8a5c9fc41693c1e83325187922 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- Literal homogeneous coordinate ratio, well defined for arbitrary
projective representatives, even before restricting to its denominator open. -/
def projectiveCoordinateRatio {N : ℕ} (i j : Fin (N + 1))
    (p : SGPT.Projective.ComplexProjectiveSpace N) : ℂ := p.rep i / p.rep j

theorem projectiveCoordinateRatio_mk {N : ℕ} (i j : Fin (N + 1))
    (X : Fin (N + 1) → ℂ) (hX : X ≠ 0) :
    projectiveCoordinateRatio i j (SGPT.Projective.ComplexProjectiveSpace.mk X hX) = X i / X j := by
  obtain ⟨c, hc, hrep⟩ := SGPT.Projective.ComplexProjectiveSpace.rep_smul
    (SGPT.Projective.ComplexProjectiveSpace.mk X hX) hX rfl
  unfold projectiveCoordinateRatio
  rw [hrep]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

/-- The four LITERAL classical incidence coordinate functions. -/
def blowupIncidenceOrderedCoordinates (k : Fin 4) (q : blowupIncidenceSet) : Fin 2 → ℂ :=
  ![![projectiveCoordinateRatio 1 0 q.val.1, projectiveCoordinateRatio 1 0 q.val.2],
    ![projectiveCoordinateRatio 2 1 q.val.1, projectiveCoordinateRatio 0 1 q.val.1],
    ![projectiveCoordinateRatio 0 2 q.val.1, projectiveCoordinateRatio 1 2 q.val.1],
    ![projectiveCoordinateRatio 0 1 q.val.2, projectiveCoordinateRatio 2 0 q.val.1]] k

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The literal ratios invert the actual whole original parametrization;
this identifies the analytic meaning beyond a transported topology. -/
theorem blowupIncidenceOrderedCoordinates_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    blowupIncidenceOrderedCoordinates k
      (originalBlowupIncidenceHomeomorph hs (blowupOriginalChartPoint hs k z)) = z := by
  unfold blowupIncidenceOrderedCoordinates
  simp only [originalBlowupIncidenceHomeomorph_projection, originalBlowupIncidenceHomeomorph_direction,
    originalBlowdown_chart, originalBlowupDirection_chart, projectiveCoordinateRatio_mk]
  fin_cases k <;> funext j <;> fin_cases j <;>
    simp [blowdownChartVector, blowupDirectionChartVector]

/-- Every point of a specified actual original vertex source is produced
in that SAME original whole-affine chart. -/
theorem exists_blowupOriginalChartPoint_of_mem (k : Fin 4)
    (p : PolytopeToricVariety blowupGenerator hs)
    (hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source) :
    ∃ z, blowupOriginalChartPoint hs k z = p := by
  let z : Fin 2 → ℂ := fun j => originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p
    ((blowupOriginalPermutation hs k).symm j)
  refine ⟨z, ?_⟩
  have hc : blowupOriginalCoordinates hs k z =
      originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p := by
    ext j
    simp [blowupOriginalCoordinates, z, modelPoint_apply]
  unfold blowupOriginalChartPoint
  rw [hc]
  exact (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).left_inv hp

/-- On EVERY point of the actual natural incidence open, the inverse
native chart is the printed classical ratio formula, up to the internally
proved source basis permutation. No analytic model dictionary is supplied. -/
theorem blowupIncidenceNativeChart_coordinate (k : Fin 4)
    (q : blowupIncidenceSet) (hq : q ∈ blowupIncidenceNaturalOpen k) (j : Fin 2) :
    blowupIncidenceOrderedCoordinates k q j =
      blowupIncidenceNativeChart hs (blowupVertex k) q ((blowupOriginalPermutation hs k).symm j) := by
  let p := (originalBlowupIncidenceHomeomorph hs).symm q
  have hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source :=
    (originalChart_source_iff_incidenceOpen hs k p).mpr (by
      simpa only [p, Homeomorph.apply_symm_apply] using hq)
  obtain ⟨z, hz⟩ := exists_blowupOriginalChartPoint_of_mem hs k p hp
  have hqeq : q = originalBlowupIncidenceHomeomorph hs (blowupOriginalChartPoint hs k z) := by
    rw [hz]
    exact ((originalBlowupIncidenceHomeomorph hs).apply_symm_apply q).symm
  rw [hqeq, blowupIncidenceOrderedCoordinates_chart]
  change z j = originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)
    ((originalBlowupIncidenceHomeomorph hs).symm
      (originalBlowupIncidenceHomeomorph hs (blowupOriginalChartPoint hs k z)))
        ((blowupOriginalPermutation hs k).symm j)
  rw [Homeomorph.symm_apply_apply, blowupOriginalChartPoint_coordinate]
  simp [blowupOriginalCoordinates, modelPoint_apply]

/-- The ENTIRE actual native coordinate vector is the explicit ratio
vector in its derived native basis order. -/
theorem blowupIncidenceNativeChart_eq_ratios (k : Fin 4)
    (q : blowupIncidenceSet) (hq : q ∈ blowupIncidenceNaturalOpen k) :
    blowupIncidenceNativeChart hs (blowupVertex k) q =
      modelPoint (fun j => blowupIncidenceOrderedCoordinates k q (blowupOriginalPermutation hs k j)) := by
  ext j
  rw [modelPoint_apply, blowupIncidenceNativeChart_coordinate hs k q hq]
  simp only [Equiv.symm_apply_apply]

end SGPT.Toric.BlowdownDraft

end
/- END OriginalIncidenceRatioChartsDraft -/
end PointBlowupCanonicalFragment010

section PointBlowupCanonicalFragment011
/- BEGIN OriginalBlowdownCartierTransitionDraft; original source SHA256 66c4b73402f57164ee126d18be60e4d6c8d8439857d737b11055a2dfae28871f -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Native simplex realization of the actual projective target. -/
abbrev targetSimplexSmooth : latticePolytopeEdgeSmooth (simplexGenerator 2) := simplex_edgeSmooth

/-- The same actual blowdown, composed with the established genuine
biholomorphism from projective space to its original simplex toric model. -/
def originalBlowdownToSimplex : PolytopeToricVariety blowupGenerator hs →
    PolytopeToricVariety (simplexGenerator 2) targetSimplexSmooth :=
  (simplexProjectiveHomeomorph targetSimplexSmooth).symm ∘ originalBlowdown hs

theorem contMDiff_originalBlowdownToSimplex :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalBlowdownToSimplex hs) :=
  (contMDiff_simplexProjectiveHomeomorph_symm targetSimplexSmooth).comp
    (contMDiff_originalBlowdown hs)

/-- The target section indexing has the source character exponents exactly. -/
theorem simplexGenerator_finSucc_blowdown (i : Fin 3) :
    simplexGenerator 2 (finSuccEquiv 2 i) = blowdownExponent i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [finSuccEquiv_zero, simplexGenerator_none]
    funext j
    fin_cases j <;> simp [blowdownExponent]
  · rw [finSuccEquiv_succ, simplexGenerator_some]
    funext j
    fin_cases k <;> fin_cases j <;> simp [blowdownExponent]

/-- On the SAME original dense torus the actual map is literally the
identity into the simplex torus, proved by its genuine projective images. -/
theorem originalBlowdownToSimplex_torus (a : Fin 2 → ℂˣ) :
    originalBlowdownToSimplex hs (polytopeToricEmbedding blowupGenerator hs a) =
      polytopeToricEmbedding (simplexGenerator 2) targetSimplexSmooth a := by
  apply (simplexProjectiveHomeomorph targetSimplexSmooth).injective
  simp only [originalBlowdownToSimplex, Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [simplexProjectiveHomeomorph_embedding]
  unfold originalBlowdown
  rw [originalMonomialProjectiveMap_torus]
  congr 1
  funext i
  fin_cases i <;> simp [blowdownLatticePoint, blowdownExponent, latticeCharacter,
    Fin.prod_univ_two, Fin.cons] <;> rfl

/-- Every original source chart chooses its target hyperplane frame from
its already computed Cartier datum; no target-chart witness is supplied. -/
def blowdownFrameIndex (v : latticePolytopeVertices blowupGenerator) : Fin 3 :=
  (blowdownDatum_occurs hs v).choose

theorem blowdownFrameIndex_exponent (v : latticePolytopeVertices blowupGenerator) :
    blowdownExponent (blowdownFrameIndex hs v) = toricCartierDatum (blowupHyperplaneDivisor hs) v :=
  (blowdownDatum_occurs hs v).choose_spec

def blowdownTargetVertex (v : latticePolytopeVertices blowupGenerator) :
    latticePolytopeVertices (simplexGenerator 2) :=
  simplexVertex (finSuccEquiv 2 (blowdownFrameIndex hs v))

/-- The chosen target datum is EXACTLY the original H datum. -/
theorem blowdownTargetVertex_datum (v : latticePolytopeVertices blowupGenerator) :
    toricCartierDatum (simplexHyperplaneDivisor targetSimplexSmooth) (blowdownTargetVertex hs v) =
      toricCartierDatum (blowupHyperplaneDivisor hs) v := by
  rw [blowdownTargetVertex, toricCartierDatum_simplexHyperplaneDivisor,
    simplexGenerator_finSucc_blowdown, blowdownFrameIndex_exponent]

/-- The chosen homogeneous lift coordinate is constant one on the ENTIRE
original chart, so the actual image lies in the corresponding target open. -/
theorem blowdownFrameVector_index (v : latticePolytopeVertices blowupGenerator)
    (z : ComplexModel 2) :
    originalMonomialVector (blowupHyperplaneDivisor hs) (blowdownLatticePoint hs) v z
      (blowdownFrameIndex hs v) = 1 := by
  change toricMonomial _ v (blowdownExponent (blowdownFrameIndex hs v)) z = 1
  rw [blowdownFrameIndex_exponent]
  simp [toricMonomial]

theorem originalBlowdown_frame_rep_ne_zero (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source) :
    (originalBlowdown hs p).rep (blowdownFrameIndex hs v) ≠ 0 := by
  intro hz
  have hmap := originalMonomialProjectiveMap_eq_chart (blowupHyperplaneDivisor hs)
    (blowdownLatticePoint hs) (blowdownDatum_occurs hs) v hv
  change (originalMonomialProjectiveMap _ _ _ p).rep _ = 0 at hz
  rw [hmap] at hz
  have hzero := (projective_rep_mk_eq_zero_iff _ _ (blowdownFrameIndex hs v)).mp hz
  rw [blowdownFrameVector_index] at hzero
  exact one_ne_zero hzero

/-- Actual image membership in the selected ORIGINAL target simplex chart,
including all source boundary points. -/
theorem originalBlowdownToSimplex_mem_chart (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source) :
    originalBlowdownToSimplex hs p ∈
      (originalPolytopeNativeModelChart (simplexGenerator 2) targetSimplexSmooth
        (blowdownTargetVertex hs v)).source := by
  rw [mem_vertexChart_source_iff]
  have hn : (simplexProjectiveHomeomorph targetSimplexSmooth (originalBlowdownToSimplex hs p)).rep
      (blowdownFrameIndex hs v) ≠ 0 := by
    simpa only [originalBlowdownToSimplex, Function.comp_apply, Homeomorph.apply_symm_apply] using
      originalBlowdown_frame_rep_ne_zero hs v hv
  have hc := (not_congr (simplexProjectiveHomeomorph_rep_eq_zero_iff targetSimplexSmooth
    (originalBlowdownToSimplex hs p) (blowdownFrameIndex hs v))).mp hn
  simpa only [blowdownTargetVertex, simplex_vertexIndex, simplexHomogeneousIndex_apply] using hc

/-- The ACTUAL Cartier cocycle of O(H) is the ACTUAL pullback of the genuine
native simplex hyperplane cocycle on every entire original chart overlap.
The proof uses literal torus identity and genuine original density. -/
theorem originalBlowdown_cartierTransition (v w : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs w).source) :
    toricCartierTransition (blowupHyperplaneDivisor hs) v w p =
      toricCartierTransition (simplexHyperplaneDivisor targetSimplexSmooth)
        (blowdownTargetVertex hs v) (blowdownTargetVertex hs w) (originalBlowdownToSimplex hs p) := by
  let U := (originalPolytopeNativeModelChart blowupGenerator hs v).source ∩
    (originalPolytopeNativeModelChart blowupGenerator hs w).source
  have hU : IsOpen U := (originalPolytopeNativeModelChart blowupGenerator hs v).open_source.inter
    (originalPolytopeNativeModelChart blowupGenerator hs w).open_source
  have hf : ContinuousOn (toricCartierTransition (blowupHyperplaneDivisor hs) v w) U :=
    continuousOn_toricCartierTransition _ _ _
  have hg : ContinuousOn
      (fun q => toricCartierTransition (simplexHyperplaneDivisor targetSimplexSmooth)
        (blowdownTargetVertex hs v) (blowdownTargetVertex hs w) (originalBlowdownToSimplex hs q)) U :=
    (continuousOn_toricCartierTransition _ _ _).comp
      (contMDiff_originalBlowdownToSimplex hs).continuous.continuousOn (fun q hq =>
        ⟨originalBlowdownToSimplex_mem_chart hs v hq.1,
          originalBlowdownToSimplex_mem_chart hs w hq.2⟩)
  have h := toricCartier_eqOn_of_denseTorus U hU _ _ hf hg (by
    intro a _
    rw [originalBlowdownToSimplex_torus, toricCartierTransition_embedding,
      toricCartierTransition_embedding, blowdownTargetVertex_datum, blowdownTargetVertex_datum])
  exact h ⟨hv, hw⟩

end SGPT.Toric.BlowdownDraft

end
/- END OriginalBlowdownCartierTransitionDraft -/
end PointBlowupCanonicalFragment011


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden flat/private provider in proper toric point-blowup module: {m}"
