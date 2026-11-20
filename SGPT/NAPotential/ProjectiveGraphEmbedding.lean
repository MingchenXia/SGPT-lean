import SGPT.NAPotential.ProjectiveGraphQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The actual closed projective graph quotient

The generic quotient-Proj construction below is reused, with namespace relocation,
from active the homogeneous quotient construction. It is retained
locally to avoid the EP-to-SGPT dependency cycle. All imports are Mathlib or this
lane's checked graph sources; no EP proof artifact or resolution input is used.

Blueprint: `projective-graph-embedding.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
noncomputable section
universe u
namespace SGPT.NAPotential.AlgPrimes3.GradedGraphQuotient
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- Same-degree quotient lifts make the actual homogeneous away-ring map surjective. -/
theorem awayMap_surjective {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map (gradedMk 𝒜 J.toIdeal) s) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := z.mk_surjective _ ((gradedMk 𝒜 J.toIdeal).map_mem hs)
  obtain ⟨b, hb⟩ := componentMap_surjective 𝒜 J.toIdeal (n • d) ⟨a, ha⟩
  refine ⟨Away.mk 𝒜 hs n b b.2, ?_⟩
  have he : (gradedMk 𝒜 J.toIdeal) b = a := congrArg Subtype.val hb
  simp only [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, he]
  rfl

/-- The actual scheme morphism from the genuinely graded original ideal quotient. -/
def quotientSchemeMap : Proj (grading 𝒜 J.toIdeal) ⟶ Proj 𝒜 :=
  Proj.map (gradedMk 𝒜 J.toIdeal) (irrelevant_le_map 𝒜 J)

/-- The whole quotient chart square is a genuine scheme pullback. -/
theorem isPullback_awayMap {d : ℕ} {s : A} (hd : 0 < d) (hs : s ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedMk 𝒜 J.toIdeal) s)))
      (Proj.awayι (grading 𝒜 J.toIdeal) ((gradedMk 𝒜 J.toIdeal) s)
        ((gradedMk 𝒜 J.toIdeal).map_mem hs) hd)
      (Proj.awayι 𝒜 s hs hd) (quotientSchemeMap 𝒜 J) := by
  apply IsOpenImmersion.isPullback
  · exact (Proj.awayι_comp_map (gradedMk 𝒜 J.toIdeal) (irrelevant_le_map 𝒜 J) hd s hs)
  · simp only [Proj.opensRange_awayι, quotientSchemeMap, Proj.map_preimage_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/-- The actual projective scheme map of the original homogeneous quotient is a closed immersion. -/
instance instIsClosedImmersion_quotientSchemeMap : IsClosedImmersion (quotientSchemeMap 𝒜 J) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (Proj.affineOpenCover 𝒜).openCover]
  intro s
  change IsClosedImmersion (Limits.pullback.snd (quotientSchemeMap 𝒜 J)
    (Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2))
  let sq := isPullback_awayMap 𝒜 J s.1.2 s.2.2
  erw [← sq.flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  exact IsClosedImmersion.spec_of_surjective _ (awayMap_surjective 𝒜 J s.2.2)

/-- A genuine relevant homogeneous prime containing the original ideal gives an actual quotient projective point. -/
def quotientPoint (p : ProjectiveSpectrum 𝒜) (hJ : J ≤ p.asHomogeneousIdeal) :
    ProjectiveSpectrum (grading 𝒜 J.toIdeal) where
  asHomogeneousIdeal := p.asHomogeneousIdeal.map (gradedMk 𝒜 J.toIdeal)
  isPrime := by
    exact Ideal.isPrime_map_quotientMk_of_isPrime hJ
  not_irrelevant_le h := by
    apply p.not_irrelevant_le
    have he : (p.asHomogeneousIdeal.map (gradedMk 𝒜 J.toIdeal)).comap (gradedMk 𝒜 J.toIdeal) =
        p.asHomogeneousIdeal := HomogeneousIdeal.ext (Ideal.comap_map_mk hJ)
    rw [← he]
    apply HomogeneousIdeal.le_comap_of_map_le
    rw [map_irrelevant]
    exact h

/-- The actual quotient prime maps back to the entire original projective prime. -/
theorem quotientSchemeMap_quotientPoint (p : ProjectiveSpectrum 𝒜) (hJ : J ≤ p.asHomogeneousIdeal) :
    quotientSchemeMap 𝒜 J (quotientPoint 𝒜 J p hJ) = p := by
  apply ProjectiveSpectrum.ext
  exact HomogeneousIdeal.ext (Ideal.comap_map_mk hJ)

/-- The true scheme image of the projective homogeneous quotient is exactly the original homogeneous vanishing locus. -/
theorem range_quotientSchemeMap :
    Set.range (quotientSchemeMap 𝒜 J) = ProjectiveSpectrum.zeroLocus 𝒜 (J.toIdeal : Set A) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    intro a ha
    change Ideal.Quotient.mk J.toIdeal a ∈ q.asHomogeneousIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.asHomogeneousIdeal.zero_mem
  · intro hp
    exact ⟨quotientPoint 𝒜 J p hp, quotientSchemeMap_quotientPoint 𝒜 J p hp⟩

end SGPT.NAPotential.AlgPrimes3.GradedGraphQuotient

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphEmbedding

open MvPolynomial ProjectiveGraphRelations ProjectiveGraphQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ A K : Type u} [CommRing A] [CommRing K] [Algebra A K]

/-- The actual closed graph inclusion into native relative polynomial Proj. -/
def graphInclusion (b : σ → K) :
    graphScheme (A := A) b ⟶ Proj (homogeneousSubmodule (Option σ) A) :=
  GradedGraphQuotient.quotientSchemeMap (homogeneousSubmodule (Option σ) A) (relationIdeal b)

instance graphInclusion_isClosedImmersion (b : σ → K) :
    IsClosedImmersion (graphInclusion (A := A) b) := by
  dsimp only [graphInclusion]
  exact GradedGraphQuotient.instIsClosedImmersion_quotientSchemeMap
    (homogeneousSubmodule (Option σ) A) (relationIdeal b)

/-- The graph is the genuine whole-relation projective zero locus. -/
theorem range_graphInclusion (b : σ → K) :
    Set.range (graphInclusion (A := A) b) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) A)
        (graphRelationIdeal (A := A) b : Set (MvPolynomial (Option σ) A)) :=
  GradedGraphQuotient.range_quotientSchemeMap (homogeneousSubmodule (Option σ) A) (relationIdeal b)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphEmbedding
