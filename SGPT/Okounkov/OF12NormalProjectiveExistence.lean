import SGPT.Okounkov.OF12ResolutionAssembly
import SGPT.Okounkov.OF12SmoothProjectiveBirationalModel
import SGPT.Okounkov.OF12AlgebraicExceptionalTrace
import SGPT.Unibranch.UnibAnProjectiveAnalyticTrace
import SGPT.BDivisor.BD7Birational

/-! A normal projective variety admits a resolution with the actual analytic projection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace Topology
open SGPT.BDivisor.GM
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

/-- The analytification of the original integral projective scheme is connected. -/
theorem connectedSpace_projective_analytification (E : ClosedProjectiveEmbedding f) :
    ConnectedSpace (UnibAn.analytification f).obj.left := by
  let N := E.ambientDimension
  let p := polynomialProjStructureMap ℂ N
  let I := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint.identityEmbedding N
  let : IsSeparated p := I.isSeparated
  let : QuasiCompact p := I.quasiCompact
  let : LocallyOfFiniteType p := I.locallyOfFiniteType
  let : TopologicalSpace (SchemeComplexPoint p) := schemeAnalyticPointTopology p
  let : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : CompactSpace (UnibAn.analytification f).obj.left := (UnibAn.pointHomeomorph f).symm.compactSpace
  let F : UnibAn.analytification f ⟶ UnibAn.analytification p :=
    UnibAn.analytificationMorphism E.map E.over_base
  let j : (UnibAn.analytification f).obj.left → SGPT.Projective.ComplexProjectiveSpace N :=
    originalProjectiveHomeomorph N ∘ UnibAn.pointMap p ∘ F.hom.left.base
  have hj : j = ambientPoint E ∘ UnibAn.pointMap f := by
    funext x
    exact congrArg (originalProjectiveHomeomorph N)
      (UnibAn.pointMap_analytificationMorphism E.map E.over_base x)
  have hcont : Continuous j :=
    (originalProjectiveHomeomorph N).continuous.comp
      ((UnibAn.pointHomeomorph p).continuous.comp F.hom.left.base.hom.continuous)
  have hinj : Function.Injective j := by
    rw [hj]
    exact (ambientPoint_injective E).comp UnibAn.pointMap_injective
  have hRange : range j = range (ambientPoint E) := by
    rw [hj, range_comp, (UnibAn.pointMap_surjective (f := f)).range_eq, image_univ]
  let J := (hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hRange)
  have hrange := analyticallyIrreducible_ambientPoint_range E
  let : ConnectedSpace (range (ambientPoint E)) := Subtype.connectedSpace
    ⟨hrange.nonempty, CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible hrange⟩
  exact J.symm.surjective.connectedSpace J.symm.continuous

/-- The literal trace of a proper closed algebraic subset is thin on a normal projective
analytification. The trace is analytic by pullback from ordinary projective space. -/
theorem projective_algebraicTrace_isAnalyticSubset_and_thin
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (Z : Set X) (hZ : IsClosed Z) (hproper : Z ≠ univ) :
    let T := (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z
    (UnibAn.analytification f).IsAnalyticSubset T ∧ interior T = ∅ := by
  let T := (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z
  have ht : (UnibAn.analytification f).IsAnalyticSubset T :=
    UnibAn.isAnalyticSubset_projective_algebraicTrace f E Z hZ
  let := connectedSpace_projective_analytification f E
  have hTproper : T ≠ univ := by
    intro h
    apply hproper
    have hsub : range (schemeComplexPointImage f) ⊆ Z := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨x, hx⟩ := UnibAn.pointMap_surjective q
      have hxT : x ∈ T := h.symm ▸ mem_univ x
      change schemeComplexPointImage f (UnibAn.pointMap f x) ∈ Z at hxT
      simpa only [hx] using hxT
    exact Set.eq_univ_of_univ_subset fun x _ =>
      closure_minimal hsub hZ (OF14.dense_range_schemeComplexPointImage f x)
  exact ⟨ht, interior_eq_empty_of_proper_analyticSubset
    (isUnibranch_analytification_of_normal f hX) ht hTproper⟩

/-- A normal integral projective complex scheme of positive function-field dimension
has an OF12 resolution with its actual analytification and stalk-compatible field pullback. -/
theorem nonempty_resolution_of_normalProjective
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (m : ℕ)
    (hdim : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ)) :
    Nonempty (Resolution f m) := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨Y, hY, ρ, hproper, n, hsm, EY, hn, hbir, _, _⟩ :=
    exists_smooth_projective_birational_model E
  have hnm : n = m + 1 := by exact_mod_cast hn.symm.trans hdim
  subst n
  let := hY
  let := hsm
  let := hproper
  let := hbir
  let := EY.isSeparated
  let := EY.locallyOfFiniteType
  let : IsSeparated ρ := IsSeparated.of_comp (f := ρ) (g := f)
  let : LocallyOfFiniteType ρ := locallyOfFiniteType_of_comp ρ f
  obtain ⟨U, hU, hUiso⟩ := SGPT.BDivisor.BD7.exists_isIso_morphismRestrict_of_isIso_stalkMap ρ
  let : Nonempty U := hU.to_subtype
  let := hUiso
  have hnot : (U : Set X)ᶜ ≠ univ := by
    obtain ⟨x, hx⟩ := hU
    intro h
    exact (show x ∈ (U : Set X)ᶜ from h.symm ▸ mem_univ x) hx
  obtain ⟨hZ, hthin⟩ := projective_algebraicTrace_isAnalyticSubset_and_thin f E hX (U : Set X)ᶜ
    U.isOpen.isClosed_compl hnot
  exact nonempty_resolution_of_projective_model_and_isIso_restrict ρ EY U hZ hthin

end SGPT.Okounkov.OF12
