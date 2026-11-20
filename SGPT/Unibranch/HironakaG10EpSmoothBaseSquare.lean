import SGPT.Unibranch.HironakaG10EpChowBridge
import SGPT.Unibranch.HironakaG10EpBimeromorphicCancel
import SGPT.Unibranch.OriginalCommonResolutionGeneral
import SGPT.Unibranch.OriginalIntrinsicSingularLocus

/-!
# G10-05-03: the resolution base-change square of the singular-base reduction

Run 0081 lane G10EP (plan item G10-05-03).  Blueprint: `hironaka-g10ep-chow-bridge.tex`.

For a proper bimeromorphic `f : Y ⟶ X` onto a compact reduced complex space, the G11 resolution
`τ : X₁ ⟶ X` (finitely many blowups with smooth centres in the singular loci) is base-changed to a
proper bimeromorphic `p₁ : Y₁ ⟶ X₁` from a compact SMOOTH space, with `q₁ : Y₁ ⟶ Y` and the
commutative square `q₁ ≫ f = p₁ ≫ τ` (`exists_resolution_square`).  The dense good open is
`U = X \ (T ∪ Sing X)` (`T` the bad set of `f`), over which `f`, `τ` and the resolution of `Y`
composed with `f` are isomorphisms.  The square is the resolved strict transform: `Y` is resolved
by G11, the composite with `f` is proper bimeromorphic (`isProperBimeromorphic_comp_resolution`,
using that `f` is a local isomorphism over `X \ T`, so singular points of `Y` off `f⁻¹T` map to
singular points of `X`), and a compact smooth common model over `X` is taken
(`OriginalCommonResolutionGeneral`).

Consequence (the singular-base reduction): the general Chow lemma is equivalent to its case of
compact smooth bases and smooth sources (`hironakaChowLemmaGeneral_iff_smooth`).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10EpSmoothBaseSquare

open SGPT.Foundations.Analysis.Pending HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification HironakaG10ChowTowerDomination
  HironakaG10GenStatement HironakaG10GenChow HironakaG11SingularCentreModification
  OriginalIntrinsicSingularLocus HironakaG10EpBimeromorphicCancel

noncomputable section

/-- The good set of a proper bimeromorphic map: off its bad set `T` and off the singular locus of
the base. -/
def resolutionGoodOpen {X : SourceReducedComplexSpace} (T : Set X.obj.left) : Set X.obj.left :=
  (T ∪ intrinsicSingularLocus X.obj)ᶜ

/-- **The composite with a resolution of the source is proper bimeromorphic.**  Let `f : Y ⟶ X` be
proper bimeromorphic and `ν : Y' ⟶ Y` proper, an isomorphism over the regular locus of `Y`, with
thin preimage of the singular locus.  Then `ν ≫ f` is proper bimeromorphic, an isomorphism over
`X \ (T ∪ Sing X)` for every bad set `T` of `f`. -/
theorem isProperBimeromorphic_comp_resolution {X Y Y' : SourceReducedComplexSpace}
    {f : Y ⟶ X} (hf : IsProperBimeromorphic f) {ν : Y' ⟶ Y}
    (hνp : IsProperMap ν.hom.left.base) (hν : IsIsoOver ν (intrinsicRegularLocus Y.obj))
    (hνthin : interior (ν.hom.left.base ⁻¹' intrinsicSingularLocus Y.obj) = ∅) :
    IsProperBimeromorphic (ν ≫ f) := by
  have hfo := isOpenOffThin_of_isProperBimeromorphic hf
  have hνo : IsOpenOffThin ν.hom.left.base := isOpenOffThin_of_isIsoOver hν hνthin
  obtain ⟨hfp, T, hTa, hTi, -, hfT⟩ := hf
  have hTc : IsClosed T := isClosed_of_isIsoOver hfT
  have hSc : IsClosed (intrinsicSingularLocus X.obj) :=
    (isAnalyticSubset_intrinsicSingularLocus X).isClosed
  have hAo : IsOpen (resolutionGoodOpen T) := (hTc.union hSc).isOpen_compl
  have hthin : interior (T ∪ intrinsicSingularLocus X.obj) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hTc
      (interior_intrinsicSingularLocus_eq_empty X), hTi]
  have hfU : IsIsoOver f (resolutionGoodOpen T) :=
    IsIsoOver.of_isOpen_subset hfT hAo (fun x hx h => hx (Or.inl h))
  have hreg : f.hom.left.base ⁻¹' resolutionGoodOpen T ⊆ intrinsicRegularLocus Y.obj := by
    intro y hy
    have hyT : f.hom.left.base y ∈ Tᶜ := fun h => hy (Or.inl h)
    refine (IsIsoOver.mem_intrinsicRegularLocus_iff hfT hyT).mpr ?_
    by_contra h
    exact hy (Or.inr h)
  have hνU : IsIsoOver ν (f.hom.left.base ⁻¹' resolutionGoodOpen T) :=
    IsIsoOver.of_isOpen_subset hν (hAo.preimage f.hom.left.base.hom.continuous) hreg
  refine ⟨hfp.comp hνp, T ∪ intrinsicSingularLocus X.obj,
    HironakaG10SourceCSet.analytic_union hTa (isAnalyticSubset_intrinsicSingularLocus X),
    hthin, ?_, IsIsoOver.comp hfU hνU⟩
  have hcomp : IsOpenOffThin (ν ≫ f).hom.left.base := by
    show IsOpenOffThin (f.hom.left.base ∘ ν.hom.left.base)
    exact hνo.comp ν.hom.left.base.hom.continuous hfo
  exact hcomp.interior_preimage_eq_empty hthin

/-- **The resolution base-change square.**  For a proper bimeromorphic `f : Y ⟶ X` onto a compact
reduced complex space there are the G11 resolution `τ : X₁ ⟶ X` (singular-centre modification,
smooth compact source), a proper bimeromorphic `p₁ : Y₁ ⟶ X₁` from a compact smooth space and
`q₁ : Y₁ ⟶ Y` with `q₁ ≫ f = p₁ ≫ τ`; moreover `f` and `τ` are isomorphisms over the dense open
`X \ (T ∪ Sing X)` for a bad set `T` of `f`. -/
theorem exists_resolution_square {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hX : CompactSpace X.obj.left) (hf : IsProperBimeromorphic f) :
    ∃ (X₁ Y₁ : SourceReducedComplexSpace) (τ : X₁ ⟶ X) (p₁ : Y₁ ⟶ X₁) (q₁ : Y₁ ⟶ Y),
      IsSingularCentreModification τ ∧ IsModification τ ∧ X₁.IsSmooth ∧
      CompactSpace X₁.obj.left ∧ Y₁.IsSmooth ∧ CompactSpace Y₁.obj.left ∧
      IsProperBimeromorphic p₁ ∧ q₁ ≫ f = p₁ ≫ τ ∧
      ∃ T : Set X.obj.left, IsOpen (resolutionGoodOpen T) ∧ Dense (resolutionGoodOpen T) ∧
        IsIsoOver f (resolutionGoodOpen T) ∧ IsIsoOver τ (resolutionGoodOpen T) := by
  have := hX
  have hYc : CompactSpace Y.obj.left := by
    have hc : IsCompact (univ : Set Y.obj.left) := by
      simpa only [preimage_univ] using hf.1.isCompact_preimage
        (isCompact_univ : IsCompact (univ : Set X.obj.left))
    exact isCompact_univ_iff.mp hc
  obtain ⟨X₁, τ, hτs, hτm, hX₁, ⟨-, hτpb⟩, -, -, hτiso, -, -, hX₁c⟩ :=
    HironakaG11PresUnconditional.exists_endpoint X hX
  obtain ⟨Y', ν, -, -, hY', -, -, hνp, hνiso, -, hνthin, -⟩ :=
    HironakaG11PresUnconditional.exists_endpoint Y hYc
  have hνf : IsProperBimeromorphic (ν ≫ f) :=
    isProperBimeromorphic_comp_resolution hf hνp hνiso hνthin
  obtain ⟨Y₁, hY₁c, hY₁, A, B, -, hB, hAB⟩ :=
    OriginalCommonResolutionGeneral.exists_common_model_of_isProperBimeromorphic
      hY' hX₁ (ν ≫ f) τ hνf hτpb
  have hfT := hf
  obtain ⟨-, T, hTa, hTi, -, hfT'⟩ := hfT
  have hTc : IsClosed T := isClosed_of_isIsoOver hfT'
  have hSc : IsClosed (intrinsicSingularLocus X.obj) :=
    (isAnalyticSubset_intrinsicSingularLocus X).isClosed
  have hthin : interior (T ∪ intrinsicSingularLocus X.obj) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hTc
      (interior_intrinsicSingularLocus_eq_empty X), hTi]
  have hAo : IsOpen (resolutionGoodOpen T) := (hTc.union hSc).isOpen_compl
  refine ⟨X₁, Y₁, τ, B, A ≫ ν, hτs, hτm, hX₁, hX₁c hX, hY₁, hY₁c, hB, ?_, T, hAo,
    interior_eq_empty_iff_dense_compl.mp hthin,
    IsIsoOver.of_isOpen_subset hfT' hAo (fun x hx h => hx (Or.inl h)),
    IsIsoOver.of_isOpen_subset hτiso hAo (fun x hx => by
      by_contra h
      exact hx (Or.inr h))⟩
  rw [Category.assoc, hAB]

/-! ### The singular-base reduction of the Chow lemma -/

/-- The Chow lemma for compact SMOOTH bases and SMOOTH sources (a special case of
`HironakaChowLemmaGeneral`, equivalent to it by `hironakaChowLemmaGeneral_iff_smooth`). -/
def HironakaChowLemmaSmooth : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X), CompactSpace X.obj.left → X.IsSmooth →
    Y.IsSmooth → IsProperBimeromorphic f → IsDominatedByModification f

/-- **Singular-base reduction.**  The Chow lemma over compact smooth bases with smooth sources
implies the general Chow lemma: base-change along the G11 resolution. -/
theorem hironakaChowLemmaGeneral_of_smooth (H : HironakaChowLemmaSmooth) :
    HironakaChowLemmaGeneral := by
  intro X Y f hX hf
  obtain ⟨X₁, Y₁, τ, p₁, q₁, -, hτm, hX₁, hX₁c, hY₁, -, hp₁, hsq, -⟩ :=
    exists_resolution_square f hX hf
  obtain ⟨X₂, ρ, g, hρ, hg⟩ := H X₁ Y₁ p₁ hX₁c hX₁ hY₁ hp₁
  refine isDominatedByModification_of_comp (g ≫ q₁) hτm hρ ?_
  rw [Category.assoc, hsq, ← Category.assoc, hg]

/-- The general Chow lemma is equivalent to its smooth-base smooth-source case. -/
theorem hironakaChowLemmaGeneral_iff_smooth :
    HironakaChowLemmaGeneral ↔ HironakaChowLemmaSmooth :=
  ⟨fun H X Y f hX _ _ hf => H X Y f hX hf, hironakaChowLemmaGeneral_of_smooth⟩

end

end SGPT.Unibranch.HironakaG10EpSmoothBaseSquare
