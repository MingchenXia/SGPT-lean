import SGPT.Unibranch.KS3KahlerManifold
import SGPT.Unibranch.KSDimension
import SGPT.Unibranch.HironakaG11PresUnconditional
import SGPT.Unibranch.HironakaG1NoncompactSmoothComponentModel
import SGPT.Unibranch.ComplexSpaceUnibranchFibers
import SGPT.Unibranch.OriginalBimeromorphicSourceIso

/-!
# Kähler resolutions of compact Kähler spaces

Lane KS3.  `def:unibranch:L212` (`appendix_unibranch.tex`, `sec:unib_ext`) is stated on an
irreducible unibranch compact Kähler space `X`; its well-definedness (lane KS,
`KSUnibranchIEnvelope.existsUnique_isUnibranchIEnvelope`) uses a resolution of `X` by a connected
compact Kähler *manifold* (`KSUnibranchIEnvelope.KahlerResolution`).  This file produces such a
resolution from

* the compact resolution of `G11` (`HironakaG11PresUnconditional.exists_endpoint`): a finite
  sequence of blowups `p : Y → X` with smooth centres (`IsSingularCentreModification`), `Y`
  smooth and compact, `p` proper bimeromorphic;
* Kähler preservation along one blowup with smooth centre of a compact Kähler space
  (`KahlerBlowupStep`; "the blowup of a compact Kähler space along a smooth closed subspace is
  Kähler", `π^*ω + ε·Θ`);
* connectedness of `Y` (`connectedSpace_of_isProperBimeromorphic`: `X` connected and unibranch,
  fibres of `p` connected by Zariski's main theorem `thm:Zariskimain`);
* the manifold model of a connected smooth complex space
  (`HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model`) and the
  transport of the Kähler form to it (`KS3KahlerManifold.kahlerBackgroundOfIso`).

Main results: `isKahlerSpace_of_isModification`, `exists_kahlerResolution_of_kahlerBlowupStep`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.BlowupTowers (CMfd)

namespace SGPT.Unibranch.KS3KahlerResolution

open SourceReducedComplexSpace OriginalNativeModification SmoothCentreModification
  KSUnibranchIEnvelope HironakaG11SingularCentreModification

/-- **Kähler preservation under a blowup with smooth centre.**  For every blowup `p : Y → X` of a
compact Kähler space `X` along a smooth closed subspace (`IsSmoothCentreBlowup p i`), `Y` is a
Kähler space.  (Classical: `p^*ω + ε Θ`, `Θ` the curvature of a hermitian metric on
`𝒪_Y(-E)`; the manifold case is `SGPT.Foundations.Analysis.Pending.BlowupKahler`.) -/
def KahlerBlowupStep : Prop :=
  ∀ {X Y S : SourceReducedComplexSpace} (p : Y ⟶ X) (i : S ⟶ X), IsSmoothCentreBlowup p i →
    CompactSpace X.obj.left → X.IsKahlerSpace → Y.IsKahlerSpace

/-- Kähler preservation along finite compositions of smooth-centre blowups. -/
theorem isKahlerSpace_of_isModification (hstep : KahlerBlowupStep) :
    ∀ {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}, IsModification p →
      CompactSpace X.obj.left → X.IsKahlerSpace → Y.IsKahlerSpace := by
  intro X Y p hp
  induction hp with
  | id => exact fun _ h => h
  | cons f g hf hg ih =>
    intro hc hK
    have hY := ih hc hK
    have hcY := hg.source_compact
    obtain ⟨S, i, hi⟩ := hf
    exact hstep f i hi hcY hY

private theorem surjective_of_isProperBimeromorphic {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsProperBimeromorphic p) : Function.Surjective p.hom.left.base := by
  obtain ⟨hprop, Z, _hZa, hZt, _hpre, V, j, _hj, _hjr, _hjp, hjpr⟩ := hp
  have hclosed : IsClosed (range p.hom.left.base) := hprop.isClosedMap.isClosed_range
  have hsub : Zᶜ ⊆ range p.hom.left.base := by
    rw [← hjpr]
    rintro _ ⟨v, rfl⟩
    exact ⟨j.base v, rfl⟩
  have hdense : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp hZt
  have h := (hdense.mono hsub).closure_eq
  rw [hclosed.closure_eq] at h
  exact range_eq_univ.mp h

/-- **Connectedness of a resolution.**  A proper bimeromorphic morphism onto a connected
unibranch complex space has a connected source (its fibres are connected by Zariski's main
theorem, and a proper surjection is a quotient map). -/
theorem connectedSpace_of_isProperBimeromorphic {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsProperBimeromorphic p) (hX : X.IsUnibranch) [ConnectedSpace X.obj.left] :
    ConnectedSpace Y.obj.left := by
  have hsurj := surjective_of_isProperBimeromorphic hp
  have hq : Topology.IsQuotientMap p.hom.left.base :=
    hp.1.isClosedMap.isQuotientMap hp.1.continuous hsurj
  obtain ⟨x⟩ := (inferInstance : Nonempty X.obj.left)
  obtain ⟨a, -⟩ := hsurj x
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨a, ?_⟩
  have : PreconnectedSpace X.obj.left.toPresheafedSpace :=
    (inferInstance : ConnectedSpace X.obj.left).toPreconnectedSpace
  have hcc : connectedComponent (p.hom.left.base a) = univ :=
    eq_univ_of_univ_subset (isPreconnected_univ.subset_connectedComponent (mem_univ _))
  rw [← hq.isCoinducing.preimage_connectedComponent (hp.isConnected_fiber_of_isUnibranch hX) a,
    hcc, preimage_univ]

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem compactSpace_of_wholeModel [h : CompactSpace (wholeModel (n := n) M).obj.left] :
    CompactSpace M := by
  have : CompactSpace (univ : Set M) := h
  exact (Homeomorph.Set.univ M).compactSpace

theorem connectedSpace_of_wholeModel [h : ConnectedSpace (wholeModel (n := n) M).obj.left] :
    ConnectedSpace M := by
  have : ConnectedSpace (univ : Set M) := h
  exact (Homeomorph.Set.univ M).surjective.connectedSpace (Homeomorph.Set.univ M).continuous

/-- **Kähler resolutions of compact Kähler spaces**, given Kähler preservation under blowups with
smooth centres.  Every connected unibranch compact Kähler space `X` has a resolution
`π : Y → X` by a connected compact Kähler manifold `Y` (a `KahlerResolution`). -/
theorem exists_kahlerResolution_of_kahlerBlowupStep (hstep : KahlerBlowupStep)
    (X : SourceReducedComplexSpace) [hc : CompactSpace X.obj.left] [ConnectedSpace X.obj.left]
    (hX : X.IsUnibranch) (hK : X.IsKahlerSpace) :
    ∃ n : ℕ, Nonempty (KahlerResolution n X) := by
  obtain ⟨Y, p, hp, -, hYs, hres, -, -, -, -, -, hcompact⟩ :=
    HironakaG11PresUnconditional.exists_endpoint X hc
  have : CompactSpace Y.obj.left := hcompact hc
  have hYK : Y.IsKahlerSpace := isKahlerSpace_of_isModification hstep hp.toIsModification hc hK
  have : ConnectedSpace Y.obj.left := connectedSpace_of_isProperBimeromorphic hres.2 hX
  obtain ⟨n, M, ⟨F⟩⟩ :=
    HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model hYs
  obtain ⟨κ, hκ⟩ := hYK
  have : CompactSpace (wholeModel (n := n) M).obj.left := (isoHomeomorph F).symm.compactSpace
  have : ConnectedSpace (wholeModel (n := n) M).obj.left :=
    (isoHomeomorph F).symm.surjective.connectedSpace (isoHomeomorph F).symm.continuous
  have : CompactSpace M := compactSpace_of_wholeModel (n := n)
  have : ConnectedSpace M := connectedSpace_of_wholeModel (n := n)
  refine ⟨n, ⟨?_⟩⟩
  exact
    { Y := M
      kahler := KS3KahlerManifold.kahlerBackgroundOfIso hκ F.hom
      map := F.hom ≫ p
      isProperBimeromorphic := hres.2.precomp_iso F }

end SGPT.Unibranch.KS3KahlerResolution
