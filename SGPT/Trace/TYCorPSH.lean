import SGPT.Trace.TYNormalization
import SGPT.Trace.TYTrace
import SGPT.Unibranch.KSNormalizedSubvariety

/-!
# `cor:PSH` for the normalization: reduction to the descent along one resolution morphism

Source: `appendix_unibranch.tex`, `cor:PSH`: for a proper bimeromorphic morphism `π : Y → X` of
compact Kähler spaces with `X` unibranch and a smooth closed real `(1,1)`-form `θ` on `X`, the
pull-back `π^* : PSH(X, θ) → PSH(Y, π^*θ)` is a bijection.

The trace theory on `Ỹ` (`TYTrace`) takes `TildeY.CorPSH N` as a hypothesis: for the resolution
`ν : V → Ỹ` and every closed real `(1,1)`-form `θ` on `X`, `ψ ↦ ψ ∘ ν` maps `PSH(Ỹ, θ|_Ỹ)` onto
`PSH(V, ι^*θ)`. For the actual normalization (`normalizationTildeY`) this file proves:

* `exists_resolution_morphism`: `Ỹ` has a resolution `N` whose lift `ν` is (on points) a proper
  bimeromorphic morphism of complex spaces `F : (V, 𝒪_V) → Ỹ` (the strict transform of `Y` in its
  embedded resolution, lifted through the normalization; the `wholeModelIso`);
* `corPSH_of_descent`: for such `(N, F)`, the forward half of `CorPSH N` holds unconditionally
  (forward pull-back of `θ`-psh functions to a unibranch target, `IsThetaPSH.pullback_of_isProperBimeromorphic`,
  the manifold/complex-space bridge of lane KS and `F^*(θ|_Ỹ) = ι^*θ`), and the backward half is
  exactly the descent half of `cor:PSH` along `F` for the forms `θ|_Ỹ`
  (`KSUnibranchIEnvelope.CorPSHDescentAlong F (θ|_Ỹ)`, the open statement);
* `corPSH_all_of_descent`: hence the descent half of `cor:PSH` along this ONE resolution morphism
  of `Ỹ` gives `CorPSH` for every resolution of `Ỹ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification
open HironakaEmbeddedAnalytic (singularSet)
open SGPT.Unibranch.KSNormalizedSubvariety (normalization normalizationMap restrictForm)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Normalization

/-- **A resolution of `Ỹ` given by a proper bimeromorphic morphism of complex spaces.** -/
theorem exists_resolution_morphism (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (N : (normalizationTildeY omega Y).Resolution)
      (F : wholeModel (n := Y.dim) N.R.V ⟶ normalization Y.carrier Y.analytic),
      IsProperBimeromorphic F ∧ ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v := by
  have hWa : IsComplexAnalyticSubset (n := n) Y.carrier := Y.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n) Y.carrier Y.dim :=
    fun _ _ hy => PureDimension.eq_dim_of_regularAtDim Y hy
  obtain ⟨M', _, _, _, σ, E, h, hreg, _omega', hCM, hcpt, l, hl, -, htri, -, omegaR, -⟩ :=
    NativeNov16NormalizationKahlerResolution.exists_kahler_resolution_of_normalization hWa hpure
      Y.dim_le omega
  let := SubmanifoldChartedSpace.chartedSpace Y.dim_le hreg
  have hExcS : σ '' exceptionalLocus n σ ⊆ singularLocus Y := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hx
    have hc : σ y ∈ (singularSet (n := n) Y.carrier)ᶜ := by
      rw [singularSet_eq_singularLocus]
      exact hx
    exact Set.disjoint_left.mp h.isIsomorphismOver.2 hc hy
  have hconn := StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
    h.isBlowupSequence Y hExcS
  have : ConnectedSpace (strictTransform n σ Y.carrier) := isConnected_iff_connectedSpace.mp hconn
  have hval := SubmanifoldChartedSpace.contMDiff_val Y.dim_le hreg
  have hres : IsResolutionOf Y (σ ∘ (Subtype.val : strictTransform n σ Y.carrier → M')) := by
    refine ⟨?_, singularSet (n := n) Y.carrier,
      HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hWa,
      (singularSet_eq_singularLocus Y).symm.subset, ?_, ?_⟩
    · rw [range_comp, Subtype.range_coe]
      exact h.image_eq
    · intro y₁ hy₁ y₂ hy₂ heq
      exact Subtype.ext (h.isIsomorphismOver.1.injOn hy₁ hy₂ heq)
    · rw [dense_iff_closure_eq, eq_univ_iff_forall]
      intro x
      rw [closure_subtype]
      have hx : x.1 ∈ closure (σ ⁻¹' (Y.carrier \ singularSet (n := n) Y.carrier)) := by
        rw [← h.eq_closure]
        exact x.2
      refine closure_mono ?_ hx
      intro z hz
      have hz' : z ∈ strictTransform n σ Y.carrier ∩ σ ⁻¹' (singularSet (n := n) Y.carrier)ᶜ := by
        rw [h.inter_preimage_compl]
        exact hz
      exact ⟨⟨z, hz'.1⟩, hz'.2, rfl⟩
  let R : ResolutionTarget Y :=
    { V := strictTransform n σ Y.carrier
      isComplexManifold := hCM
      compactSpace := hcpt
      ι := σ ∘ Subtype.val
      contMDiff := h.contMDiff.comp hval
      isResolutionOf := hres
      kahler := omegaR }
  let K := KSSubmanifoldModel.wholeModelIso (d := Y.dim) h.isClosedSubmanifold hval
    (KSSubmanifoldModel.flattening_codRestrict Y.dim_le hreg)
  let F : wholeModel (n := Y.dim) R.V ⟶ normalization Y.carrier Y.analytic := K.hom ≫ l
  have hF : IsProperBimeromorphic F := hl.2.precomp_iso K
  have hcont : Continuous fun v : R.V => F.hom.left.base ⟨v, mem_univ v⟩ :=
    F.hom.left.base.hom.continuous.comp (continuous_id.subtype_mk fun v => mem_univ v)
  have hcomm : ∀ v : R.V, (normalizationTildeY omega Y).toX (F.hom.left.base ⟨v, mem_univ v⟩) =
      R.ι v := by
    intro v
    have hpt := congrArg (fun G => G.hom.left.base (K.hom.hom.left.base ⟨v, mem_univ v⟩)) htri
    change ((l ≫ NativeNov16NormalizationSpace.projection _).hom.left.base
      (K.hom.hom.left.base ⟨v, mem_univ v⟩)).val = σ v.val
    rw [hpt]
    rfl
  exact ⟨⟨R, fun v => F.hom.left.base ⟨v, mem_univ v⟩, hcont, hcomm⟩, F, hF, fun v => rfl⟩

/-- **The forward half of `cor:PSH` for the normalization** (unconditional): for a resolution `N`
of `Ỹ` whose lift is a proper bimeromorphic morphism `F` on points, `ψ ∘ ν` is `ι^*θ`-psh for every
`θ|_Ỹ`-psh `ψ`. -/
theorem corPSHForward_of_morphism (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (F : wholeModel (n := Y.dim) N.R.V ⟶ normalization Y.carrier Y.analytic) (hF : IsProperBimeromorphic F)
    (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v) :
    (normalizationTildeY omega Y).CorPSHForward N := by
  intro θ ψ hψ
  have hF' : ∀ y : N.R.V, ((KSNormalizedSubvariety.normalizationMap Y.carrier Y.analytic).hom.left.base
      (F.hom.left.base ⟨y, mem_univ y⟩)).val = N.R.ι y := by
    intro y
    rw [hFN y]
    exact N.toX_comp y
  have hgeo := KSNormalizedSubvariety.manifoldPullback_restrictForm Y.carrier Y.analytic θ.val F
    N.R.contMDiff hF'
  have hX : (normalization Y.carrier Y.analytic).IsUnibranch :=
    KSNormalizedSubvariety.normalization_isUnibranch Y.carrier Y.analytic
  have h := KSUnibranchIEnvelope.isThetaPshPotential_pullback hX hψ hF
  have h' : IsThetaPshPotential (SmoothRealForm.pullback N.R.contMDiff θ.val)
      (fun y => ψ (KSUnibranchIEnvelope.pt F y)) := (hgeo.thetaPshPotential_iff _).mp h
  have hfun : (fun y => ψ (KSUnibranchIEnvelope.pt F y)) = ψ ∘ N.ν := by
    funext y
    exact congrArg ψ (hFN y)
  rw [hfun] at h'
  exact h'

/-- **The forward half of `cor:PSH` holds for every resolution of the normalization.** -/
theorem corPSHForward_all (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∀ N : (normalizationTildeY omega Y).Resolution, (normalizationTildeY omega Y).CorPSHForward N := by
  obtain ⟨N, F, hF, hFN⟩ := exists_resolution_morphism omega Y
  exact TildeY.CorPSHForward.of_resolution (corPSHForward_of_morphism omega Y N F hF hFN)

/-- **`cor:PSH` for the normalization, reduced to its descent half along one resolution
morphism.** Let `N` be a resolution of `Ỹ` whose lift is the proper bimeromorphic morphism `F` on
points. The forward half of `CorPSH N` holds; if moreover every `F^*(θ|_Ỹ)`-psh function on `V`
descends to a `θ|_Ỹ`-psh function on `Ỹ` (the descent half of `cor:PSH` along `F`), then
`CorPSH N` holds. -/
theorem corPSH_of_descent (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (F : wholeModel (n := Y.dim) N.R.V ⟶ normalization Y.carrier Y.analytic) (hF : IsProperBimeromorphic F)
    (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    (hdesc : ∀ θ : ClosedRealOneOneForm n X,
      KSUnibranchIEnvelope.CorPSHDescentAlong F ((normalizationTildeY omega Y).restrict θ)) :
    (normalizationTildeY omega Y).CorPSH N := by
  intro θ
  have hF' : ∀ y : N.R.V, ((KSNormalizedSubvariety.normalizationMap Y.carrier Y.analytic).hom.left.base
      (F.hom.left.base ⟨y, mem_univ y⟩)).val = N.R.ι y := by
    intro y
    rw [hFN y]
    exact N.toX_comp y
  have hgeo := KSNormalizedSubvariety.manifoldPullback_restrictForm Y.carrier Y.analytic θ.val F
    N.R.contMDiff hF'
  constructor
  · exact corPSHForward_of_morphism omega Y N F hF hFN θ
  · intro w hw
    have h₁ : IsThetaPshPotential
        (KSManifoldForm.toManifoldForm (SpaceForm.pullback ((normalizationTildeY omega Y).restrict θ) F))
        w := (hgeo.thetaPshPotential_iff _).mpr hw
    have h₂ := KSManifoldForm.isThetaPSH_of_isThetaPshPotential h₁
    obtain ⟨u, hu, huw⟩ := hdesc θ _ h₂
    refine ⟨u, hu, ?_⟩
    funext v
    change u (N.ν v) = w v
    rw [← hFN v]
    exact huw ⟨v, mem_univ v⟩

/-- **The descent half of `cor:PSH` along one resolution morphism of `Ỹ` gives the hypothesis
`CorPSH` of the trace theory on `Ỹ` for every resolution of `Ỹ`.** -/
theorem corPSH_all_of_descent (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (N : (normalizationTildeY omega Y).Resolution)
      (F : wholeModel (n := Y.dim) N.R.V ⟶ normalization Y.carrier Y.analytic),
      IsProperBimeromorphic F ∧ (∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v) ∧
      ((∀ θ : ClosedRealOneOneForm n X,
          KSUnibranchIEnvelope.CorPSHDescentAlong F ((normalizationTildeY omega Y).restrict θ)) →
        ∀ N' : (normalizationTildeY omega Y).Resolution, (normalizationTildeY omega Y).CorPSH N') := by
  obtain ⟨N, F, hF, hFN⟩ := exists_resolution_morphism omega Y
  exact ⟨N, F, hF, hFN, fun hdesc =>
    TildeY.corPSH_forall_of_one (corPSH_of_descent omega Y N F hF hFN hdesc)⟩

/-- **`def:traceop` on the normalization: one resolution suffices** (unconditional): a
`θ|_Ỹ`-psh `ψ` is a trace operator of `φ` along `Y` iff its reading on one resolution of `Ỹ` is a
trace operator there. -/
theorem isTrace_iff_exists [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH ((normalizationTildeY omega Y).restrict θ) ψ) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔
      ∃ N : (normalizationTildeY omega Y).Resolution, TildeY.IsTraceOn N φ (ψ ∘ N.ν) :=
  TildeY.isTrace_iff_exists (corPSHForward_all omega Y) hψ

end Normalization

end SGPT.Trace.TY
