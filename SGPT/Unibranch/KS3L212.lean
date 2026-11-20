import SGPT.Unibranch.KS3KahlerBlowupStep
import SGPT.Unibranch.KS3UnibranchIEnvelope
import SGPT.Unibranch.PD2ThetaDescent

/-!
# `def:unibranch:L212`: the `𝓘`-envelope on a unibranch compact Kähler space

Source `def:unibranch:L212` (`appendix_unibranch.tex`, §`sec:unib_ext`): `X` is an
irreducible unibranch compact Kähler space, `θ` a closed real smooth `(1,1)`-form on `X`,
`φ ∈ PSH(X, θ)`; `P_θ[φ]_𝓘 ∈ PSH(X, θ)` is *the unique element* such that
`π^* P_θ[φ]_𝓘 = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic `π : Y → X` from a compact
Kähler manifold `Y`.  "It follows from `cor:PSH` and `prop:Ienvelopebimero` that `P_θ[φ]_𝓘` is
independent of the choice of `π` and is well-defined."

This file states the well-definedness without extra hypotheses:

* `exists_kahlerResolution`: every compact connected unibranch Kähler space has a resolution by a
  connected compact Kähler manifold (G11 resolution, `HironakaG11PresUnconditional`, and Kähler
  preservation under blowups with smooth centres, `KS3KahlerBlowupStep.kahlerBlowupStep`);
* `corPSHDescentAlong`: the reverse descent of `cor:PSH` along every proper bimeromorphic
  morphism onto a unibranch space (lane PD2, `PD.corPSH_bijective`);
* `existsUnique_isUnibranchIEnvelope`: **`def:unibranch:L212`** for `X` irreducible, unibranch,
  compact, Kähler (`IsKahlerSpace`), `θ` a closed real smooth `(1,1)`-form
  (`PD.IsLocallyClosedOneOne`: locally the restriction of a closed `J`-invariant ambient form) and
  `φ ∈ PSH(X, θ)`: exactly one `ψ` satisfies the defining property `IsUnibranchIEnvelopeAnyDim`
  (`ψ ∈ PSH(X, θ)` and `π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for all proper bimeromorphic `π` from compact
  Kähler manifolds of every dimension); `existsUnique_isUnibranchIEnvelope_of_connected` is the
  same statement for connected `X`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope

namespace SGPT.Unibranch.KS3L212

open SourceReducedComplexSpace KSUnibranchIEnvelope KS3KahlerResolution KS3UnibranchIEnvelope

/-- **Kähler resolutions.**  A compact connected unibranch Kähler space has a resolution by a
connected compact Kähler manifold (the `π` of `def:unibranch:L212`). -/
theorem exists_kahlerResolution (X : SourceReducedComplexSpace) [CompactSpace X.obj.left]
    [ConnectedSpace X.obj.left] (hX : X.IsUnibranch) (hK : X.IsKahlerSpace) :
    ∃ n : ℕ, Nonempty (KahlerResolution n X) :=
  exists_kahlerResolution_of_kahlerBlowupStep KS3KahlerBlowupStep.kahlerBlowupStep X hX hK

/-- **`cor:PSH`, reverse descent**: along a proper bimeromorphic morphism onto a
unibranch space, every `π^*θ`-psh function descends to a `θ`-psh function. -/
theorem corPSHDescentAlong {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) (θ : SpaceForm X 2)
    (hθ : PD.IsLocallyClosedOneOne θ) : CorPSHDescentAlong π θ :=
  (PD.thetaPSHPullback_bijective_iff θ π hπ hX).mp (PD.corPSH_bijective π hπ hX θ hθ)

/-- **`def:unibranch:L212` for a connected unibranch compact Kähler space.** -/
theorem existsUnique_isUnibranchIEnvelope_of_connected {X : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] [ConnectedSpace X.obj.left] (hX : X.IsUnibranch)
    (hK : X.IsKahlerSpace) (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) :
    ∃! ψ : X.obj.left → EReal, IsUnibranchIEnvelopeAnyDim X θ φ ψ := by
  obtain ⟨n, ⟨R⟩⟩ := exists_kahlerResolution X hX hK
  exact existsUnique_isUnibranchIEnvelopeAnyDim hX θ hθ.isClosed hθ.isOneOne hφ R
    (corPSHDescentAlong R.map R.isProperBimeromorphic hX θ hθ)

/-- **Source `def:unibranch:L212`.**  Let `X` be an irreducible unibranch compact Kähler space,
`θ` a closed real smooth `(1,1)`-form on `X` and `φ ∈ PSH(X, θ)`.  There is exactly one
`ψ = P_θ[φ]_𝓘` such that `ψ ∈ PSH(X, θ)` and `π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for every proper
bimeromorphic morphism `π : Y → X` from a compact Kähler manifold `Y`. -/
theorem existsUnique_isUnibranchIEnvelope {X : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (hirr : X.IsIrreducibleAnalyticSubset univ) (hX : X.IsUnibranch)
    (hK : X.IsKahlerSpace) (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) :
    ∃! ψ : X.obj.left → EReal, IsUnibranchIEnvelopeAnyDim X θ φ ψ :=
  existsUnique_isUnibranchIEnvelope_of_isIrreducible KS3KahlerBlowupStep.kahlerBlowupStep hirr
    hX hK θ hθ.isClosed hθ.isOneOne hφ
    (fun _ π hπ => corPSHDescentAlong π hπ hX θ hθ)

end SGPT.Unibranch.KS3L212
