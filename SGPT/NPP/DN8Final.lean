import SGPT.NPP.DN8Main
import SGPT.NPP.DN9Final

/-!
# `thm:DNT23_C11bar`: the Di Nezza–Trapani regularity theorem for big classes

Source: SGPT `thm:DNT23_C11bar` (`chapter_npp.tex`, Di Nezza–Trapani):

> Let `θ` be a smooth closed real `(1,1)`-form on `X` representing a big cohomology class.  Let
> `f ∈ C^{1,1̄}(X)`.  Then `P_θ(f) ∈ C^{1,1̄}(X ∖ nK({θ}))`.  In particular,
> `V_θ ∈ C^{1,1̄}(X ∖ nK({θ}))`.

Here `X` is a compact connected complex manifold with a Kähler form `ω`, `C^{1,1̄}(X)` is the book's
class of continuous functions with bounded `ω`-Laplacian (`HasBoundedMetricLaplacian`), and
`C^{1,1̄}(U)` for the open set `U = X ∖ nK({θ})` is the class of functions continuous on `U` (here
real-valued on `U`) with bounded distributional `ω`-Laplacian on every compact subset of `U`
(`HasBoundedMetricLaplacianOn`, FPT `thm:big-metric-laplacian-rooftop`); `P_θ(f)` is
`sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`), `V_θ` is `sourceMinimalEnvelope θ` (`eq:Vtheta`) and
`nK({θ})` is `sourceNonKahlerLocus` (`def:nKlocus`).

The proof is FPT `thm:big-metric-laplacian-rooftop` (`DN8Main`), with the joint smoothing of FPT
`lem:chern-joint-smoothing` supplied by `SGPT.NPP.DN9.jointSmoothingStatement` (lanes DN3–DN6, DN9–DN11)
and the modification data by `SGPT.NPP.DN7.exists_modificationData`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NPP.DN8

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.LapClass SGPT.PSH SGPT.PSH.VariableComplexAtlas

universe u

/-- **SGPT `thm:DNT23_C11bar`** (Di Nezza–Trapani), for every big class: if `{θ}` is big and
`f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f) = sourceRelativeEnvelope θ ⊤ f` is real-valued on
`X ∖ nK({θ})` and lies in `C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass {N : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
    (w : KahlerBackground N X) (θ : AtlasClosedRealOneOneForm (ofFixedModel N X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {f : X → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
        (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) :
          EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) :=
  sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    SGPT.NPP.DN9.jointSmoothingStatement w θ hbig hf

/-- **The "in particular" of SGPT `thm:DNT23_C11bar`**, for every big class: `V_θ`
(`sourceMinimalEnvelope`) is real-valued on `X ∖ nK({θ})` and lies in `C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass {N : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
    (w : KahlerBackground N X) (θ : AtlasClosedRealOneOneForm (ofFixedModel N X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) :=
  sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    SGPT.NPP.DN9.jointSmoothingStatement w θ hbig

/-- **`thm:DNT23_C11bar`, native form** (positive dimension, for every big class): `P_θ(f)` is
real-valued off TN's non-Kähler locus (which is contained in `nK({θ})`) and has bounded
`ω`-Laplacian on every compact subset of its complement. -/
theorem rooftopEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
    (w : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {f : X → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ),
      rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
        (((rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (fun x => (rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal) :=
  rooftopEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    SGPT.NPP.DN9.jointSmoothingStatement w θ hbig hf

end SGPT.NPP.DN8
