import SGPT.Envelopes.LapClass3Sign
import SGPT.Okounkov.TranscendentalWNRestricted
import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds

/-!
# `thm:DNT23_C11bar`: reduction to one obstacle with bounded complex Hessian

Lane DNT-BIG (blueprint `claude-dnt-big`, node `dnt-big:reduction`).  The first step of the
proof of FPT `thm:big-metric-laplacian-rooftop` ("Reduction to one obstacle with bounded complex
Hessian"): for any `θ` with `PSH(X, θ) ≠ ∅` (for instance a big class) and `f ∈ C^{1,1̄}_ω(X)`
(bounded `ω`-Laplacian), choose a Kähler form `κ = θ + Aω ≥ θ` and put `g = P_κ(f)`.  Then `g`
has bounded `ω`-Laplacian and bounded complex Hessian (it is `κ`-psh with bounded Laplacian),
`g ≤ f`, and `P_θ(f) = P_θ(g)`: every `θ`-psh function below `f` is `κ`-psh, hence below `g`.

The obstacle `g` is produced by `SGPT.Envelopes.LapClass3.exists_bounded_obstacle_between`
, applied to the `θ`-psh function `P_θ(f)`.

## Main results

* `rooftopEnvelope_eq_of_bounded_obstacle`: native form, under `PSH(X, θ) ≠ ∅`.
* `sourceObstacleEnvelope_eq_of_isBigClass`: the source envelope `P_θ(f)` (`def:Pthetaf`) for a
  big class, `P_θ(f) = P_θ(g)` with `g ≤ f` of bounded complex Hessian and bounded Laplacian.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.LapClass SGPT.Envelopes.DNTC11

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [ConnectedSpace Y]

/-- **Reduction to one obstacle with bounded complex Hessian** (FPT
`thm:big-metric-laplacian-rooftop`, first step of the proof).  If `PSH(X, θ) ≠ ∅` and `f` has
bounded `ω`-Laplacian, there is `g ≤ f` with bounded `ω`-Laplacian and bounded complex Hessian such
that `P_θ(f) = P_θ(g)`. -/
theorem rooftopEnvelope_eq_of_bounded_obstacle (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {φ : Y → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    ∃ g : Y → ℝ, HasBoundedMetricLaplacian w g ∧ HasBoundedComplexHessian (n := m + 1) g ∧
      (∀ x, g x ≤ f x) ∧
      rooftopEnvelope θ.val (fun y => (f y : EReal)) =
        rooftopEnvelope θ.val (fun y => (g y : EReal)) := by
  have hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal)) :=
    Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous w θ hf.1 hφ
  have hPf : ∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x ≤ (f x : EReal) :=
    Okounkov.TranscendentalWNReg.rooftopEnvelope_le_of_isThetaPshPotential hf.1 hP
  obtain ⟨g, hgL, hgH, hPg, hgf⟩ :=
    SGPT.Envelopes.LapClass3.exists_bounded_obstacle_between w θ hP hf hPf
  refine ⟨g, hgL, hgH, hgf, le_antisymm ?_ ?_⟩
  · exact le_rooftopEnvelope hP (quasiEverywhere_of_forall hPg)
  · exact rooftopEnvelope_mono fun x => EReal.coe_le_coe_iff.mpr (hgf x)

/-- **Reduction to one obstacle with bounded complex Hessian, source envelope.**  For a big class
`{θ}` and `f ∈ C^{1,1̄}_ω(X)`, the source envelope `P_θ(f) = sourceRelativeEnvelope θ ⊤ f`
(`def:Pthetaf`) equals `P_θ(g)` for some `g ≤ f` with bounded `ω`-Laplacian and bounded complex
Hessian. -/
theorem sourceObstacleEnvelope_eq_of_isBigClass (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    ∃ g : Y → ℝ, HasBoundedMetricLaplacian w g ∧ HasBoundedComplexHessian (n := m + 1) g ∧
      (∀ x, g x ≤ f x) ∧
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) =
        sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (g y : EReal)) := by
  obtain ⟨φ, hφ⟩ := Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  obtain ⟨g, hgL, hgH, hgf, heq⟩ :=
    rooftopEnvelope_eq_of_bounded_obstacle w (atlasClosedFormToNative θ) hφ hf
  refine ⟨g, hgL, hgH, hgf, ?_⟩
  rw [sourceObstacleEnvelope_eq_native, sourceObstacleEnvelope_eq_native, heq]

end SGPT.NPP.DNTBig
