import SGPT.NAPotential.DHFlagZero

/-!
# Full original source flag DH definition and independence theorem

Source: revised SGPT 69360cfd, def:DHm and thm:DHindep.
Every natural dimension uses the actual source flag body family, original
concave-transform pushforward, factorial, source curve and original background.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DHSource

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n F.carrier)}

/-- The literal all-dimension source formula reads the existing positive
source flag construction exactly in successor dimension. -/
theorem naDuistermaatHeckman_succ {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ = DH.naDuistermaatHeckman (F := F) hbig Γ := rfl

/-- Actual flag/intrinsic comparison in every dimension; it is an output
of the genuine zero flag pushforward and existing positive source theorem. -/
theorem naDuistermaatHeckman_eq_intrinsic (ω : KahlerBackground n F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ = DH.naIntrinsicDuistermaatHeckman ω Γ := by
  cases n with
  | zero => exact Zero.naDuistermaatHeckman_eq_intrinsic F ω hbig Γ
  | succ m => exact (DH.naIntrinsicDuistermaatHeckman_eq_flag ω hbig Γ).symm

/-- Whole original source eq:momentDHmtc2, including dimension zero. -/
theorem naDuistermaatHeckman_univ
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman F hbig Γ univ = sourceNAVolume (sourcePositiveTestCurveToNA Γ) := by
  rw [naDuistermaatHeckman_eq_intrinsic F F.omega hbig Γ]
  exact DH.naIntrinsicDuistermaatHeckman_univ F.omega Γ

/-- Whole original source eq:momentDHmtc1 for every positive integer,
including dimension zero, without a finite moment assumption. -/
theorem naDuistermaatHeckman_moment
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) (p : ℕ) (hp : 0 < p) :
    SGPT.Convex.extendedSignedIntegral (naDuistermaatHeckman F hbig Γ)
        (fun t : ℝ => (t : EReal) ^ p) =
      ((Γ.val.max ^ p * (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal : ℝ) : EReal) +
        (p : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.val.max))
          (fun t : ℝ => ((t ^ (p - 1) * (naSliceVolume F Γ t -
            (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal) : ℝ) : EReal)) := by
  cases n with
  | zero => exact Zero.naDuistermaatHeckman_moment F hbig Γ p hp
  | succ m => exact DH.naDuistermaatHeckman_moment hbig Γ p hp

section FlagIndependence

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] {θ' : AtlasClosedRealOneOneForm (ofFixedModel n M)}

local instance ofOriginalMeasurableSpace (ω : KahlerBackground n M)
    (Y : Fin (n + 1) → Set M) (hY : IsSmoothFlag Y) :
    MeasurableSpace (OriginalFlagGeometry.ofOriginal ω Y hY).carrier := ‹MeasurableSpace M›

local instance ofOriginalBorelSpace (ω : KahlerBackground n M)
    (Y : Fin (n + 1) → Set M) (hY : IsSmoothFlag Y) :
    BorelSpace (OriginalFlagGeometry.ofOriginal ω Y hY).carrier := ‹BorelSpace M›

/-- Whole original thm:DHindep flag-independence assertion in every
natural dimension, on the same original manifold/background/curve. -/
theorem naDuistermaatHeckman_flag_independent
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (ω ω' : KahlerBackground n M) (Y Y' : Fin (n + 1) → Set M)
    (hY : IsSmoothFlag Y) (hY' : IsSmoothFlag Y') (Γ : SourcePositiveIModelTestCurve θ') :
    naDuistermaatHeckman (OriginalFlagGeometry.ofOriginal ω Y hY) hbig Γ =
      naDuistermaatHeckman (OriginalFlagGeometry.ofOriginal ω' Y' hY') hbig Γ := by
  exact (naDuistermaatHeckman_eq_intrinsic
    (OriginalFlagGeometry.ofOriginal ω Y hY) ω hbig Γ).trans
      ((DH.naIntrinsicDuistermaatHeckman_independent_background ω ω' Γ).trans
        (naDuistermaatHeckman_eq_intrinsic
          (OriginalFlagGeometry.ofOriginal ω' Y' hY') ω' hbig Γ).symm)

end FlagIndependence
end SGPT.NAPotential.DHSource
