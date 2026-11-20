import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Okounkov.TranscendentalVolumeConcavityRestricted

/-!
# Witt Nyström's derivative of the volume along the first flag divisor: statements

Blueprint node `tok:ext-wn21` (chapter `claude-okounkov-transcendental`) and the WN chapter
`claude-tok-wn` (nodes `tok-wn:derivative`, `tok-wn:integrated`, `tok-wn:continuity`), the
critical external input of Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov
bodies* (DRWNXZ), Theorem 2.10: D. Witt Nyström, *Deformations of Kähler manifolds to normal
bundles and restricted volumes of big classes*, arXiv:2103.03660, Theorem C
(`references/wn21-restricted-volume`).

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1`, `Y₁ ⊆ X` the first
member of a smooth flag (a connected smooth hypersurface), `{Y₁}` its class, `ξ` a big
class whose Kähler locus `K(ξ) = X \ E_nK(ξ)` meets `Y₁`, and `vol_{X|Y₁}(ξ)` the restricted
volume (DRWNXZ §2, `TranscendentalVolumeConcavity.restrictedVolume`). This file contains
**statements only** (`def … : Prop`); nothing is asserted.

* `WNDerivativeStatement` (`tok:ext-wn21`, DRWNXZ Theorem 2.10, first point):
  `d/dt|_{t=0} vol(ξ - t{Y₁}) = -n vol_{X|Y₁}(ξ)`.
* `WNIntegratedStatement` (`tok-wn:integrated`, WN21 Theorems 1.6--1.7 combined, as stated
  after Theorem 1.7; DRWNXZ proof of Theorem 2.10): for `c ≥ 0` such that `ξ - c{Y₁}` is big
  and its Kähler locus meets `Y₁`,
  `vol(ξ) - vol(ξ - c{Y₁}) = n ∫₀^c vol_{X|Y₁}(ξ - t{Y₁}) dt`.
* `WNContinuityStatement` (`tok-wn:continuity`): under the same hypotheses
  `t ↦ vol_{X|Y₁}(ξ - t{Y₁})` is continuous on `[0, c]`.

`WNIntegratedStatement ∧ WNContinuityStatement` is exactly what the volume identity
(`tok:wn-integrated`, `tok:vol-integral`, `tok:Bn-implies-Cn`, package VOL) consumes; it is the
form in which the WN package proves Theorem C (the derivative follows from it by the
fundamental theorem of calculus, `tok-wn:derivative-from-integrated`).

## Formal conventions

* `X`, `Y•` form an `OriginalFlagGeometry (m + 1)`; `Y₁ = F.flag 1`, carried by the manifold
  `F.tail.carrier` with the holomorphic inclusion `firstFlagInclusion` (`Subtype.val`;
  `contMDiff_firstFlagInclusion`, as in `TranscendentalMain.firstFlagRestriction`).
* Classes are `RealBottChern (m + 1) F.carrier` (an `ℝ`-module); `{Y₁}` is the class of the
  curvature form `E.curvature` of any unit metric `E` of `Y₁` (`IsFirstDivisorUnitMetric`).
* Bigness is `SGPT.PSH.BookCurrent.IsBig`; the non-Kähler locus is TN's
  `NonKahlerLocus.nonKahlerLocus` (points where every Kähler current has positive Lelong number;
  equal to Boucksom's `E_nK`); `ξ` "meets `Y₁` in its Kähler locus" is
  `∃ y ∈ Y₁, y ∉ E_nK(ξ)` (DRWNXZ: `Z ∩ K(ξ) ≠ ∅`).
* The volume is `sourceClassVolume` (`def:volcohclass`, Borel measurable structure), the
  restricted volume is `TranscendentalVolumeConcavity.classRestrictedVolume` (supremum over
  `Ω(ξ)` of the non-pluripolar masses of the restrictions), both `ℝ≥0∞`-valued and finite;
  the statements use their real parts.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped ENNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The inclusion `Y₁ ↪ X` of the first flag member, `Y₁` carried by `F.tail.carrier`. -/
def firstFlagInclusion : F.tail.carrier → F.carrier := Subtype.val

/-- The inclusion `Y₁ ↪ X` of the first flag member is holomorphic. -/
theorem contMDiff_firstFlagInclusion :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (firstFlagInclusion F) :=
  SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2

/-- `vol_{X|Y₁}(ξ)` (DRWNXZ §2, `tok:restricted-volume`): the restricted volume of the class
`ξ` along the first flag member `Y₁`. -/
def firstFlagRestrictedVolume (ξ : RealBottChern (m + 1) F.carrier) : ℝ≥0∞ :=
  letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
  TranscendentalVolumeConcavity.classRestrictedVolume (firstFlagInclusion F)
    (contMDiff_firstFlagInclusion F) ξ

/-- `vol(ξ)` (`def:volcohclass`) for the Borel structure of `X`, as a real number. -/
def classVolumeReal (ξ : RealBottChern (m + 1) F.carrier) : ℝ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  (SGPT.PSH.VariableComplexAtlas.sourceClassVolume ξ).toReal

/-- The class `ξ` is big and its Kähler locus `X \ E_nK(ξ)` meets `Y₁` (DRWNXZ:
`ξ` big and `Y₁ ∩ K(ξ) ≠ ∅`). -/
def IsBigMeetingFirstDivisor (ξ : RealBottChern (m + 1) F.carrier) : Prop :=
  SGPT.PSH.BookCurrent.IsBig ξ ∧
    ∃ y ∈ F.flag (1 : Fin (m + 2)), y ∉ NonKahlerLocus.nonKahlerLocus ξ

/-- **`tok:ext-wn21`** (WN21 Theorem C, DRWNXZ Theorem 2.10, first point): for a big class
`ξ` whose Kähler locus meets `Y₁`, `t ↦ vol(ξ - t{Y₁})` is differentiable at `t = 0` with
derivative `-n vol_{X|Y₁}(ξ)`. -/
def WNDerivativeStatement : Prop :=
  ∀ (ξ : RealBottChern (m + 1) F.carrier) (E : MeteredEffectiveQDivisor (m + 1) F.carrier),
    IsFirstDivisorUnitMetric F E → IsBigMeetingFirstDivisor F ξ →
      HasDerivAt
        (fun t : ℝ => classVolumeReal F (ξ - t • RealBottChern.ofRepresentative E.curvature))
        (-((m + 1 : ℕ) : ℝ) * (firstFlagRestrictedVolume F ξ).toReal) 0

/-- **`tok-wn:integrated`** (WN21, Theorem 1.6 (3)--(4) with Theorem 1.7; DRWNXZ proof of
Theorem 2.10): if `ξ` and `ξ - c{Y₁}` (`c ≥ 0`) are big with Kähler loci meeting `Y₁`, then
`vol(ξ) - vol(ξ - c{Y₁}) = n ∫₀^c vol_{X|Y₁}(ξ - t{Y₁}) dt`. -/
def WNIntegratedStatement : Prop :=
  ∀ (ξ : RealBottChern (m + 1) F.carrier) (E : MeteredEffectiveQDivisor (m + 1) F.carrier),
    IsFirstDivisorUnitMetric F E → ∀ c : ℝ, 0 ≤ c → IsBigMeetingFirstDivisor F ξ →
      IsBigMeetingFirstDivisor F (ξ - c • RealBottChern.ofRepresentative E.curvature) →
        classVolumeReal F ξ -
            classVolumeReal F (ξ - c • RealBottChern.ofRepresentative E.curvature) =
          ((m + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..c,
            (firstFlagRestrictedVolume F
              (ξ - t • RealBottChern.ofRepresentative E.curvature)).toReal

/-- **`tok-wn:continuity`** (Matsumura 2013, Corollary 4.11, for the DRWNXZ restricted volume;
Collins--Tosatti 2022, Corollary 5.3): under the hypotheses of `WNIntegratedStatement`,
`t ↦ vol_{X|Y₁}(ξ - t{Y₁})` is continuous on `[0, c]`. -/
def WNContinuityStatement : Prop :=
  ∀ (ξ : RealBottChern (m + 1) F.carrier) (E : MeteredEffectiveQDivisor (m + 1) F.carrier),
    IsFirstDivisorUnitMetric F E → ∀ c : ℝ, 0 ≤ c → IsBigMeetingFirstDivisor F ξ →
      IsBigMeetingFirstDivisor F (ξ - c • RealBottChern.ofRepresentative E.curvature) →
        ContinuousOn
          (fun t : ℝ => (firstFlagRestrictedVolume F
            (ξ - t • RealBottChern.ofRepresentative E.curvature)).toReal) (Icc 0 c)

/-- The package statement: the integrated identity and the continuity (what VOL consumes). -/
def WNStatement : Prop :=
  WNIntegratedStatement F ∧ WNContinuityStatement F

end SGPT.Okounkov.TranscendentalWN
