import SGPT.Okounkov.TranscendentalWNVolumeStatement

/-!
# The key equality of the deformation to the normal cone: statements (package WN-KEY)

Blueprint chapter `claude-tok-wn`, § "The key equality" (nodes `tok-wn:key-easy`,
`tok-wn:convergence`, `tok-wn:key-equality`) and its supplement `claude-tok-wn-key`; source
D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted volumes of
big classes*, arXiv:2103.03660 (WN21), Theorem 1.7, proved in §§5--7
(`references/wn21-restricted-volume`).

Notation as in `TranscendentalWNVolumeStatement`: `μ : 𝒳 → X × ℙ¹` is the deformation of `X` to
the normal cone of `Z = Y₁`, `X'` the strict transform of `X × {0}` (parametrized by the lift
`ι'` of `x ↦ (x, 0)`), `ℰ` the exceptional divisor, `Eℰ` the circle-invariant metric of `𝒪(ℰ)`
(`IsDeformationExceptionalMetric`) and, for `ξ = {θ}` and `0 < c < b`,
`β = {θ̃}`, `θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ` (`deformationForm`).

WN21 Theorem 1.7 (the key equality) asserts `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) = vol(ξ)`.  Its two
halves are:

* `KeyEasyStatement` (`tok-wn:key-easy`, WN21 §5): `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) ≤ vol(ξ)`
  (lower semicontinuity of the fibre masses as `X_τ` degenerates to `X₀ = X' + ℰ`, and
  `vol_{𝒳|X_τ}(β) = vol(ξ)`, `tok-wn:formula-fibre`);
* `KeyConvergenceStatement` (`tok-wn:convergence`, WN21 §§6--7, the hard inequality up to a
  Kähler perturbation): for every Kähler form `η'` on `𝒳` and `ε > 0`,
  `vol(ξ) ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`.

The key equality `KeyEqualityStatement` (`tok-wn:key-equality`) follows from the two and the
continuity of restricted volumes (`tok-wn:restricted-perturbation`) on `𝒳` along `X'` and `ℰ`
(`TranscendentalWNKey.keyEquality_of_keyEasy_of_keyConvergence`).

This file contains **statements only** (`def … : Prop`); nothing is asserted.

## Formal conventions

As in `TranscendentalWNVolumeStatement`: restricted volumes are
`TranscendentalVolumeConcavity.classRestrictedVolume` as real numbers, along the lift `ι'`
(`sectionRestrictedVolume`) and along the inclusion of `ℰ` (`exceptionalRestrictedVolume`); the
volume of `ξ` is `classVolumeReal`; `E` is a unit metric of `𝒪(Z)` with `|s_Z|_h ≤ 1`
(`∀ x, E.weight x ≤ 0`).  The key easy inequality is stated for `0 < c < b`; the convergence and
the equality for `c + 1 < b`, as in WN21 §§6--7 (`b > c + 1` is used through
`vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)`, `tok-wn:formula-volume`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn:key-easy`** (WN21 §5, the easy inequality of Theorem 1.7): for `ξ = {θ}` and `ξ_c`
big with Kähler loci meeting `Z`, `0 < c < b`, and the lift `ι'` of `x ↦ (x, 0)` (image `X'`),
`vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) ≤ vol(ξ)`. -/
def KeyEasyStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
        ∀ (ι : F.carrier → 𝒳)
          (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
            (sectionRestrictedVolume F ι hι
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal +
              (exceptionalRestrictedVolume F hμ
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal ≤
              classVolumeReal F (RealBottChern.ofRepresentative θ)

/-- **`tok-wn:convergence`** (WN21 §§6--7: Propositions 6.1--6.4, Corollary 6.5,
Propositions 7.1--7.4, Lemma 7.5, Corollary 7.6 and the proof of the hard inequality of
Theorem 1.7): under the hypotheses of `KeyEasyStatement` with `c + 1 < b`, for every Kähler form
`η'` on `𝒳` and every `ε > 0`,
`vol(ξ) ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`. -/
def KeyConvergenceStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c + 1 < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
        ∀ (ι : F.carrier → 𝒳)
          (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
          ∀ (η' : KahlerBackground (m + 1 + 1) 𝒳) (ε : ℝ), 0 < ε →
            classVolumeReal F (RealBottChern.ofRepresentative θ) ≤
              (sectionRestrictedVolume F ι hι
                  (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) +
                    ε • RealBottChern.ofRepresentative η'.form)).toReal +
                (exceptionalRestrictedVolume F hμ
                  (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) +
                    ε • RealBottChern.ofRepresentative η'.form)).toReal

/-- **`tok-wn:key-equality`** (WN21 Theorem 1.7): under the hypotheses of `KeyEasyStatement` with
`c + 1 < b`, `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) = vol(ξ)`. -/
def KeyEqualityStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c + 1 < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
        ∀ (ι : F.carrier → 𝒳)
          (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
            (sectionRestrictedVolume F ι hι
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal +
              (exceptionalRestrictedVolume F hμ
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal =
              classVolumeReal F (RealBottChern.ofRepresentative θ)

end SGPT.Okounkov.TranscendentalWN
