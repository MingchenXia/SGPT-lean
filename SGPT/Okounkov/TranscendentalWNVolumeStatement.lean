import SGPT.Okounkov.TranscendentalWNDeformation
import SGPT.Okounkov.TranscendentalWNDeformationMetric
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-!
# The volume formulas of the deformation to the normal cone: statements (package WN-VF)

Blueprint chapter `claude-tok-wn`, §§"The volume formulas" (nodes `tok-wn:formula-volume`,
`tok-wn:formula-fibre`, `tok-wn:formula-X-prime`, `tok-wn:formula-E`) and its supplement
`claude-tok-wn-vf`; source D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles
and restricted volumes of big classes*, arXiv:2103.03660 (WN21), Theorem 1.6 and Corollary 4.7,
proved in §4 (`references/wn21-restricted-volume`).

Let `X` be the compact Kähler manifold of the flag geometry `F` (dimension `n = m + 1`),
`Z = Y₁` its first flag member, `μ : 𝒳 → X × ℙ¹` the deformation of `X` to the normal cone of
`Z` (`IsNormalConeDeformation`, the blow-up along `Z × {0}`), `ℰ` its exceptional divisor,
`X'` the strict transform of `X × {0}` and `X_τ` the fibre over `τ ∈ ℙ¹`.  For a unit metric `E`
of `𝒪(Z)` (weight `g = log |s_Z|²_h ≤ 0`, curvature `η`) the divisor `ℰ` carries the
circle-invariant metric of WN21 §4 with weight `log W ∘ μ`,
`W = (|s_Z|²_h + |τ|²) / (1 + |τ|²)` (`IsDeformationExceptionalMetric`, which exists by
`exceptionalMetric`).  For `ξ = {θ}`, `0 < c < b`, let

  `β = {θ̃}`,  `θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ`   (`deformationForm`),

and `ξ_t = ξ - t{Z}`.  Assume `ξ` and `ξ_c` are big with Kähler loci meeting `Z`
(`IsBigMeetingFirstDivisor`).  WN21 Theorem 1.6 asserts:

1. `vol(β) = (n + 1)((b - c) vol(ξ) + ∫₀^c vol(ξ_t) dt)` (`DeformationVolumeStatement`), hence
   `vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)` for `b > c + 1`
   (`DeformationVolumeDifferenceStatement`; `β - {X₀}` is `β` for the parameter `b - 1`);
2. `vol_{𝒳|X_τ}(β) = vol(ξ)` for `τ ≠ 0`, and every `θ̃`-psh potential with minimal
   singularities restricts to one with minimal singularities on `X_τ ≅ X`
   (`FibreRestrictedVolumeStatement`);
3. `vol_{𝒳|X'}(β) = vol(ξ_c)` (`StrictTransformRestrictedVolumeStatement`);
4. `vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Z}(ξ_t) dt` (`ExceptionalRestrictedVolumeStatement`).

This file contains the objects and the **statements only** (`def … : Prop`); apart from the
existence of the metric (`exists_isDeformationExceptionalMetric`, a repackaging of the proved
`exceptionalMetric`) and the elementary corollary `deformationVolumeDifference_of_volume`
(item 1, second half, from the first half) nothing is asserted.  It is the interface for the
packages WN-KEY (`tok-wn:key-easy`, `tok-wn:measure-control`, `tok-wn:key-equality`) and WN-ASM
(`tok-wn:integrated`).

## Formal conventions

* Volumes are `sourceClassVolume` (`def:volcohclass`) for the Borel structure, as real numbers
  (`classVolumeReal` on `X`, `deformationVolumeReal` on `𝒳`); restricted volumes are
  `TranscendentalVolumeConcavity.classRestrictedVolume` (DRWNXZ §2), as real numbers.
* `X_τ` (`τ ≠ 0`) and `X'` are parametrized by the holomorphic sections `s : X → 𝒳` of `μ` over
  `x ↦ (x, τ)` (resp. the lift `ι'` of `x ↦ (x, 0)`), which exist and are unique
  (`exists_fibreSection`, `exists_centralSection`); the restricted volume along such a map is
  `sectionRestrictedVolume`.
* `ℰ` is carried, as the subtype `exceptionalSet F μ`, by the submanifold atlas of TN
  (`SubmanifoldChartedSpace.chartedSpace`; `ℰ` is a closed submanifold of dimension `m + 1`,
  `regularAtDim_exceptionalSet`); `exceptionalRestrictedVolume` is the restricted volume along
  its inclusion.
* `n + 1 = m + 2` and `n = m + 1` are written `((m + 2 : ℕ) : ℝ)` and `((m + 1 : ℕ) : ℝ)`.
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
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-! ### The metric of `𝒪(ℰ)` -/

/-- The circle-invariant metric of `𝒪(ℰ)` of WN21 §4 (the conclusion of
`ExceptionalMetricStatement`): a metric of the exceptional divisor of `μ`, with support `ℰ` and
weight `log |s_ℰ|² = log W ∘ μ`, `W = (|s_Z|²_h + |τ|²) / (1 + |τ|²)`. -/
structure IsDeformationExceptionalMetric (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) : Prop where
  isDivisorMetric :
    DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ
  support_eq : Eℰ.support = exceptionalSet F μ
  weight_eq : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z)))

/-- The metric of `𝒪(ℰ)` exists for every unit metric of `𝒪(Z)` (`exceptionalMetric`). -/
theorem exists_isDeformationExceptionalMetric {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hμ : IsNormalConeDeformation F μ) :
    ∃ Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳, IsDeformationExceptionalMetric F E hμ Eℰ := by
  obtain ⟨Eℰ, hmet, hsupp, hweight, -⟩ := exists_exceptionalMetric_weight F hμ hE
  exact ⟨Eℰ, ⟨hmet, hsupp, hweight⟩⟩

/-! ### Volumes on `𝒳` and restricted volumes -/

/-- `vol(β)` (`def:volcohclass`) for a class `β` on the deformation `𝒳` (Borel structure; `𝒳` is
compact and connected, `compactSpace_normalCone`, `connectedSpace_normalCone`), as a real
number. -/
def deformationVolumeReal (hμ : IsNormalConeDeformation F μ)
    (β : RealBottChern (m + 1 + 1) 𝒳) : ℝ :=
  letI : MeasurableSpace 𝒳 := borel 𝒳
  haveI : BorelSpace 𝒳 := ⟨rfl⟩
  haveI := compactSpace_normalCone F hμ
  haveI := connectedSpace_normalCone F hμ
  (SGPT.PSH.VariableComplexAtlas.sourceClassVolume β).toReal

/-- The restricted volume `vol_{𝒳|s(X)}(β)` along a holomorphic map `s : X → 𝒳` (DRWNXZ §2;
used for `s` a section of `μ` over `x ↦ (x, τ)`, whose image is `X_τ`, or the lift of
`x ↦ (x, 0)`, whose image is `X'`). -/
def sectionRestrictedVolume (s : F.carrier → 𝒳)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (β : RealBottChern (m + 1 + 1) 𝒳) : ℝ≥0∞ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  TranscendentalVolumeConcavity.classRestrictedVolume s hs β

/-- The submanifold atlas of the exceptional divisor `ℰ` (a closed submanifold of `𝒳` of
dimension `m + 1`). -/
@[instance_reducible] def exceptionalChartedSpace (hμ : IsNormalConeDeformation F μ) :
    ChartedSpace (ComplexModel (m + 1)) (exceptionalSet F μ) :=
  SubmanifoldChartedSpace.chartedSpace (Nat.le_succ (m + 1)) fun _ hz =>
    regularAtDim_exceptionalSet F hμ hz

/-- `ℰ` is a complex manifold of dimension `m + 1`. -/
theorem isComplexManifold_exceptional (hμ : IsNormalConeDeformation F μ) :
    letI := exceptionalChartedSpace F hμ
    IsComplexManifold (m + 1) (exceptionalSet F μ) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ (m + 1)) fun _ hz =>
    regularAtDim_exceptionalSet F hμ hz

/-- The inclusion `ℰ ↪ 𝒳` is holomorphic. -/
theorem contMDiff_exceptionalInclusion (hμ : IsNormalConeDeformation F μ) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (Subtype.val : exceptionalSet F μ → 𝒳) :=
  SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (m + 1)) fun _ hz =>
    regularAtDim_exceptionalSet F hμ hz

/-- `ℰ` is compact (closed in the compact `𝒳`). -/
theorem compactSpace_exceptional (hμ : IsNormalConeDeformation F μ) :
    CompactSpace (exceptionalSet F μ) := by
  have := compactSpace_normalCone F hμ
  exact isCompact_iff_compactSpace.mp (isClosed_exceptionalSet F hμ).isCompact

/-- The restricted volume `vol_{𝒳|ℰ}(β)` along the exceptional divisor (DRWNXZ §2). -/
def exceptionalRestrictedVolume (hμ : IsNormalConeDeformation F μ)
    (β : RealBottChern (m + 1 + 1) 𝒳) : ℝ≥0∞ :=
  letI := exceptionalChartedSpace F hμ
  haveI := isComplexManifold_exceptional F hμ
  letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  haveI := compactSpace_exceptional F hμ
  TranscendentalVolumeConcavity.classRestrictedVolume Subtype.val
    (contMDiff_exceptionalInclusion F hμ) β

end Deformation

/-! ### The statements -/

/-- **`tok-wn:formula-volume`** (WN21 Theorem 1.6 (1), proved in §4): for `ξ = {θ}` and `ξ_c`
big with Kähler loci meeting `Z` and `0 < c < b`,
`vol(β) = (n + 1)((b - c) vol(ξ) + ∫₀^c vol(ξ_t) dt)`. -/
def DeformationVolumeStatement : Prop :=
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
          deformationVolumeReal F hμ
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)) =
            ((m + 2 : ℕ) : ℝ) * ((b - c) * classVolumeReal F (RealBottChern.ofRepresentative θ) +
              ∫ t in (0 : ℝ)..c, classVolumeReal F (RealBottChern.ofRepresentative θ -
                t • RealBottChern.ofRepresentative E.curvature))

/-- **`tok-wn:formula-volume`, second half** (WN21 Corollary 4.7): for `b > c + 1`,
`vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)`, where `β - {X₀}` is the class `β` for the parameter
`b - 1` (`{X₀} = {(π_{ℙ¹} μ)^*ω_FS}`). -/
def DeformationVolumeDifferenceStatement : Prop :=
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
          deformationVolumeReal F hμ
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)) -
            deformationVolumeReal F hμ
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ (b - 1) c Eℰ)) =
            ((m + 2 : ℕ) : ℝ) * classVolumeReal F (RealBottChern.ofRepresentative θ)

/-- **`tok-wn:formula-fibre`** (WN21 Theorem 1.6 (2)): for `τ ≠ 0` and the section `s` of `μ`
over `x ↦ (x, τ)` (image `X_τ`), `vol_{𝒳|X_τ}(β) = vol(ξ)`; and every `θ̃`-psh potential `w`
with minimal singularities restricts to a potential with minimal singularities on `X_τ ≅ X`
(for the form `s^*θ̃`, a representative of `ξ`). -/
def FibreRestrictedVolumeStatement : Prop :=
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
        ∀ p : ProjectiveLine, p ≠ projectiveZero → ∀ (s : F.carrier → 𝒳)
          (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s),
          (∀ x, μ (s x) = (x, p)) →
            (sectionRestrictedVolume F s hs
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal =
              classVolumeReal F (RealBottChern.ofRepresentative θ) ∧
            ∀ w : 𝒳 → EReal, IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ).val w →
              MoreSingularOn (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) w
                univ →
              IsThetaPshPotential
                  (ClosedRealOneOneForm.pullback hs (deformationForm F hμ.contMDiff θ b c Eℰ)).val
                  (fun x => w (s x)) ∧
                MoreSingularOn (thetaPshSupremum
                    (ClosedRealOneOneForm.pullback hs (deformationForm F hμ.contMDiff θ b c Eℰ)).val)
                  (fun x => w (s x)) univ

/-- **`tok-wn:formula-X-prime`** (WN21 Theorem 1.6 (3), identity (4.1) and Lemma 4.8): for the
lift `ι'` of `x ↦ (x, 0)` (image the strict transform `X'`), `vol_{𝒳|X'}(β) = vol(ξ_c)`. -/
def StrictTransformRestrictedVolumeStatement : Prop :=
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
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal =
              classVolumeReal F (RealBottChern.ofRepresentative θ -
                c • RealBottChern.ofRepresentative E.curvature)

/-- **`tok-wn:formula-E`** (WN21 Theorem 1.6 (4), identity (4.2)):
`vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Z}(ξ_t) dt`. -/
def ExceptionalRestrictedVolumeStatement : Prop :=
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
          (exceptionalRestrictedVolume F hμ
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))).toReal =
            ((m + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..c,
              (firstFlagRestrictedVolume F (RealBottChern.ofRepresentative θ -
                t • RealBottChern.ofRepresentative E.curvature)).toReal

/-- The package statement of WN-VF: WN21 Theorem 1.6, items (1)--(4). -/
def WNVolumeStatement : Prop :=
  DeformationVolumeStatement F ∧ FibreRestrictedVolumeStatement F ∧
    StrictTransformRestrictedVolumeStatement F ∧ ExceptionalRestrictedVolumeStatement F

/-! ### The elementary corollary -/

/-- **`tok-wn:formula-volume`, second half, from the first** (WN21 Corollary 4.7): subtracting
the volume formula for the parameters `b` and `b - 1 > c`, the integral terms cancel. -/
theorem deformationVolumeDifference_of_volume (h : DeformationVolumeStatement F) :
    DeformationVolumeDifferenceStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  rw [h E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc (by linarith) hξ hξc,
    h E hE hE0 𝒳 μ hμ Eℰ hEℰ θ (b - 1) c hc (by linarith) hξ hξc]
  ring

end SGPT.Okounkov.TranscendentalWN
