import SGPT.Okounkov.TranscendentalWNStatement
import SGPT.Toric.ProjectiveLineNativeManifold
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.BlowupStrictSubmanifold
import SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# The deformation of `X` to the normal cone of `Y₁`: objects and statements (package WN-DEF)

Blueprint chapter `claude-tok-wn` (nodes `tok-wn:deformation`, `tok-wn:beta`,
`tok-wn:beta-big`, `tok-wn:blowup-lelong`) and its supplement `claude-tok-wn-def`; source
D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted volumes of
big classes*, arXiv:2103.03660 (WN21), §1.1, §1.6 and §4 (`references/wn21-restricted-volume`).

Let `X` be the compact Kähler manifold of the flag geometry `F` (dimension `n = m + 1`) and
`Z = Y₁ = F.flag 1` its first flag member, a connected smooth hypersurface.  The deformation of
`X` to the normal cone of `Z` is the blow-up

  `μ : 𝒳 → 𝒫 = X × ℙ¹`  along the codimension-two submanifold `Z × {0}`.

This file fixes the objects and records, as `def … : Prop`, the properties that the volume
formulas of package WN-VF consume.  **Nothing is asserted here.**  The proofs live in the files
`TranscendentalWNDeformation*.lean` of the same package (their status is recorded in the
package report).

## Objects

* `ProjectiveLine = ℙ¹ = ℙ(ℂ²)` with the native complex structure of `SGPT.Toric`
  (`projectiveNativeChartedSpace`, Fubini--Study form `projectiveNativeFSClosedForm`), its points
  `projectiveZero = [0 : 1]` (`τ = 0`) and `projectiveInfinity = [1 : 0]`, and the affine
  coordinate `projectiveAffine p = p₀ / p₁` (`τ`; the junk value `0` at `∞`).
* `X × ℙ¹` is a complex manifold of dimension `m + 1 + 1` through the scoped instance
  `SGPT.Foundations.Analysis.Pending.ProductComplexManifold.chartedSpace`.
* `deformationCentre F = Z × {0}` and `centralBase F = X × {0}`.
* `IsNormalConeDeformation F μ`: `μ : 𝒳 → X × ℙ¹` is a blow-up of `X × ℙ¹` along `Z × {0}`
  (TN's universal-property predicate `IsBlowupAlong`; any two are uniquely isomorphic over
  `X × ℙ¹`, `Pending.BlowupUniqueness`).
* For such `μ`: the exceptional divisor `ℰ = μ⁻¹(Z × {0})` (`exceptionalSet`), the central fibre
  `X₀ = μ⁻¹(X × {0})` (`centralFibre`), the strict transform `X' = closure μ⁻¹(X × {0} \ Z × {0})`
  of `X × {0}` (`strictCentralFibre`, TN's `geoStrictTransform`), the fibres
  `X_τ = μ⁻¹(X × {τ})` (`fibreAt`), and the projections `π_X ∘ μ`, `π_{ℙ¹} ∘ μ`.
* `baseExceptionalWeight F E (x, [v₀ : v₁]) = (|s_Z(x)|²_h |v₁|² + |v₀|²) / (|v₀|² + |v₁|²)` for
  a metric `E` of `𝒪(Z)` (weight `log |s_Z|²_h`); in the affine coordinate it is
  `(|s_Z|²_h + |τ|²) / (1 + |τ|²)`, equal to `1` at `τ = ∞`.  Its logarithm, pulled back by `μ`,
  is the circle-invariant weight `log |s_ℰ|²` of the metric on `𝒪(ℰ)` used by WN21 §4.
* `deformationForm θ b c Eℰ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ` (`tok-wn:beta`, the form
  `θ̃` of WN21 §4), representing `β = (π_X μ)^*ξ + b{X₀} - c{ℰ}`.

## Statements

* `DeformationExistsStatement` — a deformation to the normal cone exists
  (`tok-wn:deformation`, existence).
* `DeformationGeometryStatement` — every one is a compact connected Kähler manifold, `μ` is an
  isomorphism off `Z × {0}`, the fibres `X_τ` (`τ ≠ 0`) are copies of `X`, `X'` is the image of
  the unique lift of `x ↦ (x, 0)` (so `X' ≅ X`, and `X' ∩ ℰ` is the copy of `Z`),
  `X₀ = X' ∪ ℰ`, and `X'`, `ℰ` are closed submanifolds of dimension `m + 1`
  (`tok-wn:deformation`, geometry).
* `CentralFibreDivisorStatement` — `X₀ = X' + ℰ` as divisors: the ideal of `X × {0}` pulls
  back to the product of the ideals of `X'` and of `ℰ`.
* `ExceptionalMetricStatement` — `𝒪(ℰ)` carries a smooth metric whose weight is
  `log ((|s_Z|²_h + |τ|²) / (1 + |τ|²)) ∘ μ` (so it is circle invariant, `≤ 0`, and restricts
  to `log |s_Z|²_h` on `X' ≅ X`) and whose curvature restricts to that of `E` on `X'`.
* `BetaBigStatement` — `tok-wn:beta-big` (WN21 Proposition 4.1).
* `BlowupLelongStatement` — `tok-wn:blowup-lelong`.

Conventions: Lelong numbers are TN's `lelongNumber` (`ν(log ‖z‖, 0) = 1`), so the blueprint's
`ν ≥ c` with `log |s_ℰ|²` corresponds here to `ν ≥ c` with `log ‖σ_ℰ‖` for a local generator
`σ_ℰ` of the ideal of `ℰ`.  Bigness is `SGPT.PSH.BookCurrent.IsBig` and the non-Kähler locus
is TN's `nonKahlerLocus`, as in `TranscendentalWNStatement`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### The projective line -/

/-- The projective line `ℙ¹ = ℙ(ℂ²)`, with the native complex structure of `SGPT.Toric`. -/
abbrev ProjectiveLine : Type := Projectivization ℂ (Fin 2 → ℂ)

/-- The point `τ = 0`, i.e. `[0 : 1]`. -/
def projectiveZero : ProjectiveLine :=
  SGPT.Toric.projectiveLineHomeomorph ((0 : ℂ) : OnePoint ℂ)

/-- The point `τ = ∞`, i.e. `[1 : 0]`. -/
def projectiveInfinity : ProjectiveLine :=
  SGPT.Toric.projectiveLineHomeomorph (OnePoint.infty : OnePoint ℂ)

/-- The affine coordinate `τ = p₀ / p₁` on `ℙ¹ \ {∞}` (it takes the junk value `0` at `∞`). -/
def projectiveAffine (p : ProjectiveLine) : ℂ := p.rep 0 / p.rep 1

/-! ### The base `X × ℙ¹` and the centre `Z × {0}` -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The centre `Z × {0} ⊆ X × ℙ¹` of the deformation to the normal cone (`Z = Y₁`). -/
def deformationCentre : Set (F.carrier × ProjectiveLine) :=
  F.flag (1 : Fin (m + 2)) ×ˢ {projectiveZero}

/-- The central base fibre `X × {0} ⊆ X × ℙ¹`. -/
def centralBase : Set (F.carrier × ProjectiveLine) :=
  univ ×ˢ {projectiveZero}

/-! ### A deformation to the normal cone and its fibres -/

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳]

/-- **`tok-wn:deformation`**: `μ : 𝒳 → X × ℙ¹` is the blow-up of `X × ℙ¹` along `Z × {0}`
(WN21 §1.1: the deformation of `X` to the normal cone of `Z`). -/
def IsNormalConeDeformation (μ : 𝒳 → F.carrier × ProjectiveLine) : Prop :=
  IsBlowupAlong (m + 1 + 1) (deformationCentre F) μ

/-- The exceptional divisor `ℰ = μ⁻¹(Z × {0})`. -/
def exceptionalSet (μ : 𝒳 → F.carrier × ProjectiveLine) : Set 𝒳 :=
  μ ⁻¹' deformationCentre F

/-- The central fibre `X₀ = μ⁻¹(X × {0})`. -/
def centralFibre (μ : 𝒳 → F.carrier × ProjectiveLine) : Set 𝒳 :=
  μ ⁻¹' centralBase F

/-- The strict transform `X' = closure μ⁻¹(X × {0} \ Z × {0})` of `X × {0}`. -/
def strictCentralFibre (μ : 𝒳 → F.carrier × ProjectiveLine) : Set 𝒳 :=
  BlowupStrictSubmanifold.geoStrictTransform μ (deformationCentre F) (centralBase F)

/-- The fibre `X_τ = μ⁻¹(X × {τ})` over a point `τ ∈ ℙ¹`. -/
def fibreAt (μ : 𝒳 → F.carrier × ProjectiveLine) (p : ProjectiveLine) : Set 𝒳 :=
  μ ⁻¹' (univ ×ˢ {p})

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- `π_X ∘ μ` is holomorphic. -/
theorem contMDiff_deformationProjX {μ : 𝒳 → F.carrier × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (fun z => (μ z).1) :=
  ProductComplexManifold.contMDiff_fst.comp hμ

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- `π_{ℙ¹} ∘ μ` is holomorphic. -/
theorem contMDiff_deformationProjP1 {μ : 𝒳 → F.carrier × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel 1) ∞ (fun z => (μ z).2) :=
  ProductComplexManifold.contMDiff_snd.comp hμ

/-- **`tok-wn:beta`**: the circle-invariant representative
`θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ` of `β = (π_X μ)^*{θ} + b{X₀} - c{ℰ}`
(WN21 §1.6 and §4), for a metric `Eℰ` of `𝒪(ℰ)` with curvature `η_ℰ`. -/
def deformationForm {μ : 𝒳 → F.carrier × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) : ClosedRealOneOneForm (m + 1 + 1) 𝒳 :=
  ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ) θ +
    b • ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ)
      SGPT.Toric.projectiveNativeFSClosedForm -
    c • Eℰ.curvature

end Deformation

/-! ### The circle-invariant weight of the exceptional divisor -/

/-- `(|s_Z(x)|²_h |v₁|² + |v₀|²) / (|v₀|² + |v₁|²)` at `(x, [v₀ : v₁])`, for a metric `E` of
`𝒪(Z)` with weight `E.weight = log |s_Z|²_h`; in the affine coordinate `τ = v₀ / v₁` this is
`(|s_Z|²_h + |τ|²) / (1 + |τ|²)`.  Its logarithm pulled back by `μ` is the weight of the metric
of `𝒪(ℰ)` (`ExceptionalMetricStatement`). -/
def baseExceptionalWeight (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (q : F.carrier × ProjectiveLine) : ℝ :=
  ((EReal.exp (E.weight q.1)).toReal * ‖q.2.rep 1‖ ^ 2 + ‖q.2.rep 0‖ ^ 2) /
    (‖q.2.rep 0‖ ^ 2 + ‖q.2.rep 1‖ ^ 2)

/-! ### The statements -/

/-- **`tok-wn:deformation`, existence**: the blow-up of `X × ℙ¹` along `Z × {0}` exists. -/
def DeformationExistsStatement : Prop :=
  ∃ (𝒳 : Type u) (_ : TopologicalSpace 𝒳) (_ : ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳)
    (_ : IsComplexManifold (m + 1 + 1) 𝒳) (μ : 𝒳 → F.carrier × ProjectiveLine),
    IsNormalConeDeformation F μ

/-- **`tok-wn:deformation`, geometry** (WN21 §1.1 and the beginning of §4).  For every
deformation to the normal cone `μ : 𝒳 → X × ℙ¹`:
1. `𝒳` is a compact connected Kähler manifold;
2. `μ` is an isomorphism over the complement of `Z × {0}`;
3. for `τ ≠ 0` the fibre `X_τ` is the image of a holomorphic section `x ↦ μ⁻¹(x, τ)` (so
   `X_τ ≅ X`);
4. the strict transform `X'` is the image of a holomorphic lift `ι'` of `x ↦ (x, 0)`, and
   `ι'⁻¹(ℰ) = Z` (so `μ|_{X'} : X' → X × {0} ≅ X` is bijective and `X' ∩ ℰ` is a copy of `Z`);
5. `X₀ = X' ∪ ℰ`;
6. `X'` and `ℰ` are closed submanifolds of dimension `m + 1` (smooth hypersurfaces). -/
def DeformationGeometryStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine),
    IsNormalConeDeformation F μ →
      (CompactSpace 𝒳 ∧ ConnectedSpace 𝒳 ∧ Nonempty (KahlerBackground (m + 1 + 1) 𝒳)) ∧
      IsIsomorphismOver (m + 1 + 1) μ (deformationCentre F)ᶜ ∧
      (∀ p : ProjectiveLine, p ≠ projectiveZero → ∃ s : F.carrier → 𝒳,
        ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s ∧
          (∀ x, μ (s x) = (x, p)) ∧ range s = fibreAt F μ p) ∧
      (∃ ι : F.carrier → 𝒳,
        ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι ∧
          (∀ x, μ (ι x) = (x, projectiveZero)) ∧ range ι = strictCentralFibre F μ ∧
          ι ⁻¹' exceptionalSet F μ = F.flag (1 : Fin (m + 2))) ∧
      centralFibre F μ = strictCentralFibre F μ ∪ exceptionalSet F μ ∧
      (IsClosed (strictCentralFibre F μ) ∧
        ∀ z ∈ strictCentralFibre F μ,
          RegularAtDim (n := m + 1 + 1) (strictCentralFibre F μ) z (m + 1)) ∧
      (IsClosed (exceptionalSet F μ) ∧
        ∀ z ∈ exceptionalSet F μ, RegularAtDim (n := m + 1 + 1) (exceptionalSet F μ) z (m + 1))

/-- **`tok-wn:deformation`, `X₀ = X' + ℰ` as divisors**: the ideal of `X × {0}` pulls back to
the product of the ideal sheaves of `X'` and of `ℰ` (germwise). -/
def CentralFibreDivisorStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine),
    IsNormalConeDeformation F μ →
      ∀ (z : 𝒳) (f : 𝒳 → ℂ),
        (GermIdeal.pullback (m := m + 1 + 1) μ
            (vanishingIdeal (n := m + 1 + 1) (centralBase F))).mem z f ↔
          ((vanishingIdeal (n := m + 1 + 1) (strictCentralFibre F μ)).mul
            (vanishingIdeal (n := m + 1 + 1) (exceptionalSet F μ))).mem z f

/-- **`tok-wn:deformation`, the metric of `𝒪(ℰ)`** (WN21 §4: a circle-invariant metric with
`|s_ℰ| ≤ 1` restricting to that of `𝒪(Z)` on `X' ≅ X`).  For a metric `E` of `𝒪(Z)` with
`|s_Z|_h ≤ 1` and every deformation `μ`, there is a metric `Eℰ` of `𝒪(ℰ)` (a metered divisor
whose divisor is the exceptional divisor of `μ`) whose weight is
`log |s_ℰ|² = log ((|s_Z|²_h + |τ|²) / (1 + |τ|²)) ∘ μ` (`baseExceptionalWeight`), and whose
curvature restricts, along every holomorphic lift `ι'` of `x ↦ (x, 0)`, to the curvature of `E`.
The weight formula gives circle invariance, `log |s_ℰ|² ≤ 0` and `log |s_ℰ|² ∘ ι' = log |s_Z|²_h`. -/
def ExceptionalMetricStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ),
      ∃ Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳,
        DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ ∧
        Eℰ.support = exceptionalSet F μ ∧
        (∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z)))) ∧
        ∀ (ι : F.carrier → 𝒳)
          (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
            (ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.GeometricallyEq E.curvature.val

/-- **`tok-wn:beta-big`** (WN21 Proposition 4.1).  Let `ξ = {θ}` be big with Kähler locus
meeting `Z`, `0 < c < b`, and `ξ_c = ξ - c{Z}` big.  For every deformation `μ` and every metric
`Eℰ` of `𝒪(ℰ)`, the class `β = {θ̃}` (`deformationForm`) is big, and its Kähler locus meets every
fibre `X_τ` (`τ ≠ 0`), the strict transform `X'` and the exceptional divisor `ℰ`. -/
def BetaBigStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] [CompactSpace 𝒳]
      (μ : 𝒳 → F.carrier × ProjectiveLine) (hμ : IsNormalConeDeformation F μ)
      (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
          SGPT.PSH.BookCurrent.IsBig
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)) ∧
            (∀ p : ProjectiveLine, p ≠ projectiveZero → ∃ z ∈ fibreAt F μ p,
              z ∉ nonKahlerLocus
                (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))) ∧
            (∃ z ∈ strictCentralFibre F μ, z ∉ nonKahlerLocus
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))) ∧
            ∃ z ∈ exceptionalSet F μ, z ∉ nonKahlerLocus
              (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ))

/-- **`tok-wn:blowup-lelong`** (standard; used in WN21 Proposition 4.5).  Let
`μ : M̃ → M` be the blow-up of a complex manifold along a (nowhere dense closed) submanifold `V`
with exceptional divisor `ℰ = μ⁻¹ V`, and `φ` a quasi-psh function on `M` (`θ`-psh for a smooth
closed real `(1,1)`-form `θ`) whose Lelong number is at least `c` at every point of `V`.  Then
near every point of `ℰ`, `μ^*φ ≤ c log ‖σ_ℰ‖ + C` for a local generator `σ_ℰ` of the ideal of
`ℰ`, i.e. `μ^*φ - c log |s_ℰ|` is bounded above near every point of `ℰ` (TN normalization of
Lelong numbers, `ν(log ‖z‖, 0) = 1`). -/
def BlowupLelongStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (M' : Type u) [TopologicalSpace M']
    [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] (V : Set M) (μ : M' → M)
    (hμ : IsBlowupAlong n V μ) (θ : ClosedRealOneOneForm n M) (φ : M → EReal),
    IsThetaPshPotential θ.val φ → ∀ c : ℝ≥0,
      (∀ x ∈ V, (c : ℝ≥0∞) ≤ lelongNumber (n := n) φ x) →
        ∀ p ∈ μ ⁻¹' V, ∃ U : Set M', IsOpen U ∧ p ∈ U ∧ ∃ σ : M' → ℂ,
          MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) σ U ∧
          (∀ y ∈ U, ∀ f, (BlowupExceptionalDivisor.exceptionalDivisor hμ).ideal.mem y f ↔
            IsInSpanAt (n := n) (· = σ) y f) ∧
          ∃ C : ℝ, ∀ y ∈ U, φ (μ y) ≤ (((c : ℝ) * Real.log ‖σ y‖ + C : ℝ) : EReal)

/-- The package statement of WN-DEF: everything the volume formulas (WN-VF) consume. -/
def WNDeformationStatement : Prop :=
  DeformationExistsStatement F ∧ DeformationGeometryStatement F ∧
    CentralFibreDivisorStatement F ∧ ExceptionalMetricStatement F ∧ BetaBigStatement F ∧
    BlowupLelongStatement.{u}

end SGPT.Okounkov.TranscendentalWN
