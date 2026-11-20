import SGPT.Okounkov.TranscendentalWNKeyStatement
import SGPT.Okounkov.TranscendentalWNRegStatement

/-!
# Measure control on the deformation to the normal cone: statement (package WN, lane WN-CONV6)

Blueprint chapter `claude-tok-wn`, node `tok-wn:measure-control` (sub-lemmas in
`claude-tok-wn-conv6`); source D. Witt Nyström, *Deformations of Kähler manifolds to normal
bundles and restricted volumes of big classes*, arXiv:2103.03660 (WN21), §6: Propositions
6.1--6.4 and Corollary 6.5 (`references/wn21-restricted-volume`).

Notation as in `TranscendentalWNVolumeStatement` and `TranscendentalWNKeyStatement`:
`μ : 𝒳 → X × ℙ¹` is the deformation of `X` to the normal cone of `Z = Y₁`, `X_τ` the fibre over
`τ ∈ ℙ¹`, parametrized for `τ ≠ 0` by the holomorphic section `s` of `μ` over `x ↦ (x, τ)`;
for `ξ = {θ}` and `0 < c`, `c + 1 < b`, `β = {θ̃}` with
`θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ` (`deformationForm`).

## The objects of WN21 §6

* `IsWNCutoff χ`: `χ : ℝ → ℝ` is smooth and convex, `χ(x) = x` for `x ≥ 0` and
  `χ(x) = eˣ - 1` for `x ≤ -1`.
* `cutoffObstacleLine χ k : ℙ¹ → ℝ`: the obstacle
  `g_k(τ) = χ(log |τ|² + k) - k - log(1 + |τ|²)` in the affine coordinate `τ` (`projectiveAffine`),
  with its continuous values `g_k(0) = -1 - k` (`χ(-∞) = -1`) and `g_k(∞) = 0`.  The factor
  `χ(log |τ|² + k)` is written `cutoffLog χ (eᵏ |τ|²)`, where `cutoffLog χ r = χ(log r)` for
  `r ≠ 0` and `cutoffLog χ 0 = -1`.
* `cutoffObstacle μ χ k = g_k ∘ π_{ℙ¹} ∘ μ`, the obstacle on `𝒳`.
* `cutoffEnvelope θ̃ μ χ k = P_{θ̃}(g_k)` (`u_k`, the rooftop envelope of the obstacle, as in
  `TranscendentalWNReg`), and `cutoffContactSet θ̃ μ χ k = {u_k = g_k}` (`D_k`).
* `fibreContactMass θ̃ μ χ k s hs = ∫_{X_τ ∩ D_k} θ̃ⁿ` (`I_k(τ)`): for a holomorphic map
  `s : X → 𝒳` (the section over `x ↦ (x, τ)`), the measure of `s⁻¹(D_k)` for the top power of
  `s^*θ̃` (`TranscendentalWNReg.positiveTopMeasure` against the Kähler form `ω` of `X`; on the
  contact set the density of `θ̃ⁿ|_{X_τ}` is nonnegative, `tok-wn:contact-positivity`, so this is the
  genuine measure `𝟙_{X_τ ∩ D_k} θ̃ⁿ`).
* `affineLinePoint τ ∈ ℙ¹`, the point with affine coordinate `τ ∈ ℂ`.

## The statement

`MeasureControlStatement F` (WN21 Corollary 6.5, the conclusion of `tok-wn:measure-control` in
the form WN21 §7 consumes it): under the hypotheses of `KeyConvergenceStatement` (`c + 1 < b`;
`ξ` and `ξ_c` big with Kähler loci meeting `Z`), for every cutoff `χ` there are `τ_k ∈ ℂ \ {0}`
with `e^{k/2} |τ_k| → 0` such that, for every choice of the sections `s_k` of `μ` over
`x ↦ (x, τ_k)`, `I_k(τ_k) → vol(ξ)`.

This file contains the definitions and the **statement only** (`def … : Prop`); nothing is
asserted.  The statement is the interface between lanes WN-CONV6 (WN21 §6, which proves it) and
WN-CONV7 (WN21 §7, which consumes it in `KeyConvergenceStatement`).
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

/-! ### The cutoff `χ` and the obstacles `g_k` -/

/-- **The cutoff of WN21 §6**: `χ : ℝ → ℝ` smooth and convex with `χ(x) = x` for `x ≥ 0` and
`χ(x) = eˣ - 1` for `x ≤ -1`. -/
structure IsWNCutoff (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ χ
  convexOn : ConvexOn ℝ univ χ
  eq_of_nonneg : ∀ x, 0 ≤ x → χ x = x
  eq_of_le_neg_one : ∀ x, x ≤ -1 → χ x = Real.exp x - 1

/-- The point of `ℙ¹` with affine coordinate `τ ∈ ℂ` (i.e. `[τ : 1]`). -/
def affineLinePoint (τ : ℂ) : ProjectiveLine :=
  SGPT.Toric.projectiveLineHomeomorph (τ : OnePoint ℂ)

/-- `χ(log r)`, extended by its limit `-1` at `r = 0` (`χ(x) = eˣ - 1` for `x ≤ -1`). -/
def cutoffLog (χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then -1 else χ (Real.log r)

/-- **The obstacle `g_k` on `ℙ¹`** (WN21 §6): `g_k(τ) = χ(log |τ|² + k) - k - log(1 + |τ|²)` in
the affine coordinate `τ` (`χ(log |τ|² + k) = cutoffLog χ (eᵏ |τ|²)`), with the continuous values
`g_k(0) = -1 - k` and `g_k(∞) = 0`. -/
def cutoffObstacleLine (χ : ℝ → ℝ) (k : ℕ) (p : ProjectiveLine) : ℝ :=
  haveI := Classical.propDecidable (p = projectiveInfinity)
  if p = projectiveInfinity then 0 else
    cutoffLog χ (Real.exp k * ‖projectiveAffine p‖ ^ 2) - k -
      Real.log (1 + ‖projectiveAffine p‖ ^ 2)

section Deformation

variable {X : Type*} {N : ℕ} {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳]

/-- **The obstacle `g_k` on `𝒳`**: `g_k ∘ π_{ℙ¹} ∘ μ`. -/
def cutoffObstacle (μ : 𝒳 → X × ProjectiveLine) (χ : ℝ → ℝ) (k : ℕ) (z : 𝒳) : ℝ :=
  cutoffObstacleLine χ k (μ z).2

/-- **The envelope `u_k = P_{θ̃}(g_k)`** (WN21 §6): the rooftop envelope
`(sup {v ∈ PSH(𝒳, θ̃) : v ≤ g_k})^*` of the obstacle `g_k`. -/
def cutoffEnvelope (θ : ClosedRealOneOneForm N 𝒳) (μ : 𝒳 → X × ProjectiveLine) (χ : ℝ → ℝ)
    (k : ℕ) : 𝒳 → EReal :=
  rooftopEnvelope θ.val fun z => (cutoffObstacle μ χ k z : EReal)

/-- **The contact set `D_k = {u_k = g_k}`** (WN21 §6). -/
def cutoffContactSet (θ : ClosedRealOneOneForm N 𝒳) (μ : 𝒳 → X × ProjectiveLine) (χ : ℝ → ℝ)
    (k : ℕ) : Set 𝒳 :=
  {z | cutoffEnvelope θ μ χ k z = (cutoffObstacle μ χ k z : EReal)}

end Deformation

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`I_k(τ) = ∫_{X_τ ∩ D_k} θ̃ⁿ`** (WN21 §6), along a holomorphic map `s : X → 𝒳` (used for the
section of `μ` over `x ↦ (x, τ)`, whose image is `X_τ`): the measure of `s⁻¹(D_k)` for the top
power of `s^*θ̃` (`TranscendentalWNReg.positiveTopMeasure`, against the Kähler form of `X`; Borel
structure). -/
def fibreContactMass {𝒳 : Type u} [TopologicalSpace 𝒳]
    [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
    (θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (μ : 𝒳 → F.carrier × ProjectiveLine)
    (χ : ℝ → ℝ) (k : ℕ) (s : F.carrier → 𝒳)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s) : ℝ≥0∞ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure F.omega
    (ClosedRealOneOneForm.pullback hs θ) (s ⁻¹' cutoffContactSet θ μ χ k)

/-! ### The statement -/

/-- **`tok-wn:measure-control`** (WN21 §6, Corollary 6.5, in the form WN21 §7 consumes it): under
the hypotheses of `KeyConvergenceStatement` (`0 < c`, `c + 1 < b`, `ξ = {θ}` and `ξ_c` big with
Kähler loci meeting `Z`), for every cutoff `χ` (`IsWNCutoff`) there are `τ_k ∈ ℂ \ {0}` with
`e^{k/2} |τ_k| → 0` such that for all holomorphic sections `s_k` of `μ` over `x ↦ (x, τ_k)`,
`I_k(τ_k) = ∫_{X_{τ_k} ∩ D_k} θ̃ⁿ → vol(ξ)`, where `D_k = {P_{θ̃}(g_k) = g_k}`. -/
def MeasureControlStatement : Prop :=
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
        ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∃ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) ∧
            Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) ∧
            ∀ (s : ℕ → F.carrier → 𝒳)
              (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
                (s k)),
              (∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) →
                Tendsto (fun k => fibreContactMass F (deformationForm F hμ.contMDiff θ b c Eℰ) μ
                    χ k (s k) (hs k)) atTop
                  (𝓝 (ENNReal.ofReal (classVolumeReal F (RealBottChern.ofRepresentative θ))))

end SGPT.Okounkov.TranscendentalWN
