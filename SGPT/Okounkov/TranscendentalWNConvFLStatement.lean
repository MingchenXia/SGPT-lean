import SGPT.Okounkov.TranscendentalWNConv7Core
import SGPT.Okounkov.TranscendentalWNEnvelopeContact

/-!
# The fibre limit of WN21 §7: decomposition into sub-statements

Blueprint `claude-tok-wn-conv7`, node `tok-wn-conv7:fibre-limit`, refined in `claude-tok-wn-fl`;
source D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted
volumes of big classes*, arXiv:2103.03660 (WN21), §7: Proposition 7.1, Lemma 7.5, Corollary 7.6,
Proposition 7.4, the estimate (eqeq) and the final limit of the proof of the hard inequality of
Theorem 1.7 (`references/wn21-restricted-volume`).

Notation of `TranscendentalWNConv7Core`: `μ : 𝒳 → X × ℙ¹` the deformation to the normal cone of
`Z = Y₁`, `X'` the strict transform of `X × {0}` (image of the lift `ι` of `x ↦ (x, 0)`), `ℰ` the
exceptional divisor, `X₀ = X' ∪ ℰ`, `Θ = θ̃ + εη'`, `Ψ` the perturbed weight with its log resolution
`π : 𝒵 → 𝒳` (`Ψ ∘ π = ψ_{D'} + h`, `ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler), `g_k = cutoffObstacle μ χ k`,
`v_k = P_Θ[Ψ](g_k)`, `ν_k = ⟨((Θ + dd^c v_k)|_{X_{τ_k}})ⁿ⟩` (a measure on `X`, through the section
`s_k`), `v_{X'}`, `v_ℰ` the limits of `v_k + k` on `X'` and `ℰ` (`centralLimitPotential`) and
`λ' = ⟨(Θ|_{X'} + dd^c v_{X'})ⁿ⟩`, `λ_ℰ = ⟨(Θ|_ℰ + dd^c v_ℰ)ⁿ⟩`.

## The decomposition

`FibreLimitStatement F` (`tok-wn-conv7:fibre-limit`) follows
(`TranscendentalWNConvFLReduction.fibreLimit_of_fibreVolumeSmall_of_local`) from three statements:

* `FibreVolumeSmallStatement F` (`tok-wn-fl:small-neighbourhood`, WN21 (eqeq)): near
  `(X' ∩ ℰ) ∪ K`, for any `K ⊆ X₀` whose traces on `X'` and `ℰ` are pluripolar, the fibre volumes
  `∫_{X_τ ∩ U} (Θ|_{X_τ})ⁿ` are uniformly small for small `τ ≠ 0`.  (Combined with the bound of
  the Monge--Ampère measure on contact sets by the obstacle, `tok-wn:contact-upper`, this makes the
  contact masses small there.)
* `StrictFibreConvergenceStatement F` (`tok-wn-fl:strict-convergence`, WN21 Proposition 7.4 near
  `X' \ ℰ`) and `ExceptionalFibreConvergenceStatement F` (`tok-wn-fl:exceptional-convergence`,
  near `ℰ \ X'`): every point of `X₀ \ ((X' ∩ ℰ) ∪ {Ψ = -∞})` has a neighbourhood `W` such that for
  every continuous `ρ ≥ 0` supported in `W` and every subsequence `k_l` with
  `Σ_l e^{k_l/2}|τ_{k_l}| < ∞`,
  `limsup_l ∫ ρ ∘ s_{k_l} dν_{k_l} ≤ ∫ ρ ∘ ι dλ' + ∫_ℰ ρ dλ_ℰ`
  (WN21 proves the convergence of the measures; the upper bound is what the final limit uses).

The strict part is decomposed further, chart-free (the product structure
`μ⁻¹((X \ Z) × ℂ) ≅ (X \ Z) × ℂ`):

* `PrescribedEnvelopeResolutionStatement` (`tok-wn-fl:resolution-identity`, WN21 Proposition 7.1):
  `v ∘ π = P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π` for every continuous obstacle `g`;
* `StrictDiscLaplacianStatement F` (`tok-wn-fl:disc-laplacian`, WN21 Lemma 7.5 restricted to the
  discs `t ↦ μ⁻¹(x, t)`, `x` near `x₀ ∉ Z`, for `k ≥ k₀`): `|v_k + k| ≤ C` on `|t| ≤ e^{-k/2}`, and
  there `v_k` is a uniform limit of smooth functions of `t` with `-C ≤ Δ_t ≤ C e^k`;
* `StrictLipschitzStatement F` (`tok-wn-fl:strict-lipschitz`, WN21 Corollary 7.6 near `X' \ ℰ`, for
  `k ≥ k₀`): `|v_k(z) - v_k(ι x)| ≤ C e^{k/2} |t|` for `μ z = (x, t)`, `0 < |t| ≤ e^{-k/2}/2`, and
  `v_k(ι x) + k ≥ -C`.

The threshold `k₀` is necessary (lane WN-FL3: for small `k` the disc may meet a pole of `Ψ`).

This file contains definitions and **statements only**; nothing is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Laplacian
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore

/-! ### Test masses of restricted non-pluripolar measures -/

section TestMass

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [CompactSpace V] {𝒳 : Type*} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- `∫_V ρ ∘ j d⟨(j^*Θ + dd^c w)ᵏ⟩` for a holomorphic `j : V → 𝒳`, a genuine `j^*Θ`-psh potential
`w` on the compact manifold `V` (Borel structure) and a test function `ρ ≥ 0` on `𝒳`. -/
def restrictedTestMass {j : V → 𝒳} (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (w : V → EReal)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj Θ).val w) (ρ : 𝒳 → ℝ) : ℝ≥0∞ :=
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  ∫⁻ y, ENNReal.ofReal (ρ (j y)) ∂(diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hj Θ) w hw)

end TestMass

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The test mass `∫ ρ ∘ ι dλ' + ∫_ℰ ρ dλ_ℰ` of the limit measures on `X'` and on `ℰ`. -/
def centralLimitTestMass {𝒳 : Type u} [TopologicalSpace 𝒳]
    [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
    {μ : 𝒳 → F.carrier × ProjectiveLine} (hμ : IsNormalConeDeformation F μ)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (χ : ℝ → ℝ) (Ψ : 𝒳 → EReal) (ι : F.carrier → 𝒳)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (centralLimitPotential Θ μ χ Ψ ι))
    (hℰ : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
        (centralLimitPotential Θ μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳)))
    (ρ : 𝒳 → ℝ) : ℝ≥0∞ :=
  restrictedTestMass hι Θ (centralLimitPotential Θ μ χ Ψ ι) hX' ρ +
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    haveI := compactSpace_exceptional F hμ
    restrictedTestMass (contMDiff_exceptionalInclusion F hμ) Θ
      (centralLimitPotential Θ μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳)) hℰ ρ

/-! ### The smallness estimate (eqeq) -/

/-- **`tok-wn-fl:small-neighbourhood`** (WN21 §7, estimate (eqeq) in the proof of the hard
inequality of Theorem 1.7, generalized from `K = X₀ ∩ {Ψ = -∞}`): for every closed real
`(1,1)`-form `Θ` on `𝒳`, every `K ⊆ X₀` whose traces `ι⁻¹(K) ⊆ X` and `K ∩ ℰ` are pluripolar, and
every `δ > 0`, there are an open `U ⊇ (X' ∩ ℰ) ∪ K` and `r > 0` such that
`∫_{X_τ ∩ U} (Θ|_{X_τ})ⁿ ≤ δ` (the measure `topFormMeasure` of the top power of `s^*Θ`, positive
part of its density, on `X`) for every `τ` with `0 < |τ| < r` and every holomorphic section `s` of
`μ` over `x ↦ (x, τ)`. -/
def FibreVolumeSmallStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
    (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (ι : F.carrier → 𝒳)
    (_ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
    (∀ x, μ (ι x) = (x, projectiveZero)) →
    ∀ K : Set 𝒳, K ⊆ centralFibre F μ →
      ManifoldLocallyPluripolar (n := m + 1) (ι ⁻¹' K) →
      (letI := exceptionalChartedSpace F hμ
       haveI := isComplexManifold_exceptional F hμ
       ManifoldLocallyPluripolar (n := m + 1) ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' K)) →
      ∀ δ : ℝ≥0∞, 0 < δ →
        ∃ U : Set 𝒳, IsOpen U ∧ strictCentralFibre F μ ∩ exceptionalSet F μ ⊆ U ∧ K ⊆ U ∧
          ∃ r : ℝ, 0 < r ∧ ∀ τ : ℂ, τ ≠ 0 → ‖τ‖ < r →
            ∀ (s : F.carrier → 𝒳)
              (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s),
              (∀ x, μ (s x) = (x, affineLinePoint τ)) →
              (letI : MeasurableSpace F.carrier := borel F.carrier
               haveI : BorelSpace F.carrier := ⟨rfl⟩
               topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback hs Θ).val (m + 1))
                 (s ⁻¹' U)) ≤ δ

/-! ### Local convergence of the fibre measures (WN21 Proposition 7.4) -/

/-- **`tok-wn-fl:strict-convergence`** (WN21 Proposition 7.4 near `X' \ ℰ`, as an upper bound):
under the hypotheses of `FibreLimitStatement`, every point `p ∈ X' \ ℰ` with `Ψ(p) ≠ -∞` has an
open neighbourhood `W` such that for every continuous `ρ ≥ 0` with `tsupport ρ ⊆ W` and every
strictly increasing `k_l` with `Σ_l e^{k_l/2}|τ_{k_l}| < ∞`,
`limsup_l ∫_X ρ ∘ s_{k_l} d⟨((Θ + dd^c v_{k_l})|_{X_{τ_{k_l}}})ⁿ⟩ ≤
  ∫_X ρ ∘ ι d⟨(Θ|_{X'} + dd^c v_{X'})ⁿ⟩ + ∫_ℰ ρ d⟨(Θ|_ℰ + dd^c v_ℰ)ⁿ⟩`. -/
def StrictFibreConvergenceStatement : Prop :=
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
          ∀ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ →
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ →
          ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
            [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
            (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
            (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
            (hh : ChartSmooth (n := m + 1 + 1) h),
            CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
            (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
            ((ClosedRealOneOneForm.pullback hπ.contMDiff
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
              ddcClosedForm h hh).val.IsKahler →
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∀ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) →
            Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) →
          ∀ (s : ℕ → F.carrier → 𝒳)
            (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1))
              ∞ (s k)),
            (∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) →
          ∀ (hw : ∀ k, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hs k)
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (fun x => prescribedEnvelope
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                (cutoffObstacle μ χ k) Ψ (s k x)))
            (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                μ χ Ψ ι))
            (hℰ : letI := exceptionalChartedSpace F hμ
              haveI := isComplexManifold_exceptional F hμ
              IsThetaPshPotential (ClosedRealOneOneForm.pullback
                (contMDiff_exceptionalInclusion F hμ)
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
                (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                  μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳))),
          ∀ p ∈ strictCentralFibre F μ, p ∉ exceptionalSet F μ → Ψ p ≠ ⊥ →
            ∃ W : Set 𝒳, IsOpen W ∧ p ∈ W ∧
              ∀ ρ : 𝒳 → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → tsupport ρ ⊆ W →
              ∀ φ : ℕ → ℕ, StrictMono φ →
                Summable (fun l => Real.exp ((φ l : ℝ) / 2) * ‖τ (φ l)‖) →
                limsup (fun l => restrictedTestMass (hs (φ l))
                    (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                    (fun x => prescribedEnvelope
                      (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ (φ l)) Ψ (s (φ l) x)) (hw (φ l)) ρ) atTop ≤
                  centralLimitTestMass F hμ (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                    χ Ψ ι hι hX' hℰ ρ

/-- **`tok-wn-fl:exceptional-convergence`** (WN21 Proposition 7.4 near `ℰ \ X'`, as an upper
bound): the statement of `StrictFibreConvergenceStatement` at the points `p ∈ ℰ \ X'` with
`Ψ(p) ≠ -∞` (in WN21, in the charts `(z̃₁, z', τ)` with `z₁ = z̃₁ τ`, in which `ℰ = {τ = 0}` and the
fibres are `{τ = const}`). -/
def ExceptionalFibreConvergenceStatement : Prop :=
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
          ∀ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ →
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ →
          ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
            [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
            (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
            (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
            (hh : ChartSmooth (n := m + 1 + 1) h),
            CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
            (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
            ((ClosedRealOneOneForm.pullback hπ.contMDiff
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
              ddcClosedForm h hh).val.IsKahler →
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∀ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) →
            Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) →
          ∀ (s : ℕ → F.carrier → 𝒳)
            (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1))
              ∞ (s k)),
            (∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) →
          ∀ (hw : ∀ k, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hs k)
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (fun x => prescribedEnvelope
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                (cutoffObstacle μ χ k) Ψ (s k x)))
            (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                μ χ Ψ ι))
            (hℰ : letI := exceptionalChartedSpace F hμ
              haveI := isComplexManifold_exceptional F hμ
              IsThetaPshPotential (ClosedRealOneOneForm.pullback
                (contMDiff_exceptionalInclusion F hμ)
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
                (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                  μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳))),
          ∀ p ∈ exceptionalSet F μ, p ∉ strictCentralFibre F μ → Ψ p ≠ ⊥ →
            ∃ W : Set 𝒳, IsOpen W ∧ p ∈ W ∧
              ∀ ρ : 𝒳 → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → tsupport ρ ⊆ W →
              ∀ φ : ℕ → ℕ, StrictMono φ →
                Summable (fun l => Real.exp ((φ l : ℝ) / 2) * ‖τ (φ l)‖) →
                limsup (fun l => restrictedTestMass (hs (φ l))
                    (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                    (fun x => prescribedEnvelope
                      (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ (φ l)) Ψ (s (φ l) x)) (hw (φ l)) ρ) atTop ≤
                  centralLimitTestMass F hμ (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                    χ Ψ ι hι hX' hℰ ρ

/-! ### Proposition 7.1, Lemma 7.5 and Corollary 7.6 near `X' \ ℰ` -/

/-- **`tok-wn-fl:resolution-identity`** (WN21 Proposition 7.1): let `Ψ` be `Θ`-psh on a compact
manifold `𝒳`, `π : 𝒵 → 𝒳` a finite sequence of blow-ups from a compact connected manifold with
exceptional locus in `Supp D'`, `Ψ ∘ π = ψ_{D'} + h` with `h` smooth and
`ω̃ = π^*Θ - Θ_{D'} + dd^c h` Kähler.  Then for every continuous obstacle `g`,
`P_Θ[Ψ](g) ∘ π = P_{ω̃}(g ∘ π - Ψ ∘ π) + Ψ ∘ π` on `𝒵` (both sides `-∞` on `Supp D'`). -/
def PrescribedEnvelopeResolutionStatement : Prop :=
  ∀ (N : ℕ) (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
    [IsComplexManifold N 𝒳] [CompactSpace 𝒳] (Θ : ClosedRealOneOneForm N 𝒳) (Ψ : 𝒳 → EReal),
    IsThetaPshPotential Θ.val Ψ →
    ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵]
      [IsComplexManifold N 𝒵] (π : 𝒵 → 𝒳) (hπ : IsBlowupSequence N 𝒳 𝒵 π)
      (D' : MeteredEffectiveQDivisor N 𝒵) (h : 𝒵 → ℝ) (hh : ChartSmooth (n := N) h),
      CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus N π ⊆ D'.support →
      (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
      ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) +
        ddcClosedForm h hh).val.IsKahler →
      ∀ g : 𝒳 → ℝ, Continuous g → ∀ z : 𝒵,
        prescribedEnvelope Θ g Ψ (π z) =
          rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.contMDiff Θ - D'.curvature) +
              ddcClosedForm h hh).val (fun y => (g (π y) : EReal) - Ψ (π y)) z + Ψ (π z)

/-- **`tok-wn-fl:disc-laplacian`** (WN21 Lemma 7.5, along the discs `t ↦ μ⁻¹(x, t)` near
`X' \ ℰ`): under the hypotheses of `FibreLimitStatement` (without the sequences), every
`x₀ ∈ X \ Z` with `Ψ(ι x₀) ≠ -∞` has an open neighbourhood `U`, a constant `C` and a threshold `k₀`
such that for all `k ≥ k₀`, all `x ∈ U` and every map `σ : ℂ → 𝒳` with `μ(σ t) = (x, t)` (the disc
over `x`, `σ(0) = ι x`),
the function `f(t) = v_k(σ t)` (`v_k = P_Θ[Ψ](g_k)`) is finite with `|f + k| ≤ C` on
`|t| ≤ e^{-k/2}`, and is there the uniform limit of smooth functions `u_j` with
`-C ≤ Δ u_j ≤ C e^k` on `|t| < e^{-k/2}` (Berman's estimate on the log resolution of `Ψ`, rescaled
to the disc).  The threshold `k₀` is necessary (lane WN-FL3, counterexample in
`tok/WN-FL3/NEEDS.md`: for small `k` the disc may meet a pole of `Ψ`; WN21 assumes `Ψ` bounded on
`U × {|τ| ≤ 1}`).  This is the same statement as WN-FL3's `StrictDiscLaplacianFromStatement F`. -/
def StrictDiscLaplacianStatement : Prop :=
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
          (_ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
          ∀ (η' : KahlerBackground (m + 1 + 1) 𝒳) (ε : ℝ), 0 < ε →
          ∀ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ →
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ →
          ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
            [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
            (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
            (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
            (hh : ChartSmooth (n := m + 1 + 1) h),
            CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
            (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
            ((ClosedRealOneOneForm.pullback hπ.contMDiff
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
              ddcClosedForm h hh).val.IsKahler →
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∀ x₀ : F.carrier, x₀ ∉ F.flag (1 : Fin (m + 2)) → Ψ (ι x₀) ≠ ⊥ →
            ∃ U : Set F.carrier, IsOpen U ∧ x₀ ∈ U ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ U,
              ∀ σ : ℂ → 𝒳, (∀ t, μ (σ t) = (x, affineLinePoint t)) →
                (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) →
                  prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t) ≠ ⊥ ∧
                  |(prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t)).toReal + k| ≤ C) ∧
                ∃ u : ℕ → ℂ → ℝ, (∀ j, ContDiff ℝ 2 (u j)) ∧
                  TendstoUniformlyOn u
                    (fun t => (prescribedEnvelope
                      (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t)).toReal) atTop
                    (Metric.closedBall 0 (Real.exp (-(k : ℝ) / 2))) ∧
                  ∀ j, ∀ t ∈ Metric.ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
                    -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k

/-- **`tok-wn-fl:strict-lipschitz`** (WN21 Corollary 7.6 near `X' \ ℰ`, with the bound
`|v_k + k| ≤ C` of WN21 Lemma 7.5): under the hypotheses of `FibreLimitStatement` (without the
sequences), every `x₀ ∈ X \ Z` with `Ψ(ι x₀) ≠ -∞` has an open neighbourhood `U`, a constant `C`
and a threshold `k₀` such that for all `k ≥ k₀` and `x ∈ U`: `v_k(ι x) ≥ -k - C`, and for every
`z ∈ 𝒳` over `(x, t)` with `0 < |t| ≤ e^{-k/2}/2`, `v_k(z)` is finite and
`|v_k(z) - v_k(ι x)| ≤ C e^{k/2} |t|` (the threshold is necessary, see
`StrictDiscLaplacianStatement`). -/
def StrictLipschitzStatement : Prop :=
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
          (_ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
          ∀ (η' : KahlerBackground (m + 1 + 1) 𝒳) (ε : ℝ), 0 < ε →
          ∀ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ →
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ →
          ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
            [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
            (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
            (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
            (hh : ChartSmooth (n := m + 1 + 1) h),
            CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
            (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
            ((ClosedRealOneOneForm.pullback hπ.contMDiff
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
              ddcClosedForm h hh).val.IsKahler →
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∀ x₀ : F.carrier, x₀ ∉ F.flag (1 : Fin (m + 2)) → Ψ (ι x₀) ≠ ⊥ →
            ∃ U : Set F.carrier, IsOpen U ∧ x₀ ∈ U ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ U,
              ((-(k : ℝ) - C : ℝ) : EReal) ≤
                  prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                    (cutoffObstacle μ χ k) Ψ (ι x) ∧
                ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) / 2 →
                  ∀ z : 𝒳, μ z = (x, affineLinePoint t) →
                    prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                        (cutoffObstacle μ χ k) Ψ z ≠ ⊥ ∧
                    |(prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                        (cutoffObstacle μ χ k) Ψ z).toReal -
                      (prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                        (cutoffObstacle μ χ k) Ψ (ι x)).toReal| ≤
                      C * Real.exp ((k : ℝ) / 2) * ‖t‖

end SGPT.Okounkov.TranscendentalWN
