import SGPT.Okounkov.TranscendentalWNConvStatement

/-!
# The convergence step of the key equality: objects and the analytic core

Blueprint chapter `claude-tok-wn`, node `tok-wn:convergence`, refined in `claude-tok-wn-conv7`;
source D. Witt Nyström, *Deformations of Kähler manifolds to normal bundles and restricted
volumes of big classes*, arXiv:2103.03660 (WN21), §7: Propositions 7.1--7.4, Lemma 7.5,
Corollary 7.6 and the proof of the hard inequality of Theorem 1.7
(`references/wn21-restricted-volume`).

Notation as in `TranscendentalWNKeyStatement` and `TranscendentalWNConvStatement`: `μ : 𝒳 → X × ℙ¹`
is the deformation of `X` to the normal cone of `Z = Y₁`, `X_τ` (`τ ≠ 0`) the fibre over `τ`,
parametrized by the section `s` of `μ` over `x ↦ (x, τ)`, `X'` the strict transform of
`X × {0}` (parametrized by the lift `ι'` of `x ↦ (x, 0)`), `ℰ` the exceptional divisor,
`θ̃ = deformationForm F hμ θ b c Eℰ` (a representative of `β`), `η'` a Kähler form on `𝒳`,
`ε > 0`, `Θ = θ̃ + ε η'`, `χ` a cutoff (`IsWNCutoff`), `g_k = cutoffObstacle μ χ k`,
`u_k = P_{θ̃}(g_k)` (`cutoffEnvelope`) and `D_k = {u_k = g_k}` (`cutoffContactSet`).

## The objects of WN21 §7

* `prescribedEnvelope Θ g ψ = P_Θ[ψ](g) = (sup {v ∈ PSH(𝒳, Θ) : v ≤ g, v ⪯ ψ})^*`, the envelope of
  the obstacle `g` with singularities prescribed by `ψ` (WN21 §7: `v_k = P_{θ̃+εη}[ψ](g_k)`);
  `prescribedCompetitors` are its competitors.  `v ⪯ ψ` is `SGPT.PSH.SingularityLE v ψ`
  (`v ≤ ψ + C`).
* `prescribedContactSet Θ g ψ = {P_Θ[ψ](g) = g}` (WN21 §7: `D'_k = {v_k = g_k}`).
* `envelopeContactMass F Θ g ψ s hs hw = ∫_{X_τ ∩ D'_k} ⟨((Θ + dd^c v_k)|_{X_τ})ⁿ⟩`: the
  non-pluripolar Monge--Ampère measure of the restriction `v_k ∘ s` (for `s^*Θ`) of the contact
  set, along a holomorphic `s : X → 𝒳`.

## The analytic core

`ContactMassLimitStatement F` (WN21 §7 minus the fibrewise lower bound (MAest)): there is a
`Θ`-psh weight `ψ` less singular than the potential `ũ = V_{θ̃}` with minimal singularities in
`β`, such that for all `τ_k ∈ ℂ \ {0}` with `e^{k/2}|τ_k| → 0` and all sections `s_k` of `μ` over
`x ↦ (x, τ_k)`,
`liminf_k ∫_{X_{τ_k} ∩ D'_k} ⟨((Θ + dd^c v_k)|_{X_{τ_k}})ⁿ⟩ ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`.

In WN21 this is the combination of: the choice of `ψ` (a gentle current above `ũ`, a Kähler log
resolution `π : 𝒵 → 𝒳` and the perturbation making `π^*(θ̃ + εη') + σ` Kähler), Proposition 7.1
(`v_k ∘ π = ṽ_k + ψ ∘ π`, hence `|v_k - ψ| ≤ C_k`), Proposition 7.2 (`v_k + k` increases, with
limits `v_{X'}`, `v_ℰ` on `X'` and `ℰ`), Proposition 7.3 (`∫ MA(v_{X'}) ≤ vol_{𝒳|X'}(β+ε{η'})`, same
on `ℰ`), Lemma 7.5 and Corollary 7.6 (Berman's Laplacian estimate on `𝒵` and the Lipschitz bound
`|v_k(z,τ) - v_k(z,0)| ≤ C e^{k/2}|τ|`), Proposition 7.4 (convergence of the fibre measures away
from `X' ∩ ℰ` and the poles of `ψ`), the uniform smallness of `∫_{X_τ ∩ U} |Θⁿ|` near
`(X' ∩ ℰ) ∪ (X₀ ∩ {ψ = -∞})`, and the bound of `MA(v_k|_{X_τ})` on `D'_k` by the obstacle
(`tok-wn:contact-upper`).  The remaining step of WN21 §7, the fibrewise estimate
`1_{X_τ ∩ D_k} θ̃ⁿ ≤ 1_{X_τ ∩ D'_k} MA(v_k|_{X_τ})` (MAest), is proved in
`TranscendentalWNConv7Envelope`, and `KeyConvergenceStatement F` is derived from
`MeasureControlStatement F` and `ContactMassLimitStatement F` in
`TranscendentalWNConv7Main`.

This file contains the definitions and the **statement only**; nothing is asserted.
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

/-! ### Envelopes with prescribed singularities -/

section Prescribed

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The competitors of the envelope with prescribed singularities: the `Θ`-psh potentials `v`
with `v ≤ g` everywhere and `v ⪯ ψ` (`v ≤ ψ + C`). -/
def prescribedCompetitors (Θ : ClosedRealOneOneForm N M) (g : M → ℝ) (ψ : M → EReal) :
    Set (M → EReal) :=
  {v | IsThetaPshPotential Θ.val v ∧ (∀ z, v z ≤ (g z : EReal)) ∧ SGPT.PSH.SingularityLE v ψ}

/-- **The envelope with prescribed singularities** (WN21 §7, `v_k`):
`P_Θ[ψ](g) = (sup {v ∈ PSH(M, Θ) : v ≤ g, v ⪯ ψ})^*`. -/
def prescribedEnvelope (Θ : ClosedRealOneOneForm N M) (g : M → ℝ) (ψ : M → EReal) :
    M → EReal :=
  uscRegularization fun z => ⨆ v : prescribedCompetitors Θ g ψ, v.1 z

/-- **The contact set** `{P_Θ[ψ](g) = g}` (WN21 §7, `D'_k`). -/
def prescribedContactSet (Θ : ClosedRealOneOneForm N M) (g : M → ℝ) (ψ : M → EReal) : Set M :=
  {z | prescribedEnvelope Θ g ψ z = (g z : EReal)}

end Prescribed

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **The contact mass on a fibre** `∫_{X_τ ∩ D'} ⟨((Θ + dd^c v)|_{X_τ})ⁿ⟩` for
`v = P_Θ[ψ](g)` and `D' = {v = g}`, along a holomorphic map `s : X → 𝒳` (used for the section of
`μ` over `x ↦ (x, τ)`, whose image is `X_τ`): the non-pluripolar Monge--Ampère measure of
`v ∘ s` for `s^*Θ` (Borel structure on `X`) of `s⁻¹(D')`. -/
def envelopeContactMass {𝒳 : Type u} [TopologicalSpace 𝒳]
    [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (g : 𝒳 → ℝ) (ψ : 𝒳 → EReal) (s : F.carrier → 𝒳)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val
      (fun x => prescribedEnvelope Θ g ψ (s x))) : ℝ≥0∞ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  DiagonalMass.diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hs Θ)
    (fun x => prescribedEnvelope Θ g ψ (s x)) hw (s ⁻¹' prescribedContactSet Θ g ψ)

/-! ### The statement -/

/-- **The analytic core of `tok-wn:convergence`** (WN21 §7: Propositions 7.1--7.4, Lemma 7.5,
Corollary 7.6, the smallness estimate near `(X' ∩ ℰ) ∪ (X₀ ∩ {ψ = -∞})` and the final limit;
blueprint `tok-wn-conv7:contact-limit`).  Under the hypotheses of `KeyConvergenceStatement`
(`0 < c`, `c + 1 < b`, `ξ = {θ}` and `ξ_c` big with Kähler loci meeting `Z`, the lift `ι'` of
`x ↦ (x, 0)`, a Kähler form `η'` on `𝒳`, `ε > 0`) and for every cutoff `χ`, there is a
`Θ`-psh weight `ψ` (`Θ = θ̃ + ε η'`) with `ũ = V_{θ̃} ⪯ ψ` such that, for every sequence
`τ_k ∈ ℂ \ {0}` with `e^{k/2}|τ_k| → 0` and all holomorphic sections `s_k` of `μ` over
`x ↦ (x, τ_k)`, the contact masses of `v_k = P_Θ[ψ](g_k)` on the fibres satisfy
`liminf_k ∫_{X_{τ_k} ∩ {v_k = g_k}} ⟨((Θ + dd^c v_k)|_{X_{τ_k}})ⁿ⟩ ≤
  vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`. -/
def ContactMassLimitStatement : Prop :=
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
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
            ∃ ψ : 𝒳 → EReal,
              IsThetaPshPotential
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val ψ ∧
              SGPT.PSH.SingularityLE
                (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) ψ ∧
              ∀ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) →
                Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) →
                ∀ (s : ℕ → F.carrier → 𝒳)
                  (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1))
                    ∞ (s k)),
                  (∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) →
                  ∀ hw : ∀ k, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hs k)
                      (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
                      (fun x => prescribedEnvelope
                        (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                        (cutoffObstacle μ χ k) ψ (s k x)),
                    liminf (fun k => envelopeContactMass F
                        (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                        (cutoffObstacle μ χ k) ψ (s k) (hs k) (hw k)) atTop ≤
                      sectionRestrictedVolume F ι hι
                          (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) +
                            ε • RealBottChern.ofRepresentative η'.form) +
                        exceptionalRestrictedVolume F hμ
                          (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) +
                            ε • RealBottChern.ofRepresentative η'.form)

end SGPT.Okounkov.TranscendentalWN
