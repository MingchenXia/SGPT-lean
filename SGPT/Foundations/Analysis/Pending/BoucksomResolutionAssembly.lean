import SGPT.Foundations.Analysis.Pending.BoucksomGlobalTypePotentials
import SGPT.Foundations.Analysis.Pending.BlowupSequencePotentialDescent
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boucksom 4.8: the assembly around the resolution step, with its two inputs as hypotheses

Source: Boucksom, proof of Theorem 4.8 and Lemma 4.10 (`bou02-volume:4.8`, `bou02-volume:4.10`).
Blueprint `ana:ambient-volume-uniform-big` (proof), `bou:resolved-nef-part`,
`bou:uniform-diagonal-domination`, `bou:pushforward-lower-bound`.  TN.4 plan, §1 F6
"(P) GRAPH ROUTE (run 0154 r0)".

Boucksom's proof of 4.8 has two parts that are not yet in the tree:

* **the resolution step** (`ResolutionStep`, a `Prop`): for a `β`-psh potential `ψ` of global analytic
  type (the output of `BoucksomGlobalTypePotentials.exists_globalTypePotential`), a blowup sequence
  `μ : Y → X`, a Kähler form `ω̃` on `Y` and a smooth closed `b` on `Y`, nef, with `∫_Y bⁿ` at least the
  non-pluripolar mass of `ψ`, the mixed bounds `∫_Y bⁱ ∧ (μ^*ω)ⁿ⁻ⁱ ≤ Cⁱ ∫_X ωⁿ` when `β ≤ Cω`, and the
  transfer "a `(b − μ^*γ)`-psh potential gives a `μ^*(β − γ)`-psh potential" (add the log-weight of the
  divisor `D`, `μ^*β − b = Θ_D`).  This is Hironaka's principalization of the ideal of `ψ` plus residual
  nefness (`bou02-volume:2.4`, `ana:residual-nef`); it is exactly what the human's decision on F2
 settles — by the existing `RelativePrincipalization.exists_factorizationData` as given, or by
  Hironaka at the end.
* **the uniform nef core** (`UniformNefCore`, a `Prop`): a constant `c > 0` depending only on `(X, ω)`,
  `η` and `C` such that every nef `b` on a blowup sequence `μ : Y → X` with `∫ bⁿ ≥ η` and mixed bounds
  `≤ C` has a `(b − c μ^*ω)`-psh potential.  This is Boucksom 4.10 + the push-forward of
  `bou:pushforward-lower-bound`, done on `Y × X` (graph route): proved pieces `NefCoreKahlerCurrent`,
  `ConcentratedCurrent`, F6; Yau's theorem and the support theorem on a graph remain.

Given both, the assembly is PROVED here (`isBigClass_of_resolutionStep_of_uniformNefCore`): global-type
potentials (proved) → resolution → uniform nef core → transfer → **exact descent** of the lower bound
along the blowup sequence (`BlowupSequencePotentialDescent.exists_descent_of_isBlowupSequence`: the
lower bound is carried as `c · μ^*ω`, a pull-back, so no quantitative push-forward of Kähler currents is
needed) → a uniform perturbed Kähler lower bound → bigness
(`UniformPerturbedKahlerLowerBound.isBigClass_of_hasUniformPerturbedKahlerLowerBound`).

The hypotheses are TRUE for a compact connected Kähler `X` of positive dimension (the uniform nef core
needs connectedness: on a disconnected `X` a nef `b` may vanish on a component).  They are hypotheses of
the theorems below, never interfaces; nothing is routed through Hironaka.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.BoucksomResolutionAssembly

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.GlobalAnalyticSingularities
  NonBigVolumeReduction FullSpaceAmbientMass DiagonalMass PerturbedAmbientEnvelopeMonotone
  UniformPerturbedKahlerLowerBound NefMixedMass IntegrationCurrent

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

open scoped Manifold in
/-- Pull-back of forms commutes with scalar multiplication. -/
theorem pullback_smul {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] {f : V → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (t : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hf (t • a) = t • ClosedRealOneOneForm.pullback hf a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- **The lower bound descends exactly** (the push-forward step of `bou:pushforward-lower-bound`,
without loss): if `μ : Y → X` is a blowup sequence and `w` is a `μ^*(β − c ω)`-psh potential on `Y`,
then `{β}` contains a Kähler current on `X` with lower bound exactly `c ω`. -/
theorem exists_kahlerCurrent_of_pullback_thetaPsh (ω : KahlerBackground n X)
    (β : ClosedRealOneOneForm n X) {c : ℝ} (hc : 0 < c)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {μ : Y → X} (hμ : IsBlowupSequence n X Y μ) {w : Y → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hμ.contMDiff (β - c • ω.form)).val w) :
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative β), T.lowerBound.form = c • ω.form := by
  obtain ⟨s, hs, -⟩ :=
    BlowupSequencePotentialDescent.exists_descent_of_isBlowupSequence hμ (β - c • ω.form) hw
  refine ⟨⟨β, rfl, s, KahlerBackground.smul hc ω, ?_⟩, KahlerBackground.smul_form hc ω⟩
  rw [KahlerBackground.smul_form]
  exact hs

/-- **What the resolution step of Boucksom 4.8 must supply** (`bou:resolved-nef-part`; Hironaka's
principalization of the coherent ideal of `ψ` and residual nefness), for every `β`-psh potential `ψ`
of global analytic type, smooth off its poles, and every `C` with `C ω − β ≥ 0`: a blowup sequence
`μ : Y → X` (`Y` compact), a Kähler form `ω̃` on `Y` and a smooth closed real `(1,1)`-form `b` on `Y`
with
1. `b` nef;
2. `∫_Y bⁿ ≥ ∫_X ⟨β_ψⁿ⟩` (the non-pluripolar mass of `ψ`; Boucksom has equality);
3. `∫_Y bⁱ ∧ (μ^*ω)ⁿ⁻ⁱ ≤ Cⁱ ∫_X ωⁿ` for `i ≤ n`;
4. the transfer: for every smooth closed `γ` on `X`, a `(b − μ^*γ)`-psh potential on `Y` gives a
   `μ^*(β − γ)`-psh potential on `Y` (add the log-weight of the divisor `D` with `μ^*β − b = Θ_D`). -/
def ResolutionStep (ω : KahlerBackground n X) : Prop :=
  ∀ (β : ClosedRealOneOneForm n X) (ψ : X → EReal) (hψ : IsThetaPshPotential β.val ψ),
    HasAnalyticSingularities (n := n) ψ → HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) ψ →
    ∀ C : ℝ, (C • ω.form - β).val.IsSemipositive →
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
        (_ : IsComplexManifold n Y) (_ : MeasurableSpace Y) (_ : BorelSpace Y) (_ : CompactSpace Y)
        (μ : Y → X) (hμ : IsBlowupSequence n X Y μ) (ω' : KahlerBackground n Y)
        (b : ClosedRealOneOneForm n Y),
        NefWithRespectTo ω' b ∧
        diagonalPotentialMass β ψ hψ ≤ ENNReal.ofReal (slotIntegral ω' fun _ => b) ∧
        (∀ i : ℕ, i ≤ n → slotIntegral ω' (fun j : Fin n =>
          if (j : ℕ) < i then b else ClosedRealOneOneForm.pullback hμ.contMDiff ω.form) ≤
            C ^ i * (kahlerVolume ω).real univ) ∧
        ∀ (γ : ClosedRealOneOneForm n X) (v : Y → EReal),
          IsThetaPshPotential (b - ClosedRealOneOneForm.pullback hμ.contMDiff γ).val v →
            ∃ w : Y → EReal,
              IsThetaPshPotential (ClosedRealOneOneForm.pullback hμ.contMDiff (β - γ)).val w

/-- **The uniform nef core** (Boucksom 4.10 + `bou:pushforward-lower-bound`, uniform in the blowup
sequence): for `η > 0` and `C` there is `c > 0` such that for every blowup sequence `μ : Y → X`, every
Kähler form `ω̃` on `Y` and every nef smooth closed `b` on `Y` with `∫ bⁿ ≥ η` and
`∫ bⁱ ∧ (μ^*ω)ⁿ⁻ⁱ ≤ C` (`i ≤ n`), the form `b − c μ^*ω` has a psh potential. -/
def UniformNefCore (ω : KahlerBackground n X) : Prop :=
  ∀ η C : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
    ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
      [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (μ : Y → X)
      (hμ : IsBlowupSequence n X Y μ) (ω' : KahlerBackground n Y) (b : ClosedRealOneOneForm n Y),
      NefWithRespectTo ω' b → η ≤ slotIntegral ω' (fun _ => b) →
      (∀ i : ℕ, i ≤ n → slotIntegral ω' (fun j : Fin n =>
        if (j : ℕ) < i then b else ClosedRealOneOneForm.pullback hμ.contMDiff ω.form) ≤ C) →
      ∃ v : Y → EReal,
        IsThetaPshPotential (b - c • ClosedRealOneOneForm.pullback hμ.contMDiff ω.form).val v

/-- **One perturbed class**: with the resolution step and the constant `c` of the uniform nef core
for `η₀` and `C' = Cⁿ ∫ ωⁿ`, every `β`-psh potential `ψ` of global analytic type with mass `> η₀`
and `C ω − β ≥ 0`, `C ≥ 1`, gives a Kähler current in `{β}` with lower bound `c ω`. -/
theorem exists_kahlerCurrent_of_globalTypePotential (ω : KahlerBackground n X)
    (hRes : ResolutionStep ω) {η₀ C c : ℝ} (hC : 1 ≤ C)
    (hcore : ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (μ : Y → X)
      (hμ : IsBlowupSequence n X Y μ) (ω' : KahlerBackground n Y) (b : ClosedRealOneOneForm n Y),
      NefWithRespectTo ω' b → η₀ ≤ slotIntegral ω' (fun _ => b) →
      (∀ i : ℕ, i ≤ n → slotIntegral ω' (fun j : Fin n =>
        if (j : ℕ) < i then b else ClosedRealOneOneForm.pullback hμ.contMDiff ω.form) ≤
          C ^ n * (kahlerVolume ω).real univ) →
      ∃ v : Y → EReal,
        IsThetaPshPotential (b - c • ClosedRealOneOneForm.pullback hμ.contMDiff ω.form).val v)
    (hc : 0 < c) (β : ClosedRealOneOneForm n X) (ψ : X → EReal)
    (hψ : IsThetaPshPotential β.val ψ) (hψa : HasAnalyticSingularities (n := n) ψ)
    (hψs : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) ψ)
    (hβ : (C • ω.form - β).val.IsSemipositive)
    (hmass : ENNReal.ofReal η₀ < diagonalPotentialMass β ψ hψ) :
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative β), T.lowerBound.form = c • ω.form := by
  obtain ⟨Y, _, _, _, _, _, _, μ, hμ, ω', b, hnef, hvol, hbd, htransfer⟩ :=
    hRes β ψ hψ hψa hψs C hβ
  have hη : η₀ ≤ slotIntegral ω' (fun _ => b) := by
    by_contra hlt
    exact absurd (hmass.trans_le hvol)
      (not_lt.mpr (ENNReal.ofReal_le_ofReal (le_of_lt (not_le.mp hlt))))
  have hbd' : ∀ i : ℕ, i ≤ n → slotIntegral ω' (fun j : Fin n =>
      if (j : ℕ) < i then b else ClosedRealOneOneForm.pullback hμ.contMDiff ω.form) ≤
        C ^ n * (kahlerVolume ω).real univ := fun i hi =>
    (hbd i hi).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hi) measureReal_nonneg)
  obtain ⟨v, hv⟩ := hcore Y μ hμ ω' b hnef hη hbd'
  rw [← pullback_smul hμ.contMDiff] at hv
  obtain ⟨w, hw⟩ := htransfer (c • ω.form) v hv
  exact exists_kahlerCurrent_of_pullback_thetaPsh ω β hc hμ hw

/-- **Boucksom 4.8, the uniform perturbed lower bound, from the resolution step and the uniform nef
core**: under the hypothesis of `UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`
there is `c > 0` such that for arbitrarily small `ε > 0` the class `α + ε{ω}` contains a Kähler current
with lower bound exactly `c ω`. -/
theorem hasUniformPerturbedKahlerLowerBound_of_resolutionStep (ω : KahlerBackground n X)
    (α : RealBottChern n X) (V : ClosedIrreducibleAnalyticSubvariety n X) (η : ℝ≥0∞)
    (hη : 0 < η) (hbound : HasUniformAmbientMassLowerBound ω α V η)
    (hRes : ResolutionStep ω) (hcore : UniformNefCore ω) :
    ∃ c : ℝ, 0 < c ∧ HasUniformPerturbedKahlerLowerBound ω α c := by
  obtain ⟨θ, hθ⟩ := Quotient.exists_rep α
  have hθα : RealBottChern.ofRepresentative θ = α := hθ
  -- `C ≥ 1` with `(C - 1) ω - θ ≥ 0`
  obtain ⟨A, hA, hAθ⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω (-θ)
  set C : ℝ := A + 1 with hCdef
  have hC : 1 ≤ C := by linarith
  -- a real level `0 < η₀` with `ofReal η₀ ≤ η`
  set η₀ : ℝ := (min η 1).toReal with hη₀def
  have hmin_ne_top : min η 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hη₀ : 0 < η₀ := ENNReal.toReal_pos (lt_min hη one_pos).ne' hmin_ne_top
  have hη₀η : ENNReal.ofReal η₀ ≤ η := by
    rw [hη₀def, ENNReal.ofReal_toReal hmin_ne_top]
    exact min_le_left _ _
  obtain ⟨c, hc, hcore'⟩ := hcore η₀ (C ^ n * (kahlerVolume ω).real univ) hη₀
  refine ⟨c, hc, fun δ hδ => ?_⟩
  -- the error `2 ε₀ < δ`, `2 ε₀ ≤ 1`
  set ε₀ : ℝ := min (δ / 4) (1 / 4) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  have hε₀δ : 2 * ε₀ < δ := by
    have := min_le_left (δ / 4) (1 / 4)
    linarith
  have hε₀1 : 2 * ε₀ ≤ 1 := by
    have := min_le_right (δ / 4) (1 / 4)
    linarith
  obtain ⟨ψ, hψ, hψa, hψs, hψm⟩ :=
    BoucksomGlobalTypePotentials.exists_globalTypePotential ω hbound θ hθα ⟨ε₀, hε₀⟩
  set β : ClosedRealOneOneForm n X := θ + (2 * ε₀) • ω.form with hβdef
  have hβ : (C • ω.form - β).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_add_smul_mono ω.isSemipositive
      (show A ≤ C - 2 * ε₀ by linarith) hAθ
    have heq : C • ω.form - β = -θ + (C - 2 * ε₀) • ω.form := by
      rw [hβdef]
      module
    rw [heq]
    exact h
  obtain ⟨T, hT⟩ := exists_kahlerCurrent_of_globalTypePotential ω hRes hC hcore' hc β ψ hψ hψa hψs
    hβ (hη₀η.trans_lt hψm)
  have hclass : RealBottChern.ofRepresentative β =
      α + (2 * ε₀) • RealBottChern.ofRepresentative ω.form := by
    rw [hβdef, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul, hθα]
  exact ⟨2 * ε₀, by positivity, hε₀δ,
    ⟨T.representative, T.represents.trans hclass, T.potential, T.lowerBound, T.strictlyPsh⟩, hT⟩

/-- **Boucksom 4.8 from the resolution step and the uniform nef core** (`bou02-volume:4.8`): under
the hypothesis of `UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound` (a
uniform lower bound `η > 0` on the perturbed ambient volumes), the resolution step and the uniform nef
core make `α` big.  Every other step of Boucksom's proof is proved. -/
theorem isBigClass_of_resolutionStep_of_uniformNefCore (ω : KahlerBackground n X)
    (α : RealBottChern n X) (V : ClosedIrreducibleAnalyticSubvariety n X) (η : ℝ≥0∞)
    (hη : 0 < η) (hbound : HasUniformAmbientMassLowerBound ω α V η)
    (hRes : ResolutionStep ω) (hcore : UniformNefCore ω) : IsBigClass α := by
  obtain ⟨c, hc, h⟩ := hasUniformPerturbedKahlerLowerBound_of_resolutionStep ω α V η hη hbound hRes hcore
  exact isBigClass_of_hasUniformPerturbedKahlerLowerBound ω α hc h

end

end SGPT.Foundations.Analysis.Pending.BoucksomResolutionAssembly
