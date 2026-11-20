import SGPT.PSH.SourceTestCurveLegendreCorrespondence
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion

/-!
# Twisted test curves (`rmk:testcurve:L815`)

Source `rmk:testcurve:L815` (chapter *Test curves*): *"One could also consider geodesic rays
emanating from another potential `Φ ∈ 𝓔(X, θ; φ)`. In this case, one can show that these
geodesic rays are in bijection with `Φ`-twisted test curves: in `def:testcur`, we replace
condition (2) by `P_θ[Γ_τ](Φ) = Γ_τ`. Furthermore, we require that `Γ_{-∞} = Φ`. The above
results equally work in the twisted setting."*

This file states the remark in Lean and proves the case `Φ = φ`:

* `SourceTwistedTestCurve θ Φ`: a `Φ`-twisted test curve — the data and conditions of
  `def:testcur` (real `Γ_max`, a concave decreasing map `(-∞, Γ_max) → PSH(X, θ)`) with
  condition (2) replaced by `P_θ[Γ_τ](Φ) = Γ_τ` (the envelope `P_θ[·](f)` of
  `def:Pthetavarphif`, `sourceRelativeEnvelope`) and with `Γ_{-∞} = usc sup_τ Γ_τ = Φ`.
  Condition (3), `∫_X θ_{Γ_{-∞}}ⁿ > 0`, is then a condition on `Φ` alone; it holds for every
  `Φ ∈ 𝓔(X, θ; φ)` (`∫_X θ_Φⁿ = ∫_X θ_φⁿ > 0`), so it is not repeated as a field.
* `sourceGeodesicRaysFrom omega θ φ hφ Φ`: geodesic rays in `𝓔(X, θ; φ)` emanating from `Φ`
  (`def:geodraydef` with `ℓ₀ = Φ`).
* `twistedLegendreRay Γ`: the Legendre transform `Γ*_t = sup_{τ < Γ_max} (tτ + Γ_τ)` (`t > 0`,
  `def:Legtrans`), `Γ*_0 = Φ`.
* `TwistedRWNCorrespondence omega θ φ hφ Φ`: the claim of the remark, the Legendre transform is
  a bijection from `Φ`-twisted test curves onto geodesic rays emanating from `Φ`;
  `TwistedRWNStatement`: the claim for every `Φ ∈ 𝓔(X, θ; φ)`.
* **`twistedRWNCorrespondence_self`**: the claim for `Φ = φ`. A `φ`-twisted test curve is the
  same as a test curve in `TC(X, θ; φ)` (`twistedTestCurveEquiv`: for `Γ_τ ≤ φ` and `φ` model,
  `P_θ[Γ_τ](φ) = Γ_τ ↔ P_θ[Γ_τ] = Γ_τ`), and the statement reduces to `thm:Legenbij`
  (`sourceTestCurveLegendreEquiv`).

The general case `Φ ≠ φ` (re-running the proofs of `lma:LegsendsTCtoR`, `lma:LegendsRtoTC`
and `thm:Legenbij` with the twisted fixed-point condition) is proved in
`SGPT.TestCurve.RWNTwistedCorrespondence` (`SGPT.TestCurve.RWNTwisted.twistedRWNStatement_holds`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.TestConf

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Source `rmk:testcurve:L815`: a *`Φ`-twisted test curve* in `PSH(X, θ)`: a real number
`Γ_max` and a concave, decreasing map `(-∞, Γ_max) → PSH(X, θ)`, `τ ↦ Γ_τ`, with
`P_θ[Γ_τ](Φ) = Γ_τ` (in place of condition (2) of `def:testcur`) and `Γ_{-∞} = Φ`. -/
structure SourceTwistedTestCurve (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (Φ : M → EReal) where
  /-- `Γ_max`. -/
  max : ℝ
  /-- `τ ↦ Γ_τ` on `(-∞, Γ_max)`. -/
  potential : Iio max → M → EReal
  thetaPSH : ∀ τ, (ofFixedModel n M).IsThetaPSH θ (potential τ)
  antitone : ∀ x, Antitone (fun τ ↦ potential τ x)
  /-- Concavity of `τ ↦ Γ_τ(x)`, as convexity of the negative trace (`+∞` off the domain). -/
  concave : ∀ x, SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace max potential x)
  /-- The twisted condition `P_θ[Γ_τ](Φ) = Γ_τ`. -/
  twistedFixedPoint : ∀ τ, sourceRelativeEnvelope θ (potential τ) Φ = potential τ
  /-- `Γ_{-∞} = usc sup_{τ < Γ_max} Γ_τ = Φ`. -/
  limit_eq : SGPT.PSH.uscSup potential = Φ

/-- The Legendre transform of a twisted test curve: `Γ*_t = sup_{τ < Γ_max} (tτ + Γ_τ)` for
`t > 0` (no usc regularization, as in `def:Legtrans`) and `Γ*_0 = Φ`. -/
def twistedLegendreRay {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {Φ : M → EReal}
    (Γ : SourceTwistedTestCurve θ Φ) : SourceRayFamily M :=
  fun t x ↦ if t.1 = 0 then Φ x else ⨆ τ : Iio Γ.max, ((t.1 * τ.1 : ℝ) : EReal) + Γ.potential τ x

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Geodesic rays in `𝓔(X, θ; φ)` emanating from `Φ` (`def:geodraydef`). -/
def sourceGeodesicRaysFrom (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (Φ : M → EReal) : Set (SourceRayFamily M) :=
  {ℓ | SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = Φ}

omit [BorelSpace M] in
/-- Rays emanating from `φ` itself are the class `𝓡(X, θ; φ)`. -/
theorem sourceGeodesicRaysFrom_self (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    sourceGeodesicRaysFrom omega θ φ hφ φ = sourceGeodesicRays omega θ φ hφ := rfl

/-- The claim of `rmk:testcurve:L815` for a fixed `Φ`: the Legendre transform maps `Φ`-twisted
test curves to geodesic rays in `𝓔(X, θ; φ)` emanating from `Φ`, injectively and onto. -/
def TwistedRWNCorrespondence (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (Φ : M → EReal) : Prop :=
  (∀ Γ : SourceTwistedTestCurve θ Φ,
      twistedLegendreRay Γ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) ∧
    Function.Injective (twistedLegendreRay : SourceTwistedTestCurve θ Φ → SourceRayFamily M) ∧
    ∀ ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ,
      ∃ Γ : SourceTwistedTestCurve θ Φ, twistedLegendreRay Γ = ℓ

/-- Source `rmk:testcurve:L815` (statement): for every `Φ ∈ 𝓔(X, θ; φ)`, geodesic rays
emanating from `Φ` correspond, through the Legendre transform, to `Φ`-twisted test curves. -/
def TwistedRWNStatement (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : Prop :=
  ∀ Φ : M → EReal, SourceRelativeFullMass θ φ Φ hφ → TwistedRWNCorrespondence omega θ φ hφ Φ

/-! ### The case `Φ = φ` -/

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem le_sourceRelativeEnvelope {u f a : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (haf : a ≤ f) (hau : SGPT.PSH.SingularityLE a u) :
    a ≤ sourceRelativeEnvelope θ u f := by
  intro x
  change a x ≤ uscRegularization (fun y => ⨆ b : sourceRelativeEnvelopeCompetitors θ u f, b.1 y) x
  exact (le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u f => b.1 x)
    ⟨a, ha, sourceQuasiEverywhere_of_forall haf, hau⟩).trans
    (le_uscRegularization (fun y => ⨆ b : sourceRelativeEnvelopeCompetitors θ u f, b.1 y) x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem sourceThetaPSH_upperSemicontinuous {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : UpperSemicontinuous u :=
  ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic.upperSemicontinuous

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem SourceTwistedTestCurve.potential_le_limit {Φ : M → EReal}
    (Γ : SourceTwistedTestCurve θ Φ) (τ : Iio Γ.max) : Γ.potential τ ≤ Φ := by
  intro x
  refine ((le_iSup (fun σ : Iio Γ.max => Γ.potential σ x) τ).trans
    (le_uscRegularization (fun y => ⨆ σ : Iio Γ.max, Γ.potential σ y) x)).trans (le_of_eq ?_)
  exact congrFun Γ.limit_eq x

variable {φ : M → EReal}

omit [BorelSpace M] in
theorem sourceModelPotential_le_zero (hφ : SourceModelPotential θ φ) : φ ≤ 0 := by
  obtain ⟨-, heq, -⟩ := hφ
  rw [heq]
  exact sourceSingularityEnvelope_le_zero θ φ

omit [BorelSpace M] in
/-- For `u ≤ φ` with `φ` model, `P_θ[u](φ) = u` implies `P_θ[u] = u`. -/
theorem sourceSingularityEnvelope_eq_of_relative (hφ : SourceModelPotential θ φ) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (huφ : u ≤ φ)
    (hfix : sourceRelativeEnvelope θ u φ = u) : sourceSingularityEnvelope θ u = u := by
  have hφ0 := sourceModelPotential_le_zero hφ
  apply le_antisymm
  · refine uscRegularization_le (sourceThetaPSH_upperSemicontinuous hu) fun x => ?_
    refine iSup_le fun v => ?_
    obtain ⟨v, hv, hv0, hvu⟩ := v
    have hvφ : SGPT.PSH.SingularityLE v φ :=
      MoreSingularOn.trans hvu ⟨0, fun y _ => by simpa using huφ y⟩
    have hvφ' : v ≤ φ := by
      have h := le_sourceSingularityEnvelope hv hv0 hvφ
      rwa [← hφ.2.1] at h
    exact (le_sourceRelativeEnvelope hv hvφ' hvu x).trans (le_of_eq (congrFun hfix x))
  · exact le_sourceSingularityEnvelope hu (huφ.trans hφ0) (MoreSingularOn.refl u univ)

omit [BorelSpace M] in
/-- For `u ≤ φ` with `φ` model, `P_θ[u] = u` implies `P_θ[u](φ) = u`. -/
theorem sourceRelativeEnvelope_eq_of_model (hφ : SourceModelPotential θ φ) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (huφ : u ≤ φ)
    (hfix : sourceSingularityEnvelope θ u = u) : sourceRelativeEnvelope θ u φ = u := by
  have hφ0 := sourceModelPotential_le_zero hφ
  apply le_antisymm
  · refine uscRegularization_le (sourceThetaPSH_upperSemicontinuous hu) fun x => ?_
    refine iSup_le fun a => ?_
    obtain ⟨ha, hle, hau⟩ := (sourceRelativeEnvelopeCompetitors_iff hφ.thetaPSH).mp a.2
    exact (le_sourceSingularityEnvelope ha (hle.trans hφ0) hau x).trans
      (le_of_eq (congrFun hfix x))
  · exact le_sourceRelativeEnvelope hu huφ (MoreSingularOn.refl u univ)

/-- A `φ`-twisted test curve (`φ` model) is a test curve in `TC(X, θ; φ)`. -/
def SourceTwistedTestCurve.toTestCurve (hφ : SourceModelPotential θ φ)
    (Γ : SourceTwistedTestCurve θ φ) : SourceTestCurve θ where
  max := Γ.max
  potential := Γ.potential
  thetaPSH := Γ.thetaPSH
  antitone := Γ.antitone
  concave := Γ.concave
  fixedPoint τ := sourceSingularityEnvelope_eq_of_relative hφ (Γ.thetaPSH τ)
    (Γ.potential_le_limit τ) (Γ.twistedFixedPoint τ)
  positiveLimitMass := by
    obtain ⟨hφpsh, -, hmass⟩ := hφ
    have key : ∀ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u), u = φ →
        0 < sourcePotentialNonPluripolarMeasure θ u hu univ := by
      rintro u hu rfl
      exact hmass
    exact key _ _ Γ.limit_eq

omit [BorelSpace M] in
theorem SourceTwistedTestCurve.toTestCurve_mem_based (hφ : SourceModelPotential θ φ)
    (Γ : SourceTwistedTestCurve θ φ) : Γ.toTestCurve hφ ∈ SourceTestCurvesBased θ φ hφ :=
  Γ.limit_eq

/-- A test curve in `TC(X, θ; φ)` is a `φ`-twisted test curve. -/
def SourceTwistedTestCurve.ofTestCurve (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) : SourceTwistedTestCurve θ φ where
  max := Γ.max
  potential := Γ.potential
  thetaPSH := Γ.thetaPSH
  antitone := Γ.antitone
  concave := Γ.concave
  twistedFixedPoint τ := by
    have hle : Γ.potential τ ≤ φ := by
      intro x
      refine ((le_iSup (fun σ : Iio Γ.max => Γ.potential σ x) τ).trans
        (le_uscRegularization (fun y => ⨆ σ : Iio Γ.max, Γ.potential σ y) x)).trans
        (le_of_eq ?_)
      exact congrFun hΓ x
    exact sourceRelativeEnvelope_eq_of_model hφ (Γ.thetaPSH τ) hle (Γ.fixedPoint τ)
  limit_eq := hΓ

/-- For `Φ = φ`, `φ`-twisted test curves are exactly the test curves in `TC(X, θ; φ)`. -/
def twistedTestCurveEquiv (hφ : SourceModelPotential θ φ) :
    SourceTwistedTestCurve θ φ ≃ {Γ : SourceTestCurve θ // Γ ∈ SourceTestCurvesBased θ φ hφ} where
  toFun Γ := ⟨Γ.toTestCurve hφ, Γ.toTestCurve_mem_based hφ⟩
  invFun Γ := SourceTwistedTestCurve.ofTestCurve hφ Γ.1 Γ.2
  left_inv _ := rfl
  right_inv _ := rfl

variable [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
/-- The twisted Legendre transform of a `φ`-twisted test curve is the Legendre transform of the
corresponding test curve. -/
theorem twistedLegendreRay_eq (hφ : SourceModelPotential θ φ) (Γ : SourceTwistedTestCurve θ φ) :
    twistedLegendreRay Γ = sourceTestCurveLegendreRay (Γ.toTestCurve hφ).toSourceTestCurvePredata := by
  funext t x
  by_cases ht : t.1 = 0
  · simp only [twistedLegendreRay, if_pos ht, sourceTestCurveLegendreRay,
      sourceTestCurveLegendreWithInitial]
    exact (congrFun Γ.limit_eq x).symm
  · simp only [twistedLegendreRay, if_neg ht, sourceTestCurveLegendreRay,
      sourceTestCurveLegendreWithInitial]
    rw [SourceTestCurvePredata.rawLegendre_eq_iSup_open]
    rfl

/-- **Source `rmk:testcurve:L815`, the case `Φ = φ`**: geodesic rays in `𝓔(X, θ; φ)`
emanating from `φ` are in bijection, through the Legendre transform, with `φ`-twisted test
curves (`thm:Legenbij`). -/
theorem twistedRWNCorrespondence_self (omega : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) : TwistedRWNCorrespondence omega θ φ hφ φ := by
  have hcomp : ∀ Γ : SourceTwistedTestCurve θ φ, twistedLegendreRay Γ =
      (sourceTestCurveLegendreEquiv omega φ hφ (twistedTestCurveEquiv hφ Γ)).1 :=
    fun Γ => twistedLegendreRay_eq hφ Γ
  refine ⟨fun Γ => ?_, fun Γ₁ Γ₂ h => ?_, fun ℓ hℓ => ?_⟩
  · rw [hcomp Γ, sourceGeodesicRaysFrom_self]
    exact (sourceTestCurveLegendreEquiv omega φ hφ (twistedTestCurveEquiv hφ Γ)).2
  · rw [hcomp Γ₁, hcomp Γ₂] at h
    exact (twistedTestCurveEquiv hφ).injective
      ((sourceTestCurveLegendreEquiv omega φ hφ).injective (Subtype.ext h))
  · rw [sourceGeodesicRaysFrom_self] at hℓ
    refine ⟨(twistedTestCurveEquiv hφ).symm ((sourceTestCurveLegendreEquiv omega φ hφ).symm
      ⟨ℓ, hℓ⟩), ?_⟩
    rw [hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end SGPT.TestCurve.TestConf
