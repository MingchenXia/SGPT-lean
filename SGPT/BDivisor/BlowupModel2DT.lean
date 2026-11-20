import SGPT.BDivisor.BlowupModel2Divisor
import SGPT.BDivisor.BlowupModelWeil
import SGPT.Siu.SiuDecompositionBook

/-!
# The b-divisor `𝔻(T)` of a closed positive current (`def:DT`)

Source `def:DT` (chapter *The theory of b-divisors*): for a closed positive `(1,1)`-current `T` on
`X` and a modification `π : Y → X`, `𝔻(T)_Y := {Reg π^*T} ∈ H^{1,1}(Y, ℝ)`. The book then asserts
that "this assignment is compatible with push-forwards: if `g : Z → Y` is a modification and
`π : Y → X`, then `g_* Reg(g^*π^*T) = Reg(π^*T)` by Siu's decomposition and `lma:Siudec_pullpush`.
Hence `g_* 𝔻(T)_Z = 𝔻(T)_Y`. Thus `𝔻(T)` is a Weil b-divisor."

Here `π^*` is the pull-back of closed positive currents along modifications
(`SGPT.BDivisor.Modification4.pull`, pull-back of local potentials), `Reg` is the residual part of
Siu's decomposition (`SGPT.Siu.siuRegularPart`), `{·}` is the Bott–Chern class map and the models
are the book's (finite compositions of blow-ups with smooth centres, `ModelSystem.blowup`).

* `PrimePushforward.pull_comp`: **functoriality `(π ∘ g)^*S = g^*π^*S`** of the current pull-back.
* `PrimePushforward.currentPushforward_siuDivisorialPart_pull`: `g_*(∑_{D'} ν(g^*S, D')[D'])
  = ∑_D ν(S, D)[D]` (push-forward commutes with the weak sum; exceptional primes push forward to
  `0`, the non-exceptional ones are the strict transforms `D̃` and `g_*[D̃] = [D]`,
  `ν(g^*S, D̃) = ν(S, D)`).
* `PrimePushforward.currentPushforward_siuRegularPart_pull`: **`g_* Reg(g^*S) = Reg(S)`**.
* `Modification.regPullClass`: `{Reg π^*T}`; `Modification.classPushforwardOfLE_regPullClass`:
  `g_*{Reg π'^*T} = {Reg π^*T}` along every domination `π' = π ∘ g`.
* `currentBDivisorOn S T`: the Weil b-divisor `𝔻(T)` over any model system `S`;
  `currentBDivisor T`: **the book's `𝔻(T)`** (over the blow-up models), with
  `currentBDivisor_onModel` (`𝔻(T)_π = {Reg π^*T}`) and `currentBDivisor_isPseudoeffective`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

namespace PrimePushforward

/-! ### Functoriality of the pull-back -/

section Functoriality

variable {m : ℕ} {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
  [CompactSpace X] [CompactSpace Y] [CompactSpace Z]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

omit [CompactSpace Z] in
/-- The pull-back only depends on the map. -/
theorem pull_congr {π π' : Y → X} (h : π = π') (hπ : IsAnalyticModification (n := m + 1) π)
    (hπ' : IsAnalyticModification (n := m + 1) π') {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    Modification4.pull hπ S hS = Modification4.pull hπ' S hS := by
  subst h
  rfl

/-- **Functoriality of the pull-back of currents** (input (c) of `def:DT`):
`(π ∘ g)^*S = g^*(π^*S)` for modifications `g : Z → Y`, `π : Y → X` and a closed positive
`(1,1)`-current `S` on `X` (both sides are `(π ∘ g)^*θ + ddᶜ(φ ∘ π ∘ g)` for `S = θ + ddᶜφ`). -/
theorem pull_comp {π : Y → X} {g : Z → Y} (hπ : IsAnalyticModification (n := m + 1) π)
    (hg : IsAnalyticModification (n := m + 1) g) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    Modification4.pull (AnalyticModificationComposition.isAnalyticModification_comp hπ hg) S hS =
      Modification4.pull hg (Modification4.pull hπ S hS)
        (Modification4.isClosedPositiveCurrent_pull hπ hS) := by
  obtain ⟨σ, φ, hφ, hSeq⟩ := hS.exists_thetaPotential
  have hc := AnalyticModificationComposition.isAnalyticModification_comp hπ hg
  have h1 := (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hc S hS.1
    hS.2.1 hS.2.2).2.2.2 σ φ hφ hSeq
  have h2 := (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ S hS.1
    hS.2.1 hS.2.2).2.2.2 σ φ hφ hSeq
  have hP := Modification4.isClosedPositiveCurrent_pull hπ hS
  have h3 := (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hg
    (Modification4.pull hπ S hS) hP.1 hP.2.1 hP.2.2).2.2.2 (ClosedRealOneOneForm.pullback hπ.1 σ)
    (φ ∘ π) (isThetaPshPotential_comp_of_isAnalyticModification hπ σ hφ) h2
  rw [Modification4.pull, h1, SGPT.Okounkov.analyticModificationThetaCurrent_comp hπ hg σ φ hφ]
  exact h3.symm

end Functoriality

/-! ### `g_* Reg(g^*S) = Reg(S)` -/

section Regular

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))
local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))

omit [CompactSpace X] in
theorem currentPushforward_smul {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π) (c : ℝ)
    (T : CurY) : currentPushforward hπ (c • T) = c • currentPushforward hπ T :=
  (currentPushforwardLM (k := degreeTwo (Nat.succ_pos m)) hπ).map_smul c T

omit [CompactSpace X] in
theorem currentPushforward_sub {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (T T' : CurY) : currentPushforward hπ (T - T') =
      currentPushforward hπ T - currentPushforward hπ T' :=
  map_sub (currentPushforwardLM (k := degreeTwo (Nat.succ_pos m)) hπ) T T'

omit [CompactSpace Y] in
theorem siuRegularPart_congr {S S' : CurX} (h : S = S') (hS : SGPT.Siu.IsClosedPositiveCurrent S)
    (hS' : SGPT.Siu.IsClosedPositiveCurrent S') :
    SGPT.Siu.siuRegularPart S hS = SGPT.Siu.siuRegularPart S' hS' := by
  subst h
  rfl

omit [CompactSpace X] [CompactSpace Y] in
/-- Strict transforms of distinct prime divisors are distinct. -/
theorem strictTransformPrime_injective {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) :
    Function.Injective (SGPT.Siu.strictTransformPrime hπ) := by
  intro D₁ D₂ h
  apply SGPT.PSH.GeometricPrimeCarrier.ext
  rw [← SGPT.Siu.image_strictTransformPrime hπ D₁, ← SGPT.Siu.image_strictTransformPrime hπ D₂, h]

/-- **The push-forward of the divisorial part**: `g_*(∑_{D'} ν(g^*S, D')[D']) = ∑_D ν(S, D)[D]`.
The weak series is pushed forward termwise (`hasSum_currentPushforward_inChart`); the exceptional
prime divisors contribute `0` (`currentPushforward_primeDivisorCurrent_eq_zero`); every other
prime divisor is the strict transform `D̃` of a prime divisor `D` of the target
(`exists_eq_strictTransformPrime`), with `g_*[D̃] = [D]` and `ν(g^*S, D̃) = ν(S, D)`. -/
theorem currentPushforward_siuDivisorialPart_pull {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    currentPushforward hπ.1 (SGPT.Siu.siuDivisorialPart (Modification4.pull hπ S hS)
      (Modification4.isClosedPositiveCurrent_pull hπ hS)) = SGPT.Siu.siuDivisorialPart S hS := by
  classical
  have hS' := Modification4.isClosedPositiveCurrent_pull hπ hS
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hS
  intro d η
  have h1 := hasSum_currentPushforward_inChart hπ.1
    (A := fun D' : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y =>
      (SGPT.Siu.currentGenericLelong (Modification4.pull hπ S hS) hS' D').toReal •
        SGPT.Siu.primeDivisorCurrent D')
    (B := SGPT.Siu.siuDivisorialPart (Modification4.pull hπ S hS) hS')
    (fun e η => SGPT.Siu.hasSum_siuDivisorialPart hS' e η) d η
  have hzero : ∀ D' ∉ Set.range (SGPT.Siu.strictTransformPrime hπ),
      (currentPushforward hπ.1
        ((SGPT.Siu.currentGenericLelong (Modification4.pull hπ S hS) hS' D').toReal •
          SGPT.Siu.primeDivisorCurrent D')).inChart d η = 0 := by
    intro D' hD'
    have hexc : D'.val ⊆ exceptionalLocus (m + 1) π := by
      by_contra h
      obtain ⟨D, hD⟩ := exists_eq_strictTransformPrime hπ D' h
      exact hD' ⟨D, hD⟩
    rw [currentPushforward_smul, currentPushforward_primeDivisorCurrent_eq_zero hπ D' hexc,
      smul_zero]
    rfl
  rw [← (strictTransformPrime_injective hπ).hasSum_iff hzero] at h1
  convert h1 using 1
  funext D
  simp only [Function.comp_apply]
  rw [currentPushforward_smul, currentPushforward_primeDivisorCurrent_strictTransformPrime,
    currentGenericLelong_pull_strictTransformPrime]

/-- **`g_* Reg(g^*S) = Reg(S)`** for a modification `g` of compact complex manifolds and a closed
positive `(1,1)`-current `S` on the target (the compatibility claim after `def:DT`). -/
theorem currentPushforward_siuRegularPart_pull {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    currentPushforward hπ.1 (SGPT.Siu.siuRegularPart (Modification4.pull hπ S hS)
      (Modification4.isClosedPositiveCurrent_pull hπ hS)) = SGPT.Siu.siuRegularPart S hS := by
  unfold SGPT.Siu.siuRegularPart
  rw [currentPushforward_sub, Modification4.pushforward_pull_eq hπ hS,
    currentPushforward_siuDivisorialPart_pull hπ hS]

end Regular

end PrimePushforward

/-! ### `def:DT` -/

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

namespace Modification

/-- `Reg π^*T` on a modification `π : Y → X`. -/
def regPull (π : Modification (m + 1) X) (T : CurX) (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    GlobalCurrent (m + 1) π.carrier (degreeTwo (Nat.succ_pos m)) :=
  SGPT.Siu.siuRegularPart (Modification4.pull π.isAnalyticModification T hT)
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT)

theorem isClosedPositiveCurrent_regPull (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    SGPT.Siu.IsClosedPositiveCurrent (π.regPull T hT) :=
  SGPT.Siu.isClosedPositiveCurrent_siuRegularPart _

/-- `{Reg π^*T} ∈ H^{1,1}(Y, ℝ)`. -/
def regPullClass (π : Modification (m + 1) X) (T : CurX)
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) : RealBottChern (m + 1) π.carrier :=
  bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
    ⟨π.regPull T hT, (π.isClosedPositiveCurrent_regPull hT).1,
      (π.isClosedPositiveCurrent_regPull hT).2.1⟩

/-- Along a domination `π' = π ∘ g`: `g_* Reg(π'^*T) = Reg(π^*T)`. -/
theorem currentPushforward_regPull {π π' : Modification (m + 1) X} (h : π ≤ π') {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    currentPushforward (contMDiff_homOfLE h) (π'.regPull T hT) = π.regPull T hT := by
  have hg := Dominates.isAnalyticModification h
  have hP := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT
  have hpull : Modification4.pull π'.isAnalyticModification T hT =
      Modification4.pull hg (Modification4.pull π.isAnalyticModification T hT) hP := by
    rw [PrimePushforward.pull_congr (map_comp_homOfLE h).symm π'.isAnalyticModification
      (AnalyticModificationComposition.isAnalyticModification_comp π.isAnalyticModification hg)]
    exact PrimePushforward.pull_comp π.isAnalyticModification hg hT
  unfold regPull
  rw [PrimePushforward.siuRegularPart_congr hpull _
    (Modification4.isClosedPositiveCurrent_pull hg hP)]
  exact PrimePushforward.currentPushforward_siuRegularPart_pull hg hP

/-- **Compatibility of `{Reg π^*T}` with push-forwards**: `g_*{Reg π'^*T} = {Reg π^*T}` whenever
`π'` dominates `π` through `g`. -/
theorem classPushforwardOfLE_regPullClass {π π' : Modification (m + 1) X} (h : π ≤ π') {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    classPushforwardOfLE (Nat.succ_pos m) h (π'.regPullClass T hT) = π.regPullClass T hT := by
  unfold classPushforwardOfLE regPullClass
  rw [← bottChernClass_closedCurrentPushforward]
  congr 1
  exact Subtype.ext (currentPushforward_regPull h hT)

/-- `{Reg π^*T}` is pseudo-effective (the class of a closed positive current). -/
theorem classPseudoeffective_regPullClass (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    ClassPseudoeffectiveViaPotentials (π.regPullClass T hT) := by
  rw [← SGPT.PSH.BookCurrent.isPseudoeffective_iff_classPseudoeffectiveViaPotentials]
  exact ⟨SGPT.Siu.toBookCurrent _ (π.isClosedPositiveCurrent_regPull hT), rfl⟩

end Modification

/-- **`def:DT` over a model system `S`**: the Weil b-divisor `𝔻(T)` with `𝔻(T)_π = {Reg π^*T}`. -/
def currentBDivisorOn (S : ModelSystem (m + 1) X) (T : CurX)
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) : WeilBDivisorOn S (Nat.succ_pos m) :=
  ⟨fun π => π.1.regPullClass T hT, fun _ _ h => Modification.classPushforwardOfLE_regPullClass h hT⟩

theorem currentBDivisorOn_onModel (S : ModelSystem (m + 1) X) (T : CurX)
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (π : S.Model) :
    (currentBDivisorOn S T hT).onModel π = π.1.regPullClass T hT := rfl

theorem currentBDivisorOn_isPseudoeffective (S : ModelSystem (m + 1) X) (T : CurX)
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) : (currentBDivisorOn S T hT).IsPseudoeffective :=
  (WeilBDivisorOn.isPseudoeffective_iff _).mpr fun π =>
    π.1.classPseudoeffective_regPullClass hT

/-- **`def:DT`: the b-divisor `𝔻(T)` of a closed positive `(1,1)`-current `T` on `X`**, over the
book's models (finite compositions of blow-ups with smooth centres): `𝔻(T)_Y = {Reg π^*T}` for every
model `π : Y → X`. It is a Weil b-divisor: `g_* 𝔻(T)_Z = 𝔻(T)_Y` along every domination. -/
def currentBDivisor (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m) :=
  currentBDivisorOn (ModelSystem.blowup (m + 1) X) T.current
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)

/-- `𝔻(T)_π = {Reg π^*T}`. -/
theorem currentBDivisor_onModel (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    (currentBDivisor T).onModel π =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨SGPT.Siu.siuRegularPart (Modification4.pull π.1.isAnalyticModification T.current
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
          (Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)),
          (π.1.isClosedPositiveCurrent_regPull (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)).1,
          (π.1.isClosedPositiveCurrent_regPull
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)).2.1⟩ := rfl

/-- `𝔻(T)` is pseudo-effective. -/
theorem currentBDivisor_isPseudoeffective (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    (currentBDivisor T).IsPseudoeffective :=
  currentBDivisorOn_isPseudoeffective _ _ _

end SGPT.BDivisor
