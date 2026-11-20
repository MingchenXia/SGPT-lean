import SGPT.Envelopes.SourceClassVolume
import SGPT.PSH.BookCurrentSpace
import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure

/-!
# Concavity and continuity of the volume, and the restricted volume: statements

Blueprint nodes `tok:ext-volume-concave` and `tok:restricted-volume` (chapter
`claude-okounkov-transcendental`), the external inputs of Darvas--Reboulet--Witt Nyström--Xia--
Zhang, *Transcendental Okounkov bodies* (DRWNXZ), Theorem 2.10 and Proposition 7.2:

* (Boucksom, *On the volume of a line bundle*, Proposition 4.5 and Theorem 4.7 of the published
  version) `α ↦ vol(α)^{1/n}` is concave on the big cone, `α ↦ vol(α)` is continuous on
  `H^{1,1}(X, ℝ)` (`vol = 0` outside the big cone), and `vol(α) > 0` iff `α` is big;
* (DRWNXZ §2, before Theorem 2.10) the restricted volume
  `vol_{X|Z}(ξ) = sup ∫_Z ⟨(T|_Z)^d⟩` over `T ∈ Ω(ξ)` whose potential is not identically `-∞`
  on `Z`.

This file contains the **definitions and statements** consumed by the packages WN and VOL;
the proofs are in `SGPT.Okounkov.TranscendentalVolumeConcavity` (no statement here is
asserted).

## Formal conventions

* `X` is a connected compact complex manifold of dimension `n = m + 1` (Kähler in the
  theorems), with its Borel measurable structure; classes are `RealBottChern (m + 1) X`
  (`H^{1,1}(X, ℝ)`), bigness is `SGPT.PSH.BookCurrent.IsBig` (`def:psefclass`: `α` contains a
  Kähler current), pseudo-effectivity `SGPT.PSH.BookCurrent.IsPseudoeffective`, and the volume
  is `SGPT.PSH.VariableComplexAtlas.sourceClassVolume` (`def:volcohclass`,
  `vol α = ∫_X ⟨T_min^n⟩`, `0` for non-pseudo-effective classes).
* `vol(α)^{1/n}` is the real number `(vol α).toReal ^ (1/n)` (`volumeRoot`); `vol α < ∞`.
* The topology of `H^{1,1}(X, ℝ)` is TN's quotient `C⁰` topology `classC0Topology ω` of
  `TranscendentalMainStatement` (independent of the Kähler form `ω`; on a compact Kähler
  manifold it is the vector-space topology of the finite-dimensional `H^{1,1}(X, ℝ)`).
* The restricted volume is defined for a holomorphic map `ι : V → X` from a compact complex
  manifold of dimension `k` (for a connected closed submanifold `Z` of dimension `d = k`: the
  inclusion of `Z` with its induced complex structure, as `firstFlagRestriction` does for `Y₁`)
  and a representative `θ` of `ξ`: `T = θ + dd^c φ` with `φ ∈ Ω(ξ)`
  (`TranscendentalCore.gentleKahlerCurrents`), `T|_Z = ι^*θ + dd^c (φ ∘ ι)`, and "the potential
  is not identically `-∞` on `Z`" is the condition that `φ ∘ ι` is a genuine `ι^*θ`-psh
  potential (`IsThetaPshPotential`, i.e. not `-∞` on any nonempty open subset of `V`; for a
  connected `V` this is `φ ∘ ι ≢ -∞`). `∫_Z ⟨(T|_Z)^d⟩` is the non-pluripolar mass
  `diagonalPotentialMass`. The supremum of the empty family is `0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set
open scoped ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.BookCurrent

section Volume

variable {m : ℕ} (X : Type*) [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]

/-- The big cone of `H^{1,1}(X, ℝ)` (`def:psefclass`). -/
def bigCone : Set (RealBottChern (m + 1) X) := {α | IsBig α}

/-- The pseudo-effective cone of `H^{1,1}(X, ℝ)` (`def:psefclass`). -/
def psefCone : Set (RealBottChern (m + 1) X) := {α | IsPseudoeffective α}

variable {X} in
/-- `vol(α)^{1/n}`, `n = m + 1`, as a real number. -/
def volumeRoot (α : RealBottChern (m + 1) X) : ℝ :=
  (sourceClassVolume α).toReal ^ (((m + 1 : ℕ) : ℝ)⁻¹)

/-- **`tok:ext-volume-concave`, concavity**: `α ↦ vol(α)^{1/n}` is concave on the big cone. -/
def VolumeRootConcaveStatement : Prop :=
  ConcaveOn ℝ (bigCone (m := m) X) volumeRoot

/-- **`tok:ext-volume-concave`, continuity**: `α ↦ vol(α)` is continuous on `H^{1,1}(X, ℝ)` for
the `C⁰` quotient topology (of any Kähler background). -/
def VolumeContinuityStatement : Prop :=
  ∀ w : KahlerBackground (m + 1) X,
    @Continuous (RealBottChern (m + 1) X) ℝ≥0∞
      (XiaoBottChernC0Closure.classC0Topology w) _ sourceClassVolume

/-- **`tok:ext-volume-concave`, positivity**: `vol(α) > 0` if and only if `α` is big. -/
def VolumePositiveIffBigStatement : Prop :=
  ∀ α : RealBottChern (m + 1) X, 0 < sourceClassVolume α ↔ IsBig α

/-- **`tok:ext-volume-concave`** (Bou02b), the conjunction of the three statements. -/
def VolumeConcavityStatement : Prop :=
  VolumeRootConcaveStatement (m := m) X ∧ VolumeContinuityStatement (m := m) X ∧
    VolumePositiveIffBigStatement (m := m) X

end Volume

section Restricted

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- **`tok:ext-volume-concave` / `tok:restricted-volume`** (DRWNXZ §2): the restricted volume
`vol_{X|Z}(ξ) = sup ∫_Z ⟨(T|_Z)^d⟩` over the currents `T = θ + dd^c φ ∈ Ω(ξ)` (`ξ = {θ}`) whose
potential is not identically `-∞` on `Z`, for the submanifold given by `ι : V → X`. -/
def restrictedVolume (ι : V → X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n X) : ℝ≥0∞ :=
  ⨆ (φ : X → EReal) (_ : φ ∈ TranscendentalCore.gentleKahlerCurrents θ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y))),
      DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (fun y => φ (ι y)) hw

end Restricted

end SGPT.Okounkov.TranscendentalVolumeConcavity
