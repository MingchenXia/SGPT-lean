import SGPT.PSH.CompactPrimeNumerical

/-!
# Characterizations of `I`-equivalence

Source `prop:Iequivchar` (`author/chapter_envelopes.tex`, lines 2004–2028): for
quasi-psh `φ, ψ` on a connected compact Kähler manifold `X`, the following are
equivalent:
1. `I(kφ) = I(kψ)` for every integer `k > 0`;
2. `I(λφ) = I(λψ)` for every real `λ > 0` (`I`-equivalence, `def:Iequiv`);
3. `ν(π^*φ, y) = ν(π^*ψ, y)` for every modification `π : Y → X` (finite composition of
   blow-ups with smooth centres) and every `y ∈ Y`;
4. the same for every proper bimeromorphic morphism `π : Y → X` from a Kähler manifold;
5. `ν(φ, E) = ν(ψ, E)` for every prime divisor `E` over `X`.

This is the symmetric form of `prop:Iequivchar2` (chapter `comp`), whose five order
clauses are verified in `SGPT.PSH.CompactPrimeNumerical.source_five_way_criterion_on_direct_primes`.
Each equality clause is the conjunction of the two order clauses (an equality of ideal
stalks is the pair of inclusions; an equality of Lelong numbers is the pair of
inequalities), so the proposition follows by applying `prop:Iequivchar2` to `(φ, ψ)` and
to `(ψ, φ)`. Clause 5 uses the same representation of prime divisors over `X` as
`prop:Iequivchar2` (the direct prime classes `DirectPrimeOver n X`, with their
every-representative generic Lelong reader).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.PSH.CompactPrimeNumerical

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Clause 1 of `prop:Iequivchar`: `I(kφ) = I(kψ)` for every positive integer `k`, as
equality of all multiplier-ideal stalks in every chart. -/
def sourcePositiveIntegerIEqual (u v : X → EReal) : Prop :=
  ∀ p : ℕ, 0 < p → ∀ i,
    chartMultiplierIncluded (ofFixedModel n X) u (p : ℝ) v (p : ℝ) i ∧
      chartMultiplierIncluded (ofFixedModel n X) v (p : ℝ) u (p : ℝ) i

/-- Clause 3 of `prop:Iequivchar`: equality of Lelong numbers at every point of every
modification (finite composition of blow-ups with smooth centres). -/
def finiteModificationPointEquality (u v : X → EReal) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (π : Y → X), IsBlowupSequence n X Y π → ∀ y : Y,
      (ofFixedModel n Y).sourceLelong (u ∘ π) y = (ofFixedModel n Y).sourceLelong (v ∘ π) y

/-- Clause 4 of `prop:Iequivchar`: equality of Lelong numbers at every point of every proper
bimeromorphic morphism from a Kähler manifold. -/
def kahlerModificationPointEquality (u v : X → EReal) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (_omegaY : KahlerBackground n Y) (π : Y → X),
    IsAnalyticModification (n := n) π → ∀ y : Y,
      (ofFixedModel n Y).sourceLelong (u ∘ π) y = (ofFixedModel n Y).sourceLelong (v ∘ π) y

theorem sourcePositiveIntegerIEqual_iff (u v : X → EReal) :
    sourcePositiveIntegerIEqual (n := n) u v ↔
      sourcePositiveIntegerOrder (n := n) u v ∧ sourcePositiveIntegerOrder (n := n) v u :=
  ⟨fun h => ⟨fun p hp i => (h p hp i).1, fun p hp i => (h p hp i).2⟩,
    fun h p hp i => ⟨h.1 p hp i, h.2 p hp i⟩⟩

theorem finiteModificationPointEquality_iff (u v : X → EReal) :
    finiteModificationPointEquality (n := n) u v ↔
      finiteModificationPointComparison (n := n) u v ∧
        finiteModificationPointComparison (n := n) v u := by
  constructor
  · intro h
    exact ⟨fun Y _ _ _ π hπ y => (h Y π hπ y).ge, fun Y _ _ _ π hπ y => (h Y π hπ y).le⟩
  · intro h Y _ _ _ π hπ y
    exact le_antisymm (h.2 Y π hπ y) (h.1 Y π hπ y)

theorem kahlerModificationPointEquality_iff (u v : X → EReal) :
    kahlerModificationPointEquality (n := n) u v ↔
      kahlerModificationPointComparison (n := n) u v ∧
        kahlerModificationPointComparison (n := n) v u := by
  constructor
  · intro h
    exact ⟨fun Y _ _ _ ω π hπ y => (h Y ω π hπ y).ge, fun Y _ _ _ ω π hπ y => (h Y ω π hπ y).le⟩
  · intro h Y _ _ _ ω π hπ y
    exact le_antisymm (h.2 Y ω π hπ y) (h.1 Y ω π hπ y)

variable [ConnectedSpace X] [CompactSpace X]

/-- **Source `prop:Iequivchar`.** For quasi-psh `u, v` on a connected compact Kähler
manifold, the five conditions are equivalent; each is stated against clause 2
(`I`-equivalence). -/
theorem source_Iequivchar (omega : KahlerBackground n X) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    (sourcePositiveIntegerIEqual (n := n) u v ↔ sourceIEquivalent (ofFixedModel n X) u v) ∧
    (sourceIEquivalent (ofFixedModel n X) u v ↔ finiteModificationPointEquality (n := n) u v) ∧
    (sourceIEquivalent (ofFixedModel n X) u v ↔ kahlerModificationPointEquality (n := n) u v) ∧
    (sourceIEquivalent (ofFixedModel n X) u v ↔
      ∀ q : DirectPrimeOver n X, directSourceQPSHReader u hu q = directSourceQPSHReader v hv q) := by
  obtain ⟨h1, h2, h3, h4⟩ := source_five_way_criterion_on_direct_primes omega hu hv
  obtain ⟨h1', h2', h3', h4'⟩ := source_five_way_criterion_on_direct_primes omega hv hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sourcePositiveIntegerIEqual_iff, h1, h1']
    rfl
  · rw [finiteModificationPointEquality_iff, ← h2, ← h2']
    rfl
  · rw [kahlerModificationPointEquality_iff, ← h3, ← h3']
    rfl
  · constructor
    · intro h q
      exact le_antisymm (h4'.mp h.2 q) (h4.mp h.1 q)
    · intro h
      exact ⟨h4.mpr fun q => (h q).ge, h4'.mpr fun q => (h q).le⟩

end SGPT.PSH.CompactPrimeNumerical
