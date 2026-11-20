import SGPT.TestCurve.FGRelMain

/-!
# Test configurations with a `𝔾_m`-linearized line bundle

Source: `rmk:PhongSturm` (chapter *Test curves*) and `rmk:NApotential:L862` (chapter
*Non-Archimedean pluripotential theory*) speak of "the filtration induced by a (smooth) test
configuration `(𝓧, 𝓛)` of `(X, L)`". The book does not define test configurations; the standard
definition is [BHJ17, Def. 2.1–2.3]: a flat proper `𝔾_m`-equivariant `π : 𝓧 → 𝔸¹`, a
**`𝔾_m`-linearized** line bundle `𝓛` on `𝓧`, and a `𝔾_m`-equivariant identification of
`(𝓧, 𝓛)` over `𝔸¹ ∖ 0` with `(X × (𝔸¹ ∖ 0), p₁^* L)`; *ample* if `𝓛` is relatively ample.

Lane TC-ENC encoded everything except the linearization
(`SGPT.TestCurve.TCEnc.TestConfiguration`, with the action `IsGmEquivariant` and relative
ampleness `IsAmple`). This file adds the linearization.

## The linearization as a `𝔾_m`-representation on sections

A `𝔾_m`-linearization of `𝓛` makes every `H⁰(𝓧, m𝓛)` a rational `𝔾_m`-representation, i.e. a
`ℤ`-graded vector space (weight decomposition; a comodule over `ℂ[T, T⁻¹] = ℂ[ℤ]` is the same as
a `ℤ`-grading), compatibly with multiplication and with `ℂ[t]` (`t` has weight `-1`). The
identification over `𝔸¹ ∖ 0` is equivariant for the trivial linearization of `p₁^* L`, so on
`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` the weight vectors of weight `λ` in `H⁰(X × 𝔾_m, p₁^* L^m) = H⁰(X, L^m)[t^{±1}]`
are the `t^{-λ} q^* s`. Hence:

*the weight-`λ` part of `H⁰(𝓧, m𝓛)` consists of sections `σ` whose restriction to `𝓧 ∖ 𝓧₀` is
`t^{-λ} q^* s` for some `s ∈ H⁰(X, L^m)`* (`TestConfiguration.Extends λ m s σ`).

`SectionLinearization T` records exactly this representation: a weight decomposition
`H⁰(𝓧, m𝓛) = ⊕_λ V_{m,λ}` (`DirectSum.IsInternal`) for every `m`, compatible with the
identification over `𝔾_m` (`compat`). Conversely, for a relatively ample `𝓛` the
representation on the section algebra `⊕_m H⁰(𝓧, m𝓛)` determines the linearization
(`𝓧 = Proj_{𝔸¹}`, `𝓛 = 𝒪(1)` up to a Veronese twist), so for ample test configurations this is
an equivalent encoding of [BHJ17, Def. 2.2]; the linearization lifting a given action is unique,
because it is fixed over the dense open `𝓧 ∖ 𝓧₀`.

The weight spaces are forced: a weight-`λ` vector restricts to some `t^{-λ} q^* s`, and weight
vectors of distinct weights are linearly independent (`TCLin.sum_mono_eq_zero`, `TCLin.graph_unique`
in `TCLinGraph`), so `V_{m,λ} = weightSpace T m λ` (`SectionLinearization.weight_eq` in
`TCLinUnique`): a linearization is unique when it exists, and it exists iff every section is a sum
of weight vectors (`SectionLinearization.mem_iSup_weightSpace`).

## Main definitions

* `weightSpace T m λ`: the sections of `𝓛^m` restricting to `t^{-λ} q^* s`.
* `SectionLinearization T`: a `𝔾_m`-linearization of `𝓛`, as the induced weight decomposition of
  the sections.
* `LinearizedTestConfiguration f a`: a test configuration (lane TC-ENC's
  `TestConfiguration`, extended) with its `𝔾_m`-action and a `𝔾_m`-linearization of `𝓛`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc SGPT.TestCurve.FGRel

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- **The weight vectors of weight `λ`** in `H⁰(𝓧, 𝓛^m)`: the sections whose restriction to
`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` is `t^{-λ} q^* s` for some `s ∈ H⁰(X, L^m)`. -/
def weightSpace (T : TestConfiguration f a) (m : ℕ) (lam : ℤ) :
    Submodule ℂ (SectionSpace T.structureMap T.line m) where
  carrier := {σ | ∃ s : SectionSpace f L m, T.Extends lam m s σ}
  zero_mem' := ⟨0, TestConfiguration'.extends_zero T lam m⟩
  add_mem' := by
    rintro σ σ' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', TestConfiguration'.extends_add T hs hs'⟩
  smul_mem' := by
    rintro c σ ⟨s, hs⟩
    exact ⟨c • s, TestConfiguration'.extends_smul T hs c⟩

theorem mem_weightSpace {T : TestConfiguration f a} {m : ℕ} {lam : ℤ}
    {σ : SectionSpace T.structureMap T.line m} :
    σ ∈ weightSpace T m lam ↔ ∃ s : SectionSpace f L m, T.Extends lam m s σ :=
  Iff.rfl

/-- **A `𝔾_m`-linearization of `𝓛`** (compatible with the identification over `𝔾_m`), recorded
by the induced `𝔾_m`-representation on the sections: a weight decomposition
`H⁰(𝓧, 𝓛^m) = ⊕_λ V_{m,λ}` for every `m` whose weight-`λ` vectors restrict to `t^{-λ} q^* s` on
`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` (see the module docstring). -/
structure SectionLinearization (T : TestConfiguration f a) where
  /-- The weight-`λ` subspace of `H⁰(𝓧, 𝓛^m)`. -/
  weight : (m : ℕ) → ℤ → Submodule ℂ (SectionSpace T.structureMap T.line m)
  /-- `H⁰(𝓧, 𝓛^m)` is the direct sum of its weight spaces. -/
  isInternal : ∀ m, DirectSum.IsInternal (weight m)
  /-- Compatibility with the identification `(𝓧 ∖ 𝓧₀, 𝓛) ≅ (X × 𝔾_m, p₁^* L)`: weight vectors of
  weight `λ` restrict to `t^{-λ} q^* s`. -/
  compat : ∀ m lam, weight m lam ≤ weightSpace T m lam

/-- **A test configuration with a `𝔾_m`-linearized line bundle** ([BHJ17, Def. 2.1–2.2]): lane
TC-ENC's test configuration (flat proper `π : 𝓧 → 𝔸¹`, line bundle `𝓛`, identification over
`𝔾_m`) together with a `𝔾_m`-action on `𝓧` lifting the scaling action of `𝔸¹`
(`TestConfiguration.IsGmEquivariant`) and a `𝔾_m`-linearization of `𝓛`
(`SectionLinearization`). Ampleness (`TestConfiguration.IsAmple`) and smoothness
(`TestConfiguration.IsSmooth`) are properties of the underlying test configuration. -/
structure LinearizedTestConfiguration (f : X ⟶ Spec (.of ℂ)) (a : LineBundleAtlas L)
    extends TestConfiguration f a where
  /-- The `𝔾_m`-action on `𝓧`. -/
  isGmEquivariant : toTestConfiguration.IsGmEquivariant
  /-- The `𝔾_m`-linearization of `𝓛`. -/
  linearization : SectionLinearization toTestConfiguration

namespace SectionLinearization

variable {T : TestConfiguration f a} (P : SectionLinearization T)
include P

/-- Every section is a sum of weight vectors. -/
theorem mem_iSup_weightSpace (m : ℕ) (σ : SectionSpace T.structureMap T.line m) :
    σ ∈ ⨆ lam, weightSpace T m lam := by
  have h : σ ∈ ⨆ lam, P.weight m lam := by
    rw [(P.isInternal m).submodule_iSup_eq_top]
    exact Submodule.mem_top
  exact (iSup_mono (P.compat m)) h

/-- Every section is a finite sum of weight vectors, with explicit weights and restrictions. -/
theorem exists_weight_decomposition (m : ℕ) (σ : SectionSpace T.structureMap T.line m) :
    ∃ (S : Finset ℤ) (ξ : ℤ → SectionSpace T.structureMap T.line m)
      (y : ℤ → SectionSpace f L m), (∀ lam, T.Extends lam m (y lam) (ξ lam)) ∧
        σ = ∑ lam ∈ S, ξ lam := by
  classical
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp
    (P.mem_iSup_weightSpace m σ)
  choose y hy using hc
  refine ⟨c.support, c, y, hy, ?_⟩
  rw [← hsum, Finsupp.sum]

end SectionLinearization

end SGPT.TestCurve.TCLin
