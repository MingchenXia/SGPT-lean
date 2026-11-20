import SGPT.TestCurve.TCEncExhaustive
import SGPT.TestCurve.TCEncIntegral

/-!
# The normalized `ℤ`-filtration of a test configuration

Source: `rmk:PhongSturm`, `rmk:NApotential:L862` (*"`𝓕` is the filtration induced by a test
configuration"*), [BHJ17, §2.5]. For a test configuration `(𝓧, 𝓛)` of an integral projective
`(X, L)` (then `𝓧` is integral, `TestConfiguration.isIntegral_space`), the filtration

`𝓕^λ H⁰(X, L^m) = {s : t^{-λ} s̄ extends to a section of 𝓛^m on 𝓧}`

is a `ℤ`-filtration of `R(X, L)` in the sense of `SGPT.TestCurve.TestConfig.SectionZFiltration`
(decreasing, multiplicative, separating and exhaustive in every degree), normalized by
`𝓕⁰ H⁰(X, 𝒪_X) = H⁰(X, 𝒪_X)`. This is the encoding used by
`SGPT.TestCurve.TestConfig.PhongSturmRemark` and by the Duistermaat–Heckman results of
`SGPT.NAPotential.NANS.TestConfig`.

## Main definitions

* `TestConfiguration.zFiltration T E`: the `ℤ`-filtration induced by `T`.
* `TestConfiguration.FiltrationFinitelyGenerated T E`: its Rees algebra is finitely generated.
  For *ample* test configurations this is the first half of [BHJ17, Prop. 2.15] (it follows from
  the finite generation of `⊕_m H⁰(𝓧, m𝓛)` over `ℂ[t]` for `𝓛` relatively ample, a relative
  form of Serre's theorem); it is **not** proved here.
* `TestConfiguration.inducedFiltration T E hfg`: the induced filtration of `R(X, L)` in the sense
  of `def:testcurve:L1134` (`𝓕^λ = 𝓕^{⌈λ⌉}`), when the Rees algebra is finitely generated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TestConfig

namespace TestConfiguration

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-- The total space of a test configuration of an integral projective `X` is integral. -/
theorem isIntegral_space_of_embedding [IsIntegral X] (E : ClosedProjectiveEmbedding f) :
    IsIntegral T.space := by
  have := E.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact T.isIntegral_space

/-- **The `ℤ`-filtration of `R(X, L)` induced by a test configuration** of an integral projective
`(X, L)` ([BHJ17, §2.5], [RWN14, §8]): `𝓕^λ H⁰(X, L^m) = {s : t^{-λ} s̄ extends to 𝓧}`
(`TestConfiguration.piece`). It is decreasing (`piece_anti`), multiplicative (`mul_mem_piece`),
separating (`exists_piece_eq_bot`) and exhaustive (`exists_piece_eq_top`). -/
def zFiltration [IsIntegral X] (E : ClosedProjectiveEmbedding f) : SectionZFiltration f a where
  piece := T.piece
  antitone_piece k := fun _ _ h => T.piece_anti h k
  mul_mem _ _ _ _ _ _ hs ht := T.mul_mem_piece hs ht
  separating k := by
    have := SectionSpace.finiteDimensional f E a k
    have := T.isIntegral_space_of_embedding E
    exact T.exists_piece_eq_bot k
  exhaustive k := by
    have := SectionSpace.finiteDimensional f E a k
    have := T.isIntegral_space_of_embedding E
    exact T.exists_piece_eq_top k

@[simp] theorem zFiltration_piece [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (lam : ℤ) (k : ℕ) : (T.zFiltration E).piece lam k = T.piece lam k := rfl

/-- **Normalization**: `𝓕⁰ H⁰(X, 𝒪_X) = H⁰(X, 𝒪_X)`. -/
theorem zFiltration_piece_zero_zero [IsIntegral X] (E : ClosedProjectiveEmbedding f) :
    (T.zFiltration E).piece 0 0 = ⊤ := by
  have := E.universallyClosed
  exact T.piece_zero_zero

/-- Finite generation of the Rees algebra `⊕_{m, λ} t^{-λ} 𝓕^λ H⁰(X, L^m)` of the filtration of
`T`. For an ample test configuration this is the finite-generation half of [BHJ17, Prop. 2.15]
(the Rees algebra is `⊕_m H⁰(𝓧, m𝓛)`, finitely generated over `ℂ[t]` since `𝓛` is relatively
ample and `π` is proper); not proved here. -/
def FiltrationFinitelyGenerated [IsIntegral X] (E : ClosedProjectiveEmbedding f) : Prop :=
  (T.zFiltration E).IsFinitelyGenerated

/-- **The filtration of `R(X, L)` induced by a test configuration**, in the sense of
`def:testcurve:L1134` (`𝓕^λ = 𝓕^{⌈λ⌉}`): defined when the Rees algebra of `T.zFiltration` is
finitely generated (which [BHJ17, Prop. 2.15] asserts for ample test configurations), so that
the filtration is linearly bounded. -/
def inducedFiltration [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (hfg : T.FiltrationFinitelyGenerated E) : SectionFiltration f a :=
  (T.zFiltration E).fgFiltration hfg (T.zFiltration_piece_zero_zero E)

@[simp] theorem inducedFiltration_piece [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (hfg : T.FiltrationFinitelyGenerated E) (μ : ℝ) (k : ℕ) :
    (T.inducedFiltration E hfg).piece μ k = T.piece ⌈μ⌉ k := rfl

end TestConfiguration

end SGPT.TestCurve.TCEnc
