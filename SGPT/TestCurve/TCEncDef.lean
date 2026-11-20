import SGPT.TestCurve.TestConfigFiltration
import SGPT.LineBundle.RiemannRochAmple
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Test configurations as schemes

Source: `rmk:PhongSturm` (chapter *Test curves*: *"`𝓕` is the filtration induced by a smooth test
configuration `(𝓧, 𝓛)` of `(X, L)`"*) and `rmk:NApotential:L862` (chapter *Non-Archimedean
pluripotential theory*). The book does not define test configurations; we follow
Boucksom–Hisamoto–Jonsson [BHJ17, Def. 2.1–2.3] (the definition used by Ross–Witt Nyström
[RWN14, §8] and Phong–Sturm [PS07]):

*a test configuration `(𝓧, 𝓛)` of `(X, L)` is a flat proper morphism `π : 𝓧 → 𝔸¹`, a line bundle
`𝓛` on `𝓧`, a `𝔾_m`-action on `𝓧` lifting the scaling action on `𝔸¹`, a `𝔾_m`-linearization of
`𝓛`, and an identification of `(𝓧_1, 𝓛_1)` with `(X, L)`.*

## The formal definition

`TestConfiguration f a` consists of

* a scheme `𝓧` (`space`) with a morphism `π : 𝓧 ⟶ 𝔸¹ = Spec ℂ[t]` (`toLine`) which is flat and
  proper;
* a line bundle `𝓛` on `𝓧` (`line`, with a rank-one atlas `atlas`, the setting of
  `SGPT.Foundations.Schemes`);
* the identification of `𝓧 ∖ 𝓧₀ = π⁻¹(𝔾_m)` with `X × 𝔾_m` over `𝔾_m`: a morphism
  `q : π⁻¹(𝔾_m) ⟶ X` over `ℂ` (`coord`) such that `(q, π) : π⁻¹(𝔾_m) ⟶ X ×_ℂ 𝔾_m` is an
  isomorphism (`coord_isIso`);
* the identification `𝓛|_{π⁻¹(𝔾_m)} ≅ q^* L`, in Čech form: for every chart `V_j` of the atlas
  `a` of `L` a frame `ε_j` of `𝓛` over `q⁻¹(V_j)` (`frame`) whose transition functions are the
  pull-backs `q^♯ g_{jk}` of the transition functions of `a` (`frame_transition`). (Line bundles
  with atlases on a common cover and equal transition functions are isomorphic by the isomorphism
  matching the frames; the `ε_j` are the pulled-back frames `q^* e_j`.)
* `IsGmEquivariant`: a `𝔾_m`-action on `𝓧` (an action of the group scheme
  `𝔾_m = Spec ℂ[T, T⁻¹]` on `𝓧` in the category of schemes over `ℂ`, Mathlib's `ModObj`) for
  which `π` is equivariant (`σ^* t = T · t`) and which is the scaling action of the second factor
  on `π⁻¹(𝔾_m) ≅ X × 𝔾_m` (`q ∘ σ = q ∘ pr₂`).

Given the action, the identification over `𝔾_m` is equivalent to the identification
`(𝓧_1, 𝓛_1) ≅ (X, L)` of the fibre over `1` used in [BHJ17] (the action carries `𝓧_1 × 𝔾_m`
isomorphically onto `π⁻¹(𝔾_m)`). The linearization of `𝓛` is not recorded: the only use of it is
that `𝓛|_{π⁻¹(𝔾_m)}` is the pull-back of `L` (recorded above) and, for normal `𝓧`, the canonical
linearization over `𝔾_m` extends uniquely (the divisors supported on `𝓧₀` are `𝔾_m`-invariant).
None of the results below uses the action; they hold for the larger class of flat proper models
with an identification over `𝔾_m`, so the universally quantified statements are stronger.

* `IsAmple`: `𝓛` is relatively ample: a power `𝓛^r` is relatively very ample, i.e.
  `𝓛^r ≅ ι^* 𝒪(1)` for a morphism `ι : 𝓧 → ℙ^N_ℂ` such that `(ι, π) : 𝓧 → ℙ^N_ℂ × 𝔸¹` is a
  closed immersion (the relative version of `SGPT.LineBundle.AmplePolarization`).
* `IsSmooth`: `𝓧` is smooth over `ℂ`.

## The induced filtration

For `s ∈ H⁰(X, L^m)` let `s̄` be its `𝔾_m`-invariant extension to `𝓧 ∖ 𝓧₀`, i.e. `q^* s`. The
filtration induced by the test configuration is ([BHJ17, §2.5], [RWN14, §8], [WN12])

`𝓕^λ H⁰(X, L^m) = {s : t^{-λ} s̄ extends to a section of 𝓛^m on 𝓧}`, `λ ∈ ℤ`.

In terms of the frames: `t^{-λ} s̄` extends iff there is `σ ∈ H⁰(𝓧, 𝓛^m)` whose coefficient in
the frame `ε_j^m` is `t^{-λ} · q^♯(s_j)` for every `j`, where `s_j` is the coefficient of `s` in
the frame `e_j^m` of `a` (a section over `π⁻¹(𝔾_m)` is determined by its coefficients on the cover
`q⁻¹(V_j)`). This is `TestConfiguration.piece`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite MonoidalCategory CartesianMonoidalCategory

/-! ### The affine line and the multiplicative group -/

/-- The affine line `𝔸¹_ℂ = Spec ℂ[t]`. -/
abbrev AffineLine : Scheme.{0} := Spec (.of (Polynomial ℂ))

/-- The structure morphism `𝔸¹ ⟶ Spec ℂ`. -/
def affineLineToBase : AffineLine ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The coordinate `t ∈ Γ(𝔸¹, 𝒪)`. -/
def coordT : Γ(AffineLine, ⊤) := (Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv Polynomial.X

/-- `𝔾_m = {t ≠ 0} ⊆ 𝔸¹`. -/
abbrev gmOpen : AffineLine.Opens := AffineLine.basicOpen coordT

/-- The multiplicative group `𝔾_m = Spec ℂ[T, T⁻¹]` as a group object over `Spec ℂ` (Mathlib's
`Spec` of the Hopf algebra `ℂ[ℤ]`). -/
abbrev GmGroup : Over (Spec (.of ℂ)) := (Spec (.of (LaurentPolynomial ℂ))).asOver (Spec (.of ℂ))

/-- The coordinate `T ∈ Γ(𝔾_m, 𝒪)` of the group scheme. -/
def coordGm : Γ(GmGroup.left, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial ℂ))).inv (LaurentPolynomial.T 1)

variable {Y : Scheme.{0}} (π : Y ⟶ AffineLine)

/-- The pull-back `t ∘ π ∈ Γ(𝓧, 𝒪)` of the coordinate. -/
def tFun : Γ(Y, ⊤) := π.appTop coordT

/-- The complement `𝓧 ∖ 𝓧₀ = π⁻¹(𝔾_m) = {t ∘ π ≠ 0}` of the central fibre. -/
abbrev offCentral : Y.Opens := Y.basicOpen (tFun π)

theorem offCentral_eq : offCentral π = π ⁻¹ᵁ gmOpen :=
  (Scheme.preimage_basicOpen_top π coordT).symm

/-- `π` restricted to `𝓧 ∖ 𝓧₀ ⟶ 𝔾_m`. -/
def toGm : (offCentral π).toScheme ⟶ gmOpen.toScheme :=
  π.resLE gmOpen (offCentral π) (offCentral_eq π).le

theorem toGm_comp_ι : toGm π ≫ gmOpen.ι = (offCentral π).ι ≫ π :=
  Scheme.Hom.resLE_comp_ι _ _

variable {π} {X : Scheme.{0}} (q : (offCentral π).toScheme ⟶ X)

/-- The open `q⁻¹(V) ⊆ 𝓧 ∖ 𝓧₀`, viewed as an open of `𝓧`. -/
abbrev overOpen (V : X.Opens) : Y.Opens := (offCentral π).ι ''ᵁ (q ⁻¹ᵁ V)

theorem overOpen_mono {V V' : X.Opens} (h : V ≤ V') : overOpen q V ≤ overOpen q V' :=
  (offCentral π).ι.image_mono (q.preimage_mono h)

theorem overOpen_le_offCentral (V : X.Opens) : overOpen q V ≤ offCentral π := by
  have := (offCentral π).ι.image_le_opensRange (q ⁻¹ᵁ V)
  simpa using this

/-- The pull-back of regular functions `q^♯ : Γ(X, V) ⟶ Γ(𝓧, q⁻¹(V))`. -/
def pullFun (V : X.Opens) : Γ(X, V) ⟶ Γ(Y, overOpen q V) :=
  q.app V ≫ ((offCentral π).ι.appIso (q ⁻¹ᵁ V)).inv

/-- The transition function of two frames of a line bundle, as a regular function. -/
def transitionFun {Z : Scheme.{0}} {M : Z.Modules} {U V W : Z.Opens} (e : LocalBundleFrame M U)
    (e' : LocalBundleFrame M V) (i : W ⟶ U) (j : W ⟶ V) : Γ(Z, W) :=
  (localBundleFrameTransition e e' i j).val

/-! ### Test configurations -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {L : X.Modules} (a : LineBundleAtlas L)

/-- **A test configuration of `(X, L)`** ([BHJ17, Def. 2.1–2.3]; see the module docstring for the
encoding of the identification over `𝔾_m` and of the `𝔾_m`-action, `IsGmEquivariant`). -/
structure TestConfiguration where
  /-- The total space `𝓧`. -/
  space : Scheme.{0}
  /-- The morphism `π : 𝓧 ⟶ 𝔸¹`. -/
  toLine : space ⟶ AffineLine
  /-- `π` is flat. -/
  flat : Flat toLine
  /-- `π` is proper. -/
  proper : IsProper toLine
  /-- The line bundle `𝓛`. -/
  line : space.Modules
  /-- A rank-one atlas of `𝓛`. -/
  atlas : LineBundleAtlas line
  /-- The projection `q : 𝓧 ∖ 𝓧₀ ⟶ X` of the identification `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`. -/
  coord : (offCentral toLine).toScheme ⟶ X
  /-- `q` is a morphism over `ℂ`. -/
  coord_over : coord ≫ f = (offCentral toLine).ι ≫ toLine ≫ affineLineToBase
  /-- `(q, π) : 𝓧 ∖ 𝓧₀ ⟶ X ×_ℂ 𝔾_m` is an isomorphism. -/
  coord_isIso : IsIso (pullback.lift (f := f) (g := gmOpen.ι ≫ affineLineToBase) coord
    (toGm toLine) (by rw [coord_over, ← Category.assoc, ← toGm_comp_ι, Category.assoc]))
  /-- The frame `ε_j = q^* e_j` of `𝓛` over `q⁻¹(V_j)`. -/
  frame : ∀ j : a.I, LocalBundleFrame line (overOpen coord (a.opens j))
  /-- The transition functions of the frames `ε_j` are the pull-backs of those of `a`: this is
  the identification `𝓛|_{𝓧 ∖ 𝓧₀} ≅ q^* L`. -/
  frame_transition : ∀ j k : a.I,
    transitionFun (frame j) (frame k)
        (homOfLE (overOpen_mono coord inf_le_left))
        (homOfLE (overOpen_mono coord inf_le_right)) =
      pullFun coord (a.opens j ⊓ a.opens k)
        (transitionFun (a.frame j) (a.frame k) (homOfLE inf_le_left) (homOfLE inf_le_right))

namespace TestConfiguration

variable {f a} (T : TestConfiguration f a)

attribute [instance] TestConfiguration.flat TestConfiguration.proper

/-- The structure morphism `𝓧 ⟶ Spec ℂ`. -/
def structureMap : T.space ⟶ Spec (.of ℂ) := T.toLine ≫ affineLineToBase

/-- `𝓧` as a scheme over `Spec ℂ`. -/
abbrev overBase : Over (Spec (.of ℂ)) := Over.mk T.structureMap

/-- **The `𝔾_m`-action** ([BHJ17, Def. 2.1]): there is an action `σ : 𝔾_m × 𝓧 ⟶ 𝓧` of the group
scheme `𝔾_m` over `ℂ` (unit and associativity axioms: Mathlib's `ModObj`) such that `π` is
equivariant for the scaling action on `𝔸¹` (`σ^*(t ∘ π) = T · (t ∘ π)`) and such that on
`𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` it is the action on the second factor (`q ∘ σ = q ∘ pr₂`). -/
def IsGmEquivariant : Prop :=
  ∃ σ : ModObj GmGroup T.overBase,
    (σ.smul.left).appTop (tFun T.toLine) =
        (fst GmGroup T.overBase).left.appTop coordGm *
          (snd GmGroup T.overBase).left.appTop (tFun T.toLine) ∧
      ∃ h : (snd GmGroup T.overBase).left ⁻¹ᵁ offCentral T.toLine ≤
          σ.smul.left ⁻¹ᵁ offCentral T.toLine,
        σ.smul.left.resLE (offCentral T.toLine) _ h ≫ T.coord =
          (snd GmGroup T.overBase).left.resLE (offCentral T.toLine) _ le_rfl ≫ T.coord

/-- **Ample test configurations**: `𝓛` is relatively ample, i.e. some power `𝓛^r` (`r > 0`) is
relatively very ample: `𝓛^r ≅ ι^* 𝒪(1)` for a morphism `ι : 𝓧 ⟶ ℙ^N_ℂ` such that
`(ι, π) : 𝓧 ⟶ ℙ^N_ℂ ×_ℂ 𝔸¹ = ℙ^N_{𝔸¹}` is a closed immersion. -/
def IsAmple : Prop :=
  ∃ (r : ℕ) (_ : 0 < r) (N : ℕ) (ι : T.space ⟶ polynomialProj ℂ N)
    (h : ι ≫ polynomialProjStructureMap ℂ N = T.toLine ≫ affineLineToBase),
    IsClosedImmersion (pullback.lift ι T.toLine h) ∧
      Nonempty (bundleTensorPower T.line r ≅
        (Scheme.Modules.pullback ι).obj (polynomialProjTwistingLine ℂ N).sheaf)

/-- **Smooth test configurations**: the total space `𝓧` is smooth over `ℂ`. -/
def IsSmooth : Prop := Smooth T.structureMap

end TestConfiguration

end SGPT.TestCurve.TCEnc
