import SGPT.TestCurve.TCEncFiltration

/-!
# Geometric `𝔾_m`-linearizations of test configurations

Source: `rmk:PhongSturm` (chapter *Test curves*), `rmk:Okounkov:L2335` (chapter *Okounkov
bodies*) and `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*) speak of
"the filtration induced by a test configuration `(𝓧, 𝓛)` of `(X, L)`". The book does not define
test configurations; the standard definition is [BHJ17, Def. 2.1–2.3]: a flat proper
`π : 𝓧 → 𝔸¹` with a `𝔾_m`-action `σ` lifting the scaling action on `𝔸¹`, a line bundle `𝓛` on
`𝓧` with a **`𝔾_m`-linearization**, and a `𝔾_m`-equivariant identification of `(𝓧_1, 𝓛_1)` with
`(X, L)`.

Following [BHJ17, §1] (Mumford's GIT, Def. 1.6), a `𝔾_m`-linearization of `𝓛` is an isomorphism

`Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` of line bundles on `𝔾_m × 𝓧`

satisfying the cocycle condition on `𝔾_m × 𝔾_m × 𝓧`:

`(μ × 1)^* Φ = pr₂₃^* Φ ∘ (1 × σ)^* Φ`,

i.e. `Φ_{(gh, x)} = Φ_{(h, x)} ∘ Φ_{(g, hx)}` for the fibre maps `Φ_{(g,x)} : 𝓛_{gx} → 𝓛_x`.

## The encoding

Lane TC-ENC (`TCEnc.TestConfiguration`) records `𝓛` as a sheaf of modules with a rank-one
atlas, and the identification `𝓛|_{𝓧 ∖ 𝓧₀} ≅ q^* L` in Čech form: frames `ε_j` of `𝓛` over
`q⁻¹(V_j)` whose transition functions are the pull-backs `q^♯ g_{jk}`. We encode the
linearization in the same (Čech) way. Let `(U_i, e_i)_{i ∈ I}` be the atlas
`T.extAtlas` of `𝓛` (the charts of `𝓛` and the frames `ε_j`), with transition functions
`τ_{ii'}` (`e_i = τ_{ii'} e_{i'}` on `U_i ∩ U_{i'}`, `atlasTransition`). The pulled-back bundles
`g^* 𝓛` along `g : Z ⟶ 𝓧` are the line bundles with frames `g^* e_i` over `g⁻¹(U_i)` and
transition functions `g^♯ τ_{ii'}`, so an isomorphism `Φ : g^* 𝓛 ≅ h^* 𝓛` is the same as its
matrix coefficients

`Φ(g^* e_i) = φ_{ij} · h^* e_j` on `g⁻¹(U_i) ∩ h⁻¹(U_j)`, `φ_{ij}` a unit,

subject to the compatibility with the transition functions
`g^♯(τ_{ii'}) φ_{i'j'} = φ_{ij} h^♯(τ_{jj'})` (`IsCechIso`). The cocycle condition becomes
`(μ × 1)^♯ φ_{ij} = (1 × σ)^♯ φ_{ik} · pr₂₃^♯ φ_{kj}` (`IsCocycle`).

`GeomLinearization T` consists of

* a `𝔾_m`-action `σ` on `𝓧` (Mathlib's `ModObj` of the group scheme `𝔾_m = Spec ℂ[T, T⁻¹]` over
  `ℂ`) lifting the scaling action of `𝔸¹` and acting on the second factor of
  `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` (`GmAction`, the data of TC-ENC's `IsGmEquivariant`);
* an isomorphism `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` (`phi`, `isCechIso`) satisfying the cocycle condition
  (`cocycle`);
* compatibility with the identification `(𝓧 ∖ 𝓧₀, 𝓛) ≅ (X × 𝔾_m, p₁^* L)`: on
  `𝔾_m × (𝓧 ∖ 𝓧₀)` the linearization is the canonical linearization of `q^* L`
  (`σ^* q^* L = (q σ)^* L = (q pr₂)^* L = pr₂^* q^* L`), i.e. `Φ(σ^* ε_j) = pr₂^* ε_j`
  (`phi_frame`). In [BHJ17] the identification over `𝔾_m` is obtained from the identification
  `(𝓧_1, 𝓛_1) ≅ (X, L)` by the action, so it is equivariant by construction.

`GeomLinearizedTestConfiguration f a` is a TC-ENC test configuration with a geometric
linearization: the test configurations of [BHJ17, Def. 2.1–2.3]. That it induces the
`𝔾_m`-representation on the sections `H⁰(𝓧, m𝓛)` used by lane TC-LIN (`SectionLinearization`)
is proved in `GeomLinSection`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open SGPT.TestCurve.TCEnc

/-! ### Čech isomorphisms between pulled-back line bundles -/

section Cech

variable {Y Z : Scheme.{0}} {M : Y.Modules} (b : LineBundleAtlas M)

/-- The transition function `τ_{ii'}` of an atlas: `e_i = τ_{ii'} e_{i'}` on `U_i ∩ U_{i'}` (the
coefficient of a section in the frame `e_{i'}` is `τ_{ii'}` times its coefficient in `e_i`). -/
abbrev atlasTransition (i i' : b.I) : Γ(Y, b.opens i ⊓ b.opens i') :=
  transitionFun (b.frame i) (b.frame i') (homOfLE inf_le_left) (homOfLE inf_le_right)

variable (g h : Z ⟶ Y)

/-- The open `g⁻¹(U_i) ∩ h⁻¹(U_j)`, on which `g^* e_i` and `h^* e_j` are both frames. -/
abbrev cechOpen (i j : b.I) : Z.Opens := g ⁻¹ᵁ b.opens i ⊓ h ⁻¹ᵁ b.opens j

/-- The open `g⁻¹(U_i ∩ U_{i'}) ∩ h⁻¹(U_j ∩ U_{j'})`. -/
abbrev cechOverlap (i i' j j' : b.I) : Z.Opens :=
  g ⁻¹ᵁ (b.opens i ⊓ b.opens i') ⊓ h ⁻¹ᵁ (b.opens j ⊓ b.opens j')

theorem cechOverlap_le_left (i i' j j' : b.I) :
    cechOverlap b g h i i' j j' ≤ cechOpen b g h i j :=
  inf_le_inf (g.preimage_mono inf_le_left) (h.preimage_mono inf_le_left)

theorem cechOverlap_le_right (i i' j j' : b.I) :
    cechOverlap b g h i i' j j' ≤ cechOpen b g h i' j' :=
  inf_le_inf (g.preimage_mono inf_le_right) (h.preimage_mono inf_le_right)

/-- **Čech form of an isomorphism `Φ : g^* M ≅ h^* M`** of pulled-back line bundles: units
`φ_{ij}` on `g⁻¹(U_i) ∩ h⁻¹(U_j)` (`Φ(g^* e_i) = φ_{ij} · h^* e_j`) compatible with the transition
functions, `g^♯(τ_{ii'}) · φ_{i'j'} = φ_{ij} · h^♯(τ_{jj'})` on
`g⁻¹(U_i ∩ U_{i'}) ∩ h⁻¹(U_j ∩ U_{j'})` (both sides are the coefficient of `Φ(g^* e_i)` in
`h^* e_{j'}`). -/
def IsCechIso (φ : ∀ i j : b.I, (Γ(Z, cechOpen b g h i j))ˣ) : Prop :=
  ∀ i i' j j' : b.I,
    g.appLE (b.opens i ⊓ b.opens i') (cechOverlap b g h i i' j j') inf_le_left
        (atlasTransition b i i') *
      Z.presheaf.map (homOfLE (cechOverlap_le_right b g h i i' j j')).op
        ((φ i' j' : Γ(Z, cechOpen b g h i' j'))) =
    Z.presheaf.map (homOfLE (cechOverlap_le_left b g h i i' j j')).op
        ((φ i j : Γ(Z, cechOpen b g h i j))) *
      h.appLE (b.opens j ⊓ b.opens j') (cechOverlap b g h i i' j j') inf_le_right
        (atlasTransition b j j')

end Cech

/-! ### The `𝔾_m`-action -/

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- `𝔾_m × 𝓧` (the fibre product over `ℂ`). -/
abbrev gmProd (T : TestConfiguration f a) : Scheme.{0} := (GmGroup ⊗ T.overBase).left

/-- The second projection `pr₂ : 𝔾_m × 𝓧 ⟶ 𝓧`. -/
abbrev gmProj (T : TestConfiguration f a) : gmProd T ⟶ T.space := (snd GmGroup T.overBase).left

/-- `(μ × 1) : 𝔾_m × 𝔾_m × 𝓧 ⟶ 𝔾_m × 𝓧`, `(g, h, x) ↦ (gh, x)`. -/
abbrev mulMap (T : TestConfiguration f a) : ((GmGroup ⊗ GmGroup) ⊗ T.overBase).left ⟶ gmProd T :=
  (μ[GmGroup] ▷ T.overBase).left

/-- `pr₂₃ : 𝔾_m × 𝔾_m × 𝓧 ⟶ 𝔾_m × 𝓧`, `(g, h, x) ↦ (h, x)`. -/
abbrev projMap (T : TestConfiguration f a) : ((GmGroup ⊗ GmGroup) ⊗ T.overBase).left ⟶ gmProd T :=
  ((α_ GmGroup GmGroup T.overBase).hom ≫ snd GmGroup (GmGroup ⊗ T.overBase)).left

/-- **A `𝔾_m`-action on the total space of a test configuration** ([BHJ17, Def. 2.1]): an action
`σ : 𝔾_m × 𝓧 ⟶ 𝓧` of the group scheme `𝔾_m` over `ℂ` (unit and associativity axioms: Mathlib's
`ModObj`) such that `π` is equivariant for the scaling action of `𝔸¹` (`σ^*(t ∘ π) = T · (t ∘ π)`)
and which is the action on the second factor of `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` (`q ∘ σ = q ∘ pr₂`). These are
the data of TC-ENC's `TestConfiguration.IsGmEquivariant`. -/
structure GmAction (T : TestConfiguration f a) where
  /-- The action `σ`. -/
  act : ModObj GmGroup T.overBase
  /-- `π` is equivariant: `σ^* t = T · pr₂^* t`. -/
  smul_tFun : act.smul.left.appTop (tFun T.toLine) =
    (fst GmGroup T.overBase).left.appTop coordGm * (gmProj T).appTop (tFun T.toLine)
  /-- `σ` preserves `𝓧 ∖ 𝓧₀`. -/
  le_preimage_offCentral : gmProj T ⁻¹ᵁ offCentral T.toLine ≤
    act.smul.left ⁻¹ᵁ offCentral T.toLine
  /-- `q ∘ σ = q ∘ pr₂` on `𝔾_m × (𝓧 ∖ 𝓧₀)`. -/
  coord_smul : act.smul.left.resLE (offCentral T.toLine) _ le_preimage_offCentral ≫ T.coord =
    (gmProj T).resLE (offCentral T.toLine) _ le_rfl ≫ T.coord

namespace GmAction

variable {T : TestConfiguration f a} (A : GmAction T)

/-- The action morphism `σ : 𝔾_m × 𝓧 ⟶ 𝓧`. -/
abbrev smulMap : gmProd T ⟶ T.space := A.act.smul.left

/-- A `GmAction` is TC-ENC's `IsGmEquivariant`. -/
theorem isGmEquivariant (A : GmAction T) : T.IsGmEquivariant :=
  ⟨A.act, A.smul_tFun, A.le_preimage_offCentral, A.coord_smul⟩

/-- `(1 × σ) : 𝔾_m × 𝔾_m × 𝓧 ⟶ 𝔾_m × 𝓧`, `(g, h, x) ↦ (g, hx)`. -/
abbrev actMap : ((GmGroup ⊗ GmGroup) ⊗ T.overBase).left ⟶ gmProd T :=
  ((α_ GmGroup GmGroup T.overBase).hom ≫ GmGroup ◁ A.act.smul).left

/-- The open of `𝔾_m × 𝔾_m × 𝓧` on which the cocycle condition for `(i, k, j)` is stated:
`{(g, h, x) : ghx ∈ U_i, hx ∈ U_k, x ∈ U_j}`. -/
abbrev cocycleOpen (i k j : T.extAtlas.I) : ((GmGroup ⊗ GmGroup) ⊗ T.overBase).left.Opens :=
  mulMap T ⁻¹ᵁ cechOpen T.extAtlas A.smulMap (gmProj T) i j ⊓
    A.actMap ⁻¹ᵁ cechOpen T.extAtlas A.smulMap (gmProj T) i k ⊓
    projMap T ⁻¹ᵁ cechOpen T.extAtlas A.smulMap (gmProj T) k j

/-- **The cocycle condition** `(μ × 1)^* Φ = pr₂₃^* Φ ∘ (1 × σ)^* Φ` for an isomorphism
`Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` with matrix coefficients `φ_{ij}`: in the frames,
`(μ × 1)^♯ φ_{ij} = (1 × σ)^♯ φ_{ik} · pr₂₃^♯ φ_{kj}` (the fibre maps
`Φ_{(g,x)} : 𝓛_{gx} → 𝓛_x` satisfy `Φ_{(gh, x)} = Φ_{(h, x)} ∘ Φ_{(g, hx)}`). -/
def IsCocycle (φ : ∀ i j : T.extAtlas.I,
    (Γ(gmProd T, cechOpen T.extAtlas A.smulMap (gmProj T) i j))ˣ) : Prop :=
  ∀ i k j : T.extAtlas.I,
    (mulMap T).appLE _ (A.cocycleOpen i k j) (inf_le_left.trans inf_le_left)
        ((φ i j : Γ(gmProd T, _))) =
      A.actMap.appLE _ (A.cocycleOpen i k j) (inf_le_left.trans inf_le_right)
          ((φ i k : Γ(gmProd T, _))) *
        (projMap T).appLE _ (A.cocycleOpen i k j) inf_le_right ((φ k j : Γ(gmProd T, _)))

end GmAction

/-! ### Linearizations -/

/-- **A `𝔾_m`-linearization of `𝓛`** ([BHJ17, Def. 2.2], [MFK, Def. 1.6]), compatible with the
identification over `𝔾_m`: a `𝔾_m`-action `σ` on `𝓧` (`GmAction`) and an isomorphism
`Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` on `𝔾_m × 𝓧`, in Čech form (see the module docstring), satisfying the
cocycle condition and equal to the canonical linearization of `q^* L` over `𝔾_m × (𝓧 ∖ 𝓧₀)`
(`Φ(σ^* ε_j) = pr₂^* ε_j`). -/
structure GeomLinearization (T : TestConfiguration f a) where
  /-- The `𝔾_m`-action `σ` on `𝓧`. -/
  action : GmAction T
  /-- The matrix coefficients `Φ(σ^* e_i) = φ_{ij} · pr₂^* e_j` of `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛`. -/
  phi : ∀ i j : T.extAtlas.I, (Γ(gmProd T, cechOpen T.extAtlas action.smulMap (gmProj T) i j))ˣ
  /-- `Φ` is a well-defined isomorphism `σ^* 𝓛 ≅ pr₂^* 𝓛`. -/
  isCechIso : IsCechIso T.extAtlas action.smulMap (gmProj T) phi
  /-- The cocycle condition. -/
  cocycle : action.IsCocycle phi
  /-- Compatibility with the identification `(𝓧 ∖ 𝓧₀, 𝓛) ≅ (X × 𝔾_m, p₁^* L)`:
  `Φ(σ^* ε_j) = pr₂^* ε_j`. -/
  phi_frame : ∀ k : a.I, phi (.inr k) (.inr k) = 1

/-- **A test configuration with a `𝔾_m`-linearized line bundle** ([BHJ17, Def. 2.1–2.3]): lane
TC-ENC's test configuration (flat proper `π : 𝓧 → 𝔸¹`, line bundle `𝓛`, identification over
`𝔾_m`) together with a `𝔾_m`-action on `𝓧` and a geometric `𝔾_m`-linearization of `𝓛`
(`GeomLinearization`). -/
structure GeomLinearizedTestConfiguration (f : X ⟶ Spec (.of ℂ)) (a : LineBundleAtlas L)
    extends TestConfiguration f a where
  /-- The `𝔾_m`-action and the `𝔾_m`-linearization of `𝓛`. -/
  linearization : GeomLinearization toTestConfiguration

theorem GeomLinearizedTestConfiguration.isGmEquivariant (T : GeomLinearizedTestConfiguration f a) :
    T.IsGmEquivariant :=
  T.linearization.action.isGmEquivariant

end SGPT.TestCurve.GeomLin
