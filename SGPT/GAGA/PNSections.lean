import SGPT.GAGA.CoreSubquotient
import SGPT.GAGA.PNCech

/-!
# Čech complexes of coherent subquotients on `ℙᴺ` for the cover `K_i = {|z_j| ≤ ρ |z_i|}`

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), milestone M3.2 of the plan in
`blueprint/src/claude-serre-core.tex`.

**Cone model.** A coherent sheaf on `ℙᴺ` is recorded on the cone `ℂ^{N+1} ∖ 0` as a
subquotient `F = M/N` (the `Subquotient`) whose germ modules are invariant under
the action of `ℂ*` (`IsConeInvariant`). A section of the twist `F(n)` over a subset `K` of
`ℙᴺ` (recorded by its cone) is a tuple which is holomorphic on an open cone `U ⊇ K`,
homogeneous of degree `n` there, and has its germs in `M` (`IsHomSection`). The sections over
`K` form the module `Γ(K, M(n))/Γ(K, N(n))` (`sectionModule`).

**The cover.** For `ρ ≥ 1` the closed sets `K_i = {[z] : |z_j| ≤ ρ |z_i| ∀ j}` cover `ℙᴺ`;
`coverSet ρ s` is the cone over `K_s = ⋂_{i ∈ s} K_i` (and `coverSet ρ ∅ = ℂ^{N+1} ∖ 0`). The
restrictions `Γ(K_s) → Γ(K_t)` (`s ⊆ t`) form a coefficient system on the finite subsets of
`Fin (N+1)` (`coverSystem F n ρ`), whose Čech complex and cohomology are those of
`PNCech`. Morphisms of subquotients given by homogeneous matrices of degree `d` induce
morphisms `coverSystem F n ρ → coverSystem G (n + d) ρ` (`coverHom`).

**Theorem B as an explicit hypothesis.** By Cartan's Theorem B in degree one on the compact
sets `K_s` (`s ≠ ∅`), which are holomorphically convex compact sets in an affine chart (compact
Reinhardt Laurent polyhedra), the section functor `Γ(K_s, -)` is exact on coherent sheaves.
We use it in the form `SectionsDecompose K`: every section over `K` of a sum `P + A(Q)` of
`ℂ*`-invariant coherent modules is `p + A a` with sections `p` of `P` and `a` of `Q` over `K`.
This is the hypothesis that lane SERRE-CORE2 discharges (see the blueprint
`claude-serre-pn.tex`, node `claude-serre-pn:interface-B`). Under it, a short exact sequence
of invariant subquotients with homogeneous matrices gives a short exact sequence of coefficient
systems (`coverSystem_shortExact`), hence the long exact Čech cohomology sequence
(`coverSystem_les`). The injectivity part does not need the hypothesis
(`coverHom_injective`).

Blueprint: `claude-serre-pn.tex`, nodes `claude-serre-pn:sections`,
`claude-serre-pn:interface-B`, `claude-serre-pn:cover-les`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

namespace SGPT.GAGA.PN

/-! ### Cones and homogeneous tuples -/

section Homogeneous

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A set invariant under the action of `ℂ*`. -/
def IsCone (U : Set X) : Prop :=
  ∀ c : ℂ, c ≠ 0 → ∀ z ∈ U, c • z ∈ U

theorem IsCone.inter {U V : Set X} (hU : IsCone U) (hV : IsCone V) : IsCone (U ∩ V) :=
  fun c hc _ hz => ⟨hU c hc _ hz.1, hV c hc _ hz.2⟩

theorem isCone_ne_zero : IsCone {z : X | z ≠ 0} :=
  fun _ hc _ hz => smul_ne_zero hc hz

/-- The tuple `a` is holomorphic and homogeneous of degree `n` on the open cone
`U ⊆ X ∖ 0`. -/
structure IsHomOn (U : Set X) (n : ℤ) (a : ι → X → ℂ) : Prop where
  isOpen : IsOpen U
  isCone : IsCone U
  subset : U ⊆ {z | z ≠ 0}
  diff : ∀ j, DifferentiableOn ℂ (a j) U
  hom : ∀ z ∈ U, ∀ c : ℂ, c ≠ 0 → ∀ j, a j (c • z) = c ^ n * a j z

theorem IsHomOn.inter {U W : Set X} {n : ℤ} {a : ι → X → ℂ} (h : IsHomOn U n a)
    (hW : IsOpen W) (hWc : IsCone W) : IsHomOn (U ∩ W) n a :=
  ⟨h.isOpen.inter hW, h.isCone.inter hWc, inter_subset_left.trans h.subset,
    fun j => (h.diff j).mono inter_subset_left, fun z hz => h.hom z hz.1⟩

theorem IsHomOn.inter_left {U W : Set X} {n : ℤ} {a : ι → X → ℂ} (h : IsHomOn U n a)
    (hW : IsOpen W) (hWc : IsCone W) : IsHomOn (W ∩ U) n a := by
  rw [inter_comm]
  exact h.inter hW hWc

theorem isHomOn_zero {U : Set X} (hU : IsOpen U) (hUc : IsCone U) (hU0 : U ⊆ {z | z ≠ 0})
    (n : ℤ) : IsHomOn U n (0 : ι → X → ℂ) :=
  ⟨hU, hUc, hU0, fun _ => differentiableOn_const 0, fun _ _ _ _ _ => by simp⟩

theorem IsHomOn.add {U : Set X} {n : ℤ} {a b : ι → X → ℂ} (ha : IsHomOn U n a)
    (hb : IsHomOn U n b) : IsHomOn U n (a + b) :=
  ⟨ha.isOpen, ha.isCone, ha.subset, fun j => (ha.diff j).add (hb.diff j),
    fun z hz c hc j => by simp only [Pi.add_apply]; rw [ha.hom z hz c hc, hb.hom z hz c hc]; ring⟩

theorem IsHomOn.smul {U : Set X} {n : ℤ} {a : ι → X → ℂ} (ha : IsHomOn U n a) (r : ℂ) :
    IsHomOn U n (r • a) :=
  ⟨ha.isOpen, ha.isCone, ha.subset, fun j => (ha.diff j).const_smul r,
    fun z hz c hc j => by simp only [Pi.smul_apply, smul_eq_mul]; rw [ha.hom z hz c hc]; ring⟩

theorem IsHomOn.sub {U : Set X} {n : ℤ} {a b : ι → X → ℂ} (ha : IsHomOn U n a)
    (hb : IsHomOn U n b) : IsHomOn U n (a - b) :=
  ⟨ha.isOpen, ha.isCone, ha.subset, fun j => (ha.diff j).sub (hb.diff j),
    fun z hz c hc j => by simp only [Pi.sub_apply]; rw [ha.hom z hz c hc, hb.hom z hz c hc]; ring⟩

/-- A matrix of functions holomorphic on `X ∖ 0` and homogeneous of degree `d`. -/
structure IsHomMatrix (A : κ → ι → X → ℂ) (d : ℤ) : Prop where
  holAt : ∀ x : X, x ≠ 0 → ∀ i j, HolAt (A i j) x
  hom : ∀ z : X, z ≠ 0 → ∀ c : ℂ, c ≠ 0 → ∀ i j, A i j (c • z) = c ^ d * A i j z

/-- Homogeneous matrices of degree `d` raise the degree of homogeneous tuples by `d`. -/
theorem IsHomOn.matApply {U : Set X} {n d : ℤ} {a : ι → X → ℂ} (ha : IsHomOn U n a)
    {A : κ → ι → X → ℂ} (hA : IsHomMatrix A d) : IsHomOn U (n + d) (matApply A a) := by
  refine ⟨ha.isOpen, ha.isCone, ha.subset, fun i => ?_, fun z hz c hc i => ?_⟩
  · refine DifferentiableOn.fun_sum fun j _ => ?_
    refine DifferentiableOn.mul (fun x hx => ?_) (ha.diff j)
    exact (hA.holAt x (ha.subset hx) i j).differentiableAt.differentiableWithinAt
  · simp only [Core.matApply_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hA.hom z (ha.subset hz) c hc i j, ha.hom z hz c hc j, zpow_add₀ hc]
    ring

end Homogeneous

/-! ### Homogeneous sections over a set -/

section Sections

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The germ module `P` is invariant under the action of `ℂ*` on `X ∖ 0`: `a ∈ P_y` iff
`a ∘ c⁻¹ ∈ P_{c y}`. These are the germ modules of coherent sheaves on `ℙ(X)` (pulled back to
the cone). -/
def IsConeInvariant (P : GermModule X ι) : Prop :=
  ∀ y : X, y ≠ 0 → ∀ c : ℂ, c ≠ 0 → ∀ a : ι → X → ℂ,
    P.mem y a ↔ P.mem (c • y) (fun j z => a j (c⁻¹ • z))

/-- `a` is a section of `P(n)` over `K`: holomorphic and homogeneous of degree `n` on an open
cone `U ⊇ K` in `X ∖ 0`, with germs in `P` at every point of `U`. -/
def IsHomSection (P : GermModule X ι) (n : ℤ) (K : Set X) (a : ι → X → ℂ) : Prop :=
  ∃ U : Set X, K ⊆ U ∧ IsHomOn U n a ∧ ∀ y ∈ U, P.mem y a

theorem IsHomSection.mono {P : GermModule X ι} {n : ℤ} {K K' : Set X} {a : ι → X → ℂ}
    (h : IsHomSection P n K a) (hK : K' ⊆ K) : IsHomSection P n K' a := by
  obtain ⟨U, hKU, hU, hP⟩ := h
  exact ⟨U, hK.trans hKU, hU, hP⟩

theorem IsHomSection.le {P P' : GermModule X ι} {n : ℤ} {K : Set X} {a : ι → X → ℂ}
    (h : IsHomSection P n K a) (hPP' : P.LeOn P' {z | z ≠ 0}) : IsHomSection P' n K a := by
  obtain ⟨U, hKU, hU, hP⟩ := h
  exact ⟨U, hKU, hU, fun y hy => hPP' y (hU.subset hy) a (hP y hy)⟩

/-- A tuple which is holomorphic and homogeneous on an open cone around `K` and agrees on an
open cone around `K` with a section of a coherent `P` is a section of `P`. -/
theorem isHomSection_of_eqOn {P : GermModule X ι} (hP : P.IsCoherentOn {z | z ≠ 0}) {n : ℤ}
    {K : Set X} {a p : ι → X → ℂ} {U W : Set X} (hKU : K ⊆ U) (ha : IsHomOn U n a)
    (hp : IsHomSection P n K p) (hKW : K ⊆ W) (hW : IsOpen W) (hWc : IsCone W)
    (hap : ∀ z ∈ W, ∀ j, a j z = p j z) : IsHomSection P n K a := by
  obtain ⟨V, hKV, hV, hpP⟩ := hp
  refine ⟨(U ∩ W) ∩ V, fun z hz => ⟨⟨hKU hz, hKW hz⟩, hKV hz⟩,
    (ha.inter hW hWc).inter hV.isOpen hV.isCone, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := ha.subset hy.1.1
  have hev : ∀ᶠ z in 𝓝 y, z ∈ W := hW.mem_nhds hy.1.2
  exact (hP y hy0).congr_mem (hpP y hy.2) fun j => hev.mono fun z hz => (hap z hz j).symm

theorem isHomSection_zero {P : GermModule X ι} (hP : P.IsCoherentOn {z | z ≠ 0}) (n : ℤ)
    {K : Set X} (hK : K ⊆ {z | z ≠ 0}) : IsHomSection P n K 0 :=
  ⟨{z | z ≠ 0}, hK, isHomOn_zero isOpen_ne isCone_ne_zero subset_rfl n,
    fun y hy => (hP y hy).zero_mem⟩

theorem IsHomSection.add {P : GermModule X ι} (hP : P.IsCoherentOn {z | z ≠ 0}) {n : ℤ}
    {K : Set X} {a b : ι → X → ℂ} (ha : IsHomSection P n K a) (hb : IsHomSection P n K b) :
    IsHomSection P n K (a + b) := by
  obtain ⟨U, hKU, hU, haP⟩ := ha
  obtain ⟨V, hKV, hV, hbP⟩ := hb
  refine ⟨U ∩ V, fun z hz => ⟨hKU hz, hKV hz⟩,
    (hU.inter hV.isOpen hV.isCone).add (hV.inter_left hU.isOpen hU.isCone), fun y hy => ?_⟩
  exact (hP y (hU.subset hy.1)).add_mem (haP y hy.1) (hbP y hy.2)

theorem IsHomSection.smul {P : GermModule X ι} (hP : P.IsCoherentOn {z | z ≠ 0}) {n : ℤ}
    {K : Set X} {a : ι → X → ℂ} (ha : IsHomSection P n K a) (r : ℂ) :
    IsHomSection P n K (r • a) := by
  obtain ⟨U, hKU, hU, haP⟩ := ha
  exact ⟨U, hKU, hU.smul r, fun y hy =>
    (hP y (hU.subset hy)).smul_mem (holAt_const r y) (haP y hy)⟩

theorem IsHomSection.sub {P : GermModule X ι} (hP : P.IsCoherentOn {z | z ≠ 0}) {n : ℤ}
    {K : Set X} {a b : ι → X → ℂ} (ha : IsHomSection P n K a) (hb : IsHomSection P n K b) :
    IsHomSection P n K (a - b) := by
  have h := ha.add hP (hb.smul hP (-1))
  convert h using 1
  funext j z
  simp [sub_eq_add_neg]

/-- A homogeneous matrix maps sections of `P(n)` to sections of `A(P)(n + d)`, and to sections
of any `P'` with `A(P) ⊆ P'`. -/
theorem IsHomSection.matApply {P : GermModule X ι} {P' : GermModule X κ} {n d : ℤ}
    {K : Set X} {a : ι → X → ℂ} (ha : IsHomSection P n K a) {A : κ → ι → X → ℂ}
    (hA : IsHomMatrix A d) (hPP' : ∀ y : X, y ≠ 0 → ∀ b, P.mem y b → P'.mem y (matApply A b)) :
    IsHomSection P' (n + d) K (matApply A a) := by
  obtain ⟨U, hKU, hU, haP⟩ := ha
  exact ⟨U, hKU, hU.matApply hA, fun y hy => hPP' y (hU.subset hy) a (haP y hy)⟩

/-- The module `Γ(K, P(n))` of sections of a coherent `P` over `K ⊆ X ∖ 0`. -/
def homSections (P : GermModule X ι) (hP : P.IsCoherentOn {z | z ≠ 0}) (n : ℤ) (K : Set X)
    (hK : K ⊆ {z | z ≠ 0}) : Submodule ℂ (ι → X → ℂ) where
  carrier := {a | IsHomSection P n K a}
  add_mem' ha hb := ha.add hP hb
  zero_mem' := isHomSection_zero hP n hK
  smul_mem' r _ ha := ha.smul hP r

theorem mem_homSections {P : GermModule X ι} {hP : P.IsCoherentOn {z | z ≠ 0}} {n : ℤ}
    {K : Set X} {hK : K ⊆ {z | z ≠ 0}} {a : ι → X → ℂ} :
    a ∈ homSections P hP n K hK ↔ IsHomSection P n K a :=
  Iff.rfl

/-- The homogeneous matrix `A` as a linear map on tuples. -/
def matLin (A : κ → ι → X → ℂ) : (ι → X → ℂ) →ₗ[ℂ] (κ → X → ℂ) where
  toFun := matApply A
  map_add' a b := by
    funext i x
    simp only [matApply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r a := by
    funext i x
    simp only [matApply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem matLin_apply (A : κ → ι → X → ℂ) (a : ι → X → ℂ) :
    matLin A a = matApply A a :=
  rfl

end Sections

/-! ### Sections of subquotients -/

section SubquotientSections

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The cone `X ∖ 0`. -/
abbrev puncture (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] : Set X := {z | z ≠ 0}

section SQ

variable (F : Subquotient X (puncture X))

/-- Sections of the numerator `M(n)` over `K`. -/
abbrev secM (n : ℤ) (K : Set X) (hK : K ⊆ puncture X) : Submodule ℂ (F.ι → X → ℂ) :=
  homSections F.M F.coherent_M n K hK

/-- Sections of the denominator `N(n)` over `K`. -/
abbrev secN (n : ℤ) (K : Set X) (hK : K ⊆ puncture X) : Submodule ℂ (F.ι → X → ℂ) :=
  homSections F.N F.coherent_N n K hK

theorem secN_le_secM (n : ℤ) (K : Set X) (hK : K ⊆ puncture X) :
    secN F n K hK ≤ secM F n K hK :=
  fun _ ha => IsHomSection.le ha F.le

/-- The module of sections `Γ(K, F(n)) = Γ(K, M(n))/Γ(K, N(n))` of the subquotient
`F = M/N` over `K`. (By Theorem B for `N` on `K`, this is the module of sections of the sheaf
`M/N`.) -/
abbrev sectionModule (n : ℤ) (K : Set X) (hK : K ⊆ puncture X) : Type :=
  secM F n K hK ⧸ (secN F n K hK).comap (secM F n K hK).subtype

/-- The class of a section of `M(n)`. -/
abbrev sectionMk {n : ℤ} {K : Set X} {hK : K ⊆ puncture X} (a : secM F n K hK) :
    sectionModule F n K hK :=
  Submodule.Quotient.mk a

theorem sectionMk_eq_zero_iff {n : ℤ} {K : Set X} {hK : K ⊆ puncture X} (a : secM F n K hK) :
    sectionMk F a = 0 ↔ IsHomSection F.N n K a.1 :=
  Submodule.Quotient.mk_eq_zero _

theorem sectionMk_eq_iff {n : ℤ} {K : Set X} {hK : K ⊆ puncture X} (a b : secM F n K hK) :
    sectionMk F a = sectionMk F b ↔ IsHomSection F.N n K (a.1 - b.1) := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, sectionMk_eq_zero_iff]
  rfl

/-- The restriction `Γ(K, F(n)) → Γ(K', F(n))` for `K' ⊆ K`. -/
def sectionRes (n : ℤ) {K K' : Set X} (hK : K ⊆ puncture X) (hK' : K' ⊆ puncture X)
    (h : K' ⊆ K) : sectionModule F n K hK →ₗ[ℂ] sectionModule F n K' hK' :=
  Submodule.mapQ _ _ (Submodule.inclusion fun _ ha => IsHomSection.mono ha h)
    (fun _ ha => IsHomSection.mono ha h)

@[simp] theorem sectionRes_mk (n : ℤ) {K K' : Set X} (hK : K ⊆ puncture X)
    (hK' : K' ⊆ puncture X) (h : K' ⊆ K) (a : secM F n K hK) :
    sectionRes F n hK hK' h (sectionMk F a) = sectionMk F ⟨a.1, IsHomSection.mono a.2 h⟩ :=
  rfl

variable {F} {G : Subquotient X (puncture X)}

/-- The map `Γ(K, F(n)) → Γ(K, G(n + d))` induced by a morphism whose matrix is homogeneous
of degree `d`. -/
def sectionMap (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) (n : ℤ) (K : Set X)
    (hK : K ⊆ puncture X) : sectionModule F n K hK →ₗ[ℂ] sectionModule G (n + d) K hK :=
  Submodule.mapQ _ _
    (((matLin φ.A).comp (secM F n K hK).subtype).codRestrict (secM G (n + d) K hK)
      fun a => IsHomSection.matApply a.2 hφ fun y hy b hb => φ.map_M y hy b hb)
    (fun _ ha => IsHomSection.matApply ha hφ fun y hy b hb => φ.map_N y hy b hb)

@[simp] theorem sectionMap_mk (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) (n : ℤ)
    (K : Set X) (hK : K ⊆ puncture X) (a : secM F n K hK) :
    sectionMap φ hφ n K hK (sectionMk F a) =
      sectionMk G ⟨matApply φ.A a.1, IsHomSection.matApply a.2 hφ
        fun y hy b hb => φ.map_M y hy b hb⟩ :=
  rfl

/-- Both modules of a subquotient are invariant under `ℂ*`. -/
def IsInvariantSubquotient (F : Subquotient X (puncture X)) : Prop :=
  IsConeInvariant F.M ∧ IsConeInvariant F.N

end SQ

/-! ### Theorem B on `K` as a hypothesis -/

/-- **Theorem B (degree one) on `K`, in the form used for long exact sequences.** For
`ℂ*`-invariant coherent modules `P ⊆ 𝒪^κ`, `Q ⊆ 𝒪^ι` on `X ∖ 0` and a homogeneous matrix `A`
of degree `d`, every section of `(P + A(Q))(n + d)` over `K` is `p + A a` near `K`, with `p` a
section of `P(n + d)` and `a` a section of `Q(n)` over `K`. Equivalently, `Γ(K, -)` maps the
surjection `P(n+d) ⊕ Q(n) → (P + A(Q))(n+d)` of coherent sheaves to a surjection; by Cartan's
Theorem B this holds on every holomorphically convex compact subset of an affine chart, e.g.
on the sets `K_s` (`s ≠ ∅`) of the cover. -/
def SectionsDecompose (K : Set X) : Prop :=
  ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (P : GermModule X κ) (Q : GermModule X ι),
    P.IsCoherentOn (puncture X) → Q.IsCoherentOn (puncture X) →
    IsConeInvariant P → IsConeInvariant Q →
    ∀ (A : κ → ι → X → ℂ) (d n : ℤ), IsHomMatrix A d →
    ∀ b : κ → X → ℂ, IsHomSection (P.sup (Q.map A)) (n + d) K b →
      ∃ (p : κ → X → ℂ) (a : ι → X → ℂ), IsHomSection P (n + d) K p ∧ IsHomSection Q n K a ∧
        ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsCone U ∧
          ∀ z ∈ U, ∀ j, b j z = p j z + matApply A a j z

/-! ### Exactness of sections -/

section SQExact

variable {F G H : Subquotient X (puncture X)}

/-- **Injectivity on sections** (no Theorem B needed): an injective morphism of subquotients
induces an injective map of sections over every `K`. -/
theorem sectionMap_injective {φ : Subquotient.Hom F G} {d : ℤ} (hφ : IsHomMatrix φ.A d)
    (hinj : Subquotient.Injective φ) (n : ℤ) (K : Set X) (hK : K ⊆ puncture X) :
    Function.Injective (sectionMap φ hφ n K hK) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  rw [sectionMap_mk, sectionMk_eq_zero_iff] at hx
  rw [sectionMk_eq_zero_iff]
  obtain ⟨U, hKU, hU, haM⟩ := a.2
  obtain ⟨V, hKV, hV, hAN⟩ := hx
  refine ⟨U ∩ V, fun z hz => ⟨hKU hz, hKV hz⟩, hU.inter hV.isOpen hV.isCone, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := hU.subset hy.1
  have hhol : HolTupleAt a.1 y := (F.coherent_M y hy0).holTupleAt_of_mem (haM y hy.1)
  exact (hinj y hy0 a.1).1 ⟨haM y hy.1, hhol, hAN y hy.2⟩

/-- The composite of two morphisms vanishes on sections when the sequence is exact. -/
theorem sectionMap_comp_eq_zero {φ : Subquotient.Hom F G} {ψ : Subquotient.Hom G H} {d e : ℤ}
    (hφ : IsHomMatrix φ.A d)
    (hψ : IsHomMatrix ψ.A e) (hex : Subquotient.Exact φ ψ) (n : ℤ) {K : Set X} (hK : K ⊆ puncture X)
    (x : sectionModule F n K hK) :
    sectionMap ψ hψ (n + d) K hK (sectionMap φ hφ n K hK x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  rw [sectionMap_mk, sectionMap_mk, sectionMk_eq_zero_iff]
  obtain ⟨U, hKU, hU, haM⟩ := a.2
  refine ⟨U, hKU, (hU.matApply hφ).matApply hψ, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := hU.subset hy
  have hsup : (G.N.sup (F.M.map φ.A)).mem y (matApply φ.A a.1) :=
    ⟨fun _ _ => 0, matApply φ.A a.1, (G.coherent_N y hy0).zero_mem,
      GermModule.mem_map_of_mem (haM y hy), fun _ => Eventually.of_forall fun x => by simp⟩
  exact ((hex y hy0 _).2 hsup).2.2

/-- **Exactness on sections**, assuming Theorem B on `K`. -/
theorem sectionMap_exact {K : Set X} (hB : SectionsDecompose K) (hFi : IsInvariantSubquotient F)
    (hGi : IsInvariantSubquotient G) {φ : Subquotient.Hom F G} {ψ : Subquotient.Hom G H} {d e : ℤ}
    (hφ : IsHomMatrix φ.A d)
    (hψ : IsHomMatrix ψ.A e) (hex : Subquotient.Exact φ ψ) (n : ℤ) (hK : K ⊆ puncture X) :
    Function.Exact (sectionMap φ hφ n K hK) (sectionMap ψ hψ (n + d) K hK) := by
  intro x
  constructor
  · induction x using Submodule.Quotient.induction_on with
    | _ b =>
    intro hb
    rw [sectionMap_mk, sectionMk_eq_zero_iff] at hb
    obtain ⟨U, hKU, hU, hbM⟩ := b.2
    obtain ⟨V, hKV, hV, hBN⟩ := hb
    -- `b` is a section of `G.N + A(F.M)`
    have hb' : IsHomSection (G.N.sup (F.M.map φ.A)) (n + d) K b.1 := by
      refine ⟨U ∩ V, fun z hz => ⟨hKU hz, hKV hz⟩, hU.inter hV.isOpen hV.isCone,
        fun y hy => ?_⟩
      have hy0 : y ≠ 0 := hU.subset hy.1
      exact (hex y hy0 b.1).1 ⟨hbM y hy.1, (G.coherent_M y hy0).holTupleAt_of_mem
        (hbM y hy.1), hBN y hy.2⟩
    obtain ⟨p, a, hp, ha, W, hW, hKW, hWc, hbpa⟩ :=
      hB G.ι F.ι G.N F.M G.coherent_N F.coherent_M hGi.2 hFi.1 φ.A d n hφ b.1 hb'
    refine ⟨sectionMk F ⟨a, ha⟩, ?_⟩
    symm
    rw [sectionMap_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, sectionMk_eq_zero_iff]
    obtain ⟨Ua, hKUa, hUa, -⟩ := ha
    refine isHomSection_of_eqOn G.coherent_N (U := U ∩ Ua)
      (fun z hz => ⟨hKU hz, hKUa hz⟩)
      ((hU.inter hUa.isOpen hUa.isCone).sub ((hUa.inter_left hU.isOpen hU.isCone).matApply hφ))
      hp hKW hW hWc fun z hz j => ?_
    show b.1 j z - matApply φ.A a j z = p j z
    rw [hbpa z hz j]
    ring
  · rintro ⟨y, rfl⟩
    exact sectionMap_comp_eq_zero hφ hψ hex n hK y

/-- **Surjectivity on sections**, assuming Theorem B on `K`. -/
theorem sectionMap_surjective {K : Set X} (hB : SectionsDecompose K)
    (hGi : IsInvariantSubquotient G) (hHi : IsInvariantSubquotient H) {ψ : Subquotient.Hom G H}
    {e : ℤ}
    (hψ : IsHomMatrix ψ.A e) (hsurj : Subquotient.Surjective ψ) (m : ℤ) (hK : K ⊆ puncture X) :
    Function.Surjective (sectionMap ψ hψ m K hK) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
  have hc' : IsHomSection (H.N.sup (G.M.map ψ.A)) (m + e) K c.1 :=
    IsHomSection.le c.2 (GermModule.EqOn.le (GermModule.EqOn.symm hsurj))
  obtain ⟨p, g, hp, hg, W, hW, hKW, hWc, hcpg⟩ :=
    hB H.ι G.ι H.N G.M H.coherent_N G.coherent_M hHi.2 hGi.1 ψ.A e m hψ c.1 hc'
  refine ⟨sectionMk G ⟨g, hg⟩, ?_⟩
  symm
  rw [sectionMap_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, sectionMk_eq_zero_iff]
  obtain ⟨U, hKU, hU, -⟩ := c.2
  obtain ⟨Ug, hKUg, hUg, -⟩ := hg
  refine isHomSection_of_eqOn H.coherent_N (U := U ∩ Ug)
    (fun z hz => ⟨hKU hz, hKUg hz⟩)
    ((hU.inter hUg.isOpen hUg.isCone).sub ((hUg.inter_left hU.isOpen hU.isCone).matApply hψ))
    hp hKW hW hWc fun z hz j => ?_
  show c.1 j z - matApply ψ.A g j z = p j z
  rw [hcpg z hz j]
  ring

end SQExact

end SubquotientSections

/-! ### The cover `K_i = {|z_j| ≤ ρ |z_i|}` of `ℙᴺ` -/

section Cover

variable {N : ℕ}

/-- The cone model `ℂ^{N+1}` of `ℙᴺ` (the same space as `ComplexModel (N + 1)`). -/
abbrev ConeSpace (N : ℕ) := EuclideanSpace ℂ (Fin (N + 1))

/-- The cone over `K_s = ⋂_{i ∈ s} K_i`, `K_i = {[z] : |z_j| ≤ ρ |z_i| for all j}`. For
`s = ∅` it is `ℂ^{N+1} ∖ 0`, the cone over `ℙᴺ`. -/
def coverSet (ρ : ℝ) (s : Finset (Fin (N + 1))) : Set (ConeSpace N) :=
  {z | z ≠ 0 ∧ ∀ i ∈ s, ∀ j, ‖z j‖ ≤ ρ * ‖z i‖}

theorem coverSet_subset (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    coverSet ρ s ⊆ puncture (ConeSpace N) :=
  fun _ hz => hz.1

theorem coverSet_anti (ρ : ℝ) {s t : Finset (Fin (N + 1))} (h : s ⊆ t) :
    coverSet ρ t ⊆ coverSet ρ s :=
  fun _ hz => ⟨hz.1, fun i hi => hz.2 i (h hi)⟩

theorem coverSet_empty (ρ : ℝ) : coverSet ρ (∅ : Finset (Fin (N + 1))) = puncture _ := by
  ext z
  simp [coverSet]

theorem isCone_coverSet (ρ : ℝ) (s : Finset (Fin (N + 1))) : IsCone (coverSet ρ s) := by
  intro c hc z hz
  refine ⟨smul_ne_zero hc hz.1, fun i hi j => ?_⟩
  have h := hz.2 i hi j
  simp only [PiLp.smul_apply, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖z j‖ ≤ ‖c‖ * (ρ * ‖z i‖) := by gcongr
    _ = ρ * (‖c‖ * ‖z i‖) := by ring

/-- **The sets `K_i` cover `ℙᴺ`** for `ρ ≥ 1`: a coordinate of maximal modulus works. -/
theorem exists_mem_coverSet {ρ : ℝ} (hρ : 1 ≤ ρ) {z : ConeSpace N} (hz : z ≠ 0) :
    ∃ i, z ∈ coverSet ρ {i} := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖)
    Finset.univ_nonempty
  refine ⟨i, hz, fun i' hi' j => ?_⟩
  rw [Finset.mem_singleton.1 hi']
  calc ‖z j‖ ≤ ‖z i‖ := hi j (Finset.mem_univ j)
    _ = 1 * ‖z i‖ := (one_mul _).symm
    _ ≤ ρ * ‖z i‖ := by gcongr

/-- `K_s` is closed in `ℂ^{N+1} ∖ 0`. -/
theorem isClosed_coverSet_inter (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    ∃ C : Set (ConeSpace N), IsClosed C ∧ coverSet ρ s = C ∩ puncture _ := by
  refine ⟨{z | ∀ i ∈ s, ∀ j, ‖z j‖ ≤ ρ * ‖z i‖}, ?_, ?_⟩
  · simp only [ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun j => ?_
    exact isClosed_le (by fun_prop) (by fun_prop)
  · ext z
    simp only [coverSet, mem_ofPred_eq, mem_inter_iff]
    tauto

variable (F : Subquotient (ConeSpace N) (puncture (ConeSpace N)))

/-- **The Čech coefficient system of `F(n)` for the cover `(K_i)`**: `s ↦ Γ(K_s, F(n))` with
the restrictions. -/
noncomputable def coverSystem (n : ℤ) (ρ : ℝ) : CechSystem ℂ (Fin (N + 1)) where
  obj s := sectionModule F n (coverSet ρ s) (coverSet_subset ρ s)
  res h := sectionRes F n _ _ (coverSet_anti ρ h)
  res_comp h₁ h₂ x := by
    induction x using Submodule.Quotient.induction_on with
    | _ a => rfl

variable {F} {G H : Subquotient (ConeSpace N) (puncture (ConeSpace N))}

/-- The morphism of coefficient systems `coverSystem F n ρ → coverSystem G (n + d) ρ` induced by
a morphism of subquotients whose matrix is homogeneous of degree `d`. -/
noncomputable def coverHom (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) (n : ℤ)
    (ρ : ℝ) :
    CechSystem.Hom (coverSystem F n ρ) (coverSystem G (n + d) ρ) where
  app s := sectionMap φ hφ n _ (coverSet_subset ρ s)
  naturality h x := by
    induction x using Submodule.Quotient.induction_on with
    | _ a => rfl

/-- **Short exact sequences of coefficient systems.** Assume Theorem B (degree one) on every
`K_s`, `s ≠ ∅` (`SectionsDecompose`). A short exact sequence `0 → F → G → H → 0` of
`ℂ*`-invariant subquotients on `ℂ^{N+1} ∖ 0`, with homogeneous matrices of degrees `d, e`,
induces a short exact sequence of the Čech coefficient systems of `F(n)`, `G(n + d)`,
`H(n + d + e)`. -/
theorem coverSystem_shortExact {ρ : ℝ}
    (hB : ∀ s : Finset (Fin (N + 1)), s.Nonempty → SectionsDecompose (coverSet ρ s))
    (hFi : IsInvariantSubquotient F) (hGi : IsInvariantSubquotient G)
    (hHi : IsInvariantSubquotient H)
    {φ : Subquotient.Hom F G} {ψ : Subquotient.Hom G H} {d e : ℤ} (hφ : IsHomMatrix φ.A d)
    (hψ : IsHomMatrix ψ.A e) (hex : Subquotient.ShortExact φ ψ) (n : ℤ) :
    CechSystem.ShortExact (coverHom φ hφ n ρ) (coverHom ψ hψ (n + d) ρ) where
  injective _ _ := sectionMap_injective hφ hex.1 n _ _
  exact s hs := sectionMap_exact (hB s hs) hFi hGi hφ hψ hex.2.1 n _
  surjective s hs := sectionMap_surjective (hB s hs) hGi hHi hψ hex.2.2 (n + d) _

/-- **The long exact Čech cohomology sequence** of a short exact sequence of invariant
subquotients, for the cover `(K_i)`, assuming Theorem B on the `K_s`:
`Ȟ^q(F(n)) → Ȟ^q(G(n+d)) → Ȟ^q(H(n+d+e)) → Ȟ^{q+1}(F(n)) → Ȟ^{q+1}(G(n+d))` is exact, and
`Ȟ⁰(F(n)) → Ȟ⁰(G(n+d))` is injective. -/
theorem coverSystem_les {ρ : ℝ}
    (hB : ∀ s : Finset (Fin (N + 1)), s.Nonempty → SectionsDecompose (coverSet ρ s))
    (hFi : IsInvariantSubquotient F) (hGi : IsInvariantSubquotient G)
    (hHi : IsInvariantSubquotient H)
    {φ : Subquotient.Hom F G} {ψ : Subquotient.Hom G H} {d e : ℤ} (hφ : IsHomMatrix φ.A d)
    (hψ : IsHomMatrix ψ.A e) (hex : Subquotient.ShortExact φ ψ) (n : ℤ) (q : ℕ) :
    Function.Injective (cechHMap (coverHom φ hφ n ρ) 0).hom ∧
    Function.Exact (cechHMap (coverHom φ hφ n ρ) q).hom
      (cechHMap (coverHom ψ hψ (n + d) ρ) q).hom ∧
    Function.Exact (cechHMap (coverHom ψ hψ (n + d) ρ) q).hom
      (cechδ (coverSystem_shortExact hB hFi hGi hHi hφ hψ hex n) q).hom ∧
    Function.Exact (cechδ (coverSystem_shortExact hB hFi hGi hHi hφ hψ hex n) q).hom
      (cechHMap (coverHom φ hφ n ρ) (q + 1)).hom :=
  let h := coverSystem_shortExact hB hFi hGi hHi hφ hψ hex n
  ⟨cechHMap_injective_zero h, cechH_exact₂ h q, cechH_exact₃ h q, cechH_exact₁ h q⟩

/-- `Ȟ^q(F(n)) = 0` for `q ≥ N + 1`: the cover has `N + 1` sets. -/
theorem coverSystem_cechH_subsingleton (n : ℤ) (ρ : ℝ) {q : ℕ} (hq : N + 1 ≤ q) :
    Subsingleton (cechH (coverSystem F n ρ) q) :=
  cechH_subsingleton _ (by simpa using hq)

end Cover

end SGPT.GAGA.PN
