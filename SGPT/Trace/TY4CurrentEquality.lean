import SGPT.Trace.TY2H11
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

/-!
# Equality of closed `(1,1)`-currents with local potentials on a complex space

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "If `T ∈ 𝒵₊(X, α)` for some pseudo-effective
class `α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if exists) closed
positive `(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

The book does not define currents on the (singular, normal) space `Ỹ`; we follow the standard
definitions for normal complex spaces of Eyssidieux–Guedj–Zeriahi (*Singular Kähler–Einstein
metrics*, J. AMS 22 (2009), §5.2, Definitions 5.7–5.8): a *pluriharmonic function* on a normal
space `V` is a continuous real function which, in a local embedding `V ↪ ℂ^N`, extends locally to
a pluriharmonic function of `ℂ^N` (one of the three equivalent conditions listed there); a closed
`(1,1)`-current with local potentials is an equivalence class of families of local potentials
`(U_i, φ_i)`, two families being equivalent iff `φ_i - φ'_j` is pluriharmonic on `U_i ∩ U'_j`.
For a presented current `θ + dd^c ψ` (`θ` a smooth closed real `(1,1)`-form on `X`,
`ψ ∈ PSH(X, θ)`) the local potentials are `g + ψ`, `g` a smooth ambient local potential of `θ`.

* `SpaceForm.SameCurrent θ₁ ψ₁ θ₂ ψ₂` (**`θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`**): near every point there
  are a local embedding `e`, smooth ambient local potentials `g₁`, `g₂` of `θ₁`, `θ₂` on `e` and a
  pluriharmonic function `P` on the ambient open set of `e` with `g₁ + ψ₁ = g₂ + ψ₂ + P` on `X`
  (`(g₁ + ψ₁) - (g₂ + ψ₂)` is pluriharmonic, in `[-∞, ∞)`-valued form).
* `SpaceForm.SameCurrentRe`: the same with `P = Re F`, `F` holomorphic (condition (i) of EGZ: the
  difference is locally the real part of a holomorphic function), `SameCurrentRe.sameCurrent`.
* `SpaceForm.SameCurrentWeak`: the same with `P` only required to be smooth with `dd^c P = 0`
  on `X` (along every holomorphic probe), the natural notion for the project's forms on complex
  spaces; `SameCurrent.weak`.
* `SpaceForm.SameCurrentWeak.exists_smooth` (**the class of a current does not depend on its
  presentation**): if `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂` and `ψ₁` is finite on a dense set, then there
  is a SMOOTH function `f` on `X` with `θ₂ = θ₁ + dd^c f` and `ψ₁ = ψ₂ + f`; in particular
  `{θ₁} = {θ₂}` in `H^{1,1}(X, ℝ)` (`SameCurrentWeak.ofForm_eq`). The local differences
  `g₂ + P - g₁` glue to `f` (continuity on the charts and density of `{ψ₁ > -∞}`), and the two
  forms agree locally (`sameForm_of_local`).
* `sameCurrentRe_of_eq_add`, `sameCurrent_of_eq_add`: conversely `(θ, ψ)` and
  `(θ + dd^c f, ψ - f)` present the same current (so the three notions of equality agree as soon as
  `ψ₁` is finite on a dense set).
* `SameCurrent.refl`, `SameCurrent.symm`, `SameCurrent.trans` (equivalence relation, under the
  density hypothesis for transitivity).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology ContDiff

namespace SGPT.Unibranch

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-! ### Equality of forms is local -/

/-- **Equality of forms on `X` is local**: if near every point `θ` and `θ'` restrict to the same
ambient form under some local embedding, then `θ` and `θ'` are the same form on `X`. -/
theorem sameForm_of_local {θ θ' : SpaceForm X k}
    (h : ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ v : AmbientForm e.dim k, θ.RestrictsTo e v ∧ θ'.RestrictsTo e v) :
    SameForm θ θ' := by
  intro i
  refine restrictsTo_of_local fun c => ?_
  obtain ⟨e, hx, v, hθ, hθ'⟩ := h ((θ'.chart i).toPoint c)
  obtain ⟨W, hW, hcW, hWU, G, hG, -, hfac⟩ :=
    (θ'.chart i).exists_contDiff_transition e c hx
  let T : Opens (ComplexModel (θ'.chart i).dim) := ⟨W, hW⟩
  refine ⟨T, hWU, hcW, ?_⟩
  have hGd : DifferentiableOn ℂ G W := hG.differentiableOn (by simp)
  have hfac' : ∀ c' : ((θ'.chart i).restrict T hWU).carrier, ∃ b : e.carrier,
      b.val.val = G c'.val.val ∧ e.toPoint b = ((θ'.chart i).restrict T hWU).toPoint c' := by
    intro c'
    obtain ⟨b, hb, hbc⟩ := hfac ⟨Opens.inclusion hWU c'.val, c'.property⟩ c'.val.property
    exact ⟨b, hb, hbc⟩
  have h₁ : θ.RestrictsTo ((θ'.chart i).restrict T hWU) (pullbackForm G v) :=
    hθ.of_lift _ hGd hfac'
  have h₂ : θ'.RestrictsTo ((θ'.chart i).restrict T hWU) (pullbackForm G v) :=
    hθ'.of_lift _ hGd hfac'
  have h₃ : θ'.RestrictsTo ((θ'.chart i).restrict T hWU) (θ'.rep i) :=
    (θ'.restrictsTo_rep i).restrict T hWU
  have h₄ := h₁.add_vanishes (h₃.vanishesOn_sub_self h₂)
  refine h₄.congr fun z _ => ?_
  change pullbackForm G v z + (θ'.rep i z - pullbackForm G v z) = θ'.rep i z
  abel

/-! ### Equality of presented currents -/

/-- A chart witnessing `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂` near a point, with the weak (probe)
pluriharmonicity of the difference of the local potentials: a local embedding `emb`, smooth
ambient local potentials `g₁`, `g₂` of `θ₁`, `θ₂`, and a smooth ambient `P` with `dd^c P = 0`
on `X`, such that `g₁ + ψ₁ = g₂ + ψ₂ + P` on `X`. -/
structure CurrentChart (θ₁ : SpaceForm X 2) (ψ₁ : X.obj.left → EReal) (θ₂ : SpaceForm X 2)
    (ψ₂ : X.obj.left → EReal) where
  /-- The local embedding. -/
  emb : LocalEmbedding X
  /-- A local potential of `θ₁`. -/
  g₁ : ComplexModel emb.dim → ℝ
  /-- A local potential of `θ₂`. -/
  g₂ : ComplexModel emb.dim → ℝ
  /-- The pluriharmonic difference. -/
  P : ComplexModel emb.dim → ℝ
  smooth₁ : ContDiffOn ℝ ∞ g₁ emb.ambient
  smooth₂ : ContDiffOn ℝ ∞ g₂ emb.ambient
  smoothP : ContDiffOn ℝ ∞ P emb.ambient
  restricts₁ : θ₁.RestrictsTo emb (smoothDDC g₁)
  restricts₂ : θ₂.RestrictsTo emb (smoothDDC g₂)
  vanishesP : emb.VanishesOn (emb.ambient : Set (ComplexModel emb.dim)) (smoothDDC P)
  eq : ∀ c : emb.carrier, (g₁ c.val.val : EReal) + ψ₁ (emb.toPoint c) =
    (g₂ c.val.val : EReal) + ψ₂ (emb.toPoint c) + (P c.val.val : EReal)

/-- **`θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂` (weak form)**: near every point the local potentials differ by
a smooth function `P` with `dd^c P = 0` on `X`. -/
def SameCurrentWeak (θ₁ : SpaceForm X 2) (ψ₁ : X.obj.left → EReal) (θ₂ : SpaceForm X 2)
    (ψ₂ : X.obj.left → EReal) : Prop :=
  ∀ x : X.obj.left, ∃ A : CurrentChart θ₁ ψ₁ θ₂ ψ₂, x ∈ range A.emb.toPoint

/-- **`θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`** (Eyssidieux–Guedj–Zeriahi, Definitions 5.7–5.8): near every
point there are a local embedding `e : V ↪ Ω ⊆ ℂ^N`, smooth local potentials `g₁`, `g₂` of `θ₁`,
`θ₂` on `Ω` and a pluriharmonic function `P` on `Ω` (smooth with `dd^c P = 0`) such that
`g₁ + ψ₁ = g₂ + ψ₂ + P` on `V`: the difference of the local potentials `g₁ + ψ₁` and `g₂ + ψ₂` is
pluriharmonic on `V` (it extends to a pluriharmonic function of the ambient space). -/
def SameCurrent (θ₁ : SpaceForm X 2) (ψ₁ : X.obj.left → EReal) (θ₂ : SpaceForm X 2)
    (ψ₂ : X.obj.left → EReal) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ g₁ g₂ P : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g₁ e.ambient ∧
      ContDiffOn ℝ ∞ g₂ e.ambient ∧ θ₁.RestrictsTo e (smoothDDC g₁) ∧
      θ₂.RestrictsTo e (smoothDDC g₂) ∧ ContDiffOn ℝ ∞ P e.ambient ∧
      (∀ z ∈ e.ambient, smoothDDC P z = 0) ∧
      ∀ c : e.carrier, (g₁ c.val.val : EReal) + ψ₁ (e.toPoint c) =
        (g₂ c.val.val : EReal) + ψ₂ (e.toPoint c) + (P c.val.val : EReal)

/-- An ambient form vanishing on the ambient open set vanishes on `X`. -/
theorem vanishesOn_of_eq_zero {e : LocalEmbedding X} {v : AmbientForm e.dim 2}
    (hv : ∀ z ∈ e.ambient, v z = 0) :
    e.VanishesOn (e.ambient : Set (ComplexModel e.dim)) v := by
  intro m D h _ _ hm z hz
  simp only [pullbackForm, hv (h z) (hm z hz).1]
  rfl

/-- Ambient pluriharmonicity implies the weak (probe) pluriharmonicity. -/
theorem SameCurrent.weak {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrent θ₁ ψ₁ θ₂ ψ₂) : SameCurrentWeak θ₁ ψ₁ θ₂ ψ₂ := by
  intro x
  obtain ⟨e, hx, g₁, g₂, P, hg₁, hg₂, hr₁, hr₂, hP, hP0, heq⟩ := h x
  exact ⟨⟨e, g₁, g₂, P, hg₁, hg₂, hP, hr₁, hr₂, vanishesOn_of_eq_zero hP0, heq⟩, hx⟩

/-- Case analysis on an extended real. -/
theorem ereal_cases (x : EReal) : x = ⊥ ∨ x = ⊤ ∨ ∃ t : ℝ, x = t := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | top => exact Or.inr (Or.inl rfl)
  | coe t => exact Or.inr (Or.inr ⟨t, rfl⟩)

/-- **`θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`, with the first condition of Eyssidieux–Guedj–Zeriahi**:
near every point the difference of the local potentials `g₁ + ψ₁` and `g₂ + ψ₂` is the real part
of a holomorphic function on `V` (the restriction of a holomorphic function `F` of the ambient
space, i.e. a section of `𝒪_V`). -/
def SameCurrentRe (θ₁ : SpaceForm X 2) (ψ₁ : X.obj.left → EReal) (θ₂ : SpaceForm X 2)
    (ψ₂ : X.obj.left → EReal) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ (g₁ g₂ : ComplexModel e.dim → ℝ) (F : ComplexModel e.dim → ℂ), ContDiffOn ℝ ∞ g₁ e.ambient ∧
      ContDiffOn ℝ ∞ g₂ e.ambient ∧ θ₁.RestrictsTo e (smoothDDC g₁) ∧
      θ₂.RestrictsTo e (smoothDDC g₂) ∧ DifferentiableOn ℂ F e.ambient ∧
      ∀ c : e.carrier, (g₁ c.val.val : EReal) + ψ₁ (e.toPoint c) =
        (g₂ c.val.val : EReal) + ψ₂ (e.toPoint c) + ((F c.val.val).re : EReal)

/-- The real part of a holomorphic function is pluriharmonic: condition (i) of EGZ implies
condition (ii). -/
theorem SameCurrentRe.sameCurrent {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrentRe θ₁ ψ₁ θ₂ ψ₂) : SameCurrent θ₁ ψ₁ θ₂ ψ₂ := by
  intro x
  obtain ⟨e, hx, g₁, g₂, F, hg₁, hg₂, hr₁, hr₂, hF, heq⟩ := h x
  have hFc : ContDiffOn ℂ ∞ F e.ambient := contDiffOn_of_differentiableOn_complex hF e.ambient.isOpen
  refine ⟨e, hx, g₁, g₂, fun z => (F z).re, hg₁, hg₂, hr₁, hr₂,
    Complex.reCLM.contDiff.comp_contDiffOn (hFc.restrict_scalars ℝ), fun z hz =>
      Pending.PluriharmonicLogNorm.smoothDDC_re_comp_eq_zero e.ambient.isOpen hF hz, heq⟩

namespace CurrentChart

variable {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}

/-- The local smooth function `g₂ + P - g₁` (`= ψ₁ - ψ₂` on `X`). -/
def diff (A : CurrentChart θ₁ ψ₁ θ₂ ψ₂) : ComplexModel A.emb.dim → ℝ :=
  fun z => A.g₂ z + A.P z - A.g₁ z

theorem diff_smooth (A : CurrentChart θ₁ ψ₁ θ₂ ψ₂) : ContDiffOn ℝ ∞ A.diff A.emb.ambient :=
  (A.smooth₂.add A.smoothP).sub A.smooth₁

/-- `ψ₁ = ψ₂ + (g₂ + P - g₁)` on `X`, everywhere (also at the poles). -/
theorem eq_add_diff (A : CurrentChart θ₁ ψ₁ θ₂ ψ₂) (c : A.emb.carrier) :
    ψ₁ (A.emb.toPoint c) = ψ₂ (A.emb.toPoint c) + (A.diff c.val.val : EReal) := by
  have h := A.eq c
  have h' : ψ₁ (A.emb.toPoint c) = (A.g₁ c.val.val : EReal) + ψ₁ (A.emb.toPoint c) +
      ((-A.g₁ c.val.val : ℝ) : EReal) := by
    rw [add_comm (A.g₁ c.val.val : EReal), add_assoc, ← EReal.coe_add, add_neg_cancel,
      EReal.coe_zero, add_zero]
  rw [h', h]
  simp only [diff]
  rw [add_comm (A.g₂ c.val.val : EReal), add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add,
    show A.g₂ c.val.val + (A.P c.val.val + -A.g₁ c.val.val) =
      A.g₂ c.val.val + A.P c.val.val - A.g₁ c.val.val by ring]

/-- The value of `ψ₁ - ψ₂` read in a chart, at a point where `ψ₁` is finite. -/
theorem diff_eq_of_eq {A : CurrentChart θ₁ ψ₁ θ₂ ψ₂} {c : A.emb.carrier} {r s : ℝ}
    (hr : ψ₁ (A.emb.toPoint c) = r) (hs : ψ₁ (A.emb.toPoint c) = ψ₂ (A.emb.toPoint c) + s) :
    A.diff c.val.val = s := by
  have h := A.eq_add_diff c
  rw [hr] at h hs
  rcases ereal_cases (ψ₂ (A.emb.toPoint c)) with hψ | hψ | ⟨t, hψ⟩
  · rw [hψ, EReal.bot_add] at h
    exact absurd h (EReal.coe_ne_bot r)
  · rw [hψ, EReal.top_add_coe] at h
    exact absurd h (EReal.coe_ne_top r)
  · rw [hψ, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h hs
    linarith

/-- **Two charts give the same local difference.** Where two charts meet, the local functions
`g₂ + P - g₁` agree: they are continuous and agree where `ψ₁` is finite, which is dense. -/
theorem diff_eq_diff (hdense : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop : ∀ x, ψ₁ x ≠ ⊤) (A B : CurrentChart θ₁ ψ₁ θ₂ ψ₂) (c : A.emb.carrier)
    (d : B.emb.carrier) (hcd : A.emb.toPoint c = B.emb.toPoint d) :
    A.diff c.val.val = B.diff d.val.val := by
  obtain ⟨W, hW, hcW, hWU, G, hG, hGmaps, hfac⟩ :=
    A.emb.exists_transition B.emb c ⟨d, hcd.symm⟩
  -- the transition carries `c` to `d`
  have hGc : G c.val.val = d.val.val := by
    obtain ⟨z, hz, hzc⟩ := hfac c hcW
    have : z = d := B.emb.toPoint_injective (hzc.trans hcd)
    rw [← hz, this]
  let S : Set A.emb.carrier := {y | y.val.val ∈ W}
  have hval : Continuous fun y : A.emb.carrier => (y.val.val : ComplexModel A.emb.dim) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hSo : IsOpen S := hW.preimage hval
  let φ₁ : A.emb.carrier → ℝ := fun y => A.diff y.val.val
  let φ₂ : A.emb.carrier → ℝ := fun y => B.diff (G y.val.val)
  have hφ₁ : ContinuousOn φ₁ S :=
    (A.diff_smooth.continuousOn.mono hWU).comp hval.continuousOn (fun y hy => hy)
  have hφ₂ : ContinuousOn φ₂ S :=
    (B.diff_smooth.continuousOn.comp hG.continuousOn hGmaps).comp hval.continuousOn
      (fun y hy => hy)
  let D : Set A.emb.carrier := A.emb.toPoint ⁻¹' {x | ψ₁ x ≠ ⊥}
  have hD : Dense D := hdense.preimage A.emb.isOpenEmbedding_toPoint.isOpenMap
  have heq : EqOn φ₁ φ₂ (S ∩ D) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hfac y hy.1
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ψ₁ (A.emb.toPoint y) = r := by
      rcases ereal_cases (ψ₁ (A.emb.toPoint y)) with hψ | hψ | ⟨t, hψ⟩
      · exact absurd hψ hy.2
      · exact absurd hψ (htop _)
      · exact ⟨t, hψ⟩
    have hB := B.eq_add_diff z
    rw [hzy] at hB
    change A.diff y.val.val = B.diff (G y.val.val)
    rw [← hz]
    exact diff_eq_of_eq hr hB
  have hsub : S ⊆ closure (S ∩ D) := hD.open_subset_closure_inter hSo
  have key := heq.of_subset_closure hφ₁ hφ₂ inter_subset_left hsub (show c ∈ S from hcW)
  change A.diff c.val.val = B.diff (G c.val.val) at key
  rw [key, hGc]

end CurrentChart

/-! ### The main theorem: the class of a current does not depend on its presentation -/

/-- **Presentation-independence of the class of a current.** If `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`
(weak form) and `ψ₁` is finite on a dense set (and `< +∞`), then there is a smooth function `f`
on `X` with `θ₂ = θ₁ + dd^c f` and `ψ₁ = ψ₂ + f`. -/
theorem SameCurrentWeak.exists_smooth {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrentWeak θ₁ ψ₁ θ₂ ψ₂) (hdense : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop : ∀ x, ψ₁ x ≠ ⊤) :
    ∃ (f : X.obj.left → ℝ) (hf : X.IsSmoothFunction f),
      SameForm (θ₁.add (ddcOf f hf)) θ₂ ∧ ∀ x, ψ₁ x = ψ₂ x + (f x : EReal) := by
  classical
  choose A hA using h
  have hA' : ∀ x, ∃ y, (A x).emb.toPoint y = x := hA
  choose c hc using hA'
  let f : X.obj.left → ℝ := fun x => (A x).diff (c x).val.val
  have hf_eq : ∀ (B : CurrentChart θ₁ ψ₁ θ₂ ψ₂) (b : B.emb.carrier),
      f (B.emb.toPoint b) = B.diff b.val.val := fun B b =>
    CurrentChart.diff_eq_diff hdense htop _ _ _ _ (hc _)
  have hf : X.IsSmoothFunction f := fun x =>
    ⟨(A x).emb, ⟨c x, hc x⟩, (A x).diff, (A x).diff_smooth, fun b => (hf_eq (A x) b).symm⟩
  refine ⟨f, hf, sameForm_of_local fun x => ?_, fun x => ?_⟩
  · let B := A x
    refine ⟨B.emb, ⟨c x, hc x⟩, smoothDDC B.g₂ + smoothDDC B.P, ?_, ?_⟩
    · have h₁ := restrictsTo_add
        (Pending.LogWeightFactorization.smoothDDC_contDiffOn B.emb.ambient.isOpen B.smooth₁)
        (Pending.LogWeightFactorization.smoothDDC_contDiffOn B.emb.ambient.isOpen B.diff_smooth)
        B.restricts₁ (restrictsTo_ddcOf hf B.diff_smooth fun b => (hf_eq B b).symm)
      refine h₁.congr fun z hz => ?_
      have hU := B.emb.ambient.isOpen
      change smoothDDC B.g₁ z + smoothDDC B.diff z = smoothDDC B.g₂ z + smoothDDC B.P z
      have hd : smoothDDC B.diff z = smoothDDC B.g₂ z + smoothDDC B.P z - smoothDDC B.g₁ z := by
        change smoothDDC (fun y => B.g₂ y + B.P y - B.g₁ y) z = _
        rw [PositiveClasses.smoothDDC_sub hU (B.smooth₂.add B.smoothP) B.smooth₁ hz,
          smoothDDC_add hU B.smooth₂ B.smoothP hz]
      rw [hd]
      abel
    · exact B.restricts₂.add_vanishes B.vanishesP
  · have h := (A x).eq_add_diff (c x)
    rw [hc x] at h
    exact h

/-- **The class in `H^{1,1}(X, ℝ)` of a current does not depend on its presentation.** -/
theorem SameCurrentWeak.ofForm_eq {θ₁ θ₂ : SpaceClosedOneOneForm X} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrentWeak θ₁.val ψ₁ θ₂.val ψ₂) (hdense : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop : ∀ x, ψ₁ x ≠ ⊤) : H11.ofForm θ₁ = H11.ofForm θ₂ := by
  obtain ⟨f, hf, hS, -⟩ := h.exists_smooth hdense htop
  exact H11.ofForm_eq_of_rel hf hS

/-- **The class of a current does not depend on its presentation** (`SameCurrent`, EGZ). -/
theorem SameCurrent.exists_smooth {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrent θ₁ ψ₁ θ₂ ψ₂) (hdense : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop : ∀ x, ψ₁ x ≠ ⊤) :
    ∃ (f : X.obj.left → ℝ) (hf : X.IsSmoothFunction f),
      SameForm (θ₁.add (ddcOf f hf)) θ₂ ∧ ∀ x, ψ₁ x = ψ₂ x + (f x : EReal) :=
  h.weak.exists_smooth hdense htop

theorem SameCurrent.ofForm_eq {θ₁ θ₂ : SpaceClosedOneOneForm X} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrent θ₁.val ψ₁ θ₂.val ψ₂) (hdense : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop : ∀ x, ψ₁ x ≠ ⊤) : H11.ofForm θ₁ = H11.ofForm θ₂ :=
  h.weak.ofForm_eq hdense htop

/-! ### The converse and the equivalence relation -/

/-- **`(θ, ψ)` and `(θ + dd^c f, ψ - f)` present the same current**: if `ψ₁ ∈ PSH(X, θ₁)`,
`f` is smooth, `θ₂ = θ₁ + dd^c f` and `ψ₁ = ψ₂ + f`, then `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`, even in
the sense of condition (i) (with `F = 0`). -/
theorem sameCurrentRe_of_eq_add {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (hψ₁ : X.IsThetaPSH θ₁ ψ₁) {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f)
    (hS : SameForm (θ₁.add (ddcOf f hf)) θ₂) (hψ : ∀ x, ψ₁ x = ψ₂ x + (f x : EReal)) :
    SameCurrentRe θ₁ ψ₁ θ₂ ψ₂ := by
  intro x
  obtain ⟨e, ⟨c, rfl⟩, -, g, hg, hθ, -⟩ := hψ₁ x
  obtain ⟨T, hT, hcT, F, hF, hFeq⟩ := hf.exists_local_extension e c
  have hTo : IsOpen (T : Set (ComplexModel e.dim)) := T.isOpen
  refine ⟨e.restrict T hT, ⟨⟨⟨c.val.val, hcT⟩, ?_⟩, ?_⟩, g, fun z => g z + F z, fun _ => 0,
    hg.mono hT, (hg.mono hT).add hF, hθ.restrict T hT, ?_, differentiableOn_const 0, ?_⟩
  · change Opens.inclusion hT ⟨c.val.val, hcT⟩ ∈ e.carrier
    have hcc : Opens.inclusion hT ⟨c.val.val, hcT⟩ = c.val := Subtype.ext rfl
    rw [hcc]
    exact c.property
  · rw [LocalEmbedding.restrict_toPoint]
    rfl
  · have h₁ := restrictsTo_add (e := e.restrict T hT)
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn hTo (hg.mono hT))
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn hTo hF) (hθ.restrict T hT)
      (restrictsTo_ddcOf hf (e := e.restrict T hT) hF
        (fun y => hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property))
    refine (hS.restrictsTo h₁).congr fun z hz => ?_
    change smoothDDC g z + smoothDDC F z = smoothDDC (fun z => g z + F z) z
    rw [smoothDDC_add hTo (hg.mono hT) hF hz]
  · intro y
    have hFy : F y.val.val = f ((e.restrict T hT).toPoint y) :=
      hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property
    dsimp only
    rw [hψ, hFy, Complex.zero_re, EReal.coe_zero, add_zero, EReal.coe_add]
    rw [add_comm (ψ₂ _), ← add_assoc]

/-- **`(θ, ψ)` and `(θ + dd^c f, ψ - f)` present the same current** (condition (ii)). -/
theorem sameCurrent_of_eq_add {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (hψ₁ : X.IsThetaPSH θ₁ ψ₁) {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f)
    (hS : SameForm (θ₁.add (ddcOf f hf)) θ₂) (hψ : ∀ x, ψ₁ x = ψ₂ x + (f x : EReal)) :
    SameCurrent θ₁ ψ₁ θ₂ ψ₂ :=
  (sameCurrentRe_of_eq_add hψ₁ hf hS hψ).sameCurrent

/-- `θ + dd^c ψ = θ + dd^c ψ` (for `ψ ∈ PSH(X, θ)`). -/
theorem SameCurrent.refl {θ : SpaceForm X 2} {ψ : X.obj.left → EReal} (hψ : X.IsThetaPSH θ ψ) :
    SameCurrent θ ψ θ ψ := by
  intro x
  obtain ⟨e, hx, -, g, hg, hθ, -⟩ := hψ x
  exact ⟨e, hx, g, g, fun _ => 0, hg, hg, hθ, hθ, contDiffOn_const,
    fun z _ => smoothDDC_zero z, fun c => by simp only [EReal.coe_zero, add_zero]⟩

/-- Symmetry of `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂`. -/
theorem SameCurrent.symm {θ₁ θ₂ : SpaceForm X 2} {ψ₁ ψ₂ : X.obj.left → EReal}
    (h : SameCurrent θ₁ ψ₁ θ₂ ψ₂) : SameCurrent θ₂ ψ₂ θ₁ ψ₁ := by
  intro x
  obtain ⟨e, hx, g₁, g₂, P, hg₁, hg₂, hr₁, hr₂, hP, hP0, heq⟩ := h x
  refine ⟨e, hx, g₂, g₁, fun z => -P z, hg₂, hg₁, hr₂, hr₁, hP.neg, fun z hz => ?_, fun c => ?_⟩
  · rw [smoothDDC_neg e.ambient.isOpen hP hz, hP0 z hz, neg_zero]
  · dsimp only
    rw [heq c, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- `θ₂ + dd^c (f + g) = θ₃` from `θ₁ + dd^c f = θ₂` and `θ₂ + dd^c g = θ₃`. -/
theorem sameForm_add_ddcOf_add {θ₁ θ₂ θ₃ : SpaceForm X 2} {f g : X.obj.left → ℝ}
    (hf : X.IsSmoothFunction f) (hg : X.IsSmoothFunction g)
    (h₁ : SameForm (θ₁.add (ddcOf f hf)) θ₂) (h₂ : SameForm (θ₂.add (ddcOf g hg)) θ₃) :
    SameForm (θ₁.add (ddcOf (fun y => f y + g y) (hf.add hg))) θ₃ := by
  refine sameForm_of_local fun x => ?_
  obtain ⟨i, c, rfl⟩ := θ₁.covers x
  let e := θ₁.chart i
  obtain ⟨T₁, hT₁, hcT₁, F, hF, hFeq⟩ := hf.exists_local_extension e c
  obtain ⟨T₂, hT₂, hcT₂, G, hG, hGeq⟩ := hg.exists_local_extension e c
  let T : Opens (ComplexModel e.dim) := T₁ ⊓ T₂
  have hT : T ≤ e.ambient := inf_le_left.trans hT₁
  have hTo : IsOpen (T : Set (ComplexModel e.dim)) := T.isOpen
  have hTF : ContDiffOn ℝ ∞ F T := hF.mono inf_le_left
  have hTG : ContDiffOn ℝ ∞ G T := hG.mono inf_le_right
  have hv : ContDiffOn ℝ ∞ (θ₁.rep i) T := (θ₁.smooth i).mono hT
  have hdF := Pending.LogWeightFactorization.smoothDDC_contDiffOn hTo hTF
  have hdG := Pending.LogWeightFactorization.smoothDDC_contDiffOn hTo hTG
  have hr : θ₁.RestrictsTo (e.restrict T hT) (θ₁.rep i) := (θ₁.restrictsTo_rep i).restrict T hT
  have hrF : (ddcOf f hf).RestrictsTo (e.restrict T hT) (smoothDDC F) :=
    restrictsTo_ddcOf hf (e := e.restrict T hT) hTF
      (fun y => hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.1)
  have hrG : (ddcOf g hg).RestrictsTo (e.restrict T hT) (smoothDDC G) :=
    restrictsTo_ddcOf hg (e := e.restrict T hT) hTG
      (fun y => hGeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.2)
  have hrFG : (ddcOf (fun y => f y + g y) (hf.add hg)).RestrictsTo (e.restrict T hT)
      (smoothDDC fun z => F z + G z) :=
    restrictsTo_ddcOf (hf.add hg) (e := e.restrict T hT) (hTF.add hTG)
      (fun y => by
        rw [hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.1,
          hGeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.2]
        rfl)
  have e₂ : θ₂.RestrictsTo (e.restrict T hT) (θ₁.rep i + smoothDDC F) :=
    h₁.restrictsTo (restrictsTo_add hv hdF hr hrF)
  have e₃ : θ₃.RestrictsTo (e.restrict T hT) (θ₁.rep i + smoothDDC F + smoothDDC G) :=
    h₂.restrictsTo (restrictsTo_add (hv.add hdF) hdG e₂ hrG)
  have e₁ := restrictsTo_add hv
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn hTo (hTF.add hTG)) hr hrFG
  refine ⟨e.restrict T hT, ⟨⟨⟨c.val.val, ⟨hcT₁, hcT₂⟩⟩, ?_⟩, ?_⟩,
    θ₁.rep i + smoothDDC F + smoothDDC G, ?_, e₃⟩
  · change Opens.inclusion hT ⟨c.val.val, ⟨hcT₁, hcT₂⟩⟩ ∈ e.carrier
    have hcc : Opens.inclusion hT ⟨c.val.val, ⟨hcT₁, hcT₂⟩⟩ = c.val := Subtype.ext rfl
    rw [hcc]
    exact c.property
  · rw [LocalEmbedding.restrict_toPoint]
    rfl
  · refine e₁.congr fun z hz => ?_
    change θ₁.rep i z + smoothDDC (fun z => F z + G z) z =
      θ₁.rep i z + smoothDDC F z + smoothDDC G z
    rw [smoothDDC_add hTo hTF hTG hz, add_assoc]

/-- **Transitivity** of `θ₁ + dd^c ψ₁ = θ₂ + dd^c ψ₂` (for `ψ₁` finite on a dense set and
`ψ₁ ∈ PSH(X, θ₁)`). -/
theorem SameCurrent.trans {θ₁ θ₂ θ₃ : SpaceForm X 2} {ψ₁ ψ₂ ψ₃ : X.obj.left → EReal}
    (hψ₁ : X.IsThetaPSH θ₁ ψ₁) (hdense₁ : Dense {x : X.obj.left | ψ₁ x ≠ ⊥})
    (htop₁ : ∀ x, ψ₁ x ≠ ⊤) (hdense₂ : Dense {x : X.obj.left | ψ₂ x ≠ ⊥})
    (htop₂ : ∀ x, ψ₂ x ≠ ⊤)
    (h₁₂ : SameCurrent θ₁ ψ₁ θ₂ ψ₂) (h₂₃ : SameCurrent θ₂ ψ₂ θ₃ ψ₃) :
    SameCurrent θ₁ ψ₁ θ₃ ψ₃ := by
  obtain ⟨f, hf, hS₁, hψf⟩ := h₁₂.exists_smooth hdense₁ htop₁
  obtain ⟨g, hg, hS₂, hψg⟩ := h₂₃.exists_smooth hdense₂ htop₂
  refine sameCurrent_of_eq_add hψ₁ (hf.add hg) (sameForm_add_ddcOf_add hf hg hS₁ hS₂)
    fun x => ?_
  rw [hψf, hψg, EReal.coe_add, add_assoc, add_comm (g x : EReal)]

end SpaceForm

end SGPT.Unibranch
