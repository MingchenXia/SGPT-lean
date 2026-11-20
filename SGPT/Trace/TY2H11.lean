import SGPT.Trace.TY2CorPSH
import SGPT.Unibranch.KS2KahlerSpace

/-!
# `H^{1,1}(Ỹ, ℝ)` and `rmk:tracecurrent` on the normalization

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "If `T ∈ 𝒵₊(X, α)` for some pseudo-effective
class `α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if exists) closed
positive `(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

## `H^{1,1}` of a complex space

On a compact complex manifold the project's `H^{1,1}(X, ℝ)` is the real Bott–Chern space
`RealBottChern`: closed smooth real `(1,1)`-forms modulo `dd^c` of smooth functions. On a complex
space (here the normal space `Ỹ`) the same definition is the standard one (`H^{1,1}_{BC}(Ỹ, ℝ)
= H^1(Ỹ, 𝒫ℋ_Ỹ)`, the cohomology of the sheaf of pluriharmonic functions, for spaces whose smooth
closed `(1,1)`-forms have local potentials): `H11 X` is the quotient of the smooth closed real
`(1,1)`-forms on `X` in the sense of `def:unibranch:L105` (`PD.IsLocallyClosedOneOne`) by the
relation `θ' = θ + dd^c f`, `f` a smooth function on `X` (the `IsSmoothFunction`,
`SpaceForm.ddcOf`, `SpaceForm.add`). Two forms are equal on `X` when each restricts to the other
on every chart (`SpaceForm.SameForm`). We prove that the relation is an equivalence relation, so
two forms have the same class iff they differ by `dd^c` of a smooth function
(`H11.ofForm_eq_iff`).

## Currents on `Ỹ` in a class

A closed positive `(1,1)`-current on `Ỹ` (with local potentials) is given, as for `rmk:qpshtocurrents`,
by a presentation `S = θ̃ + dd^c ψ`, `θ̃` a smooth closed real `(1,1)`-form on `Ỹ` and
`ψ ∈ PSH(Ỹ, θ̃)`; its class is `{θ̃} ∈ H^{1,1}(Ỹ, ℝ)`. `TildeY.IsTraceCurrentIn T Tc β θ̃ ψ`
(`Tr^β_Y(T)`) says that this current lies in `β` and represents `Tr_Y(Tc)` (`ψ` is a trace
operator of a potential of `Tc`; this forces `ν(Tc, Y) = 0`). Changing the presentation by a
smooth `f` (`θ̃ + dd^c f`, `ψ - f`) does not change the class (`H11.ofForm_eq_of_rel`).

* `IsTraceCurrentIn.isTrace`: independence of the presentation of `Tc`;
* `IsTraceCurrentIn.pEquivalent`: two currents representing `Tr_Y(Tc)` (in any classes) have
  `P`-equivalent potentials;
* `Normalization.exists_isTraceCurrentIn_of_corPSH`: on the normalization, if `ν(Tc, Y) = 0` and
  `Tc = θ + dd^c φ`, then for every Kähler form `ω` on `X` some current in the class
  `{(θ + ω)|_Ỹ}` represents `Tr_Y(Tc)` (`cor:PSH`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology ContDiff

namespace SGPT.Unibranch

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-! ### Smooth functions on a complex space -/

namespace SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}

/-- **Local extensions of a smooth function on every local embedding**: near every point of the
carrier of any local embedding `e`, a smooth function `f` on `X` is the restriction of a smooth
ambient function on an open subset of the ambient space of `e`. -/
theorem IsSmoothFunction.exists_local_extension {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f)
    (e : LocalEmbedding X) (c : e.carrier) :
    ∃ T : Opens (ComplexModel e.dim), T ≤ e.ambient ∧ c.val.val ∈ T ∧
      ∃ F : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ F T ∧
        ∀ y : e.carrier, y.val.val ∈ T → F y.val.val = f (e.toPoint y) := by
  obtain ⟨e₂, hx, g, hg, heq⟩ := hf (e.toPoint c)
  obtain ⟨W, hW, hcW, hWU, G, hG, hmaps, hfac⟩ := e.exists_contDiff_transition e₂ c hx
  refine ⟨⟨W, hW⟩, hWU, hcW, g ∘ G, hg.comp (hG.restrict_scalars ℝ) hmaps, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hfac y hy
  change g (G y.val.val) = f (e.toPoint y)
  rw [← hz, heq z, hzy]

theorem isSmoothFunction_zero : X.IsSmoothFunction fun _ => 0 := by
  intro x
  exact ⟨LocalEmbedding.ofPoint X x, LocalEmbedding.mem_range_ofPoint X x, fun _ => 0,
    contDiffOn_const, fun _ => rfl⟩

theorem IsSmoothFunction.neg {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f) :
    X.IsSmoothFunction fun y => -f y := by
  intro x
  obtain ⟨e, hx, g, hg, heq⟩ := hf x
  exact ⟨e, hx, fun z => -g z, hg.neg, fun c => by
    show -g c.val.val = -f (e.toPoint c)
    rw [heq c]⟩

theorem IsSmoothFunction.add {f g : X.obj.left → ℝ} (hf : X.IsSmoothFunction f)
    (hg : X.IsSmoothFunction g) : X.IsSmoothFunction fun y => f y + g y := by
  intro x
  obtain ⟨e, ⟨c, rfl⟩, F, hF, heq⟩ := hf x
  obtain ⟨T, hT, hcT, G, hG, hGeq⟩ := hg.exists_local_extension e c
  refine ⟨e.restrict T hT, ⟨⟨⟨c.val.val, hcT⟩, ?_⟩, ?_⟩, fun z => F z + G z,
    (hF.mono hT).add hG, ?_⟩
  · change Opens.inclusion hT ⟨c.val.val, hcT⟩ ∈ e.carrier
    have hcc : Opens.inclusion hT ⟨c.val.val, hcT⟩ = c.val := Subtype.ext rfl
    rw [hcc]
    exact c.property
  · rw [LocalEmbedding.restrict_toPoint]
    rfl
  · intro y
    change F y.val.val + G y.val.val =
      f (e.toPoint ⟨Opens.inclusion hT y.val, y.property⟩) +
        g (e.toPoint ⟨Opens.inclusion hT y.val, y.property⟩)
    rw [← heq ⟨Opens.inclusion hT y.val, y.property⟩,
      ← hGeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property]

end SourceReducedComplexSpace

/-! ### Equality of forms on a complex space -/

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-- Restriction to a local embedding only depends on the ambient form on the ambient open set. -/
theorem RestrictsTo.congr {θ : SpaceForm X k} {e : LocalEmbedding X} {v w : AmbientForm e.dim k}
    (hv : θ.RestrictsTo e v) (hvw : EqOn v w (e.ambient : Set (ComplexModel e.dim))) :
    θ.RestrictsTo e w := by
  intro i W G hG m D h hD hd hm z hz
  have h0 := hv i W G hG m D h hD hd hm z hz
  have hwv : w (h z) = v (h z) := (hvw (hG.2.1 (hm z hz).1)).symm
  simp only [pullbackForm, Pi.sub_apply] at h0 ⊢
  rw [hwv]
  exact h0

/-- **Restriction is local on the local embedding**: if near every point of its carrier the
restriction of `θ` to a smaller ambient open set is given by `v`, then `θ` restricts to `v`. -/
theorem restrictsTo_of_local {θ : SpaceForm X k} {e : LocalEmbedding X} {v : AmbientForm e.dim k}
    (hloc : ∀ c : e.carrier, ∃ (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient),
      c.val.val ∈ T ∧ θ.RestrictsTo (e.restrict T hT) v) : θ.RestrictsTo e v := by
  intro i W G hG m D h hD hd hm z hz
  obtain ⟨c, hc⟩ := (hm z hz).2
  obtain ⟨T, hT, hcT, hres⟩ := hloc c
  have hG' : (e.restrict T hT).IsTransition (θ.chart i) (W ∩ (T : Set (ComplexModel e.dim))) G := by
    refine ⟨hG.1.inter T.isOpen, inter_subset_right, hG.2.2.1.mono inter_subset_left,
      fun w hw => hG.2.2.2.1 hw.1, ?_⟩
    intro y hy
    obtain ⟨z', hz', hzy⟩ := hG.2.2.2.2 ⟨Opens.inclusion hT y.val, y.property⟩ hy.1
    exact ⟨z', hz', hzy.trans (LocalEmbedding.restrict_toPoint e T hT y).symm⟩
  have hD' : IsOpen (D ∩ h ⁻¹' (T : Set (ComplexModel e.dim))) :=
    hd.continuousOn.isOpen_inter_preimage hD T.isOpen
  have hzD' : z ∈ D ∩ h ⁻¹' (T : Set (ComplexModel e.dim)) := by
    refine ⟨hz, ?_⟩
    change h z ∈ (T : Set (ComplexModel e.dim))
    rw [← hc]
    exact hcT
  have hm' : ∀ w ∈ D ∩ h ⁻¹' (T : Set (ComplexModel e.dim)),
      h w ∈ W ∩ (T : Set (ComplexModel e.dim)) ∧
        ∃ c' : (e.restrict T hT).carrier, c'.val.val = h w := by
    intro w hw
    obtain ⟨hwW, c', hc'⟩ := hm w hw.1
    refine ⟨⟨hwW, hw.2⟩, ⟨⟨h w, hw.2⟩, ?_⟩, rfl⟩
    have hcc : Opens.inclusion hT ⟨h w, hw.2⟩ = c'.val := Subtype.ext hc'.symm
    change Opens.inclusion hT ⟨h w, hw.2⟩ ∈ e.carrier
    rw [hcc]
    exact c'.property
  exact hres i (W ∩ (T : Set (ComplexModel e.dim))) G hG' m _ h hD' (hd.mono inter_subset_left)
    hm' z hzD'

/-- The identity is a holomorphic transition of a local embedding to itself. -/
theorem isTransition_id (e : LocalEmbedding X) :
    e.IsTransition e (e.ambient : Set (ComplexModel e.dim)) id :=
  ⟨e.ambient.isOpen, subset_rfl, differentiableOn_id, fun _ hz => hz,
    fun y _ => ⟨y, rfl, rfl⟩⟩

theorem pullbackForm_id {N : ℕ} (v : AmbientForm N k) : pullbackForm id v = v := by
  funext z
  ext a
  simp [pullbackForm]

/-- Two ambient representatives of the same form on the same local embedding differ by a form
vanishing on `X`. -/
theorem RestrictsTo.vanishesOn_sub_self {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v w : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) (hw : θ.RestrictsTo e w) :
    e.VanishesOn (e.ambient : Set (ComplexModel e.dim)) (v - w) := by
  have h := hv.vanishesOn_sub hw (isTransition_id e)
  rwa [pullbackForm_id] at h

/-- Adding an ambient form which vanishes on `X` does not change the restriction. -/
theorem RestrictsTo.add_vanishes {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v u : AmbientForm e.dim k} (hv : θ.RestrictsTo e v)
    (hu : e.VanishesOn (e.ambient : Set (ComplexModel e.dim)) u) : θ.RestrictsTo e (v + u) := by
  intro i W G hG m D h hD hd hm z hz
  have h₁ := hv i W G hG m D h hD hd hm z hz
  have h₂ := hu m D h hD hd (fun w hw => ⟨hG.2.1 (hm w hw).1, (hm w hw).2⟩) z hz
  have hsplit : v + u - pullbackForm G (θ.rep i) = (v - pullbackForm G (θ.rep i)) + u := by
    abel
  rw [hsplit, pullbackForm_add, Pi.add_apply, h₁, h₂, add_zero]

/-- **`θ` and `θ'` are the same form on `X`**: `θ` restricts, on every chart of `θ'`, to the
representative of `θ'`. -/
def SameForm (θ θ' : SpaceForm X k) : Prop :=
  ∀ i : θ'.ι, θ.RestrictsTo (θ'.chart i) (θ'.rep i)

/-- Equal forms have the same restrictions. -/
theorem SameForm.restrictsTo {θ θ' : SpaceForm X k} (h : SameForm θ θ') {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) : θ'.RestrictsTo e v :=
  fun i _ _ hG => hv.vanishesOn_sub (h i) hG

theorem SameForm.refl (θ : SpaceForm X k) : SameForm θ θ := fun i => θ.restrictsTo_rep i

theorem SameForm.symm {θ θ' : SpaceForm X k} (h : SameForm θ θ') : SameForm θ' θ :=
  fun j => h.restrictsTo (θ.restrictsTo_rep j)

theorem SameForm.trans {θ θ' θ'' : SpaceForm X k} (h₁ : SameForm θ θ') (h₂ : SameForm θ' θ'') :
    SameForm θ θ'' :=
  fun i => h₁.symm.restrictsTo (h₂ i)

theorem SameForm.restrictsTo_iff {θ θ' : SpaceForm X k} (h : SameForm θ θ') {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} : θ.RestrictsTo e v ↔ θ'.RestrictsTo e v :=
  ⟨h.restrictsTo, h.symm.restrictsTo⟩

/-! ### `θ' = θ + dd^c f` -/

/-- `θ + dd^c f` restricts, near every point of every chart of `θ`, to the representative of `θ`
plus `dd^c` of a local extension of `f`. -/
private theorem restrictsTo_add_ddcOf_local {θ : SpaceForm X 2} {f : X.obj.left → ℝ}
    (hf : X.IsSmoothFunction f) (e : LocalEmbedding X) {v : AmbientForm e.dim 2}
    (hv : ContDiffOn ℝ ∞ v e.ambient) (hθ : θ.RestrictsTo e v) {T : Opens (ComplexModel e.dim)}
    (hT : T ≤ e.ambient) {F : ComplexModel e.dim → ℝ} (hF : ContDiffOn ℝ ∞ F T)
    (hFeq : ∀ y : e.carrier, y.val.val ∈ T → F y.val.val = f (e.toPoint y)) :
    (θ.add (ddcOf f hf)).RestrictsTo (e.restrict T hT) (v + smoothDDC F) := by
  refine restrictsTo_add (hv.mono hT)
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hF) (hθ.restrict T hT) ?_
  exact restrictsTo_ddcOf hf (e := e.restrict T hT) hF
    (fun y => hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property)

/-- The relation `θ' = θ + dd^c f` for a smooth function `f` on `X`, with equality of forms on
`X`. -/
def AddDDC (θ θ' : SpaceForm X 2) : Prop :=
  ∃ (f : X.obj.left → ℝ) (hf : X.IsSmoothFunction f), SameForm (θ.add (ddcOf f hf)) θ'

/-- `θ + dd^c 0 = θ`. -/
theorem sameForm_add_ddcOf_zero (θ : SpaceForm X 2) :
    SameForm (θ.add (ddcOf (fun _ => 0) SourceReducedComplexSpace.isSmoothFunction_zero)) θ := by
  intro i
  have h := restrictsTo_add (θ.smooth i)
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn (θ.chart i).ambient.isOpen
      (contDiffOn_const (c := (0 : ℝ)))) (θ.restrictsTo_rep i)
    (restrictsTo_ddcOf SourceReducedComplexSpace.isSmoothFunction_zero (e := θ.chart i)
      (g := fun _ => 0) contDiffOn_const (fun _ => rfl))
  refine h.congr fun z _ => ?_
  simp

theorem AddDDC.refl (θ : SpaceForm X 2) : AddDDC θ θ :=
  ⟨fun _ => 0, SourceReducedComplexSpace.isSmoothFunction_zero, sameForm_add_ddcOf_zero θ⟩

theorem AddDDC.of_sameForm {θ θ' : SpaceForm X 2} (h : SameForm θ θ') : AddDDC θ θ' :=
  ⟨fun _ => 0, SourceReducedComplexSpace.isSmoothFunction_zero,
    (sameForm_add_ddcOf_zero θ).trans h⟩

theorem AddDDC.symm {θ θ' : SpaceForm X 2} (h : AddDDC θ θ') : AddDDC θ' θ := by
  obtain ⟨f, hf, hS⟩ := h
  refine ⟨fun y => -f y, hf.neg, fun i => ?_⟩
  refine restrictsTo_of_local fun c => ?_
  obtain ⟨T, hT, hcT, F, hF, hFeq⟩ := hf.exists_local_extension (θ.chart i) c
  refine ⟨T, hT, hcT, ?_⟩
  have h₁ : θ'.RestrictsTo ((θ.chart i).restrict T hT) (θ.rep i + smoothDDC F) :=
    hS.restrictsTo (restrictsTo_add_ddcOf_local hf (θ.chart i) (θ.smooth i) (θ.restrictsTo_rep i)
      hT hF hFeq)
  have h₂ : (ddcOf (fun y => -f y) hf.neg).RestrictsTo ((θ.chart i).restrict T hT)
      (smoothDDC fun z => -F z) :=
    restrictsTo_ddcOf hf.neg (e := (θ.chart i).restrict T hT) hF.neg
      (fun y => by
        rw [hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property]
        rfl)
  have h₃ := restrictsTo_add (((θ.smooth i).mono hT).add
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hF))
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hF.neg) h₁ h₂
  refine h₃.congr fun z hz => ?_
  change θ.rep i z + smoothDDC F z + smoothDDC (fun z => -F z) z = θ.rep i z
  rw [smoothDDC_neg T.isOpen hF hz]
  abel

theorem AddDDC.trans {θ θ' θ'' : SpaceForm X 2} (h₁ : AddDDC θ θ') (h₂ : AddDDC θ' θ'') :
    AddDDC θ θ'' := by
  obtain ⟨f, hf, hS₁⟩ := h₁
  obtain ⟨g, hg, hS₂⟩ := h₂
  refine ⟨fun y => f y + g y, hf.add hg, SameForm.symm fun A => ?_⟩
  -- `A` is a chart of `θ + dd^c (f + g)`: one local embedding with representatives of both
  refine restrictsTo_of_local fun c => ?_
  obtain ⟨T₁, hT₁, hcT₁, F, hF, hFeq⟩ := hf.exists_local_extension A.emb c
  obtain ⟨T₂, hT₂, hcT₂, G, hG, hGeq⟩ := hg.exists_local_extension A.emb c
  let T : Opens (ComplexModel A.emb.dim) := T₁ ⊓ T₂
  have hT : T ≤ A.emb.ambient := inf_le_left.trans hT₁
  have hTF : ContDiffOn ℝ ∞ F T := hF.mono inf_le_left
  have hTG : ContDiffOn ℝ ∞ G T := hG.mono inf_le_right
  refine ⟨T, hT, ⟨hcT₁, hcT₂⟩, ?_⟩
  -- `θ' = θ + dd^c f` near `c`
  have e₁ : θ'.RestrictsTo (A.emb.restrict T hT) (A.rep₁ + smoothDDC F) :=
    hS₁.restrictsTo (restrictsTo_add_ddcOf_local hf A.emb A.smooth₁ A.restricts₁ hT hTF
      fun y hy => hFeq y hy.1)
  -- `θ'' = θ' + dd^c g` near `c`
  have e₂ : θ''.RestrictsTo (A.emb.restrict T hT) (A.rep₁ + smoothDDC F + smoothDDC G) := by
    have h := restrictsTo_add ((A.smooth₁.mono hT).add
        (Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hTF))
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hTG) e₁
      (restrictsTo_ddcOf hg (e := A.emb.restrict T hT) hTG
        (fun y => hGeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.2))
    exact hS₂.restrictsTo h
  -- `dd^c (f + g)` restricts both to `A.rep₂` and to `dd^c (F + G)`
  have e₃ : (ddcOf (fun y => f y + g y) (hf.add hg)).RestrictsTo (A.emb.restrict T hT)
      (smoothDDC fun z => F z + G z) :=
    restrictsTo_ddcOf (hf.add hg) (e := A.emb.restrict T hT) (hTF.add hTG)
      (fun y => by
        change F y.val.val + G y.val.val = f (A.emb.toPoint _) + g (A.emb.toPoint _)
        rw [hFeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.1,
          hGeq ⟨Opens.inclusion hT y.val, y.property⟩ y.val.property.2]
        rfl)
  have hvan := (A.restricts₂.restrict T hT).vanishesOn_sub_self e₃
  have e₄ := e₂.add_vanishes hvan
  refine e₄.congr fun z hz => ?_
  change A.rep₁ z + smoothDDC F z + smoothDDC G z + (A.rep₂ z - smoothDDC (fun z => F z + G z) z) =
    A.rep₁ z + A.rep₂ z
  rw [smoothDDC_add T.isOpen hTF hTG hz]
  abel

end SpaceForm

/-! ### `H^{1,1}(X, ℝ)` of a complex space -/

/-- **Smooth closed real `(1,1)`-forms on a complex space** (`def:unibranch:L105`): near every
point the restriction of ONE closed `(1,1)` smooth ambient form under a local embedding. -/
def SpaceClosedOneOneForm (X : SourceReducedComplexSpace) : Type 1 :=
  {θ : SpaceForm X 2 // PD.IsLocallyClosedOneOne θ}

namespace SpaceClosedOneOneForm

variable {X : SourceReducedComplexSpace}

/-- **The Bott–Chern relation**: `θ' = θ + dd^c f` for a smooth function `f` on `X`. -/
def BottChernRel (θ θ' : SpaceClosedOneOneForm X) : Prop :=
  SpaceForm.AddDDC θ.val θ'.val

/-- The Bott–Chern relation is an equivalence relation. -/
def bottChernSetoid : Setoid (SpaceClosedOneOneForm X) where
  r := BottChernRel
  iseqv := ⟨fun θ => SpaceForm.AddDDC.refl θ.val, fun h => SpaceForm.AddDDC.symm h,
    fun h₁ h₂ => SpaceForm.AddDDC.trans h₁ h₂⟩

end SpaceClosedOneOneForm

/-- **`H^{1,1}(X, ℝ)`** of a complex space: smooth closed real `(1,1)`-forms modulo `dd^c` of
smooth functions (the real Bott–Chern space; on manifolds this is the project's `RealBottChern`,
the book's `H^{1,1}(X, ℝ)`). -/
def H11 (X : SourceReducedComplexSpace) : Type 1 :=
  Quotient (SpaceClosedOneOneForm.bottChernSetoid (X := X))

namespace H11

variable {X : SourceReducedComplexSpace}

/-- The class `{θ} ∈ H^{1,1}(X, ℝ)` of a smooth closed real `(1,1)`-form. -/
def ofForm (θ : SpaceClosedOneOneForm X) : H11 X := Quotient.mk _ θ

theorem ofForm_surjective : Function.Surjective (ofForm (X := X)) :=
  Quotient.mk_surjective

/-- **Two forms have the same class iff they differ by `dd^c` of a smooth function.** -/
theorem ofForm_eq_iff (θ θ' : SpaceClosedOneOneForm X) :
    ofForm θ = ofForm θ' ↔
      ∃ (f : X.obj.left → ℝ) (hf : X.IsSmoothFunction f),
        SpaceForm.SameForm (θ.val.add (SpaceForm.ddcOf f hf)) θ'.val :=
  Quotient.eq

theorem ofForm_eq_of_rel {θ θ' : SpaceClosedOneOneForm X} {f : X.obj.left → ℝ}
    (hf : X.IsSmoothFunction f) (h : SpaceForm.SameForm (θ.val.add (SpaceForm.ddcOf f hf)) θ'.val) :
    ofForm θ = ofForm θ' :=
  (ofForm_eq_iff θ θ').mpr ⟨f, hf, h⟩

/-- Equal forms on `X` have the same class. -/
theorem ofForm_eq_of_sameForm {θ θ' : SpaceClosedOneOneForm X}
    (h : SpaceForm.SameForm θ.val θ'.val) : ofForm θ = ofForm θ' :=
  Quotient.sound (SpaceForm.AddDDC.of_sameForm h)

end H11

end SGPT.Unibranch
