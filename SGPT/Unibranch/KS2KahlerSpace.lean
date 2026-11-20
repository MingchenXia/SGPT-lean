import SGPT.Unibranch.KS3KahlerSpace
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Kähler forms on complex spaces: sums, `ddᶜ` of smooth functions, domination

Infrastructure for the Kähler form `ω̃` on the normalization `Ỹ` used in the footnote of
`def:traceop` (`chapter_trace.tex`: "Take a Kähler form `ω̃` on `Ỹ` so that `ω̃ ≥ (θ+ω)|_Ỹ`").

**The notion of Kähler form on a complex space** is the EXISTING one,
`SGPT.Unibranch.SpaceForm.IsKahler` (`NativeNov16AmbientFormRestriction`): near every point the
form is the restriction, under a local embedding `V ↪ Ω ⊆ ℂ^N`, of ONE smooth ambient real
two-form which is closed, of type `(1,1)` and strictly positive. No parallel notion is introduced.
We prove that it is equivalent to the other usual definition (Grauert, Varouchas): local strictly
plurisubharmonic smooth potentials in local embeddings (`isKahler_iff_strictlyPsh_potentials`),
which is the potential-theoretic reading matching `def:unibranch:L105` (`θ`-psh functions are
defined through the same local data `θ = (ddᶜ g)|_V`).

New general API for smooth forms on complex spaces (`SpaceForm`, `def:unibranch:L105`):

* `SpaceForm.RestrictsTo.vanishesOn_sub`: two ambient representatives of the same form agree on
  `X` along every holomorphic transition; `RestrictsTo.of_lift`, `RestrictsTo.restrict`,
  `exists_restrictsTo_nhd` (local representatives exist on every local embedding).
* `SpaceForm.add`: the sum of two smooth forms on a complex space (`restrictsTo_add`).
* `SourceReducedComplexSpace.IsSmoothFunction` (locally the restriction of a smooth ambient
  function) and `SpaceForm.ddcOf f hf`, the form `ddᶜ f` (`restrictsTo_ddcOf`).
* `SpaceForm.Dominates ω θ` ("`ω ≥ θ`"): `ω - θ` is locally the restriction of a smooth closed
  semipositive real `(1,1)`-form: near every point ONE local embedding carries ambient
  representatives `v` of `ω` and `w` of `θ` with `v - w` closed, of type `(1,1)` and
  `w(u, iu) ≤ v(u, iu)` everywhere on the ambient open set; `SpaceForm.IsSemipositive`.
* Kähler spaces: the shared notion `SourceReducedComplexSpace.IsKahlerSpace X` ("`X` carries a
  Kähler form") is the (`KS3KahlerSpace`), imported here.

Blueprint: `blueprint/src/KS2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch

/-- Pull-back of forms is additive. -/
theorem pullbackForm_add {m N k : ℕ} (G : ComplexModel m → ComplexModel N)
    (v w : AmbientForm N k) :
    pullbackForm G (v + w) = pullbackForm G v + pullbackForm G w := by
  funext z
  ext a
  simp [pullbackForm]

/-- Pull-back of forms is homogeneous. -/
theorem pullbackForm_smul {m N k : ℕ} (G : ComplexModel m → ComplexModel N) (c : ℝ)
    (v : AmbientForm N k) :
    pullbackForm G (c • v) = c • pullbackForm G v := by
  funext z
  ext a
  simp [pullbackForm]

/-- On complex tangent lines, the pull-back of a two-form along a holomorphic map is the
two-form on the image line: `(F^*a)(u, iu) = a(dF u, i dF u)`. -/
theorem pullbackForm_apply_complexLine {m N : ℕ} {F : ComplexModel m → ComplexModel N}
    {z : ComplexModel m} (hF : DifferentiableAt ℂ F z) (a : AmbientForm N 2)
    (u : ComplexModel m) :
    pullbackForm F a z ![u, Complex.I • u] =
      a (F z) ![fderiv ℝ F z u, Complex.I • fderiv ℝ F z u] := by
  have hlin : fderiv ℝ F z (Complex.I • u) = Complex.I • fderiv ℝ F z u := by
    rw [hF.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ F z).map_smul Complex.I u
  change a (F z) ((fderiv ℝ F z) ∘ ![u, Complex.I • u]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp [hlin]

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-- A space form restricts, on each of its own charts, to its own representative. -/
theorem restrictsTo_rep (θ : SpaceForm X k) (i : θ.ι) : θ.RestrictsTo (θ.chart i) (θ.rep i) :=
  fun j W G hG => θ.compatible i j W G hG

/-- **Uniqueness of restrictions on `X`.** Two ambient representatives of the same form, on two
local embeddings, agree on `X` along every holomorphic transition map. -/
theorem RestrictsTo.vanishesOn_sub {θ : SpaceForm X k} {e e' : LocalEmbedding X}
    {v : AmbientForm e.dim k} {v' : AmbientForm e'.dim k}
    (hv : θ.RestrictsTo e v) (hv' : θ.RestrictsTo e' v')
    {W : Set (ComplexModel e.dim)} {G : ComplexModel e.dim → ComplexModel e'.dim}
    (hG : e.IsTransition e' W G) : e.VanishesOn W (v - pullbackForm G v') := by
  intro m D h hD hd hm z hz
  obtain ⟨c, hc⟩ := (hm z hz).2
  obtain ⟨j, hj⟩ := θ.covers (e.toPoint c)
  obtain ⟨W₁, T, hcW₁, hT⟩ := e.exists_isTransition (θ.chart j) c hj
  let D' : Set (ComplexModel m) := D ∩ h ⁻¹' W₁
  have hD' : IsOpen D' := hd.continuousOn.isOpen_inter_preimage hD hT.1
  have hzD' : z ∈ D' := ⟨hz, by change h z ∈ W₁; rw [← hc]; exact hcW₁⟩
  have hhD' : DifferentiableOn ℂ h D' := hd.mono inter_subset_left
  have hTh : DifferentiableOn ℂ (T ∘ h) D' := hT.2.2.1.comp hhD' (fun w hw => hw.2)
  have hGh : DifferentiableOn ℂ (G ∘ h) D' :=
    hG.2.2.1.comp hhD' (fun w hw => (hm w hw.1).1)
  have h1 : pullbackForm h v z = pullbackForm (T ∘ h) (θ.rep j) z := by
    refine pullback_eq_of_restrictsTo θ hv j hD' hhD' hTh ?_ hzD'
    intro w hw
    obtain ⟨a, ha⟩ := (hm w hw.1).2
    obtain ⟨b, hb, hba⟩ := hT.2.2.2.2 a (by rw [ha]; exact hw.2)
    exact ⟨a, b, ha, by rw [hb, ha]; rfl, hba.symm⟩
  have h2 : pullbackForm (G ∘ h) v' z = pullbackForm (T ∘ h) (θ.rep j) z := by
    refine pullback_eq_of_restrictsTo θ hv' j hD' hGh hTh ?_ hzD'
    intro w hw
    obtain ⟨a, ha⟩ := (hm w hw.1).2
    obtain ⟨a', ha', ha'a⟩ := hG.2.2.2.2 a (by rw [ha]; exact (hm w hw.1).1)
    obtain ⟨b, hb, hba⟩ := hT.2.2.2.2 a (by rw [ha]; exact hw.2)
    exact ⟨a', b, by rw [ha', ha]; rfl, by rw [hb, ha]; rfl, ha'a.trans hba.symm⟩
  have hhz : DifferentiableAt ℝ h z :=
    (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hGz : DifferentiableAt ℝ G (h z) :=
    (hG.2.2.1.differentiableAt (hG.1.mem_nhds (hm z hz).1)).restrictScalars ℝ
  rw [pullbackForm_sub, Pi.sub_apply, pullbackForm_comp hhz hGz, h1, h2, sub_self]

/-- Restriction along a holomorphic map of ambient spaces which is compatible with the points. -/
theorem RestrictsTo.of_lift {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) (a : LocalEmbedding X)
    {G : ComplexModel a.dim → ComplexModel e.dim} (hG : DifferentiableOn ℂ G a.ambient)
    (hfac : ∀ c : a.carrier, ∃ b : e.carrier,
      b.val.val = G c.val.val ∧ e.toPoint b = a.toPoint c) :
    θ.RestrictsTo a (pullbackForm G v) := by
  intro i W H hH m D h hD hd hm z hz
  have hmapA : MapsTo h D a.ambient := fun w hw => hH.2.1 (hm w hw).1
  have hGh : DifferentiableOn ℂ (G ∘ h) D := hG.comp hd hmapA
  have hHh : DifferentiableOn ℂ (H ∘ h) D := hH.2.2.1.comp hd (fun w hw => (hm w hw).1)
  have hcore : pullbackForm (G ∘ h) v z = pullbackForm (H ∘ h) (θ.rep i) z := by
    refine pullback_eq_of_restrictsTo θ hv i hD hGh hHh ?_ hz
    intro w hw
    obtain ⟨c, hc⟩ := (hm w hw).2
    obtain ⟨b, hb, hbc⟩ := hfac c
    obtain ⟨d, hd', hdc⟩ := hH.2.2.2.2 c (by rw [hc]; exact (hm w hw).1)
    exact ⟨b, d, by rw [hb, hc]; rfl, by rw [hd', hc]; rfl, hbc.trans hdc.symm⟩
  have hhz : DifferentiableAt ℝ h z :=
    (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hGz : DifferentiableAt ℝ G (h z) :=
    (hG.differentiableAt (a.ambient.isOpen.mem_nhds (hmapA hz))).restrictScalars ℝ
  have hHz : DifferentiableAt ℝ H (h z) :=
    (hH.2.2.1.differentiableAt (hH.1.mem_nhds (hm z hz).1)).restrictScalars ℝ
  rw [pullbackForm_sub, Pi.sub_apply, pullbackForm_comp hhz hGz, pullbackForm_comp hhz hHz,
    hcore, sub_self]

/-- Restriction passes to the restriction of a local embedding to a smaller ambient open set. -/
theorem RestrictsTo.restrict {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) : θ.RestrictsTo (e.restrict T hT) v := by
  intro i W G hG
  have hWT : W ⊆ (T : Set (ComplexModel e.dim)) := hG.2.1
  have hG' : e.IsTransition (θ.chart i) W G := by
    refine ⟨hG.1, fun z hz => hT (hWT hz), hG.2.2.1, hG.2.2.2.1, ?_⟩
    intro y hy
    let y' : e.restrictCarrier T hT := ⟨⟨y.val.val, hWT hy⟩, by
      have hyy : Opens.inclusion hT ⟨y.val.val, hWT hy⟩ = y.val := Subtype.ext rfl
      change Opens.inclusion hT ⟨y.val.val, hWT hy⟩ ∈ e.carrier
      rw [hyy]
      exact y.property⟩
    obtain ⟨z, hz, hzy⟩ := hG.2.2.2.2 y' hy
    refine ⟨z, hz, ?_⟩
    rw [hzy, LocalEmbedding.restrict_toPoint]
    rfl
  have hvan := hv i W G hG'
  intro m D h hD hh hmaps z hz
  have hmaps' : ∀ z ∈ D, h z ∈ W ∧ ∃ c : e.carrier, c.val.val = h z := by
    intro z hz
    obtain ⟨hzW, c, hc⟩ := hmaps z hz
    exact ⟨hzW, ⟨⟨Opens.inclusion hT c.val, c.property⟩, hc⟩⟩
  exact hvan m D h hD hh hmaps' z hz

/-- **Local representatives exist on every local embedding.** Near every point of every local
embedding `e`, the form restricts to a smooth ambient form on a smaller ambient open set. -/
theorem exists_restrictsTo_nhd (θ : SpaceForm X k) (e : LocalEmbedding X) (c : e.carrier) :
    ∃ (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient), c.val.val ∈ T ∧
      ∃ v : AmbientForm e.dim k, ContDiffOn ℝ ∞ v T ∧ θ.RestrictsTo (e.restrict T hT) v := by
  obtain ⟨i, hi⟩ := θ.covers (e.toPoint c)
  obtain ⟨W, hW, hcW, hWU, G, hG, hmaps, hfac⟩ := e.exists_contDiff_transition (θ.chart i) c hi
  let T : Opens (ComplexModel e.dim) := ⟨W, hW⟩
  refine ⟨T, hWU, hcW, pullbackForm G (θ.rep i), ?_, ?_⟩
  · apply SmoothRealForm.contDiffOn_compContinuousLinearMap
    · exact (θ.smooth i).comp (hG.restrict_scalars ℝ) hmaps
    · exact (hG.restrict_scalars ℝ).fderiv_of_isOpen hW (by simp)
  · refine (θ.restrictsTo_rep i).of_lift (e.restrict T hWU) (hG.differentiableOn (by simp)) ?_
    intro c'
    obtain ⟨b, hb, hbc⟩ := hfac ⟨Opens.inclusion hWU c'.val, c'.property⟩ c'.val.property
    exact ⟨b, hb, hbc⟩

/-! ### Sums of forms -/

/-- A chart of the sum of two forms: one local embedding carrying smooth ambient
representatives of both summands. -/
structure AddChart (θ₁ θ₂ : SpaceForm X k) where
  /-- The local embedding. -/
  emb : LocalEmbedding X
  /-- Ambient representative of the first summand. -/
  rep₁ : AmbientForm emb.dim k
  /-- Ambient representative of the second summand. -/
  rep₂ : AmbientForm emb.dim k
  smooth₁ : ContDiffOn ℝ ∞ rep₁ emb.ambient
  smooth₂ : ContDiffOn ℝ ∞ rep₂ emb.ambient
  restricts₁ : θ₁.RestrictsTo emb rep₁
  restricts₂ : θ₂.RestrictsTo emb rep₂

theorem addChart_cover (θ₁ θ₂ : SpaceForm X k) (x : X.obj.left) :
    ∃ A : AddChart θ₁ θ₂, x ∈ range A.emb.toPoint := by
  obtain ⟨i, c, hc⟩ := θ₁.covers x
  obtain ⟨T, hT, hcT, v, hv, hres⟩ := exists_restrictsTo_nhd θ₂ (θ₁.chart i) c
  refine ⟨⟨(θ₁.chart i).restrict T hT, θ₁.rep i, v, (θ₁.smooth i).mono hT, hv,
    (θ₁.restrictsTo_rep i).restrict T hT, hres⟩, ⟨⟨c.val.val, hcT⟩, c.property⟩, ?_⟩
  rw [LocalEmbedding.restrict_toPoint]
  exact hc

/-- **The sum of two smooth forms on a complex space.** Its charts are the local embeddings
carrying representatives of both forms; the representative is the sum. -/
def add (θ₁ θ₂ : SpaceForm X k) : SpaceForm X k where
  ι := AddChart θ₁ θ₂
  chart A := A.emb
  covers := addChart_cover θ₁ θ₂
  rep A := A.rep₁ + A.rep₂
  smooth A := A.smooth₁.add A.smooth₂
  compatible A B W G hG := by
    intro m D h hD hd hm z hz
    have h₁ := A.restricts₁.vanishesOn_sub B.restricts₁ hG m D h hD hd hm z hz
    have h₂ := A.restricts₂.vanishesOn_sub B.restricts₂ hG m D h hD hd hm z hz
    change pullbackForm h (A.rep₁ + A.rep₂ - pullbackForm G (B.rep₁ + B.rep₂)) z = 0
    have hsplit : A.rep₁ + A.rep₂ - pullbackForm G (B.rep₁ + B.rep₂) =
        (A.rep₁ - pullbackForm G B.rep₁) + (A.rep₂ - pullbackForm G B.rep₂) := by
      rw [pullbackForm_add]
      abel
    rw [hsplit, pullbackForm_add, Pi.add_apply, h₁, h₂, add_zero]

/-- The sum restricts to the sum of representatives. -/
theorem restrictsTo_add {θ₁ θ₂ : SpaceForm X k} {e : LocalEmbedding X}
    {v₁ v₂ : AmbientForm e.dim k} (hv₁ : ContDiffOn ℝ ∞ v₁ e.ambient)
    (hv₂ : ContDiffOn ℝ ∞ v₂ e.ambient) (h₁ : θ₁.RestrictsTo e v₁) (h₂ : θ₂.RestrictsTo e v₂) :
    (θ₁.add θ₂).RestrictsTo e (v₁ + v₂) :=
  (θ₁.add θ₂).restrictsTo_rep ⟨e, v₁, v₂, hv₁, hv₂, h₁, h₂⟩

end SpaceForm

/-! ### `ddᶜ` of a smooth function -/

namespace SourceReducedComplexSpace

/-- A real function on a complex space is *smooth* if near every point it is the restriction of
a smooth function on the ambient space of a local embedding. -/
def IsSmoothFunction (X : SourceReducedComplexSpace) (f : X.obj.left → ℝ) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
      ∀ c : e.carrier, g c.val.val = f (e.toPoint c)

end SourceReducedComplexSpace

namespace SpaceForm

variable {X : SourceReducedComplexSpace}

/-- A chart of `ddᶜ f`: a local embedding with a smooth ambient extension of `f`. -/
structure DDCChart (f : X.obj.left → ℝ) where
  /-- The local embedding. -/
  emb : LocalEmbedding X
  /-- A smooth ambient extension of `f`. -/
  pot : ComplexModel emb.dim → ℝ
  smooth : ContDiffOn ℝ ∞ pot emb.ambient
  eq : ∀ c : emb.carrier, pot c.val.val = f (emb.toPoint c)

/-- **`ddᶜ f` for a smooth function `f` on a complex space**: locally `ddᶜ` of any smooth ambient
extension of `f` (well defined on `X`: two extensions agree on `X`, hence so do their `ddᶜ`
along every holomorphic probe). -/
def ddcOf (f : X.obj.left → ℝ) (hf : X.IsSmoothFunction f) : SpaceForm X 2 where
  ι := DDCChart f
  chart A := A.emb
  covers x := by
    obtain ⟨e, hx, g, hg, heq⟩ := hf x
    exact ⟨⟨e, g, hg, heq⟩, hx⟩
  rep A := smoothDDC A.pot
  smooth A :=
    Pending.LogWeightFactorization.smoothDDC_contDiffOn A.emb.ambient.isOpen A.smooth
  compatible A B W G hG := by
    intro m D h hD hd hm z hz
    change pullbackForm h (smoothDDC A.pot - pullbackForm G (smoothDDC B.pot)) z = 0
    have hhc : ContDiffOn ℂ ∞ h D := contDiffOn_of_differentiableOn_complex hd hD
    have hGc : ContDiffOn ℂ ∞ G W := contDiffOn_of_differentiableOn_complex hG.2.2.1 hG.1
    have hGh : ContDiffOn ℂ ∞ (G ∘ h) D := hGc.comp hhc (fun w hw => (hm w hw).1)
    have hmapA : MapsTo h D A.emb.ambient := fun w hw => hG.2.1 (hm w hw).1
    have hmapB : MapsTo (G ∘ h) D B.emb.ambient := fun w hw => hG.2.2.2.1 (hm w hw).1
    have hhz : DifferentiableAt ℝ h z :=
      (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
    have hGz : DifferentiableAt ℝ G (h z) :=
      (hG.2.2.1.differentiableAt (hG.1.mem_nhds (hm z hz).1)).restrictScalars ℝ
    have e1 : pullbackForm h (smoothDDC A.pot) z = smoothDDC (fun y => A.pot (h y)) z :=
      (HolomorphicDDC.smoothDDC_comp hD A.emb.ambient.isOpen hhc A.smooth hmapA hz).symm
    have e2 : pullbackForm h (pullbackForm G (smoothDDC B.pot)) z =
        smoothDDC (fun y => B.pot ((G ∘ h) y)) z := by
      rw [pullbackForm_comp hhz hGz]
      exact (HolomorphicDDC.smoothDDC_comp hD B.emb.ambient.isOpen hGh B.smooth hmapB hz).symm
    have e3 : (fun y => A.pot (h y)) =ᶠ[𝓝 z] (fun y => B.pot ((G ∘ h) y)) := by
      filter_upwards [hD.mem_nhds hz] with w hw
      obtain ⟨c, hc⟩ := (hm w hw).2
      obtain ⟨c', hc', hc'c⟩ := hG.2.2.2.2 c (by rw [hc]; exact (hm w hw).1)
      show A.pot (h w) = B.pot (G (h w))
      rw [← hc, A.eq c, ← hc', B.eq c', hc'c]
    rw [pullbackForm_sub, Pi.sub_apply, e1, e2, smoothDDC_congr e3, sub_self]

/-- `ddᶜ f` restricts to `ddᶜ g` for every smooth ambient extension `g` of `f`. -/
theorem restrictsTo_ddcOf {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f) {e : LocalEmbedding X}
    {g : ComplexModel e.dim → ℝ} (hg : ContDiffOn ℝ ∞ g e.ambient)
    (heq : ∀ c : e.carrier, g c.val.val = f (e.toPoint c)) :
    (ddcOf f hf).RestrictsTo e (smoothDDC g) :=
  (ddcOf f hf).restrictsTo_rep ⟨e, g, hg, heq⟩

/-! ### Positivity and domination -/

/-- Semipositivity of a real two-form on a complex space: near every point it is the restriction,
under a local embedding, of a smooth ambient form `v` with `v(u, iu) ≥ 0` everywhere. -/
def IsSemipositive (θ : SpaceForm X 2) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v : AmbientForm e.dim 2, ContDiffOn ℝ ∞ v e.ambient ∧ θ.RestrictsTo e v ∧
      ∀ z ∈ e.ambient, ∀ u : ComplexModel e.dim, 0 ≤ v z ![u, Complex.I • u]

/-- **Domination `ω ≥ θ`** of real two-forms on a complex space (the inequality
`ω̃ ≥ (θ + ω)|_Ỹ` in the footnote of `def:traceop`): `ω - θ` is locally the restriction of a
smooth closed semipositive real `(1,1)`-form. Precisely, near every point there are ONE local
embedding and smooth ambient representatives `v` of `ω` and `w` of `θ` on it such that, at every
point of the ambient open set, `v - w` is closed, of type `(1,1)`, and `w(u, iu) ≤ v(u, iu)`. -/
def Dominates (om θ : SpaceForm X 2) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v w : AmbientForm e.dim 2, ContDiffOn ℝ ∞ v e.ambient ∧ ContDiffOn ℝ ∞ w e.ambient ∧
      om.RestrictsTo e v ∧ θ.RestrictsTo e w ∧
      ∀ z ∈ e.ambient, extDeriv (v - w) z = 0 ∧ FirstPass.IsOneOne ((v - w) z) ∧
        ∀ u : ComplexModel e.dim, w z ![u, Complex.I • u] ≤ v z ![u, Complex.I • u]

/-- A Kähler form dominates the zero form (`ω ≥ 0`). -/
theorem IsKahler.isSemipositive {θ : SpaceForm X 2} (h : θ.IsKahler) : θ.IsSemipositive := by
  intro x
  obtain ⟨e, hx, v, hv, -, hpos, hres⟩ := h x
  refine ⟨e, hx, v, hv, hres, fun z hz u => ?_⟩
  by_cases hu : u = 0
  · subst hu
    rw [(v z).map_coord_zero (0 : Fin 2) rfl]
  · exact ((hpos z hz).2 u hu).le

/-! ### Kähler forms and strictly psh local potentials -/

private theorem contDiffAt_two_of_contDiffOn {N : ℕ} {g : ComplexModel N → ℝ}
    {U : Set (ComplexModel N)} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {z : ComplexModel N}
    (hz : z ∈ U) : ContDiffAt ℝ 2 g z :=
  (hg.contDiffAt (hU.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- **Kähler forms have local strictly psh potentials** (Grauert's definition): near every point
there are a local embedding `V ↪ Ω` and a smooth `g` on `Ω` with `θ = (ddᶜ g)|_V` and `g`
strictly plurisubharmonic on `Ω` (positive definite Levi form). -/
theorem IsKahler.exists_strictlyPsh_potential {θ : SpaceForm X 2} (h : θ.IsKahler)
    (x : X.obj.left) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        θ.RestrictsTo e (smoothDDC g) ∧
        ∀ z ∈ e.ambient, ∀ u : ComplexModel e.dim, u ≠ 0 → 0 < leviForm g z u := by
  obtain ⟨e, ⟨c, rfl⟩, v, hv, hcl, hpos, hres⟩ := h x
  obtain ⟨W, ρ, hcW, hW, hWe, hρ, heq⟩ :=
    Pending.LocalPotentials.exists_smooth_local_ddc_potential e.ambient.isOpen v hv hcl
      (fun z hz => (hpos z hz).1) c.val.property
  let T : Opens (ComplexModel e.dim) := ⟨W, hW⟩
  have hT : T ≤ e.ambient := fun z hz => hWe hz
  refine ⟨e.restrict T hT, ⟨⟨⟨c.val.val, hcW⟩, c.property⟩, ?_⟩, ρ, hρ, ?_, ?_⟩
  · rw [LocalEmbedding.restrict_toPoint]
    rfl
  · exact restrictsTo_congr (hres.restrict T hT) (fun z hz => (heq hz).symm)
  · intro z hz u hu
    have hlevi := smoothDDC_complexDiagonal_eq_leviForm
      (contDiffAt_two_of_contDiffOn hW hρ hz) u
    rw [heq hz] at hlevi
    have hp : 0 < v z ![u, Complex.I • u] := (hpos z (hWe hz)).2 u hu
    rw [hlevi] at hp
    exact (div_pos_iff_of_pos_right Real.pi_pos).mp hp

/-- **Local strictly psh potentials give a Kähler form.** -/
theorem isKahler_of_strictlyPsh_potentials {θ : SpaceForm X 2}
    (h : ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        θ.RestrictsTo e (smoothDDC g) ∧
        ∀ z ∈ e.ambient, ∀ u : ComplexModel e.dim, u ≠ 0 → 0 < leviForm g z u) :
    θ.IsKahler := by
  intro x
  obtain ⟨e, hx, g, hg, hres, hlevi⟩ := h x
  refine ⟨e, hx, smoothDDC g,
    Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hg, ?_, ?_, hres⟩
  · intro z hz
    exact extDeriv_extDeriv_apply
      ((smoothDc_contDiffOn e.ambient.isOpen hg).contDiffAt (e.ambient.isOpen.mem_nhds hz))
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · intro z hz
    have h2 := contDiffAt_two_of_contDiffOn e.ambient.isOpen hg hz
    refine ⟨fun a b => MongeAmpere.smoothDDC_isOneOne h2 a b, fun u hu => ?_⟩
    rw [smoothDDC_complexDiagonal_eq_leviForm h2 u]
    exact div_pos (hlevi z hz u hu) Real.pi_pos

/-- **Equivalence of the two definitions of a Kähler form on a complex space**: locally the
restriction of a closed strictly positive `(1,1)`-form under a local embedding
(`SpaceForm.IsKahler`) if and only if locally `ddᶜ` of a smooth strictly psh ambient
function. -/
theorem isKahler_iff_strictlyPsh_potentials (θ : SpaceForm X 2) :
    θ.IsKahler ↔ ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        θ.RestrictsTo e (smoothDDC g) ∧
        ∀ z ∈ e.ambient, ∀ u : ComplexModel e.dim, u ≠ 0 → 0 < leviForm g z u :=
  ⟨fun h => h.exists_strictlyPsh_potential, isKahler_of_strictlyPsh_potentials⟩

end SpaceForm

end SGPT.Unibranch

end
