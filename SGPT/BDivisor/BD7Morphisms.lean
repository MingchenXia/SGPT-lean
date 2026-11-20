import SGPT.BDivisor.BD7Models
import SGPT.Okounkov.SchemeAnalyticMorphism

/-!
# the projections and dominations of the algebraized models are algebraic

Source: `rmk:bdiv:L749` ("our transcendental intersection theory coincides with [Dang–Favre's] in
the algebraic setting").  Dang–Favre's b-divisor classes live on algebraic models: the comparison
needs, besides the identification of the Néron–Severi spaces (`BD7Models`), that the book's analytic
models and the maps between them are algebraic.

Lane BD5 algebraized every model `π : Y → X(ℂ)` of the book's blow-up system: `Y ≃ V(ℂ)` for a
smooth projective complex scheme `V`.  Here:

* `hom_ext_of_schemeComplexPointMap_eq`: a morphism over `ℂ` from a reduced scheme of finite type
  to a separated one is determined by its complex points;
* `GAGAMorphismsSmooth` — **GAGA for morphisms** between smooth projective complex schemes: every
  holomorphic map `V(ℂ) → W(ℂ)` is the analytification of a morphism `V → W` over `ℂ` (lane GM's
  statement, in the form used here);
* `exists_algebraic_projection`: given GAGA for morphisms, for every algebraization
  `e : V(ℂ) ≃ Y` of a model `π : Y → X(ℂ)` there is a (unique) morphism `p : V → X` over `ℂ` whose
  analytification is `π ∘ e`;
* `exists_algebraic_domination`: the domination `Y' → Y` between two models is, read through the
  algebraizations, the analytification of a (unique) morphism `q : V' → V` over `ℂ`, and
  `q ≫ p = p'` for the algebraic projections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.Projective

local instance bd7MorTopology {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd7MorCharts {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd7MorManifold {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-! ### Morphisms are determined by their complex points -/

section Ext

variable {V W : Scheme.{0}} (gV : V ⟶ Spec (.of ℂ)) (gW : W ⟶ Spec (.of ℂ))

theorem schemeComplexPointMap_comp {Z : Scheme.{0}} (gZ : Z ⟶ Spec (.of ℂ)) (F : V ⟶ W)
    (hF : F ≫ gW = gV) (G : W ⟶ Z) (hG : G ≫ gZ = gW) (q : SchemeComplexPoint gV) :
    schemeComplexPointMap gV gZ (F ≫ G) (by rw [Category.assoc, hG, hF]) q =
      schemeComplexPointMap gW gZ G hG (schemeComplexPointMap gV gW F hF q) :=
  Subtype.ext (Category.assoc _ _ _).symm

/-- **A morphism over `ℂ` is determined by its complex points**, for a reduced source locally of
finite type and a separated target locally of finite type over `ℂ` (Mathlib's `ext_of_apply_eq`:
the closed points are the complex points). -/
theorem hom_ext_of_schemeComplexPointMap_eq [IsReduced V] [LocallyOfFiniteType gV]
    [IsSeparated gW] [LocallyOfFiniteType gW] {F₁ F₂ : V ⟶ W} (h₁ : F₁ ≫ gW = gV)
    (h₂ : F₂ ≫ gW = gV)
    (h : ∀ q, schemeComplexPointMap gV gW F₁ h₁ q = schemeComplexPointMap gV gW F₂ h₂ q) :
    F₁ = F₂ := by
  have : LocallyOfFiniteType (F₁ ≫ gW) := by rw [h₁]; infer_instance
  refine ext_of_apply_eq gW Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => ?_) (h₁.trans h₂.symm)
  set q := pointOfClosedPoint gV x hx
  have hq : q (IsLocalRing.closedPoint ℂ) = x := pointOfClosedPoint_apply gV x hx _
  have hqc : q ≫ gV = 𝟙 _ := pointOfClosedPoint_comp gV x hx
  have hval : q ≫ F₁ = q ≫ F₂ := congrArg Subtype.val (h ⟨q, hqc⟩)
  rw [← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hval]

end Ext

/-! ### GAGA for morphisms -/

/-- **GAGA for morphisms between smooth projective complex schemes**: every holomorphic map
`φ : V(ℂ) → W(ℂ)` between the complex manifolds of smooth projective complex schemes is the
analytification of a morphism `F : V → W` over `ℂ`.  (Lane GM proves GAGA for morphisms from a smooth
projective `V` to a reduced projective `W`; this is the special case used for the book's models.) -/
def GAGAMorphismsSmooth : Prop :=
  ∀ (V W : Scheme.{0}) (gV : V ⟶ Spec (.of ℂ)) (gW : W ⟶ Spec (.of ℂ)) (n m : ℕ)
    [SmoothOfRelativeDimension n gV] [SmoothOfRelativeDimension m gW],
    ClosedProjectiveEmbedding gV → ClosedProjectiveEmbedding gW →
    ∀ φ : SchemeComplexPoint gV → SchemeComplexPoint gW,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ φ →
      ∃ (F : V ⟶ W) (hF : F ≫ gW = gV), ∀ q, schemeComplexPointMap gV gW F hF q = φ q

/-! ### The book's models -/

section Models

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) {d : ℕ}
  [SmoothOfRelativeDimension d f]

/-- **The projection of a model is algebraic.**  Given GAGA for morphisms, for every model
`π : Y → X(ℂ)` of the book's blow-up system and every algebraization `e : V(ℂ) ≃ Y` by a smooth
projective complex scheme `V`, the projection `π ∘ e` is the analytification of a morphism
`p : V → X` over `ℂ`. -/
theorem exists_algebraic_projection (H : GAGAMorphismsSmooth) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ (π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model) {V : Scheme.{0}}
      (g : V ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension d g] (_ : ClosedProjectiveEmbedding g)
      (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π.1.carrier),
      ∃ (p : V ⟶ X) (hp : p ≫ f = g), ∀ q, schemeComplexPointMap g f p hp q = π.1.map (e q) := by
  intro _ _ _ π V g _ EV e
  exact H V X g f d d EV E (π.1.map ∘ e) (π.1.contMDiff_map.comp e.contMDiff)

/-- **The dominations between models are algebraic.**  Given GAGA for morphisms, let `π ≤ π'` be
models of the book's blow-up system (`π' = π ∘ k` for the dominating holomorphic map
`k : Y' → Y`), with algebraizations `e : V(ℂ) ≃ Y`, `e' : V'(ℂ) ≃ Y'` and algebraic projections
`p : V → X`, `p' : V' → X` (`p(ℂ) = π ∘ e`, `p'(ℂ) = π' ∘ e'`).  Then `e⁻¹ ∘ k ∘ e'` is the
analytification of a morphism `q : V' → V` over `ℂ`, and `q ≫ p = p'`. -/
theorem exists_algebraic_domination (H : GAGAMorphismsSmooth) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ {π π' : (ModelSystem.blowup d (SchemeComplexPoint f)).Model} (hle : π ≤ π')
      {V V' : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (g' : V' ⟶ Spec (.of ℂ))
      [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
      (EV : ClosedProjectiveEmbedding g) (EV' : ClosedProjectiveEmbedding g')
      (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π.1.carrier)
      (e' : SchemeComplexPoint g' ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π'.1.carrier)
      (p : V ⟶ X) (hp : p ≫ f = g) (p' : V' ⟶ X) (hp' : p' ≫ f = g'),
      (∀ q, schemeComplexPointMap g f p hp q = π.1.map (e q)) →
      (∀ q, schemeComplexPointMap g' f p' hp' q = π'.1.map (e' q)) →
      ∃ (q : V' ⟶ V) (hq : q ≫ g = g'),
        (∀ z, e (schemeComplexPointMap g' g q hq z) =
          Modification.homOfLE (show π.1 ≤ π'.1 from hle) (e' z)) ∧
        q ≫ p = p' := by
  intro _ _ _ π π' hle V V' g g' _ _ EV EV' e e' p hp p' hp' hpe hpe'
  let k := Modification.homOfLE (show π.1 ≤ π'.1 from hle)
  have hk : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ k :=
    Modification.contMDiff_homOfLE _
  obtain ⟨q, hq, hqe⟩ := H V' V g' g d d EV' EV (e.symm ∘ k ∘ e')
    (e.symm.contMDiff.comp (hk.comp e'.contMDiff))
  refine ⟨q, hq, fun z => ?_, ?_⟩
  · rw [hqe z]
    exact e.apply_symm_apply _
  · let := EV'.isSeparated
    let := EV'.quasiCompact
    have := SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothScheme_isReduced g' d
    have := EV'.locallyOfFiniteType
    have := EV.isSeparated
    have := EV.locallyOfFiniteType
    have hpX : LocallyOfFiniteType f := E.locallyOfFiniteType
    have := E.isSeparated
    have hcomp : (q ≫ p) ≫ f = g' := by rw [Category.assoc, hp, hq]
    refine hom_ext_of_schemeComplexPointMap_eq g' f hcomp hp' (fun z => ?_)
    have h1 : schemeComplexPointMap g' f (q ≫ p) hcomp z =
        schemeComplexPointMap g f p hp (schemeComplexPointMap g' g q hq z) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [h1, hpe, hpe', hqe z]
    change π.1.map (e (e.symm (k (e' z)))) = _
    rw [e.apply_symm_apply]
    exact congrFun (Modification.map_comp_homOfLE (show π.1 ≤ π'.1 from hle)) (e' z)

end Models

end SGPT.BDivisor.BD7
