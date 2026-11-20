import SGPT.BDivisor.BD6Chart
import SGPT.Foundations.Schemes.PolynomialProjectiveProper
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# gluing chart maps to `ℙʳ` that agree on complex points

Source: `rmk:bdiv:L749` (GAGA on the algebraized models; the morphisms to projective space used
to algebraize line bundles and divisors).

Let `X` be a reduced scheme, locally of finite type over `ℂ`, covered by opens `O_a`, and on each
`O_a` let `c_a = (c_{a,k})_k` be regular functions with `c_{a, j_a} = 1`.  The chart maps
`O_a → D₊(y_{j_a}) ⊆ ℙʳ` (`BD6Chart.chartMap`) send a complex point `p` to `[c_a(p)]`.  If these
points agree at every complex point of every overlap, the chart maps glue to a morphism
`X → ℙʳ` over `ℂ` (`glueChartMaps`): on an overlap the two chart maps agree as morphisms because a
morphism from a reduced scheme of finite type over `ℂ` to a separated one is determined by its
values on closed points (Mathlib's `ext_of_apply_eq`), and the closed points are the complex
points (`pointOfClosedPoint`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (g : X ⟶ Spec (.of ℂ)) {r : ℕ}

/-- The value of a regular function on `U` at a complex point of `U`. -/
def pointValue (p : SchemeComplexPoint g) (U : X.Opens) (hp : schemeComplexPointImage g p ∈ U)
    (s : Γ(X, U)) : ℂ :=
  schemeComplexPointStalkEval g p (X.presheaf.germ U (schemeComplexPointImage g p) hp s)

theorem pointValue_congr {p p' : SchemeComplexPoint g} (h : p = p') (U : X.Opens)
    (hU : schemeComplexPointImage g p ∈ U) (hU' : schemeComplexPointImage g p' ∈ U)
    (s : Γ(X, U)) : pointValue g p U hU s = pointValue g p' U hU' s := by
  subst h; rfl

/-- The complex points of a chart map, in terms of the values of its functions. -/
theorem comp_chartMap_pointValue (U : X.Opens) (j : Fin (r + 1)) (c : Fin (r + 1) → Γ(X, U))
    (hc : c j = 1) (q : Spec (.of ℂ) ⟶ U.toScheme) (hq : (q ≫ U.ι) ≫ g = 𝟙 _) :
    q ≫ chartMap g U j c = (polynomialProjVectorChartPoint r j
      (fun k => pointValue g ⟨q ≫ U.ι, hq⟩ U (q default).2 (c k))).val := by
  rw [comp_chartMap g U j c hc q hq]
  congr 2
  funext k
  exact (stalkEval_germ_eq_specPreimage g U q hq (q default).2 (c k)).symm

variable [IsReduced X] [LocallyOfFiniteType g]

/-- **Two chart maps agreeing on complex points agree on the overlap.** -/
theorem chartMaps_agree (U V : X.Opens) (j₁ j₂ : Fin (r + 1)) (c₁ : Fin (r + 1) → Γ(X, U))
    (c₂ : Fin (r + 1) → Γ(X, V)) (hc₁ : c₁ j₁ = 1) (hc₂ : c₂ j₂ = 1)
    (hcompat : ∀ (p : SchemeComplexPoint g) (hU : schemeComplexPointImage g p ∈ U)
      (hV : schemeComplexPointImage g p ∈ V),
      polynomialProjVectorChartPoint r j₁ (fun k => pointValue g p U hU (c₁ k)) =
        polynomialProjVectorChartPoint r j₂ (fun k => pointValue g p V hV (c₂ k))) :
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ chartMap g U j₁ c₁ =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ chartMap g V j₂ c₂ := by
  set W := U ⊓ V
  have hs₁ : (X.homOfLE (inf_le_left : W ≤ U) ≫ chartMap g U j₁ c₁) ≫
      polynomialProjStructureMap ℂ r = W.ι ≫ g := by
    rw [Category.assoc, chartMap_structure, Scheme.homOfLE_ι_assoc]
  have hs₂ : (X.homOfLE (inf_le_right : W ≤ V) ≫ chartMap g V j₂ c₂) ≫
      polynomialProjStructureMap ℂ r = W.ι ≫ g := by
    rw [Category.assoc, chartMap_structure, Scheme.homOfLE_ι_assoc]
  have : LocallyOfFiniteType ((X.homOfLE (inf_le_left : W ≤ U) ≫ chartMap g U j₁ c₁) ≫
      polynomialProjStructureMap ℂ r) := by
    rw [hs₁]; infer_instance
  have : IsSeparated (polynomialProjStructureMap ℂ r) := inferInstance
  refine ext_of_apply_eq (polynomialProjStructureMap ℂ r) Set.univ isOpen_univ.isLocallyClosed
    dense_univ (fun w _ hw => ?_) (hs₁.trans hs₂.symm)
  have : LocallyOfFiniteType (W.ι ≫ g) := inferInstance
  set qW := pointOfClosedPoint (W.ι ≫ g) w hw
  have hqW : qW default = w := pointOfClosedPoint_apply (W.ι ≫ g) w hw default
  have hqWc : qW ≫ W.ι ≫ g = 𝟙 _ := pointOfClosedPoint_comp (W.ι ≫ g) w hw
  set p : SchemeComplexPoint g := ⟨qW ≫ W.ι, by rw [Category.assoc]; exact hqWc⟩
  have h₁ : (qW ≫ X.homOfLE (inf_le_left : W ≤ U)) ≫ U.ι = qW ≫ W.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
  have h₂ : (qW ≫ X.homOfLE (inf_le_right : W ≤ V)) ≫ V.ι = qW ≫ W.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hq₁ : ((qW ≫ X.homOfLE (inf_le_left : W ≤ U)) ≫ U.ι) ≫ g = 𝟙 _ := by
    rw [h₁]; exact p.2
  have hq₂ : ((qW ≫ X.homOfLE (inf_le_right : W ≤ V)) ≫ V.ι) ≫ g = 𝟙 _ := by
    rw [h₂]; exact p.2
  have e₁ := comp_chartMap_pointValue g U j₁ c₁ hc₁ _ hq₁
  have e₂ := comp_chartMap_pointValue g V j₂ c₂ hc₂ _ hq₂
  have hp₁ : (⟨(qW ≫ X.homOfLE (inf_le_left : W ≤ U)) ≫ U.ι, hq₁⟩ : SchemeComplexPoint g) = p :=
    Subtype.ext h₁
  have hp₂ : (⟨(qW ≫ X.homOfLE (inf_le_right : W ≤ V)) ≫ V.ι, hq₂⟩ : SchemeComplexPoint g) = p :=
    Subtype.ext h₂
  have key : (qW ≫ X.homOfLE (inf_le_left : W ≤ U)) ≫ chartMap g U j₁ c₁ =
      (qW ≫ X.homOfLE (inf_le_right : W ≤ V)) ≫ chartMap g V j₂ c₂ := by
    rw [e₁, e₂]
    have hU : schemeComplexPointImage g p ∈ U := by
      rw [← hp₁]; exact ((qW ≫ X.homOfLE (inf_le_left : W ≤ U)) default).2
    have hV : schemeComplexPointImage g p ∈ V := by
      rw [← hp₂]; exact ((qW ≫ X.homOfLE (inf_le_right : W ≤ V)) default).2
    have := hcompat p hU hV
    convert congrArg Subtype.val this using 3
    · funext k; exact pointValue_congr g hp₁ U _ _ _
    · funext k; exact pointValue_congr g hp₂ V _ _ _
  rw [← hqW, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  simp only [← Category.assoc]
  rw [key]

/-! ### The glued morphism -/

section Glue

variable {ι : Type} (O : ι → X.Opens) (hO : TopologicalSpace.IsOpenCover O)
  (j : ι → Fin (r + 1)) (c : ∀ a, Fin (r + 1) → Γ(X, O a)) (hc : ∀ a, c a (j a) = 1)
  (hcompat : ∀ (a b : ι) (p : SchemeComplexPoint g) (hU : schemeComplexPointImage g p ∈ O a)
      (hV : schemeComplexPointImage g p ∈ O b),
      polynomialProjVectorChartPoint r (j a) (fun k => pointValue g p (O a) hU (c a k)) =
        polynomialProjVectorChartPoint r (j b) (fun k => pointValue g p (O b) hV (c b k)))

include hc hcompat in
theorem glue_compat (a b : ι) :
    pullback.fst (O a).ι (O b).ι ≫ chartMap g (O a) (j a) (c a) =
      pullback.snd (O a).ι (O b).ι ≫ chartMap g (O b) (j b) (c b) := by
  apply (cancel_epi (isPullback_opens_inf (O a) (O b)).isoPullback.hom).mp
  simp only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact chartMaps_agree g (O a) (O b) (j a) (j b) (c a) (c b) (hc a) (hc b) (hcompat a b)

/-- **The morphism `X → ℙʳ` glued from compatible chart maps.** -/
def glueChartMaps : X ⟶ polynomialProj ℂ r :=
  (X.openCoverOfIsOpenCover O hO).glueMorphisms (fun a => chartMap g (O a) (j a) (c a))
    (fun a b => glue_compat g O j c hc hcompat a b)

theorem ι_glueChartMaps (a : ι) :
    (O a).ι ≫ glueChartMaps g O hO j c hc hcompat = chartMap g (O a) (j a) (c a) :=
  (X.openCoverOfIsOpenCover O hO).ι_glueMorphisms _ _ a

/-- The glued morphism lies over `ℂ`. -/
theorem glueChartMaps_structure :
    glueChartMaps g O hO j c hc hcompat ≫ polynomialProjStructureMap ℂ r = g := by
  apply (X.openCoverOfIsOpenCover O hO).hom_ext
  intro a
  change (O a).ι ≫ _ = (O a).ι ≫ g
  rw [← Category.assoc, ι_glueChartMaps, chartMap_structure]

/-- **The complex points of the glued morphism**: on `O_a` it is `p ↦ [c_a(p)]`. -/
theorem glueChartMaps_point (p : SchemeComplexPoint g) (a : ι)
    (hp : schemeComplexPointImage g p ∈ O a) :
    schemeComplexPointMap g (polynomialProjStructureMap ℂ r) (glueChartMaps g O hO j c hc hcompat)
        (glueChartMaps_structure g O hO j c hc hcompat) p =
      polynomialProjVectorChartPoint r (j a) (fun k => pointValue g p (O a) hp (c a k)) := by
  have hrange : Set.range p.val ⊆ Set.range (O a).ι := by
    rintro _ ⟨t, rfl⟩
    have ht : t = default := Subsingleton.elim _ _
    subst ht
    rw [Scheme.Opens.range_ι]
    exact hp
  set q := IsOpenImmersion.lift (O a).ι p.val hrange
  have hqp : q ≫ (O a).ι = p.val := IsOpenImmersion.lift_fac _ _ _
  have hq : (q ≫ (O a).ι) ≫ g = 𝟙 _ := by rw [hqp]; exact p.2
  apply Subtype.ext
  change p.val ≫ glueChartMaps g O hO j c hc hcompat = _
  rw [← hqp, Category.assoc, ι_glueChartMaps, comp_chartMap_pointValue g (O a) (j a) (c a) (hc a) q hq]
  congr 2
  funext k
  exact pointValue_congr g (Subtype.ext hqp) (O a) _ _ _

end Glue

end SGPT.BDivisor.BD6
