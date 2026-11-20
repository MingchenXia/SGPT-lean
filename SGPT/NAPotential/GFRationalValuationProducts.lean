import SGPT.NAPotential.GFRationalVertexSectionFamily

/-! # The SAME actual original products add logarithmic values at EVERY original Berkovich point
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Classical

/-- Actual negative valuation logarithms add, including infinite vanishing. -/
theorem negativeValue_add (x y : WithTop ℝ) : negativeValue (x + y) = negativeValue x + negativeValue y := by
  cases x with
  | top => simp
  | coe x =>
    cases y with
    | top => simp
    | coe y =>
      change ((-(x + y) : ℝ) : EReal) = ((-x : ℝ) : EReal) + ((-y : ℝ) : EReal)
      rw [← EReal.coe_add]
      congr 1
      ring

theorem negativeValue_list_sum (l : List (WithTop ℝ)) :
    negativeValue l.sum = (l.map negativeValue).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [negativeValue_add, ih]

variable {X : Scheme.{0}} {L : X.Modules} {f : X ⟶ Spec (.of ℂ)} [IsProper f] {ι : Type}

/-- The literal actual chosen product adds its ORIGINAL logarithmic values at ALL original points. -/
theorem chosenSectionProduct_logValue (b : LineBundleAtlas L) (N : ℕ) (I : ι → Type*)
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (w : List ι) (σ : WordChoice I w)
    (v : BerkovichPoint f) :
    negativeValue (powerSectionValue b (N * w.length) (chosenSectionProduct b N I t w σ) v) =
      ∑ k : Fin w.length, negativeValue (powerSectionValue b N (t (w.get k) (σ k)) v) := by
  rw [chosenSectionProduct, castDegreeSection_value, sectionWordProduct_value, negativeValue_list_sum]
  simp [List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Finite maxima of the SAME actual products add the original finite logarithmic maxima. -/
theorem chosenSectionProduct_logValue_finiteMaximum (b : LineBundleAtlas L) (N : ℕ)
    (I : ι → Type*) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (w : List ι) (v : BerkovichPoint f) :
    finiteMaximum (fun σ : WordChoice I w => fun v : BerkovichPoint f =>
      negativeValue (powerSectionValue b (N * w.length) (chosenSectionProduct b N I t w σ) v)) v =
      ∑ k : Fin w.length, finiteMaximum (fun j => fun v : BerkovichPoint f =>
        negativeValue (powerSectionValue b N (t (w.get k) j) v)) v := by
  simp only [finiteMaximum_apply, chosenSectionProduct_logValue]
  exact finiteMaximum_independent_sum (fun k : Fin w.length => I (w.get k))
    (fun k j => negativeValue (powerSectionValue b N (t (w.get k) j) v))

variable [Fintype ι]

/-- The actual common-degree monomials have the exact ORIGINAL integral logarithmic sum on ALL X^An. -/
theorem monomialSection_logValue_finiteMaximum (b : LineBundleAtlas L) (N Q : ℕ)
    (a : ι → ℕ) (ha : ∑ i, a i = Q) (I : ι → Type*)
    [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (v : BerkovichPoint f) :
    finiteMaximum (fun σ : WordChoice I (multiIndexWord a) => fun v : BerkovichPoint f =>
      negativeValue (powerSectionValue b (N * Q) (monomialSection b N Q a ha I t σ) v)) v =
      ∑ i, a i • finiteMaximum (fun j => fun v : BerkovichPoint f =>
        negativeValue (powerSectionValue b N (t i j) v)) v := by
  simp only [monomialSection, castDegreeSection_value]
  rw [chosenSectionProduct_logValue_finiteMaximum]
  exact multiIndexWord_sum a (fun i => finiteMaximum (fun j => fun v : BerkovichPoint f =>
    negativeValue (powerSectionValue b N (t i j) v)) v)

/-- ALL original vertex monomials have precisely the original vertex maximum on ALL X^An. -/
theorem vertexSectionFamily_logValue_finiteMaximum (b : LineBundleAtlas L) (N Q : ℕ)
    {V : Type} [Fintype V] [Nonempty V] (a : V → ι → ℕ) (ha : ∀ v, ∑ i, a v i = Q)
    (I : ι → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (v : BerkovichPoint f) :
    finiteMaximum (fun σ => fun v : BerkovichPoint f => negativeValue (powerSectionValue b (N * Q)
      ((vertexSectionFamily b N Q a ha I t).sections σ) v)) v =
      ⨆ u : V, ∑ i, a u i • finiteMaximum (fun j => fun v : BerkovichPoint f =>
        negativeValue (powerSectionValue b N (t i j) v)) v := by
  rw [finiteMaximum_eq_iSup]
  change (⨆ σ : (u : V) × WordChoice I (multiIndexWord (a u)), negativeValue
    (powerSectionValue b (N * Q) (monomialSection b N Q (a σ.1) (ha σ.1) I t σ.2) v)) = _
  rw [iSup_sigma]
  congr 1
  funext u
  change (⨆ σ : WordChoice I (multiIndexWord (a u)), negativeValue
    (powerSectionValue b (N * Q) (monomialSection b N Q (a u) (ha u) I t σ) v)) = _
  rw [← finiteMaximum_eq_iSup (fun σ => fun v : BerkovichPoint f => negativeValue
    (powerSectionValue b (N * Q) (monomialSection b N Q (a u) (ha u) I t σ) v)) v]
  exact monomialSection_logValue_finiteMaximum b N Q (a u) (ha u) I t v

end SGPT.NAPotential.BJ.GfIm.RationalHull
