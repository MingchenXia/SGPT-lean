import SGPT.NAPotential.GFRationalSectionMaximum

/-! # Literal repeated-generator monomials in the original common tensor degree
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

/-- Repeat each ORIGINAL node as many times as its actual integer exponent. -/
def multiIndexWord {ι : Type*} [Fintype ι] (a : ι → ℕ) : List ι :=
  Finset.univ.toList.flatMap (fun i => List.replicate (a i) i)

theorem multiIndexWord_length {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    (multiIndexWord a).length = ∑ i, a i := by
  simp [multiIndexWord, List.length_flatMap]

/-- Repetition yields the actual integral weighted sum, including original polar values. -/
theorem multiIndexWord_sum {ι : Type*} [Fintype ι] (a : ι → ℕ) (A : ι → EReal) :
    ∑ k : Fin (multiIndexWord a).length, A ((multiIndexWord a).get k) = ∑ i, a i • A i := by
  have hlist (l : List ι) :
      ((l.flatMap (fun i => List.replicate (a i) i)).map A).sum =
        (l.map (fun i => a i • A i)).sum := by
    induction l with
    | nil => simp
    | cons i l ih => simp [ih]
  calc
    _ = ((multiIndexWord a).map A).sum := by
      rw [← List.sum_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map (multiIndexWord a) A
    _ = ∑ i, a i • A i := by
      rw [multiIndexWord, hlist]
      exact Finset.sum_map_toList _ _

variable {X : Scheme.{0}} {L : X.Modules} {ι : Type*} [Fintype ι]

/-- The original multi-index manufactures the ACTUAL section in the prescribed common degree. -/
def monomialSection (b : LineBundleAtlas L) (N Q : ℕ) (a : ι → ℕ) (ha : ∑ i, a i = Q)
    (I : ι → Type*) (t : (i : ι) → I i → bundlePowerGlobalSections L N)
    (σ : WordChoice I (multiIndexWord a)) : bundlePowerGlobalSections L (N * Q) :=
  castDegreeSection (congrArg (N * ·) ((multiIndexWord_length a).trans ha))
    (chosenSectionProduct b N I t (multiIndexWord a) σ)

variable {f : X ⟶ Spec (.of ℂ)} [IsProper f]

include f in
/-- All actual monomials are nonzero, derived from the ORIGINAL section nonvanishing. -/
theorem monomialSection_ne_zero [IsIntegral X] (b : LineBundleAtlas L) (N Q : ℕ)
    (a : ι → ℕ) (ha : ∑ i, a i = Q) (I : ι → Type*)
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (ht : ∀ i j, t i j ≠ 0)
    (σ : WordChoice I (multiIndexWord a)) : monomialSection b N Q a ha I t σ ≠ 0 :=
  castDegreeSection_ne_zero _ _ (chosenSectionProduct_ne_zero (f := f) b N I t ht _ σ)

variable (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  (H : SchemeLineBundleMetric f n E L)

omit [IsProper f] in
/-- The ACTUAL common-degree section family has EXACTLY the original integral weighted node maximum. -/
theorem monomialSection_finiteMaximum (b : LineBundleAtlas L) (N Q : ℕ)
    (a : ι → ℕ) (ha : ∑ i, a i = Q) (I : ι → Type*)
    [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) :
    finiteMaximum (fun σ : WordChoice I (multiIndexWord a) =>
      H.sectionLogNormSq b (N * Q) (monomialSection b N Q a ha I t σ)) =
      fun p => ∑ i, a i • finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p := by
  simp only [monomialSection, castDegreeSection_logNormSq]
  rw [chosenSectionProduct_finiteMaximum]
  funext p
  exact multiIndexWord_sum a (fun i => finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p)

end SGPT.NAPotential.BJ.GfIm.RationalHull
