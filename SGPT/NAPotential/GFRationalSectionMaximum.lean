import SGPT.NAPotential.GFRationalSectionProducts
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi

/-! # Actual common-degree products manufacture the original finite section maxima
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators
open scoped Classical

/-- A finite maximum of the ORIGINAL functions. -/
def finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] {P : Type*}
    (A : ι → P → EReal) : P → EReal :=
  Finset.univ.sup' Finset.univ_nonempty A

theorem finiteMaximum_apply {ι : Type*} [Fintype ι] [Nonempty ι] {P : Type*}
    (A : ι → P → EReal) (p : P) :
    finiteMaximum A p = Finset.univ.sup' Finset.univ_nonempty (fun i => A i p) := by
  simp [finiteMaximum, Finset.sup'_apply]

/-- Independent actual finite maximizers manufacture the maximum of all genuine products. -/
theorem finiteMaximum_independent_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : κ → Type*) [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (φ : (k : κ) → I k → EReal) :
    Finset.univ.sup' Finset.univ_nonempty (fun σ : (k : κ) → I k => ∑ k, φ k (σ k)) =
      ∑ k, Finset.univ.sup' Finset.univ_nonempty (φ k) := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro σ _
    exact Finset.sum_le_sum fun k _ => Finset.le_sup' (φ k) (Finset.mem_univ (σ k))
  · choose σ hmem hmax using fun k =>
      Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (φ k)
    have heq : (∑ k, Finset.univ.sup' Finset.univ_nonempty (φ k)) = ∑ k, φ k (σ k) :=
      Finset.sum_congr rfl fun k _ => hmax k
    rw [heq]
    exact Finset.le_sup' (fun σ : (k : κ) → I k => ∑ k, φ k (σ k)) (Finset.mem_univ σ)

variable {X : Scheme.{0}} {L : X.Modules} {ι : Type*}

/-- Every occurrence in the original word independently chooses an ORIGINAL generating section. -/
abbrev WordChoice (I : ι → Type*) (w : List ι) := (k : Fin w.length) → I (w.get k)

/-- The ACTUAL product of the chosen original sections, in degree N times the original word length. -/
def chosenSectionProduct (a : LineBundleAtlas L) (N : ℕ) (I : ι → Type*)
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (w : List ι) (σ : WordChoice I w) :
    bundlePowerGlobalSections L (N * w.length) :=
  castDegreeSection (by simp) (sectionWordProduct a N (List.ofFn (fun k => t (w.get k) (σ k))))

theorem castDegreeSection_ne_zero {r s : ℕ} (h : r = s)
    (t : bundlePowerGlobalSections L r) (ht : t ≠ 0) : castDegreeSection h t ≠ 0 := by
  cases h
  exact ht

variable {f : X ⟶ Spec (.of ℂ)} [IsProper f]

include f in
/-- These are actual original nonzero products, including repeated choices of one generator. -/
theorem chosenSectionProduct_ne_zero [IsIntegral X] (a : LineBundleAtlas L) (N : ℕ)
    (I : ι → Type*) (t : (i : ι) → I i → bundlePowerGlobalSections L N)
    (ht : ∀ i j, t i j ≠ 0) (w : List ι) (σ : WordChoice I w) :
    chosenSectionProduct a N I t w σ ≠ 0 := by
  have h := sectionWordProduct_ne_zero (f := f) a N
    (List.ofFn (fun k => t (w.get k) (σ k))) (by
      intro u hu
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
      exact ht _ _)
  exact castDegreeSection_ne_zero _ _ h

variable (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  (H : SchemeLineBundleMetric f n E L)

omit [IsProper f] in
/-- The literal product has the sum of the ORIGINAL whole metric logarithms, at every point. -/
theorem chosenSectionProduct_logNormSq (a : LineBundleAtlas L) (N : ℕ) (I : ι → Type*)
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (w : List ι) (σ : WordChoice I w) :
    H.sectionLogNormSq a (N * w.length) (chosenSectionProduct a N I t w σ) =
      fun p => ∑ k : Fin w.length, H.sectionLogNormSq a N (t (w.get k) (σ k)) p := by
  rw [chosenSectionProduct, castDegreeSection_logNormSq, sectionWordProduct_logNormSq]
  funext p
  simp only [List.map_ofFn, List.sum_ofFn]
  rfl

omit [IsProper f] in
/-- The maximum of the ACTUAL section products is the sum of the original node maxima. -/
theorem chosenSectionProduct_finiteMaximum (a : LineBundleAtlas L) (N : ℕ)
    (I : ι → Type*) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (w : List ι) :
    finiteMaximum (fun σ : WordChoice I w =>
      H.sectionLogNormSq a (N * w.length) (chosenSectionProduct a N I t w σ)) =
    fun p => ∑ k : Fin w.length, finiteMaximum (fun j => H.sectionLogNormSq a N (t (w.get k) j)) p := by
  funext p
  simp only [finiteMaximum_apply, chosenSectionProduct_logNormSq]
  exact finiteMaximum_independent_sum (fun k : Fin w.length => I (w.get k))
    (fun k j => H.sectionLogNormSq a N (t (w.get k) j) p)

end SGPT.NAPotential.BJ.GfIm.RationalHull
