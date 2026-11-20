import SGPT.NAPotential.GFRationalVertices
import SGPT.NAPotential.GFRationalSectionMonomials

/-! # All ORIGINAL rational simplex vertices use actual products in one original degree
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Convex.CutSimplex
open scoped BigOperators Classical

/-- A family contains actual ORIGINAL sections in a specified ORIGINAL tensor degree. -/
structure ActualSectionFamily {X : Scheme.{0}} (L : X.Modules) (N : ℕ) where
  I : Type
  finite : Fintype I
  nonempty : Nonempty I
  sections : I → bundlePowerGlobalSections L N

instance {X : Scheme.{0}} {L : X.Modules} {N : ℕ} (F : ActualSectionFamily L N) : Fintype F.I :=
  F.finite

instance {X : Scheme.{0}} {L : X.Modules} {N : ℕ} (F : ActualSectionFamily L N) : Nonempty F.I :=
  F.nonempty

theorem finiteMaximum_eq_iSup {ι : Type*} [Fintype ι] [Nonempty ι] {P : Type*}
    (A : ι → P → EReal) (p : P) : finiteMaximum A p = ⨆ i, A i p := by
  rw [finiteMaximum_apply]
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => le_iSup (fun i => A i p) i)
  · exact iSup_le (fun i => Finset.le_sup' (fun i => A i p) (Finset.mem_univ i))

theorem finiteMaximum_scale {ι : Type*} [Fintype ι] [Nonempty ι] {P : Type*}
    (A : ι → P → EReal) (c : ℝ) (hc : 0 ≤ c) (p : P) :
    finiteMaximum (fun i p => (c : EReal) * A i p) p = (c : EReal) * finiteMaximum A p := by
  rw [finiteMaximum_apply, finiteMaximum_apply]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun i => A i p)
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => A i p) (Finset.mem_univ j)) (EReal.coe_nonneg.mpr hc)
  · rw [hmax]
    exact Finset.le_sup' (fun i => (c : EReal) * A i p) hi

/-- Finite ORIGINAL vertex suprema commute with nonnegative scaling, including poles. -/
theorem scale_iSup_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → EReal) (c : ℝ) (hc : 0 ≤ c) :
    (c : EReal) * (⨆ i, A i) = ⨆ i, (c : EReal) * A i := by
  have h := finiteMaximum_scale (fun i (_ : Unit) => A i) c hc ()
  simpa only [finiteMaximum_eq_iSup] using h.symm

theorem scale_finite_sum {ι : Type*} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (A : ι → EReal) :
    (c : EReal) * ∑ i ∈ s, A i = ∑ i ∈ s, (c : EReal) * A i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

/-- Exact original scalar arithmetic, valid even on the common zero loci. -/
theorem normalized_integer_sum {ι : Type*} [Fintype ι] (K Q : ℕ) (hK : 0 < K) (hQ : 0 < Q)
    (a : ι → ℕ) (A : ι → EReal) :
    ((((K * Q : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (∑ i, a i • A i) =
      ∑ i, (((a i : ℝ) / Q : ℝ) : EReal) * ((((K : ℝ)⁻¹ : ℝ) : EReal) * A i) := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [scale_finite_sum _ _ (by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EReal.nsmul_eq_mul, ← mul_assoc, ← EReal.coe_natCast, ← EReal.coe_mul]
  have heq : (((K * Q : ℕ) : ℝ)⁻¹ * (a i : ℝ)) = ((a i : ℝ) / Q) * (K : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [heq, EReal.coe_mul, mul_assoc]

variable {X : Scheme.{0}} {L : X.Modules} {ι : Type} [Fintype ι]

/-- The literal union of all monomial choices from ALL original vertices. -/
def vertexSectionFamily (b : LineBundleAtlas L) (N Q : ℕ) {V : Type} [Fintype V] [Nonempty V]
    (a : V → ι → ℕ) (ha : ∀ v, ∑ i, a v i = Q) (I : ι → Type)
    [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) : ActualSectionFamily L (N * Q) where
  I := (v : V) × WordChoice I (multiIndexWord (a v))
  finite := inferInstance
  nonempty := ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
  sections σ := monomialSection b N Q (a σ.1) (ha σ.1) I t σ.2

variable {f : X ⟶ Spec (.of ℂ)} [IsProper f]

include f in
/-- The actual union of all original vertex product families consists of nonzero original sections. -/
theorem vertexSectionFamily_ne_zero [IsIntegral X] (b : LineBundleAtlas L) (N Q : ℕ)
    {V : Type} [Fintype V] [Nonempty V] (a : V → ι → ℕ) (ha : ∀ v, ∑ i, a v i = Q)
    (I : ι → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (ht : ∀ i j, t i j ≠ 0)
    (σ : (vertexSectionFamily b N Q a ha I t).I) :
    (vertexSectionFamily b N Q a ha I t).sections σ ≠ 0 :=
  monomialSection_ne_zero (f := f) b N Q (a σ.1) (ha σ.1) I t ht σ.2

variable (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  (H : SchemeLineBundleMetric f n E L)

omit [IsProper f] in
/-- The genuine common-degree section maximum is the maximum of ALL original integral vertex sums. -/
theorem vertexSectionFamily_finiteMaximum (b : LineBundleAtlas L) (N Q : ℕ)
    {V : Type} [Fintype V] [Nonempty V] (a : V → ι → ℕ) (ha : ∀ v, ∑ i, a v i = Q)
    (I : ι → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : ι) → I i → bundlePowerGlobalSections L N) (p : SchemeComplexPoint f) :
    finiteMaximum (fun σ => H.sectionLogNormSq b (N * Q)
      ((vertexSectionFamily b N Q a ha I t).sections σ)) p =
      ⨆ v : V, ∑ i, a v i • finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p := by
  rw [finiteMaximum_eq_iSup]
  change (⨆ σ : (v : V) × WordChoice I (multiIndexWord (a v)),
      H.sectionLogNormSq b (N * Q) (monomialSection b N Q (a σ.1) (ha σ.1) I t σ.2) p) = _
  rw [iSup_sigma]
  congr 1
  funext v
  rw [← finiteMaximum_eq_iSup]
  change finiteMaximum (fun σ : WordChoice I (multiIndexWord (a v)) =>
    H.sectionLogNormSq b (N * Q) (monomialSection b N Q (a v) (ha v) I t σ)) p = _
  exact congrFun (monomialSection_finiteMaximum n E H b N Q (a v) (ha v) I t) p

end SGPT.NAPotential.BJ.GfIm.RationalHull
