import SGPT.PSH.OriginalValuativeStalkCriterion
import SGPT.PSH.CompactPrimeOver
import SGPT.PSH.Manifold

/-!
# `thm:valuativemulti` in dimension zero

Source: `chapter_pshfunctions.tex`, `thm:valuativemulti`: for `φ ∈ PSH(X)`, `x ∈ X` and a nonzero
germ `f ∈ 𝒪_{X,x}`, `f ∈ 𝓘(φ)_x` iff there is `ε > 0` with
`ord_E(f) ≥ (1 + ε) ν(φ, E) - A_X(E)` for every prime divisor `E` over `X` whose centre contains
`x`.

The positive-dimensional case (`n = m + 1`) is `SGPT.PSH.ActualGermValuative` (both
implications on the actual colimit stalk).  This file treats complex dimension `0`, where the book's
statement is degenerate but true:

* a psh function on a zero-dimensional manifold is finite at every point
  (`ne_bot_of_manifoldPSH_dim_zero`; the book's `PSH(X)` excludes functions identically `-∞` on a
  connected component, and in dimension `0` every point is a component);
* hence the constant `1` is multiplier-integrable at every point, and the actual multiplier stalk
  ideal `𝓘(φ)_x` is the whole stalk (`actualWholeSheafStalkIdeal_multiplierIdeal_eq_top_dim_zero`):
  condition (1) holds for every germ;
* there is no prime divisor over a zero-dimensional manifold (a prime divisor is a connected smooth
  hypersurface, of dimension `-1` here): `isEmpty_primePresentation_dim_zero`, so condition (2)
  holds vacuously.

Together: `valuativemulti_dim_zero`.  Blueprint: `claude-r-iso-a.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.RIsoAValuativeDimZero

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X]

instance : Subsingleton (ComplexModel 0) where
  allEq a b := by
    ext i
    exact i.elim0

omit [IsComplexManifold 0 X] in
/-- In dimension zero a psh function (`def:pshmfd`) is finite at every point. -/
theorem ne_bot_of_manifoldPSH_dim_zero {φ : X → EReal} (hφ : ManifoldPSH (n := 0) φ) (x : X) :
    φ x ≠ ⊥ ∧ φ x ≠ ⊤ := by
  obtain ⟨e, hxe, V, _hV, _hVc, _hVt, hxV, hpsh⟩ := hφ x
  have hval : chartFunction φ e (e.val x) = φ x := by
    simp only [chartFunction, e.val.left_inv hxe]
  obtain ⟨z, _hzV, hz⟩ := hpsh.nontrivial
  have hz' : z = e.val x := Subsingleton.elim _ _
  subst hz'
  refine ⟨hval ▸ hz, ?_⟩
  rw [← hval]
  exact hpsh.disc.ne_top _ hxV

omit [IsComplexManifold 0 X] in
/-- In dimension zero the constant `1` lies in the multiplier ideal `𝓘(φ)` at every point. -/
theorem one_mem_multiplierIdeal_dim_zero {φ : X → EReal} (hφ : ManifoldPSH (n := 0) φ) (x : X) :
    (multiplierIdeal (n := 0) 1 φ).mem x (fun _ => (1 : ℂ)) := by
  have hfin := (ne_bot_of_manifoldPSH_dim_zero hφ x).1
  set e := (complexChartAt (n := 0) x).val with he
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨holomorphicAt_const (n := 0) 1, one_pos, univ, isOpen_univ, mem_univ _,
    differentiableOn_const _, (measurable_of_countable _).aemeasurable, ?_⟩
  have hdens : ∀ y : ComplexModel 0,
      multiplierDensity (chartFunction φ (complexChartAt (n := 0) x)) 1
        (fun _ => (1 : ℂ)) y = multiplierWeight 1 (φ x) := by
    intro y
    have hy : y = e x := Subsingleton.elim _ _
    subst hy
    simp only [multiplierDensity, chartFunction, ← he, e.left_inv hxe, norm_one, one_pow,
      ENNReal.ofReal_one, one_mul]
  simp_rw [hdens, Measure.restrict_univ, lintegral_const]
  refine ENNReal.mul_lt_top ?_ (isCompact_univ.measure_lt_top)
  simp only [multiplierWeight, EReal.coe_one, one_mul]
  rw [EReal.exp_lt_top_iff]
  exact lt_top_iff_ne_top.mpr (by rwa [ne_eq, EReal.neg_eq_top_iff])

/-- The germ of the constant function `1` is the unit of the actual structure-sheaf stalk. -/
theorem actualOriginalFunctionGerm_one {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (y : M) :
    actualOriginalFunctionGerm y (fun _ => (1 : ℂ)) (holomorphicAt_const (n := n) 1) = 1 := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [actualOriginalFunctionGerm_chart, map_one]
  rfl

/-- In dimension zero the actual multiplier stalk ideal of a psh function is the whole stalk. -/
theorem actualWholeSheafStalkIdeal_multiplierIdeal_eq_top_dim_zero {φ : X → EReal}
    (hφ : ManifoldPSH (n := 0) φ) (x : X) :
    actualWholeSheafStalkIdeal (multiplierIdeal (n := 0) 1 φ) x = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  exact ⟨fun _ => 1, holomorphicAt_const (n := 0) 1, one_mem_multiplierIdeal_dim_zero hφ x,
    (actualOriginalFunctionGerm_one x).symm⟩

/-- There is no prime divisor over a zero-dimensional manifold: a prime divisor is a connected
smooth hypersurface of a modification, and hypersurfaces have dimension `n - 1`. -/
theorem isEmpty_primePresentation_dim_zero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] :
    IsEmpty (CompactPrimeOver.PrimePresentation 0 Y) :=
  ⟨fun p => (Nat.lt_irrefl 0) p.dimension_pos⟩

/-- **Source `thm:valuativemulti`, complex dimension `0`.** Let `X` be a zero-dimensional complex
manifold, `φ ∈ PSH(X)`, `x ∈ X`.  Every germ `g` of the actual structure-sheaf stalk `𝒪_{X,x}` lies
in the actual multiplier stalk `𝓘(φ)_x` (condition (1)), and there is no prime divisor over `X`, so
the valuative condition (2) holds vacuously for every germ and every `ε > 0`; in particular
(1) ⟺ (2).  The finite log-resolution test is vacuous as well: the resolved polar divisor of a
log resolution of `X` has no components. -/
theorem valuativemulti_dim_zero {φ : X → EReal} (hφ : ManifoldPSH (n := 0) φ) (x : X)
    (g : actualComplexStructureStalk (n := 0) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := 0) 1 φ) x ∧
      IsEmpty (CompactPrimeOver.PrimePresentation 0 X) := by
  refine ⟨?_, isEmpty_primePresentation_dim_zero⟩
  rw [actualWholeSheafStalkIdeal_multiplierIdeal_eq_top_dim_zero hφ x]
  exact Submodule.mem_top

end SGPT.PSH.RIsoAValuativeDimZero
