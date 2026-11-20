import SGPT.GAGA.H0SSchemeSections
import SGPT.NAPotential.GAGAMult2Faithful

/-!
# Polynomial equations of `X(ℂ) ⊆ ℙᴺ` in the affine charts


`Iᵢ = ker(ℂ[t₁, …, t_N] → Γ(X, Uᵢ))` (`affinePresentation`) is the ideal of `X ∩ D₊(xᵢ)` in the
affine space `D₊(xᵢ)`.  By Hilbert's basis theorem it has finitely many generators; padding with
zeros we get `chartEquations f E i j`, `j < q`.

* `eval_eq_zero_of_mem_ker`: every element of `Iᵢ` vanishes on `X(ℂ) ∩ Uᵢ` (in the affine
  coordinates).
* `exists_point_of_eval_eq_zero`: a point `y ∈ ℂᴺ` where `Iᵢ` vanishes is a complex point of
  `Uᵢ`: the evaluation at `y` factors through `Γ(X, Uᵢ)` (the presentation is surjective), and
  its kernel, a maximal ideal, is a complex point (lane GAGAMULT2's
  `exists_schemeComplexPoint_fromSpec`), at which every regular function takes the value given
  by the factored evaluation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0S

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0sEqTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0sEqCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0sEqManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-! ### Generators of the ideals of the affine pieces -/

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem exists_chartGenerators (i : Fin (E.ambientDimension + 1)) :
    ∃ (m : ℕ) (s : Fin m → MvPolynomial (Fin E.ambientDimension) ℂ),
      Ideal.span (range s) = RingHom.ker (affinePresentation f E i) :=
  Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian _)

/-- The number of generators of `Iᵢ`. -/
def chartGenCount (i : Fin (E.ambientDimension + 1)) : ℕ :=
  (exists_chartGenerators f E i).choose

/-- The generators of `Iᵢ`. -/
def chartGen (i : Fin (E.ambientDimension + 1)) :
    Fin (chartGenCount f E i) → MvPolynomial (Fin E.ambientDimension) ℂ :=
  (exists_chartGenerators f E i).choose_spec.choose

theorem span_chartGen (i : Fin (E.ambientDimension + 1)) :
    Ideal.span (range (chartGen f E i)) = RingHom.ker (affinePresentation f E i) :=
  (exists_chartGenerators f E i).choose_spec.choose_spec

/-- A common number of equations for all charts. -/
def chartEqCount : ℕ := Finset.univ.sup (chartGenCount f E)

/-- The equations of `X ∩ D₊(xᵢ)`: the generators of `Iᵢ`, padded with zeros. -/
def chartEquations (i : Fin (E.ambientDimension + 1)) (j : Fin (chartEqCount f E)) :
    MvPolynomial (Fin E.ambientDimension) ℂ :=
  if h : (j : ℕ) < chartGenCount f E i then chartGen f E i ⟨j, h⟩ else 0

theorem chartEquations_mem (i : Fin (E.ambientDimension + 1)) (j : Fin (chartEqCount f E)) :
    chartEquations f E i j ∈ RingHom.ker (affinePresentation f E i) := by
  unfold chartEquations
  split_ifs with h
  · rw [← span_chartGen]; exact Ideal.subset_span ⟨_, rfl⟩
  · exact zero_mem _

/-- An ideal containing the equations of the chart `i` contains `Iᵢ`. -/
theorem ker_le_of_chartEquations (i : Fin (E.ambientDimension + 1))
    {J : Ideal (MvPolynomial (Fin E.ambientDimension) ℂ)}
    (hJ : ∀ j, chartEquations f E i j ∈ J) : RingHom.ker (affinePresentation f E i) ≤ J := by
  rw [← span_chartGen, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hk : (k : ℕ) < chartEqCount f E :=
    lt_of_lt_of_le k.2 (Finset.le_sup (f := chartGenCount f E) (Finset.mem_univ i))
  have := hJ ⟨k, hk⟩
  unfold chartEquations at this
  rwa [dif_pos k.2] at this

/-! ### Vanishing and zero set -/

theorem schemeOpenRegularFunction_zero' (U : X.Opens) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) : schemeOpenRegularFunction f n E U 0 p = 0 := by
  rw [schemeOpenRegularFunction_apply f n E U 0 p hp, map_zero, map_zero, map_zero]

/-- Elements of `Iᵢ` vanish at the affine coordinates of the points of `Uᵢ(ℂ)`. -/
theorem eval_eq_zero_of_mem_ker (i : Fin (E.ambientDimension + 1))
    {P : MvPolynomial (Fin E.ambientDimension) ℂ} (hP : P ∈ RingHom.ker (affinePresentation f E i))
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    MvPolynomial.eval (fun a => affineCoords f E n i p a) P = 0 := by
  rw [← schemeOpenRegularFunction_affinePresentation f E n i P p hp, RingHom.mem_ker.mp hP,
    schemeOpenRegularFunction_zero' f E n _ p hp]

/-- The points of `X(ℂ)` in `D₊(xᵢ) ≅ ℂᴺ` are the points `y` with `affinePoint i y` in the image. -/
theorem affineCoords_of_mem_range (i : Fin (E.ambientDimension + 1)) {y : ComplexModel E.ambientDimension}
    {p : SchemeComplexPoint f} (hp : projectivePoint f E n p = affinePoint i y) :
    schemeComplexPointImage f p ∈ coordOpen E i ∧ affineCoords f E n i p = y := by
  have hi : schemeComplexPointImage f p ∈ coordOpen E i := by
    rw [← projectivePoint_mem_source_iff f E n i, hp]; exact affinePoint_mem_source i y
  refine ⟨hi, ?_⟩
  rw [← affineChart_projectivePoint f E n i hi, hp, affineChart_affinePoint]

/-- A point of `ℂᴺ` where `Iᵢ` vanishes is (the affine coordinates of) a complex point of `Uᵢ`. -/
theorem exists_point_of_eval_eq_zero (i : Fin (E.ambientDimension + 1))
    (y : ComplexModel E.ambientDimension)
    (hy : ∀ P ∈ RingHom.ker (affinePresentation f E i), MvPolynomial.eval (fun a => y a) P = 0) :
    ∃ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ coordOpen E i ∧
      affineCoords f E n i p = y := by
  have := E.locallyOfFiniteType
  set π := affinePresentation f E i
  have hsurj := affinePresentation_surjective f E i
  set χ : Γ(X, coordOpen E i) →+* ℂ := RingHom.liftOfSurjective π hsurj
    ⟨MvPolynomial.eval (fun a => y a), fun P hP => hy P hP⟩ with hχdef
  have hχ : ∀ P, χ (π P) = MvPolynomial.eval (fun a => y a) P := fun P =>
    RingHom.liftOfSurjective_comp_apply π hsurj _ P
  have hχc : ∀ b : ℂ, χ (π (MvPolynomial.C b)) = b := by
    intro b
    rw [hχ, MvPolynomial.eval_C]
  have hχs : Function.Surjective χ := fun b => ⟨_, hχc b⟩
  have hU := isAffineOpen_coordOpen E i
  set P := RingHom.ker χ
  have hPmax : P.IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχs
  obtain ⟨p, hp⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P hPmax
  have hpU : schemeComplexPointImage f p ∈ coordOpen E i := by
    rw [hp]; exact SGPT.NAPotential.Berkovich.fromSpec_mem hU _
  -- values at `p` are given by `χ`
  have hval : ∀ r, schemeOpenRegularFunction f n E (coordOpen E i) r p = χ r := by
    intro r
    set r' := r - π (MvPolynomial.C (χ r))
    have hr' : r' ∈ P := by
      change χ (r - π (MvPolynomial.C (χ r))) = 0
      rw [map_sub, hχc, sub_self]
    have hnot : schemeComplexPointImage f p ∉ X.basicOpen r' := by
      intro hb
      have hb' : (⟨P, hPmax.isPrime⟩ : PrimeSpectrum Γ(X, coordOpen E i)) ∈
          hU.fromSpec ⁻¹ᵁ X.basicOpen r' := by
        change hU.fromSpec ⟨P, hPmax.isPrime⟩ ∈ X.basicOpen r'
        rw [← hp]; exact hb
      rw [hU.fromSpec_preimage_basicOpen r'] at hb'
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hb' hr'
    have h0 : schemeOpenRegularFunction f n E (coordOpen E i) r' p = 0 := by
      by_contra h
      exact hnot ((schemeOpenRegularFunction_ne_zero_iff f E n _ r' p hpU).mp h)
    have hr : r = r' + π (MvPolynomial.C (χ r)) := by rw [sub_add_cancel]
    rw [hr, schemeOpenRegularFunction_add f n E _ _ _ hpU]
    beta_reduce
    rw [h0, zero_add, schemeOpenRegularFunction_affinePresentation f E n i _ p hpU,
      MvPolynomial.eval_C, ← hr]
  refine ⟨p, hpU, ?_⟩
  ext a
  change schemeOpenRegularFunction f n E (coordOpen E i) (ratio E i (i.succAbove a)) p = y a
  rw [hval, ← affinePresentation_X, hχ, MvPolynomial.eval_X]

end SGPT.GAGA.H0S
