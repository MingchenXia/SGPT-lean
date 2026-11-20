import SGPT.Foundations.Analysis.Pending.AdaptedProjectionGerm

set_option autoImplicit false

/-!
# Demailly's perturbed decomposable basis at a point of a subvariety

This is the geometric input of CADG III.2.6 in Demailly's own shape.  His proof
(`\source{demailly-cadg:III.2.6}`, `agbook.tex:8704`) reads:

> If we write the monomials `dz_K ∧ d\bar z_L` in terms of an arbitrary basis of
> `Λ^{p,p}T^⋆Ω` consisting of decomposable forms `β_s = iβ_{s,1}∧\bar β_{s,1}∧…`,
> we see that the measures `T_{I,J}·τ` are linear combinations of the positive
> measures `T ∧ β_s`.  It is thus sufficient to prove that all `T ∧ β_s` have
> finite mass near `A_sing`. … Take new coordinates `w` such that
> `w_j = β_{s,j}(z − z_0)`, `1 ≤ j ≤ p`.  **After a slight perturbation of the
> `β_{s,j}`, we may assume that each projection `π_s` defines a ramified covering
> of `A ∩ (Δ'×Δ'')`, and that `(β_s)` remains a basis of `Λ^{p,p}T^⋆Ω`.**

The two clauses of that last sentence are the two clauses of
`exists_decomposableBasisSheetBound` below: `SpansPlucker` is "`(β_s)` remains a
basis" (weakened to the separation of points that the estimate actually uses),
and the maps/fibre clauses are "each `π_s` defines a ramified covering", in the
almost-everywhere form that `Pending.MultiplicityAreaBound` consumes.

WHAT THIS BUYS over the fixed-chart formulation it replaces.  The coordinate
projections `π_I` of one chart are a spanning family
(`spansPlucker_subsetProjection` below, where the Plücker matrix is the
identity), so the old route is the special case in which no perturbation is
performed — and it is precisely the case Demailly does NOT use, because a fixed
projection need not be a ramified covering of the germ and the classical
theorems do not bound its local degree.  Perturbing is allowed exactly because
spanning is an OPEN condition, while being adapted to the germ is a DENSE one;
so each `β_s` may be moved on its own, and no simultaneously generic linear
change of `ℂⁿ` is ever needed.

Consequently this interface asks only for ramified coverings in ADAPTED
coordinates, one germ at a time — the situation of Demailly CADG II.3.8/II.3.19
and of this project's own
`Pending.GermParametrizationData.SetsData.ncard_fibre` — and not for the finite
local degree of a projection of a FIXED chart, which had no source anchor.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Matrix

namespace SGPT.Foundations.Analysis.Pending.DecomposableBasisSheetBound

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.SubsetProjection
  SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian
  SGPT.Foundations.Analysis.Pending.PluckerSpanningBound

section Coordinate

variable {k n : ℕ}

/-- The `(I, J)` entry block of the Plücker matrix of the coordinate projections:
`1` on the diagonal of `I.emb` against `J.emb`, `0` off it. -/
theorem rectMatrix_subsetProjection_submatrix (I J : CardSubset k n) (i j : Fin k) :
    ((rectMatrix (subsetProjection I)).submatrix id J.emb) i j =
      if I.emb i = J.emb j then 1 else 0 := by
  simp [Matrix.submatrix_apply, rectMatrix_apply, coordinateVector]

/-- **The Plücker matrix of the coordinate projections is the identity.** -/
theorem plucker_subsetProjection (I J : CardSubset k n) :
    plucker (rectMatrix (subsetProjection I)) J = if I = J then 1 else 0 := by
  classical
  rw [plucker]
  by_cases h : I = J
  · subst h
    have hone : (rectMatrix (subsetProjection I)).submatrix id I.emb = 1 := by
      ext i j
      rw [rectMatrix_subsetProjection_submatrix, Matrix.one_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp only [if_neg hij]
        exact if_neg fun hh => hij (I.injective_emb hh)
    rw [hone, Matrix.det_one, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨a, haJ, haI⟩ : ∃ a, a ∈ J.1 ∧ a ∉ I.1 := by
      by_contra hc
      push Not at hc
      exact h (Subtype.ext
        (Finset.eq_of_subset_of_card_le hc (le_of_eq (by rw [I.2, J.2]))).symm)
    obtain ⟨j₀, -, hj₀⟩ : ∃ j₀ ∈ Finset.univ, J.emb j₀ = a := by
      rw [← J.image_emb] at haJ
      simpa using Finset.mem_image.1 haJ
    refine Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_
    rw [rectMatrix_subsetProjection_submatrix]
    refine if_neg fun hh => haI ?_
    have hai : a = I.emb i := by rw [← hj₀, hh]
    rw [hai, ← I.image_emb]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- **The coordinate projections of a chart are a spanning family.**  This is the
degenerate choice in Demailly's step — no perturbation at all — and it recovers
`Pending.CauchyBinet` with constant `1`.  It is recorded here to show that
`SpansPlucker` is satisfiable, and that the perturbation in
`exists_decomposableBasisSheetBound` starts from a family that already spans. -/
theorem spansPlucker_subsetProjection :
    SpansPlucker (fun I : CardSubset k n => rectMatrix (subsetProjection I)) := by
  classical
  intro ξ hξ
  funext I
  have h := hξ I
  have hsum : ∑ J : CardSubset k n,
      plucker (rectMatrix (subsetProjection I)) J * ξ J = ξ I := by
    simp [plucker_subsetProjection]
  rw [hsum] at h
  exact h

end Coordinate

section Interface

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly CADG III.2.6, the perturbed decomposable basis.**  Every point `x`
of an irreducible analytic subvariety `V` of dimension `k` admits

* a finite family `B` of `ℂ`-linear maps `ℂⁿ → ℂ^k` — the decomposable
  `(k,k)`-forms `β_s = iβ_{s,1}∧\bar β_{s,1}∧…`, read through their rows — whose
  Plücker functionals separate points of `Λ^k ℂⁿ` (`(β_s)` is still a basis);
* a neighbourhood `U` of `x` inside the source of its preferred chart, and a
  measurable `Δ ⊆ ℂ^k` of finite volume;
* an integer `N`,

such that every `B_s` maps the part of `V` in `U` into `Δ`, with at most `N`
points over almost every value.

This is the ONLY input of `Pending.LocalFlatVolumeBound.exists_localFlatVolumeBound`,
hence of the Lelong local bound at singular points.  Both clauses are Demailly's
own sentence; see the module docstring for the quotation.

It is no longer a bare `sorry`.  It is now ASSEMBLED from Demailly's two clauses
taken separately:

* the OPEN clause, `Pending.PluckerSpanningOpen.exists_dist_lt_spansPlucker`
  (sorry-free): a spanning family has a radius within which every family still
  spans, so each `β_s` may be moved on its own;
* the DENSE clause, `Pending.AdaptedProjectionGerm.exists_adaptedProjection`
  (the single named classical input that is left): ONE direction, prescribed up
  to `δ`, that is a ramified covering of the germ of `V` at `x`.

The assembly below starts from the coordinate projections, which span by
`spansPlucker_subsetProjection`, perturbs each of them inside the radius the
first clause provides, and then intersects the neighbourhoods, unites the
targets and maximizes the sheet numbers over the `binom n k` members.

Why the perturbation is the whole point.  `spansPlucker_subsetProjection` above
shows that the `binom n k` coordinate projections of the chart already span, so
taking `B` to be them would satisfy the first clause with no work; the second
clause is then the finite local degree of a FIXED projection of a FIXED chart,
which is false for every `y` (the fibre through `x` may be positive-dimensional)
and, in its almost-everywhere form, has no source anchor in this blueprint.
Demailly instead moves each `β_{s,j}` slightly, which costs nothing because
spanning is open, and buys adaptedness to the germ, which is dense.  What the
second clause then asks for is a ramified covering of ONE germ in coordinates
ADAPTED to it, i.e. Demailly CADG II.3.8/II.3.19, whose exact fibre count off the
discriminant is already in this project
(`Pending.GermParametrizationData.SetsData.ncard_fibre`, and its
almost-everywhere form `Pending.ParametrizationFibreBound.exists_fibreBound`).
The openness argument that keeps the perturbed family spanning is now proved
(`Pending.PluckerSpanningOpen`); the one unbuilt piece is the producer of that
data for the germ of a `ClosedIrreducibleAnalyticSubvariety`.

Checked against the degenerate cases.  For `k = 0` the family may be taken to be
the single zero map: `CardSubset 0 n` is a singleton and `plucker` of the empty
matrix is `1`, so `SpansPlucker` holds, and the fibre clause says that `U ∩ V` is
finite, which a small enough `U` gives since `V` is then discrete.  For `n = 0`
the same applies.  The almost-everywhere quantifier is not cosmetic: on
`V = (t,s) ↦ (t, ts, s)` the fibre of the first two coordinates over `0` is a
line, so no bound can hold for every `y`. -/
theorem exists_decomposableBasisSheetBound (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ V.carrier) :
    ∃ (m : ℕ) (B : Fin m → (ComplexModel n →L[ℂ] ComplexModel V.dim))
      (U : Set M) (Δ : Set (ComplexModel V.dim)) (N : ℕ),
      SpansPlucker (fun s => rectMatrix (B s)) ∧
        IsOpen U ∧ x ∈ U ∧ U ⊆ (complexChartAt (n := n) x).val.source ∧
        MeasurableSet Δ ∧ volume Δ ≠ ⊤ ∧
        (∀ s : Fin m, ∀ z ∈ U ∩ V.carrier,
          B s ((complexChartAt (n := n) x).val z) ∈ Δ) ∧
        (∀ s : Fin m, ∀ᵐ y : ComplexModel V.dim,
          {z | z ∈ U ∩ V.carrier ∧ B s ((complexChartAt (n := n) x).val z) = y}.encard
            ≤ (N : ℕ∞)) := by
  classical
  obtain ⟨δ, hδ, hstable⟩ :=
    PluckerSpanningOpen.exists_dist_lt_spansPlucker
      (fun I : CardSubset V.dim n => subsetProjection I) spansPlucker_subsetProjection
  choose B U Δ N hclose hUopen hxU hUsrc hΔmeas hΔtop hmaps hfib using
    fun I : CardSubset V.dim n =>
      AdaptedProjectionGerm.exists_adaptedProjection V hx (subsetProjection I) hδ
  set e : Fin (Fintype.card (CardSubset V.dim n)) ≃ CardSubset V.dim n :=
    (Fintype.equivFin (CardSubset V.dim n)).symm with he
  refine ⟨Fintype.card (CardSubset V.dim n), fun i => B (e i),
    (complexChartAt (n := n) x).val.source ∩ ⋂ I, U I, ⋃ I, Δ I,
    Finset.univ.sup N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AdaptedProjectionGerm.spansPlucker_comp
      (hstable B fun I => hclose I) e.surjective
  · exact ((complexChartAt (n := n) x).val.open_source).inter
      (isOpen_iInter_of_finite fun I => hUopen I)
  · exact ⟨mem_complexChartAt_source x, mem_iInter.2 fun I => hxU I⟩
  · exact inter_subset_left
  · exact MeasurableSet.iUnion fun I => hΔmeas I
  · refine ne_of_lt ((measure_iUnion_fintype_le volume Δ).trans_lt ?_)
    exact ENNReal.sum_lt_top.2 fun I _ => (hΔtop I).lt_top
  · intro s z hz
    exact mem_iUnion.2 ⟨e s, hmaps (e s) z ⟨mem_iInter.1 hz.1.2 (e s), hz.2⟩⟩
  · intro s
    filter_upwards [hfib (e s)] with y hy
    refine le_trans (le_trans (Set.encard_mono ?_) hy) ?_
    · intro z hz
      exact ⟨⟨mem_iInter.1 hz.1.1.2 (e s), hz.1.2⟩, hz.2⟩
    · exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ (e s))

end Interface

end SGPT.Foundations.Analysis.Pending.DecomposableBasisSheetBound
