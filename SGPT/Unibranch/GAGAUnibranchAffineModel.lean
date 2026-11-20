import SGPT.Unibranch.GAGAUnibranchGerms
import SGPT.Foundations.Analysis.Pending.RueckertNullstellensatz
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra
import Mathlib.RingTheory.Nullstellensatz

/-!
# The embedded affine analytic model and algebraic unibranchness

For an ideal `I` of `ℂ[z₁, …, zₙ]`, let `V(I) ⊆ ℂⁿ` be its common zero set, carried by
the coordinate open `⊤ ⊆ ℂⁿ`, and let `modelOver ⊤ V(I)` be the project's actual reduced
analytic model (whole germ vanishing-ideal quotient sheaf). At a point `x ∈ V(I)` the model
stalk is `𝒪_{ℂⁿ,x}/W` where `W` is the whole chart stalk ideal of the vanishing ideal of
`V(I)`. We prove `I𝒪 ⊆ W ⊆ √(I𝒪)`: the first inclusion because polynomials of `I` vanish on
`V(I)`, the second by Rückert's Nullstellensatz (`RueckertNullstellensatz.vanishingIdeal_le_radical`).
Combined with `sourceUnibranchReducedRing_localization_of_germs` this gives:

* `sourceUnibranchReducedRing_pointLocalization_of_model`: if the model stalk at `x` is
  unibranch, the algebraic local ring of `ℂ[z]/I` at `x` is unibranch;
* `schemeIsUnibranch_of_modelUnibranch`: if `I` is radical and the reduced analytic model of
  `V(I)` is unibranch at every point, then `Spec (ℂ[z]/I)` is unibranch (Stacks 0BQ2, at every
  scheme point, including the non-closed ones).

This is the implication "`𝒳^An` unibranch ⟹ `𝒳` unibranch" of `prop:unibranch_gaga` for an
affine `𝒳 = Spec ℂ[z]/I` with its embedded analytic model.

Blueprint: `claude-gaga2.tex`.
-/

set_option autoImplicit false

open TopologicalSpace Filter Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves (HolomorphicAt vanishingIdeal
  holomorphicAt_comp_val_iff)
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci (wholeChartStalkIdeal
  chartTranslatedGerm translatedGerm)
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace (actualSubspaceStalkChartEquiv)
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces (modelOver)

namespace SGPT.Unibranch

noncomputable section

variable {n : ℕ}

/-- The coordinates of a point of `ℂⁿ`. -/
def complexCoordinates (z : ComplexModel n) : Fin n → ℂ := fun i => z i

theorem complexCoordinates_apply (z : ComplexModel n) (i : Fin n) :
    complexCoordinates z i = z i := rfl

theorem complexCoordinates_add (z w : ComplexModel n) :
    complexCoordinates (z + w) = fun i => z i + complexCoordinates w i := by
  funext i
  rw [complexCoordinates_apply, complexCoordinates_apply, PiLp.add_apply]

/-- The common zero set `V(I)`, inside the coordinate open `⊤ ⊆ ℂⁿ`. -/
def polynomialZeroSet (I : Ideal (MvPolynomial (Fin n) ℂ)) : Set (⊤ : Opens (ComplexModel n)) :=
  {y | ∀ p ∈ I, MvPolynomial.eval (complexCoordinates (y : ComplexModel n)) p = 0}

/-! ### The chart of the coordinate open `⊤` -/

private theorem chart_top_apply (x w : (⊤ : Opens (ComplexModel n))) :
    chartAt (ComplexModel n) x w = (w : ComplexModel n) := rfl

private theorem chart_top_mem_source (x w : (⊤ : Opens (ComplexModel n))) :
    w ∈ (chartAt (ComplexModel n) x).source := by
  change w ∈ ((chartAt (ComplexModel n) (x : ComplexModel n)).subtypeRestr ⟨x⟩).source
  rw [OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq]
  simp

private theorem chart_top_symm (x : (⊤ : Opens (ComplexModel n))) (z : ComplexModel n) :
    (chartAt (ComplexModel n) x).symm z = ⟨z, trivial⟩ := by
  have h := (chartAt (ComplexModel n) x).left_inv (chart_top_mem_source x ⟨z, trivial⟩)
  rwa [chart_top_apply] at h

/-- The chart-translated germ at a point of `⊤` is the germ at `0` of `z ↦ f(z + x)`. -/
private theorem chartTranslatedGerm_top (x : (⊤ : Opens (ComplexModel n)))
    (f : (⊤ : Opens (ComplexModel n)) → ℂ) (hf : HolomorphicAt n f x) :
    ∃ hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ (fun z => f ⟨z + (x : ComplexModel n), trivial⟩) z,
      chartTranslatedGerm x x (mem_chart_source (ComplexModel n) x) f hf =
        HolGerm.mk (fun z => f ⟨z + (x : ComplexModel n), trivial⟩) hF := by
  unfold chartTranslatedGerm translatedGerm
  generalize_proofs hp
  simp only [chart_top_apply, chart_top_symm] at hp ⊢
  exact ⟨hp, trivial⟩

/-! ### The model stalk ideal lies between `I𝒪` and its radical -/

variable (I : Ideal (MvPolynomial (Fin n) ℂ))

/-- The whole chart stalk ideal of the vanishing ideal of `V(I)` at `x`; the model stalk of
`V(I)` at `x` is the quotient of the germ ring by it. -/
abbrev modelStalkIdeal (x : (⊤ : Opens (ComplexModel n))) : Ideal (HolGerm (ComplexModel n)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := n) (polynomialZeroSet I)) x x
    (mem_chart_source (ComplexModel n) x)

private theorem holomorphicAt_polynomial (p : MvPolynomial (Fin n) ℂ)
    (x : (⊤ : Opens (ComplexModel n))) :
    HolomorphicAt n (fun w : (⊤ : Opens (ComplexModel n)) =>
      MvPolynomial.eval (complexCoordinates (w : ComplexModel n)) p) x := by
  have hF : Differentiable ℂ (translatedPolynomialFunction 0 p) :=
    differentiable_translatedPolynomialFunction 0 p
  have heq : (fun w : (⊤ : Opens (ComplexModel n)) =>
      MvPolynomial.eval (complexCoordinates (w : ComplexModel n)) p) =
      translatedPolynomialFunction 0 p ∘ Subtype.val := by
    funext w
    simp only [Function.comp_apply, translatedPolynomialFunction, Pi.zero_apply, add_zero]
    rfl
  rw [heq, holomorphicAt_comp_val_iff]
  exact Filter.Eventually.of_forall fun y => (hF y).mdifferentiableAt

/-- Polynomials of `I` vanish on `V(I)`, so `I𝒪 ⊆ W`. -/
theorem map_le_modelStalkIdeal (x : (⊤ : Opens (ComplexModel n))) :
    I.map (polynomialPointGerm (complexCoordinates (x : ComplexModel n))) ≤
      modelStalkIdeal I x := by
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  rw [Ideal.mem_comap]
  let f := fun w : (⊤ : Opens (ComplexModel n)) =>
    MvPolynomial.eval (complexCoordinates (w : ComplexModel n)) p
  have hf : HolomorphicAt n f x := holomorphicAt_polynomial p x
  obtain ⟨hF, hgerm⟩ := chartTranslatedGerm_top x f hf
  apply Ideal.subset_span
  refine ⟨f, hf, ⟨hf, Filter.Eventually.of_forall fun y hy => hy p hp⟩, ?_⟩
  rw [hgerm, polynomialPointGerm_eq_mk, HolGerm.mk_eq_mk_iff]
  exact Filter.Eventually.of_forall fun z => by
    simp only [f, translatedPolynomialFunction, complexCoordinates_add]

/-- Rückert's Nullstellensatz gives `W ⊆ √(I𝒪)`. -/
theorem modelStalkIdeal_le_radical (x : (⊤ : Opens (ComplexModel n))) :
    modelStalkIdeal I x ≤
      (I.map (polynomialPointGerm (complexCoordinates (x : ComplexModel n)))).radical := by
  classical
  obtain ⟨s, q, hq⟩ : ∃ (s : ℕ) (q : Fin s → MvPolynomial (Fin n) ℂ),
      Submodule.span (MvPolynomial (Fin n) ℂ) (Set.range q) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  let c := complexCoordinates (x : ComplexModel n)
  let J := I.map (polynomialPointGerm c)
  have hR := RueckertNullstellensatz.vanishingIdeal_le_radical J
    (fun j => translatedPolynomialFunction c (q j))
    (fun j => ⟨eventually_differentiableAt_translatedPolynomialFunction c (q j) 0, by
      rw [← polynomialPointGerm_eq_mk]
      exact Ideal.mem_map_of_mem _ (hq ▸ Submodule.subset_span ⟨j, rfl⟩)⟩)
  refine le_trans ?_ hR
  rw [modelStalkIdeal, wholeChartStalkIdeal, Ideal.span_le]
  rintro _ ⟨f, hf, ⟨-, hvan⟩, rfl⟩
  obtain ⟨hF, hgerm⟩ := chartTranslatedGerm_top x f hf
  rw [SetLike.mem_coe, hgerm, AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  have hcont : Tendsto (fun z : ComplexModel n =>
      (⟨z + (x : ComplexModel n), trivial⟩ : (⊤ : Opens (ComplexModel n)))) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun z : ComplexModel n =>
        (⟨z + (x : ComplexModel n), trivial⟩ : (⊤ : Opens (ComplexModel n)))) :=
      (continuous_id.add continuous_const).subtype_mk _
    have h0 : (⟨(0 : ComplexModel n) + (x : ComplexModel n), trivial⟩ :
        (⊤ : Opens (ComplexModel n))) = x := Subtype.ext (zero_add _)
    simpa [h0] using hc.tendsto 0
  filter_upwards [hcont.eventually hvan] with z hz hzT
  apply hz
  intro p hp
  rw [← hq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨j, rfl⟩ := hp
    have h1 := hzT j
    simp only [translatedPolynomialFunction] at h1
    rw [complexCoordinates_add]
    exact h1
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

/-- The model stalk of `V(I)` at `x` is `𝒪/W`. -/
def modelStalkEquiv (x : polynomialZeroSet I) :
    ((modelOver (⊤ : Opens (ComplexModel n)) (polynomialZeroSet I)).left.presheaf.stalk
      x).carrier ≃+* HolGerm (ComplexModel n) ⧸ modelStalkIdeal I x.val :=
  actualSubspaceStalkChartEquiv (n := n) (polynomialZeroSet I) x

/-- **Closed points.** If the actual reduced analytic model of `V(I)` is unibranch at
`x ∈ V(I)`, then the algebraic local ring of `ℂ[z]/I` at `x` is unibranch. -/
theorem sourceUnibranchReducedRing_pointLocalization_of_model (hI : I.IsRadical)
    (x : polynomialZeroSet I)
    (h : SourceUnibranchReducedRing
      ((modelOver (⊤ : Opens (ComplexModel n)) (polynomialZeroSet I)).left.presheaf.stalk
        x).carrier) :
    SourceUnibranchReducedRing (Localization.AtPrime
      (pointIdeal I (complexCoordinates ((x.val : (⊤ : Opens (ComplexModel n))) :
        ComplexModel n)) (fun p hp => x.property p hp))) :=
  sourceUnibranchReducedRing_localization_of_germs I hI _ (fun p hp => x.property p hp)
    (modelStalkIdeal I x.val)
    (map_le_modelStalkIdeal I x.val) (modelStalkIdeal_le_radical I x.val)
    ((sourceUnibranchReducedRing_iff_of_ringEquiv (modelStalkEquiv I x)).mp h)

/-- Localizations at equal prime ideals have the same unibranchness. -/
theorem sourceUnibranchReducedRing_localization_congr {R : Type*} [CommRing R]
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (h : P = Q) :
    SourceUnibranchReducedRing (Localization.AtPrime P) ↔
      SourceUnibranchReducedRing (Localization.AtPrime Q) := by
  subst h
  rfl

open AlgebraicGeometry in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Embedded affine form of "`𝒳^An` unibranch ⟹ `𝒳` unibranch".** Let `I` be a radical ideal
of `ℂ[z₁,…,zₙ]`. If the actual reduced analytic model of `V(I) ⊆ ℂⁿ` is unibranch at every
point, then the scheme `Spec ℂ[z]/I` is unibranch at every point (Stacks 0BQ2). -/
theorem schemeIsUnibranch_of_modelUnibranch (hI : I.IsRadical)
    (h : ∀ x : polynomialZeroSet I, SourceUnibranchReducedRing
      ((modelOver (⊤ : Opens (ComplexModel n)) (polynomialZeroSet I)).left.presheaf.stalk
        x).carrier) :
    SchemeIsUnibranch (Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))) := by
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  apply schemeIsUnibranch_of_closedPoints
  intro y hy
  have hmax : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  rw [schemeIsUnibranchAt_spec_iff, sourceUnibranchLocalRing_iff_of_isReduced]
  -- the Nullstellensatz identifies the closed point with a point `c ∈ V(I)`
  have hmax' : (y.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨c, hc⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).mp hmax'
  have hcI : ∀ p ∈ I, MvPolynomial.eval c p = 0 := by
    intro p hp
    have h1 : p ∈ y.asIdeal.comap (Ideal.Quotient.mk I) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact y.asIdeal.zero_mem
    rw [hc, MvPolynomial.mem_vanishingIdeal_singleton_iff] at h1
    simpa [MvPolynomial.aeval_eq_eval] using h1
  have hy' : y.asIdeal = pointIdeal I c hcI := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.mem_comap, hc, MvPolynomial.mem_vanishingIdeal_singleton_iff, pointIdeal,
      RingHom.mem_ker, Ideal.Quotient.lift_mk]
    simp [MvPolynomial.aeval_eq_eval]
  let z : ComplexModel n := WithLp.toLp 2 c
  have hz : complexCoordinates z = c := rfl
  let x : polynomialZeroSet I := ⟨⟨z, trivial⟩, fun p hp => by
    change MvPolynomial.eval (complexCoordinates z) p = 0
    rw [hz]
    exact hcI p hp⟩
  rw [sourceUnibranchReducedRing_localization_congr hy']
  exact sourceUnibranchReducedRing_pointLocalization_of_model I hI x (h x)

/-! ### The embedded affine complex space -/

/-- `V(I)` is an analytic subset of `ℂⁿ`: in the identity chart it is the common zero set of
finitely many generators of `I`. -/
theorem polynomialZeroSet_isComplexAnalyticSubset :
    IsComplexAnalyticSubset (n := n) (polynomialZeroSet I) := by
  classical
  obtain ⟨s, q, hq⟩ : ∃ (s : ℕ) (q : Fin s → MvPolynomial (Fin n) ℂ),
      Submodule.span (MvPolynomial (Fin n) ℂ) (Set.range q) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  intro x
  refine ⟨{ generatorCount := s
            generator := fun j z => MvPolynomial.eval (complexCoordinates z) (q j)
            coordinateNeighborhood := Set.univ
            isOpen_coordinateNeighborhood := isOpen_univ
            center_mem_coordinateNeighborhood := Set.mem_univ _
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro z _
    have h := (chartAt (ComplexModel n) x).map_source (chart_top_mem_source x ⟨z, trivial⟩)
    rwa [chart_top_apply] at h
  · intro j
    have hF := differentiable_translatedPolynomialFunction 0 (q j)
    have heq : (fun z : ComplexModel n => MvPolynomial.eval (complexCoordinates z) (q j)) =
        translatedPolynomialFunction 0 (q j) := by
      funext z
      simp only [translatedPolynomialFunction, Pi.zero_apply, add_zero]
      rfl
    rw [heq]
    exact hF.differentiableOn
  · intro y _ _
    change y ∈ polynomialZeroSet I ↔
      ∀ j, MvPolynomial.eval (complexCoordinates (chartAt (ComplexModel n) x y)) (q j) = 0
    rw [chart_top_apply]
    constructor
    · intro hy j
      exact hy (q j) (hq ▸ Submodule.subset_span ⟨j, rfl⟩)
    · intro hy p hp
      rw [← hq] at hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨j, rfl⟩ := hp
        exact hy j
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul a b _ hb => simp [hb]

/-- The complex space `V(I)` (reduced, with its embedded analytic model structure); for a
radical `I` it is the complex space associated with `Spec ℂ[z]/I`. -/
def polynomialZeroSetComplexSpace : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel ⊤ (polynomialZeroSet I)
    (polynomialZeroSet_isComplexAnalyticSubset I)

/-- **`prop:unibranch_gaga`, direction "analytic ⟹ algebraic", embedded affine case.**
If `I ⊆ ℂ[z₁,…,zₙ]` is radical and the complex space `V(I)` is unibranch
(`def:unibranch:L21`), then `Spec ℂ[z]/I` is unibranch (Stacks 0BQ2). -/
theorem schemeIsUnibranch_of_isUnibranch (hI : I.IsRadical)
    (h : (polynomialZeroSetComplexSpace I).IsUnibranch) :
    SchemeIsUnibranch (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))) :=
  schemeIsUnibranch_of_modelUnibranch I hI h

end

end SGPT.Unibranch
