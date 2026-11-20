import SGPT.NAPotential.ProjectiveGraphRelations
import SGPT.NAPotential.ProjectiveGraphQuotientGrading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The actual affine open of the homogeneous graph quotient

The actual quotient `Q = A[Y₀,Yᵢ] / H_b` carries the genuine quotient grading.
Its degree-zero homogeneous localization at `Y₀` is canonically the actual
subalgebra `A[b]`, via homogeneous lifts and evaluation at `(1,b)`.
Mathlib's native `Proj.basicOpenIsoSpec` then identifies the actual `Y₀ ≠ 0`
open subscheme with `Spec A[b]`.

Blueprint: `projective-graph-quotient.tex`. No graph-chart equivalence, analytic
graph, or smooth model is assumed as input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphQuotient

open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization
open ProjectiveGraphRelations

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {σ A K : Type u} [CommRing A] [CommRing K] [Algebra A K]

/-- The actual homogeneous graph ideal, bundled with its proved homogeneity. -/
def relationIdeal (b : σ → K) : HomogeneousIdeal (homogeneousSubmodule (Option σ) A) :=
  ⟨graphRelationIdeal (A := A) b, graphRelationIdeal_isHomogeneous b⟩

/-- The original polynomial quotient by every homogeneous graph relation. -/
abbrev GraphRing (b : σ → K) :=
  MvPolynomial (Option σ) A ⧸ graphRelationIdeal (A := A) b

/-- Its degree-`n` component is the actual image of degree-`n` polynomials. -/
abbrev graphGrading (b : σ → K) : ℕ → Submodule A (GraphRing (A := A) b) :=
  GradedGraphQuotient.grading (homogeneousSubmodule (Option σ) A)
    (graphRelationIdeal (A := A) b)

instance graphGradedRing (b : σ → K) : GradedRing (graphGrading (A := A) b) :=
  GradedGraphQuotient.gradedRing (homogeneousSubmodule (Option σ) A)
    (graphRelationIdeal (A := A) b) (graphRelationIdeal_isHomogeneous b)

/-- The actual class of the distinguished homogeneous coordinate. -/
def chartCoordinate (b : σ → K) : GraphRing (A := A) b :=
  Ideal.Quotient.mk (graphRelationIdeal (A := A) b) (X none)

theorem chartCoordinate_mem (b : σ → K) :
    chartCoordinate (A := A) b ∈ graphGrading b 1 :=
  Submodule.mem_map.mpr ⟨X none, isHomogeneous_X A none, rfl⟩

/-- Evaluation into the actual generated subalgebra. -/
def graphEval (b : σ → K) :
    MvPolynomial (Option σ) A →ₐ[A] Algebra.adjoin A (Set.range b) :=
  aeval (fun j => match j with
    | none => 1
    | some i => ⟨b i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem coe_graphEval (b : σ → K) (p : MvPolynomial (Option σ) A) :
    (graphEval b p : K) = aeval (graphCoordinates b) p := by
  have h : (Algebra.adjoin A (Set.range b)).val.comp (graphEval b) =
      aeval (graphCoordinates b) := by
    ext j
    cases j <;> simp [graphEval, graphCoordinates]
  exact DFunLike.congr_fun h p

theorem graphRelationIdeal_le_ker_graphEval (b : σ → K) :
    graphRelationIdeal (A := A) b ≤ RingHom.ker (graphEval b) := by
  intro p hp
  apply Subtype.ext
  simpa only [coe_graphEval, ZeroMemClass.coe_zero, RingHom.mem_ker] using
    graphRelationIdeal_le_ker b hp

/-- Evaluation descends to the actual homogeneous quotient. -/
def quotientEval (b : σ → K) : GraphRing (A := A) b →+* Algebra.adjoin A (Set.range b) :=
  Ideal.Quotient.lift (graphRelationIdeal (A := A) b) (graphEval b).toRingHom
    (graphRelationIdeal_le_ker_graphEval b)

@[simp]
theorem quotientEval_mk (b : σ → K) (p : MvPolynomial (Option σ) A) :
    quotientEval b (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p) = graphEval b p :=
  Ideal.Quotient.lift_mk _ _ _

@[simp]
theorem quotientEval_chartCoordinate (b : σ → K) :
    quotientEval b (chartCoordinate (A := A) b) = 1 := by
  simp [chartCoordinate, graphEval]

/-- Evaluation on the full localization; its inverted coordinate maps to one. -/
def localizationEval (b : σ → K) :
    Localization.Away (chartCoordinate (A := A) b) →+* Algebra.adjoin A (Set.range b) :=
  Localization.awayLift (quotientEval b) (chartCoordinate b)
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [quotientEval_chartCoordinate, mul_one]⟩)

/-- The native degree-zero homogeneous localization of this very graph quotient. -/
abbrev GraphChartRing (b : σ → K) :=
  HomogeneousLocalization.Away (graphGrading (A := A) b) (chartCoordinate b)

/-- Restriction of the genuine localization evaluation to its degree-zero subring. -/
def chartEval (b : σ → K) : GraphChartRing (A := A) b →+* Algebra.adjoin A (Set.range b) :=
  (localizationEval b).comp
    (algebraMap (GraphChartRing (A := A) b) (Localization.Away (chartCoordinate b)))

theorem chartEval_fraction (b : σ → K) (n : ℕ) (q : GraphRing (A := A) b)
    (hq : q ∈ graphGrading b (n • 1)) :
    chartEval b (HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) n q hq) =
      quotientEval b q := by
  change localizationEval b
    (HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) n q hq).val = _
  rw [HomogeneousLocalization.Away.val_mk]
  simpa only [localizationEval, one_pow, mul_one] using
    (Localization.awayLift_mk (quotientEval b) (chartCoordinate b) q 1
      (by rw [quotientEval_chartCoordinate, mul_one]) n)

theorem chartEval_mk (b : σ → K) (n : ℕ) (p : MvPolynomial (Option σ) A)
    (hp : p.IsHomogeneous n) :
    chartEval b (HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) n
      (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p)
      (Submodule.mem_map.mpr ⟨p, by simpa using hp, rfl⟩)) = graphEval b p := by
  change localizationEval b
    (HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) n
      (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p) _).val = graphEval b p
  rw [HomogeneousLocalization.Away.val_mk]
  simpa only [localizationEval, quotientEval_mk, one_pow, mul_one] using
    (Localization.awayLift_mk (quotientEval b) (chartCoordinate b)
      (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p) 1
      (by rw [quotientEval_chartCoordinate, mul_one]) n)

theorem chartEval_injective (b : σ → K) : Function.Injective (chartEval (A := A) b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, q, hq, rfl⟩ := z.mk_surjective (graphGrading b) (chartCoordinate_mem b)
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  have hp' : p.IsHomogeneous n := by simpa using hp
  rw [chartEval_fraction] at hz
  change graphEval b p = 0 at hz
  have hpzero : aeval (graphCoordinates b) p = 0 := by
    simpa only [coe_graphEval, ZeroMemClass.coe_zero] using congrArg Subtype.val hz
  have hpH : p ∈ graphRelationIdeal (A := A) b := Ideal.subset_span ⟨n, hp', hpzero⟩
  have hqzero : Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hpH
  change HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) n
    (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) p) hq = 0
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, hqzero,
    Localization.mk_zero]

theorem chartEval_surjective (b : σ → K) : Function.Surjective (chartEval (A := A) b) := by
  intro x
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial σ A, aeval b p = (x : K) := by
    have hmem : (x : K) ∈ (aeval (R := A) b).range := by
      rw [aeval_range]
      exact x.property
    exact hmem
  refine ⟨HomogeneousLocalization.Away.mk (graphGrading b) (chartCoordinate_mem b) p.totalDegree
    (Ideal.Quotient.mk (graphRelationIdeal (A := A) b) (homogenize p))
    (Submodule.mem_map.mpr ⟨homogenize p, by simpa using isHomogeneous_homogenize p, rfl⟩), ?_⟩
  rw [chartEval_mk b p.totalDegree (homogenize p) (isHomogeneous_homogenize p)]
  apply Subtype.ext
  rw [coe_graphEval, aeval_graphCoordinates, dehomogenize_homogenize]
  exact hp

/-- The actual homogeneous localization ring of the graph quotient is `A[b]`. -/
def graphChartRingEquiv (b : σ → K) : GraphChartRing (A := A) b ≃+* Algebra.adjoin A (Set.range b) :=
  RingEquiv.ofBijective (chartEval b) ⟨chartEval_injective b, chartEval_surjective b⟩

/-- The actual native projective scheme of the homogeneous graph quotient. -/
def graphScheme (b : σ → K) : Scheme := Proj (graphGrading (A := A) b)

/-- Its actual distinguished open subset, rather than a supplied affine-chart model. -/
def graphChartOpen (b : σ → K) : (graphScheme (A := A) b).Opens :=
  Proj.basicOpen (graphGrading b) (chartCoordinate b)

/-- **Native scheme-chart identification** for this very homogeneous graph quotient. -/
def graphChartSchemeIso (b : σ → K) :
    (graphChartOpen (A := A) b).toScheme ≅ Spec (.of (Algebra.adjoin A (Set.range b))) :=
  (Proj.basicOpenIsoSpec (graphGrading b) (chartCoordinate b) (chartCoordinate_mem b) one_pos) ≪≫
    (Scheme.Spec.mapIso (graphChartRingEquiv b).toCommRingCatIso.symm.op)

/-- The affine graph algebra is an actual open subscheme of the projective graph. -/
def affineGraphChartImmersion (b : σ → K) :
    Spec (.of (Algebra.adjoin A (Set.range b))) ⟶ graphScheme (A := A) b :=
  (graphChartSchemeIso b).inv ≫ (graphChartOpen b).ι

instance affineGraphChartImmersion_isOpenImmersion (b : σ → K) :
    IsOpenImmersion (affineGraphChartImmersion (A := A) b) := by
  dsimp only [affineGraphChartImmersion]
  infer_instance

/-- Its image is precisely the original distinguished open of the actual Proj quotient. -/
theorem opensRange_affineGraphChartImmersion (b : σ → K) :
    (affineGraphChartImmersion (A := A) b).opensRange = graphChartOpen b := by
  change ((graphChartSchemeIso b).inv ≫ (graphChartOpen b).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphQuotient
