import SGPT.NAPotential.ProjectiveGraphPivotScheme
import SGPT.NAPotential.ProjectiveGraphEmbedding
import SGPT.NAPotential.ProjectiveGraphAnalyticZero
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# The actual homogeneous prime ideal of the native graph divisor

Complete blueprint: `graph-divisor-residue-ideal.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphDivisorResidueIdeal

open AlgebraicGeometry CategoryTheory MvPolynomial
open SGPT.NAPotential.AlgPrimes3
open ProjectiveGraphRelationCore ProjectiveGraphRelations ProjectiveGraphSegreAlgebra
open ProjectiveGraphPivotScheme
attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : Type} [CommRing B] [Algebra ℂ B] {N : ℕ}

/-- Images of the SAME normalized native graph coordinates in the actual divisor quotient. -/
def residueCoordinates (p : Ideal B) (v : Fin (N + 1) → B) : Fin (N + 1) → B ⧸ p :=
  fun i => Ideal.Quotient.mk p (v i)

/-- All original homogeneous equations of the actual native divisor quotient vector. -/
def residueRelationIdeal (p : Ideal B) (v : Fin (N + 1) → B) :
    HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) ℂ) :=
  relationCore (A := ℂ) (residueCoordinates p v)

/-- Residue evaluation is the actual original polynomial value followed by the quotient map. -/
theorem aeval_residueCoordinates (p : Ideal B) (v : Fin (N + 1) → B)
    (F : MvPolynomial (Fin (N + 1)) ℂ) :
    aeval (residueCoordinates p v) F = Ideal.Quotient.mk p (aeval v F) := by
  have h : (Ideal.Quotient.mkₐ ℂ p).comp (aeval v) = aeval (residueCoordinates p v) := by
    ext i
    simp [residueCoordinates]
  exact (DFunLike.congr_fun h F).symm

/-- The ACTUAL divisor relation ideal is prime, from the ACTUAL native contracted prime. -/
theorem residueRelationIdeal_isPrime (p : Ideal B) [p.IsPrime] (v : Fin (N + 1) → B) :
    (residueRelationIdeal p v).toIdeal.IsPrime :=
  (RingHom.ker_isPrime (aeval (R := ℂ) (residueCoordinates p v))).homogeneousCore
    (𝒜 := homogeneousSubmodule (Fin (N + 1)) ℂ)

/-- Every actual graph relation remains an actual equation of this divisor closure. -/
theorem graphRelations_le_residueIdeal (p : Ideal B) (v : Fin (N + 1) → B) :
    (relationCore (A := ℂ) v).toIdeal ≤ (residueRelationIdeal p v).toIdeal := by
  apply Ideal.homogeneousCore_mono (homogeneousSubmodule (Fin (N + 1)) ℂ)
  intro F hF
  change aeval (residueCoordinates p v) F = 0
  rw [aeval_residueCoordinates, show aeval v F = 0 from hF, map_zero]

/-- Its actual normalized pivot survives in the actual divisor quotient. -/
theorem pivot_not_mem_residueIdeal (p : Ideal B) [p.IsPrime]
    (v : Fin (N + 1) → B) (j : Fin (N + 1)) (hj : v j = 1) :
    X j ∉ (residueRelationIdeal p v).toIdeal := by
  intro h
  have hz := relationCore_le_ker (A := ℂ) (residueCoordinates p v) h
  change aeval (residueCoordinates p v) (X j) = 0 at hz
  exact one_ne_zero (by simpa only [aeval_X, residueCoordinates, hj, map_one] using hz)

/-- Original algebra generation descends to the SAME actual divisor quotient. -/
theorem residue_adjoin_eq_top (p : Ideal B) (v : Fin (N + 1) → B)
    (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) :
    Algebra.adjoin ℂ (Set.range (residueCoordinates p v)) = ⊤ := by
  have hsurj : Function.Surjective (aeval (R := ℂ) v) := by
    rw [← AlgHom.range_eq_top, aeval_range, hgen]
  have hres : Function.Surjective (aeval (R := ℂ) (residueCoordinates p v)) := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨F, hF⟩ := hsurj b
    exact ⟨F, by rw [aeval_residueCoordinates, hF]⟩
  rw [← aeval_range]
  rwa [AlgHom.range_eq_top]

/-- Removing the normalized pivot leaves the WHOLE original divisor quotient algebra. -/
def residueChartAlgebraEquiv (p : Ideal B) (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1)
    (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) :
    Algebra.adjoin ℂ (Set.range (pivotTail (residueCoordinates p v) j)) ≃ₐ[ℂ] B ⧸ p := by
  have hres : residueCoordinates p v j = 1 := by simp [residueCoordinates, hj]
  have htail : Algebra.adjoin ℂ (Set.range (pivotTail (residueCoordinates p v) j)) = ⊤ :=
    (adjoin_pivotTail (residueCoordinates p v) j hres).trans (residue_adjoin_eq_top p v hgen)
  exact (Subalgebra.equivOfEq _ _ htail).trans Subalgebra.topEquiv

/-- The actual native projective divisor constructed from the original prime quotient. -/
def residueScheme (p : Ideal B) (v : Fin (N + 1) → B) : Scheme :=
  relationScheme (A := ℂ) (residueCoordinates p v)

/-- Its actual inclusion into the SAME original native projective space. -/
def residueInclusion (p : Ideal B) (v : Fin (N + 1) → B) :
    residueScheme p v ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) ℂ) :=
  GradedGraphQuotient.quotientSchemeMap _ (residueRelationIdeal p v)

instance residueInclusion_isClosedImmersion (p : Ideal B) (v : Fin (N + 1) → B) :
    IsClosedImmersion (residueInclusion p v) := by
  unfold residueInclusion
  infer_instance

/-- The ACTUAL pivot open of the ACTUAL full homogeneous divisor quotient is Spec(B/p). -/
def residueChartSchemeIso (p : Ideal B) (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1)
    (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤) :
    (originalPivotOpen (A := ℂ) (residueCoordinates p v) j).toScheme ≅ Spec (.of (B ⧸ p)) :=
  originalPivotChartSchemeIso (A := ℂ) (residueCoordinates p v) j
    (by simp [residueCoordinates, hj]) ≪≫
      Scheme.Spec.mapIso (residueChartAlgebraEquiv p v j hj hgen).toRingEquiv.toCommRingCatIso.symm.op

/-- The actual projective point determined by the original prime of the native graph. -/
def residueProjectivePoint (p : Ideal B) [p.IsPrime] (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1) :
    ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) ℂ) where
  asHomogeneousIdeal := residueRelationIdeal p v
  isPrime := residueRelationIdeal_isPrime p v
  not_irrelevant_le h := pivot_not_mem_residueIdeal p v j hj
    (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (isHomogeneous_X ℂ j)))

/-- The native projective divisor is the ACTUAL closure of its original native prime. -/
theorem range_residueInclusion (p : Ideal B) [p.IsPrime] (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1) :
    Set.range (residueInclusion p v) = closure {residueProjectivePoint p v j hj} := by
  change Set.range (GradedGraphQuotient.quotientSchemeMap
    (homogeneousSubmodule (Fin (N + 1)) ℂ) (residueRelationIdeal p v)) = _
  rw [GradedGraphQuotient.range_quotientSchemeMap]
  ext q
  change residueProjectivePoint p v j hj ≤ q ↔ _
  exact ProjectiveSpectrum.le_iff_mem_closure (homogeneousSubmodule (Fin (N + 1)) ℂ) _ _

open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphAnalyticZero
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- The actual global complex-analytic zero locus of the original divisor equations. -/
def divisorZeroLocus (p : Ideal B) (v : Fin (N + 1) → B) : Set (ComplexProjectiveSpace N) :=
  relationZeroLocus (residueCoordinates p v)

/-- Analyticity follows from actual finite homogeneous equations of the original ideal. -/
theorem isComplexAnalyticSubset_divisorZeroLocus (p : Ideal B) (v : Fin (N + 1) → B) :
    IsComplexAnalyticSubset (n := N) (divisorZeroLocus p v) :=
  isComplexAnalyticSubset_relationZeroLocus (residueCoordinates p v)

/-- The divisor closure lies in the original whole-relation graph zero locus. -/
theorem divisorZeroLocus_subset_graph (p : Ideal B) (v : Fin (N + 1) → B) :
    divisorZeroLocus p v ⊆ relationZeroLocus v := by
  intro x hx F hF
  exact hx F (graphRelations_le_residueIdeal p v hF)

/-- The actual evaluated normalized coordinate vector is nonzero at every evaluator. -/
theorem evaluatedCoordinates_ne_zero (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1) (χ : B →ₐ[ℂ] ℂ) :
    (fun i => χ (v i)) ≠ 0 := by
  intro hz
  have h := congrFun hz j
  exact one_ne_zero (by simpa only [hj, map_one, Pi.zero_apply] using h)

/-- The original complex projective point of the literal evaluated coordinate vector. -/
def evaluatedPoint (v : Fin (N + 1) → B) (j : Fin (N + 1)) (hj : v j = 1)
    (χ : B →ₐ[ℂ] ℂ) : ComplexProjectiveSpace N :=
  mk (fun i => χ (v i)) (evaluatedCoordinates_ne_zero v j hj χ)

/-- Actual coordinate evaluation commutes with the original algebra evaluator. -/
theorem eval_evaluatedCoordinates (v : Fin (N + 1) → B) (χ : B →ₐ[ℂ] ℂ)
    (F : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial.eval (fun i => χ (v i)) F = χ (aeval v F) := by
  have h : χ.comp (aeval v) = aeval (fun i => χ (v i)) := by
    ext i
    simp
  change aeval (R := ℂ) (fun i => χ (v i)) F = _
  exact (DFunLike.congr_fun h F).symm

set_option maxHeartbeats 600000 in
/-- EXACT divisor trace: global actual projective equations cut out the ORIGINAL
native prime ideal, with no trace or closure-equality certificate in the hypotheses. -/
theorem divisorZeroLocus_iff_primeVanishing (p : Ideal B) (v : Fin (N + 1) → B)
    (j : Fin (N + 1)) (hj : v j = 1) (hgen : Algebra.adjoin ℂ (Set.range v) = ⊤)
    (χ : B →ₐ[ℂ] ℂ) :
    evaluatedPoint v j hj χ ∈ divisorZeroLocus p v ↔ ∀ b ∈ p, χ b = 0 := by
  have heval : Function.Surjective (aeval (R := ℂ) (pivotTail v j)) := by
    rw [← AlgHom.range_eq_top, aeval_range, adjoin_pivotTail v j hj, hgen]
  constructor
  · intro hΔ b hb
    obtain ⟨q, hq⟩ := heval b
    let F := rename (finSuccEquiv' j).symm (homogenize q)
    have hFhom : F.IsHomogeneous q.totalDegree :=
      (isHomogeneous_homogenize q).rename_isHomogeneous
    have hFv : aeval v F = b := by
      rw [show F = rename (finSuccEquiv' j).symm (homogenize q) from rfl,
        aeval_rename, vector_pivotRenaming v j hj, aeval_graphCoordinates,
        dehomogenize_homogenize, hq]
    have hFmem : F ∈ (residueRelationIdeal p v).toIdeal := by
      apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨q.totalDegree, hFhom⟩
      change aeval (residueCoordinates p v) F = 0
      rw [aeval_residueCoordinates, hFv]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have hz := (eval_rep_eq_zero_iff hFhom (evaluatedPoint v j hj χ)
      (fun i => χ (v i)) (evaluatedCoordinates_ne_zero v j hj χ) rfl).mp (hΔ F hFmem)
    rw [eval_evaluatedCoordinates, hFv] at hz
    exact hz
  · intro hpχ
    obtain ⟨S, hS, hspan⟩ := exists_finite_homogeneous_generators (residueRelationIdeal p v)
    have hle : (residueRelationIdeal p v).toIdeal ≤
        RingHom.ker (MvPolynomial.eval (evaluatedPoint v j hj χ).rep) := by
      rw [← hspan]
      apply Ideal.span_le.mpr
      intro F hF
      obtain ⟨⟨n, hn⟩, hmem⟩ := hS F hF
      have hzero := relationCore_le_ker (A := ℂ) (residueCoordinates p v) hmem
      have hval : aeval v F ∈ p := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        exact (aeval_residueCoordinates p v F).symm.trans hzero
      have hz : MvPolynomial.eval (fun i => χ (v i)) F = 0 := by
        rw [eval_evaluatedCoordinates]
        exact hpχ _ hval
      exact (eval_rep_eq_zero_iff hn (evaluatedPoint v j hj χ)
        (fun i => χ (v i)) (evaluatedCoordinates_ne_zero v j hj χ) rfl).mpr hz
    intro F hF
    exact hle hF

end SGPT.NAPotential.GraphDivisorResidueIdeal
