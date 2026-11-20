import SGPT.BDivisor.StrictVolume.PencilFubiniStudyMetric

/-! Literal whole-chart FS weights of the SAME original H-E pencil. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators

def originalBlowupVertexEquiv : Fin 4 ≃ latticePolytopeVertices blowupGenerator :=
  Equiv.ofBijective blowupVertex (by
    constructor
    · intro i j hij
      have h := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | norm_num [blowupVertex, blowupGenerator, funext_iff, Fin.forall_fin_two] at h
    · intro v
      obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
      exact ⟨k, Subtype.ext hk⟩)

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalPencilFsSum_eq_directionNorm (k : Fin 4) (z : Fin 2 → ℂ) :
    fsSum (blowupDirectionDivisor hs) (blowupVertex k) (blowupOriginalCoordinates hs k z) =
      2 * (‖blowupDirectionChartVector k z 0‖ ^ 2 + ‖blowupDirectionChartVector k z 1‖ ^ 2) := by
  classical
  let : Fintype (latticePolytopeVertices blowupGenerator) :=
    (finite_latticePolytopeVertices blowupGenerator).fintype
  let D := blowupDirectionDivisor hs
  let v := blowupVertex k
  let Z := blowupOriginalCoordinates hs k z
  have hsum : fsSum D v Z = ∑ w : latticePolytopeVertices blowupGenerator,
      ‖toricMonomial D v (toricCartierDatum D w) Z‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro w _
    simp only [toricMonomial, norm_prod, norm_pow]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have hexp : (fsExponent D v w i).toNat =
        (intPairing (toricCartierDatum D w) (polytopeToricRayGenerator blowupGenerator hs v i) -
          intPairing (toricCartierDatum D v) (polytopeToricRayGenerator blowupGenerator hs v i)).toNat := by
      simp only [fsExponent, intPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hexp, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have h0 := congrFun (blowupDirectionOriginalVector hs k z) (0 : Fin 2)
  have h1 := congrFun (blowupDirectionOriginalVector hs k z) (1 : Fin 2)
  change toricMonomial D v ![1, 0] Z = blowupDirectionChartVector k z 0 at h0
  change toricMonomial D v ![0, 1] Z = blowupDirectionChartVector k z 1 at h1
  change fsSum D v Z = _
  rw [hsum, ← originalBlowupVertexEquiv.sum_comp]
  change (∑ j : Fin 4, ‖toricMonomial D v
    (toricCartierDatum D (blowupVertex j)) Z‖ ^ 2) = _
  have hd (j : Fin 4) : toricCartierDatum D (blowupVertex j) = blowupDirectionDatum j :=
    blowupDirection_cartierDatum hs j
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hd]
  dsimp only [blowupDirectionDatum]
  change ‖toricMonomial D v ![1, 0] Z‖ ^ 2 +
    (‖toricMonomial D v ![1, 0] Z‖ ^ 2 +
      (‖toricMonomial D v ![0, 1] Z‖ ^ 2 + ‖toricMonomial D v ![0, 1] Z‖ ^ 2)) = _
  simp only [h0, h1]
  ring

theorem originalPencilFsWeight_ordered (k : Fin 4) (z : Fin 2 → ℂ) :
    (originalPencilFsMetric hs).weight (blowupVertex k) (blowupOriginalCoordinates hs k z) =
      Real.log 2 +
        Real.log (‖blowupDirectionChartVector k z 0‖ ^ 2 +
          ‖blowupDirectionChartVector k z 1‖ ^ 2) := by
  rw [originalPencilFsMetric_weight, fsWeight, originalPencilFsSum_eq_directionNorm]
  apply Real.log_mul (by norm_num)
  have hpos : 0 < ‖blowupDirectionChartVector k z 0‖ ^ 2 +
      ‖blowupDirectionChartVector k z 1‖ ^ 2 := by
    fin_cases k <;> simp [blowupDirectionChartVector] <;> positivity
  exact hpos.ne'

end SGPT.BDivisor.StrictPencilNext
