import SGPT.Convex.CutSimplexVertices
import SGPT.NAPotential.FiniteNodeSimplexConcavity

/-! The actual source EReal simplex maximum. Polar coordinates are removed
by their genuine zero-coordinate face; no global nodal finiteness or
maximizer/vertex certificate is a caller hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
namespace LP
open SGPT.Convex.CutSimplex
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem coe_finset_sum (S : Finset ι) (r : ι → ℝ) :
    (∑ i ∈ S, (r i : EReal)) = ((∑ i ∈ S, r i : ℝ) : EReal) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

theorem le_coe_toReal_of_ne_top (a : EReal) (ha : a ≠ ⊤) : a ≤ (a.toReal : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact (ha rfl).elim
  | coe r => simp

omit [Fintype ι] in
theorem sum_weighted_le_coe_real (S : Finset ι) (a : ι → EReal) (w : ι → ℝ)
    (ha : ∀ i ∈ S, a i ≠ ⊤) (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, (w i : EReal) * a i) ≤ ((∑ i ∈ S, w i * (a i).toReal : ℝ) : EReal) := by
  calc
    (∑ i ∈ S, (w i : EReal) * a i) ≤ ∑ i ∈ S, (w i : EReal) * ((a i).toReal : EReal) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (le_coe_toReal_of_ne_top (a i) (ha i hi))
        (EReal.coe_nonneg.mpr (hw i hi))
    _ = ∑ i ∈ S, ((w i * (a i).toReal : ℝ) : EReal) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (EReal.coe_mul _ _).symm
    _ = ((∑ i ∈ S, w i * (a i).toReal : ℝ) : EReal) := coe_finset_sum S _

/-- A genuinely positive coefficient at a pole forces the entire actual
weighted expression to bottom; all other terms have finite real uppers. -/
theorem sum_weighted_eq_bot_of_pole (a : ι → EReal) (w : ι → ℝ)
    (ha : ∀ i, a i ≠ ⊤) (hw : ∀ i, 0 ≤ w i) (i : ι)
    (hi : a i = ⊥) (hwi : 0 < w i) : (∑ j, (w j : EReal) * a j) = ⊥ := by
  classical
  have hterm : (w i : EReal) * a i = ⊥ := by rw [hi]; exact EReal.coe_mul_bot_of_pos hwi
  have hother := sum_weighted_le_coe_real (Finset.univ.erase i) a w
    (fun j _ => ha j) (fun j _ => hw j)
  apply le_antisymm _ bot_le
  calc
    (∑ j, (w j : EReal) * a j) = (∑ j ∈ Finset.univ.erase i, (w j : EReal) * a j) + ⊥ := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hterm]
    _ ≤ ((∑ j ∈ Finset.univ.erase i, w j * (a j).toReal : ℝ) : EReal) + ⊥ :=
      add_le_add hother le_rfl
    _ = ⊥ := by simp

/-- On the actual polar-coordinate face, the full EReal expression is
literally the real objective. Zero times bottom is retained exactly. -/
theorem weighted_eq_coe_objective_on_face (τ : ι → ℝ) (s : ℝ) (a : ι → EReal)
    (ha : ∀ i, a i ≠ ⊤) {w : ι → ℝ}
    (hw : w ∈ coordinateFace τ s (Finset.univ.filter fun i => a i ≠ ⊥)) :
    (∑ i, (w i : EReal) * a i) = (objective (fun i => (a i).toReal) w : EReal) := by
  classical
  rw [objective_apply, ← coe_finset_sum Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hbot : a i = ⊥
  · have hzero : w i = 0 := hw.2 i (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact hbot)
    simp only [hzero, EReal.coe_zero, zero_mul]
  · induction hval : a i using EReal.rec with
    | bot => exact (hbot hval).elim
    | top => exact (ha i hval).elim
    | coe r => simp only [EReal.toReal_coe, EReal.coe_mul]

/-- Every non-bottom weighted expression belongs to its actual polar face. -/
theorem mem_coordinateFace_of_weighted_ne_bot (τ : ι → ℝ) (s : ℝ) (a : ι → EReal)
    (ha : ∀ i, a i ≠ ⊤) {w : ι → ℝ} (hw : w ∈ cut τ s)
    (hval : (∑ i, (w i : EReal) * a i) ≠ ⊥) :
    w ∈ coordinateFace τ s (Finset.univ.filter fun i => a i ≠ ⊥) := by
  classical
  refine ⟨hw, ?_⟩
  intro i hi
  have hpole : a i = ⊥ := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  apply le_antisymm _ (hw.1.1 i)
  exact le_of_not_gt (fun hpos => hval
    (sum_weighted_eq_bot_of_pole a w ha hw.1.1 i hpole hpos))
end LP

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The pure real cut is EXACTLY the original feasible source simplex. -/
theorem feasibleWeights_iff_cut (D : PiecewiseLinearData θ) (s : ℝ) (w : Fin (D.N + 1) → ℝ) :
    w ∈ feasibleWeights D s ↔ w ∈ SGPT.Convex.CutSimplex.cut D.τ s := by
  rw [SGPT.Convex.CutSimplex.mem_cut_iff]
  constructor
  · intro hw
    exact ⟨fun i => (hw.1 i).1, hw.2.1, hw.2.2⟩
  · rintro ⟨hw, hsum, hbary⟩
    exact ⟨fun i => mem_Icc_of_mem_stdSimplex (show w ∈ stdSimplex ℝ _ from ⟨hw, hsum⟩) i, hsum, hbary⟩

/-- Every actual vertex returned by the LP is genuinely feasible in D. -/
theorem vertexVector_feasible (D : PiecewiseLinearData θ) (s : ℝ)
    (v : SGPT.Convex.CutSimplex.VertexIndex D.τ s) :
    SGPT.Convex.CutSimplex.vertexVector D.τ s v ∈ feasibleWeights D s :=
  (feasibleWeights_iff_cut D s _).mpr (SGPT.Convex.CutSimplex.vertexVector_isExtreme D.τ s v).1

/-- The WHOLE source simplex supremum is an attained actual vertex maximum,
including zero weights, arbitrary common poles, N=0 and every spatial n. -/
theorem simplexValue_attained_vertex (D : PiecewiseLinearData θ) (s : ℝ) (hs : s ≤ D.τ 0) (x : M) :
    ∃ v : SGPT.Convex.CutSimplex.VertexIndex D.τ s,
      simplexValue D s x = weightedValue D (SGPT.Convex.CutSimplex.vertexVector D.τ s v) x := by
  classical
  let a : Fin (D.N + 1) → EReal := fun i => D.A i x
  have ha : ∀ i, a i ≠ ⊤ := fun i => (D.isThetaPSH i).1 x
  let J := Finset.univ.filter fun i => a i ≠ ⊥
  by_cases hfinite : ∃ w ∈ feasibleWeights D s, weightedValue D w x ≠ ⊥
  · obtain ⟨w, hw, hwfinite⟩ := hfinite
    have hwface := LP.mem_coordinateFace_of_weighted_ne_bot D.τ s a ha
      ((feasibleWeights_iff_cut D s w).mp hw) hwfinite
    obtain ⟨v, hvface, hvmax⟩ := SGPT.Convex.CutSimplex.exists_vertex_coordinateFace_max
      D.τ D.strictAnti.injective (fun i => (a i).toReal) s J ⟨w, hwface⟩
    refine ⟨v, le_antisymm ?_ ?_⟩
    · apply iSup_le
      intro u
      apply iSup_le
      intro hu
      by_cases hubot : weightedValue D u x = ⊥
      · rw [hubot]
        exact bot_le
      have huface := LP.mem_coordinateFace_of_weighted_ne_bot D.τ s a ha
        ((feasibleWeights_iff_cut D s u).mp hu) hubot
      have hureal := LP.weighted_eq_coe_objective_on_face D.τ s a ha huface
      have hvreal := LP.weighted_eq_coe_objective_on_face D.τ s a ha hvface
      change (∑ i, (u i : EReal) * a i) ≤ _
      rw [hureal]
      change _ ≤ (∑ i, ((SGPT.Convex.CutSimplex.vertexVector D.τ s v) i : EReal) * a i)
      rw [hvreal]
      exact EReal.coe_le_coe_iff.mpr (hvmax u huface)
    · exact le_iSup_of_le _ (le_iSup_of_le (vertexVector_feasible D s v) le_rfl)
  · let v : SGPT.Convex.CutSimplex.VertexIndex D.τ s := Sum.inl ⟨0, hs⟩
    refine ⟨v, ?_⟩
    have hbot : ∀ w ∈ feasibleWeights D s, weightedValue D w x = ⊥ := by
      intro w hw
      by_contra hne
      exact hfinite ⟨w, hw, hne⟩
    rw [hbot _ (vertexVector_feasible D s v)]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    exact le_of_eq (hbot w hw)

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
