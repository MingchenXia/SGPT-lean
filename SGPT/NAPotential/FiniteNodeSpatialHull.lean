import SGPT.NAPotential.FiniteNodeMaximumPSH
import SGPT.NAPotential.HullSourceRegularization
import SGPT.NAPotential.HullRawChartAE

/-! The source spatial USC identity, retaining its literal raw LCE at poles. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

theorem affine_nodes_le_simplexValue (D : PiecewiseLinearData θ)
    (i j : Fin (D.N+1)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (x : M) :
    (a:EReal)*D.A i x+(b:EReal)*D.A j x ≤ simplexValue D (a*D.τ i+b*D.τ j) x := by
  have hi := vertexWeights_mem D i le_rfl
  have hj := vertexWeights_mem D j le_rfl
  have hm := mixedWeights_mem D hi hj ha hb hab
  have he := weightedValue_mixedWeights D x a b (vertexWeights i) (vertexWeights j)
    ha hb (fun k => (hi.1 k).1) (fun k => (hj.1 k).1)
  rw [weightedValue_vertex, weightedValue_vertex] at he
  rw [← he]
  exact le_iSup_of_le _ (le_iSup_of_le hm le_rfl)

/-- Genuine domination of the original curve by the canonical simplex,
proved using its actual segment weights. -/
theorem curve_le_simplexValue (D : PiecewiseLinearData θ) (s : ℝ) (x : M) :
    D.curve s x ≤ simplexValue D s x := by
  by_cases h : D.τ 0 < s
  · rw [D.curve_of_lt h]
    exact bot_le
  unfold curve
  rw [dif_neg h]
  split_ifs with hi
  · let i := D.segIndex s (not_lt.mp h)
    let j := D.nextIdx i hi
    have hjs : D.τ j < s := D.tau_lt_of_segIndex_lt s _ (D.lt_nextIdx i hi)
    have his : s ≤ D.τ i := D.le_tau_segIndex s _
    have hd : 0 < D.τ i-D.τ j := by linarith
    let t := D.param i hi s
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr his) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hparam : (1-t)*D.τ i+t*D.τ j=s := by
      dsimp [t, param]
      change (1-(D.τ i-s)/(D.τ i-D.τ j))*D.τ i+
        ((D.τ i-s)/(D.τ i-D.τ j))*D.τ j=s
      field_simp [hd.ne']
      ring
    have hc := affine_nodes_le_simplexValue D i j (1-t) t (sub_nonneg.mpr ht1) ht0 (by ring) x
    rw [hparam] at hc
    exact hc
  · exact node_le_simplexValue D _ (D.le_tau_segIndex s _) x

/-- The unchanged raw concave envelope is globally dominated by the actual
simplex, including polar points where equality may fail. -/
theorem pointwiseUpperConcaveEnvelope_le_simplexValue (D : PiecewiseLinearData θ) (s : ℝ) (x : M) :
    D.pointwiseUpperConcaveEnvelope s x ≤ simplexValue D s x :=
  D.pointwiseUpperConcaveEnvelope_le (simplexValue D) (simplexValue_concave D)
    (curve_le_simplexValue D) s x

theorem pointwiseUpperConcaveEnvelope_eq_simplexValue_of_nodes_ne_bot
    (D : PiecewiseLinearData θ) (s : ℝ) (x : M) (hx : ∀ i,D.A i x≠⊥) :
    D.pointwiseUpperConcaveEnvelope s x = simplexValue D s x :=
  le_antisymm (pointwiseUpperConcaveEnvelope_le_simplexValue D s x)
    (simplexValue_le_pointwiseUpperConcaveEnvelope_of_nodes_ne_bot D s x hx)

/-- Exactly the printed spatial upper-regularization identity, with no
change to the raw pointwise LCE and no incoming polar/null certificate. -/
theorem uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue
    (D : PiecewiseLinearData θ) (s : ℝ) :
    uscRegularization (D.pointwiseUpperConcaveEnvelope s) = simplexValue D s := by
  by_cases hs : s ≤ D.τ 0
  · apply SGPT.PSH.VariableComplexAtlas.WholeClosureNA.HullAnalytic.uscRegularization_eq_of_sourceThetaPSH_of_ae_chart_eq (isThetaPSH_simplexValue D s hs)
      (pointwiseUpperConcaveEnvelope_le_simplexValue D s)
    intro e
    filter_upwards [simplexValue_le_pointwiseUpperConcaveEnvelope_ae_chart D s e] with z hz
    exact le_antisymm (pointwiseUpperConcaveEnvelope_le_simplexValue D s _) hz
  · have hb : simplexValue D s = fun _ => ⊥ := by
      funext x
      exact simplexValue_eq_bot_of_lt_first D (lt_of_not_ge hs) x
    have hf : D.pointwiseUpperConcaveEnvelope s = fun _ => ⊥ := by
      funext x
      apply le_antisymm _ bot_le
      have h := pointwiseUpperConcaveEnvelope_le_simplexValue D s x
      simpa only [hb] using h
    rw [hf,hb,uscRegularization_const]

/-- The first corrected node stays exactly the original first potential. -/
theorem simplexValue_first (D : PiecewiseLinearData θ) (x : M) :
    simplexValue D (D.τ 0) x=D.A 0 x := by
  obtain ⟨v,hv⟩ := simplexValue_attained_vertex D (D.τ 0) le_rfl x
  rw [hv]
  cases v with
  | inl i =>
    have hi : i.val=0 := D.strictAnti.injective (le_antisymm (D.tau_le_tau_zero i.val) i.property)
    change weightedValue D (SGPT.Convex.CutSimplex.basis i.val) x = _
    rw [weightedValue_basis,hi]
  | inr p => exact (not_lt_of_ge (D.tau_le_tau_zero p.val.1) p.property.2).elim

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
