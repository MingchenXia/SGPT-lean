import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation

set_option autoImplicit false

/-!
# Translation by varying finite constants

A finite scalar translation may vary along the indexing filter.  Its variation
contributes at most the volume of the chart compactum times the scalar error,
which tends to zero when the scalars converge.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Translating the two extended-real values by possibly different finite
constants costs at most the absolute difference of those constants. -/
theorem canonicalERealAbsDiff_add_coe_add_coe_le
    (a b : EReal) (c d : ℝ) :
    canonicalERealAbsDiff (a + (c : EReal)) (b + (d : EReal)) ≤
      canonicalERealAbsDiff a b + ENNReal.ofReal |c - d| := by
  cases a with
  | bot =>
      cases b <;>
        simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  | top =>
      cases b <;>
        simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  | coe a =>
      cases b with
      | bot => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
      | top => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
      | coe b =>
          simp only [← EReal.coe_add, canonicalERealAbsDiff_coe_coe]
          calc
            ENNReal.ofReal |a + c - (b + d)| ≤
                ENNReal.ofReal (|a - b| + |c - d|) :=
              ENNReal.ofReal_le_ofReal <| by
                calc
                  |a + c - (b + d)| = |(a - b) + (c - d)| := by ring_nf
                  _ ≤ |a - b| + |c - d| := abs_add_le _ _
            _ = ENNReal.ofReal |a - b| + ENNReal.ofReal |c - d| :=
              ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- On a chart compactum, different finite translations cost at most the
compactum's volume times the scalar translation error. -/
theorem chartL1EDistance_add_coe_add_coe_le
    (u v : M → EReal) (c d : ℝ) (e : ComplexChart n M)
    (K : Set (ComplexModel n)) :
    chartL1EDistance (fun x => u x + (c : EReal))
        (fun x => v x + (d : EReal)) e K ≤
      chartL1EDistance u v e K +
        ENNReal.ofReal |c - d| * volume K := by
  rw [chartL1EDistance, chartL1EDistance]
  calc
    (∫⁻ z in K, canonicalERealAbsDiff
        (chartFunction (fun x => u x + (c : EReal)) e z)
        (chartFunction (fun x => v x + (d : EReal)) e z) ∂volume) ≤
        ∫⁻ z in K, canonicalERealAbsDiff
          (chartFunction u e z) (chartFunction v e z) +
            ENNReal.ofReal |c - d| ∂volume := by
      apply lintegral_mono
      intro z
      exact canonicalERealAbsDiff_add_coe_add_coe_le
        (chartFunction u e z) (chartFunction v e z) c d
    _ = (∫⁻ z in K, canonicalERealAbsDiff
          (chartFunction u e z) (chartFunction v e z) ∂volume) +
          ∫⁻ _z in K, ENNReal.ofReal |c - d| ∂volume := by
      rw [lintegral_add_right _ measurable_const]
    _ = (∫⁻ z in K, canonicalERealAbsDiff
          (chartFunction u e z) (chartFunction v e z) ∂volume) +
          ENNReal.ofReal |c - d| * volume K := by
      rw [lintegral_const]
      simp

/-- Chart-local `L¹` convergence is stable under a convergent family of finite
translations. -/
theorem ManifoldL1LocallyTendsto.add_tendsto_const {α : Type*}
    {u : α → M → EReal} {l : Filter α} {v : M → EReal}
    {c : α → ℝ} {d : ℝ}
    (hu : ManifoldL1LocallyTendsto (n := n) u l v)
    (hc : Tendsto c l (𝓝 d)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun i x => u i x + (c i : EReal)) l
      (fun x => v x + (d : EReal)) := by
  intro e K hK hKe
  have hscalar_real : Tendsto (fun i => |c i - d|) l (𝓝 0) := by
    have hd : Tendsto (fun _ : α => d) l (𝓝 d) := tendsto_const_nhds
    simpa using (hc.sub hd).abs
  have hscalar : Tendsto (fun i => ENNReal.ofReal |c i - d|) l (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hscalar_real
  have hvolume : volume K ≠ ∞ := hK.measure_ne_top
  have herr : Tendsto
      (fun i => ENNReal.ofReal |c i - d| * volume K) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hscalar (Or.inr hvolume)
  have hbound : Tendsto
      (fun i => chartL1EDistance (u i) v e K +
        ENNReal.ofReal |c i - d| * volume K) l (𝓝 0) := by
    simpa using (hu e K hK hKe).add herr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) fun i => ?_
  exact chartL1EDistance_add_coe_add_coe_le (u i) v (c i) d e K

end

end SGPT.Foundations.Analysis.FirstPass
