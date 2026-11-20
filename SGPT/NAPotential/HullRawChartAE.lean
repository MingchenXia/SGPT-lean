import SGPT.NAPotential.HullRawFiniteNodes
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

/-! Genuine original-chart a.e. simplex-to-raw comparison from the actual
source nodes' quasi-psh finiteness. No incoming polar-null certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Original source θ-psh nodes internally produce the actual chartwise a.e.
comparison with the unchanged raw envelope, in all dimensions and node counts. -/
theorem simplexValue_le_pointwiseUpperConcaveEnvelope_ae_chart
    (D : PiecewiseLinearData θ) (s : ℝ) (e : ComplexChart n M) :
    ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
      simplexValue D s (e.val.symm z) ≤ D.pointwiseUpperConcaveEnvelope s (e.val.symm z) := by
  have hfinite : ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
      ∀ i, D.A i (e.val.symm z) ≠ ⊥ := by
    rw [ae_all_iff]
    intro i
    have hn := (isThetaPSH_iff_nativeThetaPotential θ (D.A i)).mp (D.isThetaPSH i)
    exact (hn.quasiPshPotential.ae_finite_chart e).mono fun _ hz => hz.2
  filter_upwards [hfinite] with z hz
  exact simplexValue_le_pointwiseUpperConcaveEnvelope_of_nodes_ne_bot D s (e.val.symm z) hz
end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
