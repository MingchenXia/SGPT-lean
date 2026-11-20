import SGPT.Foundations.Analysis.Pending.PshRepresentative
import SGPT.Foundations.Analysis.Pending.QuasiPshAlmostEverywhereComparison

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.QuasiPshPositiveLeviRepresentative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Positive Levi identifies the original genuine quasi-PSH function, retaining its actual poles. -/
theorem plurisubharmonicOn_of_nonnegative_distributionalLevi
    {Ω : Opens E} {u : E → EReal} (hu : QuasiPlurisubharmonicOn u Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (huf : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥)
    (huL : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ)
    (hLevi : HasNonnegativeDistributionalLevi
      (regularDistribution μ (fun x => (u x).toReal) huL)) :
    PlurisubharmonicOn u Ω := by
  obtain ⟨v, hvP, hvf, hvL, hvT⟩ := exists_pshRepresentative μ hLevi
  have hreal := ae_eq_of_regularDistribution_eq μ huL hvL hvT
  have hae : u =ᵐ[μ.restrict Ω] v := by
    filter_upwards [huf, hvf, hreal] with x hux hvx hx
    rw [← EReal.coe_toReal hux.1 hux.2, ← EReal.coe_toReal hvx.1 hvx.2, hx]
  have heq := QuasiPshAlmostEverywhereComparison.eqOn_of_ae_eq hu
    (fun x hx => (hvP x hx).quasiPlurisubharmonicAt) Ω.isOpen μ hae
  intro x hx
  apply (hvP x hx).congr
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  exact (heq hy).symm

end SGPT.Foundations.Analysis.Pending.QuasiPshPositiveLeviRepresentative
