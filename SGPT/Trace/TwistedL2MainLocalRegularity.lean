import SGPT.Trace.TwistedL2MainLocalWeak
import SGPT.Trace.TwistedL2MainLocalWeyl

/-!
# Holomorphic local representatives of the actual correction

The only hypotheses below are the actual Hilbert test equations. The global
section gluing and the producer of those equations remain separate tasks.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- Subtracting the actual L² correction from G has a holomorphic local
representative, once the genuine local adjoint-test equations are known. -/
theorem exists_holomorphic_chart_representative
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (htest : ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing)
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F (T.pieceDomain c e) ∧
      ∀ᵐ z ∂(volume.restrict (T.pieceDomain c e)),
        chartCoeff T.L c e T.G z - T.correctionFrameCoeff u e (c.val.symm z) = F z := by
  apply exists_holomorphic_local_representative (T.isOpen_pieceDomain c e)
    (T.continuousOn_localH1Weight c e hρ)
    ((T.G_smooth c e).of_le (by norm_num))
    (T.memLp_chartCorrectionCoeff u c e hρ)
  exact T.weakDbarEq_chartCorrectionCoeff u htest c e hρ


/-- The local representative describes the actual bundle-valued difference
`G - correction` almost everywhere for the original manifold measure on the
corresponding chart piece. -/
theorem exists_chart_representative_ae_manifold
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (htest : ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing)
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F (T.pieceDomain c e) ∧
      ∀ᵐ x ∂((T.μ.restrict c.val.source).restrict (c.val ⁻¹' T.pieceDomain c e)),
        (e.val ⟨x, T.G x - T.correctionSection u x⟩).2 = F (c.val x) := by
  obtain ⟨F, hFhol, hF⟩ := T.exists_holomorphic_chart_representative u htest c e hρ
  refine ⟨F, hFhol, ?_⟩
  let D := T.pieceDomain c e
  have hDm : MeasurableSet D := (T.isOpen_pieceDomain c e).measurableSet
  have hDt : D ⊆ c.val.target := T.pieceDomain_subset_target c e
  let ν : Measure X := (T.μ.restrict c.val.source).restrict (c.val ⁻¹' D)
  have he : AEMeasurable c.val ν :=
    (c.val.continuousOn.aemeasurable c.val.open_source.measurableSet).restrict
  have hpush : Measure.map c.val ν =
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) :=
    chartDensity_map_restrict c hρ hDm hDt
  have hFmap : ∀ᵐ z ∂(Measure.map c.val ν),
      chartCoeff T.L c e T.G z - T.correctionFrameCoeff u e (c.val.symm z) = F z := by
    rw [hpush]
    exact (withDensity_absolutelyContinuous _ _).ae_le hF
  have hDmap : ∀ᵐ z ∂(Measure.map c.val ν), z ∈ D := by
    rw [hpush]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hDm)
  have hsource : ∀ᵐ x ∂ν, x ∈ c.val.source :=
    (ae_restrict_mem c.val.open_source.measurableSet).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [ae_of_ae_map he hFmap, ae_of_ae_map he hDmap, hsource] with x hFx hxD hxs
  have hbase : x ∈ e.val.baseSet := by
    simpa only [mem_preimage, c.val.left_inv hxs] using hxD.1.2
  rw [frameCoeff_sub_apply e hbase, ← T.correctionFrameCoeff_of_mem u e hbase]
  have key : ∀ y, y = x → (e.val ⟨y, T.G y⟩).2 = (e.val ⟨x, T.G x⟩).2 := by
    rintro _ rfl; rfl
  simp only [chartCoeff, frameCoeff, key _ (c.val.left_inv hxs), c.val.left_inv hxs] at hFx
  exact hFx

end TwistedDatum
end SGPT.Trace.TwistedL2
