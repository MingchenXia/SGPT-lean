import SGPT.Trace.TwistedL2MainLocalPairing

/-!
# Change of variables for actual local test pairings

The support-controlled integral transport here is intended for the actual
H₁ inner-product integrand. Converting the two resulting weighted integrals
to the Euclidean adjoint pairing remains to be completed.
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

/-- An a.e. measurable scalar integrand supported over the actual chart piece
is transported exactly by the chart-density witness. -/
theorem integral_chart_piece (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    {f : X → ℂ} (hf : AEStronglyMeasurable f (T.μ.restrict T.U))
    (hzero : ∀ x ∉ c.val.source ∩ c.val ⁻¹' T.pieceDomain c e, f x = 0) :
    (∫ x, f x ∂(T.μ.restrict T.U)) =
      ∫ z in T.pieceDomain c e, (ρ z : ℂ) * f (c.val.symm z) := by
  let D := T.pieceDomain c e
  let S := c.val.source ∩ c.val ⁻¹' D
  have hDm : MeasurableSet D := (T.isOpen_pieceDomain c e).measurableSet
  have hDt : D ⊆ c.val.target := T.pieceDomain_subset_target c e
  have hSm : MeasurableSet S :=
    (c.val.continuousOn.isOpen_inter_preimage c.val.open_source
      (T.isOpen_pieceDomain c e)).measurableSet
  have hSU : S ⊆ T.U := by
    intro x hx
    have hxu : c.val.symm (c.val x) ∈ T.U := hx.2.2
    simpa only [c.val.left_inv hx.1] using hxu
  let ν := (T.μ.restrict c.val.source).restrict (c.val ⁻¹' D)
  have hν : (T.μ.restrict T.U).restrict S = ν := by
    dsimp only [ν]
    rw [Measure.restrict_restrict hSm, inter_eq_left.mpr hSU,
      Measure.restrict_restrict' c.val.open_source.measurableSet]
    change T.μ.restrict (c.val.source ∩ c.val ⁻¹' D) =
      T.μ.restrict (c.val ⁻¹' D ∩ c.val.source)
    rw [inter_comm]
  have hle : ν ≤ T.μ.restrict T.U := by
    rw [← hν]
    exact Measure.restrict_le_self
  have hs : AEMeasurable c.val.symm
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) :=
    ((c.val.continuousOn_symm.mono hDt).aemeasurable hDm).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map c.val.symm
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) = ν :=
    chartDensity_map_symm_restrict c hρ hDm hDt
  have hfchart : AEStronglyMeasurable (fun z => f (c.val.symm z))
      (volume.restrict D) := by
    have hfmap : AEMeasurable f (Measure.map c.val.symm (volume.restrict D)) :=
      hf.aemeasurable.mono_ac (T.inverseChart_piece_absolutelyContinuous c e hρ)
    exact (hfmap.comp_aemeasurable
      ((c.val.continuousOn_symm.mono hDt).aemeasurable hDm)).aestronglyMeasurable
  have hrho : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict D) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρ.1.continuousOn.mono hDt)).aemeasurable hDm
  have hind : f = S.indicator f := by
    ext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  calc
    (∫ x, f x ∂(T.μ.restrict T.U)) =
        ∫ x, S.indicator f x ∂(T.μ.restrict T.U) := by rw [← hind]
    _ = ∫ x, f x ∂((T.μ.restrict T.U).restrict S) := integral_indicator hSm
    _ = ∫ x, f x ∂ν := by rw [hν]
    _ = ∫ z, f (c.val.symm z) ∂((volume.restrict D).withDensity
          (fun z => ENNReal.ofReal (ρ z))) := by
        rw [← hmap]
        have hfm : AEStronglyMeasurable f (Measure.map c.val.symm
            ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)))) := by
          rw [hmap]
          exact hf.mono_measure hle
        exact integral_map hs hfm
    _ = ∫ z in D, (ρ z : ℂ) * f (c.val.symm z) := by
        rw [integral_withDensity_eq_integral_toReal_smul₀ hrho
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hDm] with z hz
        simp [ENNReal.toReal_ofReal (hρ.2.1 z (hDt hz)).le, Complex.real_smul]


/-- The Hilbert pairing of an actual local test adjoint and the actual L²
correction is the corresponding chart weighted integral. -/
theorem inner_tstar_eq_chart_integral
    (u : Lp ℂ 2 (T.μ.restrict T.U)) (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    {h : ComplexModel n → ComplexModel n} (hh : IsLocalTestField T.L T.U c e h) :
    ⟪T.tstarL2 hρ hh, u⟫_ℂ =
      ∫ z in T.pieceDomain c e,
        conj (T.pieceTheta c e ρ h z) * T.correctionFrameCoeff u e (c.val.symm z) *
          (Real.exp (-T.localH1Weight c e ρ z) : ℂ) := by
  let f : X → ℂ := fun x =>
    conj (T.H1coord (T.localTStar c e ρ h) x) * (u : X → ℂ) x
  have hf : AEStronglyMeasurable f (T.μ.restrict T.U) :=
    (Complex.continuous_conj.measurable.comp
      (T.measurable_H1coord_localTStar hρ hh)).aestronglyMeasurable.mul (Lp.memLp u).1
  have hzero : ∀ x ∉ c.val.source ∩ c.val ⁻¹' T.pieceDomain c e, f x = 0 := by
    intro x hx
    have hK : x ∉ pieceSupport c h := by
      intro hxK
      exact hx ⟨hxK.1, hh.2.2 hxK.2⟩
    simp [f, H1coord, T.localTStar_eq_zero hK]
  calc
    ⟪T.tstarL2 hρ hh, u⟫_ℂ = ∫ x, f x ∂(T.μ.restrict T.U) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(T.memLp_H1coord_localTStar hρ hh).coeFn_toLp] with x hx
      simp only [RCLike.inner_apply, tstarL2, hx, f, mul_comm]
    _ = ∫ z in T.pieceDomain c e, (ρ z : ℂ) * f (c.val.symm z) :=
      T.integral_chart_piece c e hρ hf hzero
    _ = ∫ z in T.pieceDomain c e,
        conj (T.pieceTheta c e ρ h z) * T.correctionFrameCoeff u e (c.val.symm z) *
          (Real.exp (-T.localH1Weight c e ρ z) : ℂ) := by
      refine setIntegral_congr_fun (T.isOpen_pieceDomain c e).measurableSet fun z hz => ?_
      have hsource : c.val.symm z ∈ c.val.source := c.val.map_target hz.1.1
      have hp := T.H1coord_localTStar_pairing u c e ρ h hz.2 ⟨hsource, hz.1.2⟩
      rw [c.val.right_inv hz.1.1] at hp
      rw [show f (c.val.symm z) =
        conj (T.H1coord (T.localTStar c e ρ h) (c.val.symm z)) *
          (u : X → ℂ) (c.val.symm z) by rfl, hp,
        T.exp_neg_localH1Weight c e hρ hz]
      push_cast
      ring

end TwistedDatum
end SGPT.Trace.TwistedL2
