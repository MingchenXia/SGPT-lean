import SGPT.Trace.BertiniUniversalCutoffMeasurable

/-! Actual Tonelli -> AE finite literal original tangential cutoff residue
integral, from genuine global original multiplier sections. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

theorem ae_originalCutoffResidue_tangent_integral_lt_top
    (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {C : Set (ComplexModel (k + 1))} (hC : IsCompact C) (hCb : C ⊆ ball c.ζ₀ c.r)
    (β : X → ℝ) (hβc : Continuous β) (hβ : HasCompactSupport β) (hβle : ∀ x, β x ≤ 1)
    (hsource : ∀ ζ ∈ C, tsupport β ⊆ c.originalSliceAmbientSource ζ)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) :
    ∀ᵐ ζ ∂(volume.restrict C),
      (∫⁻ b : ComplexModel d, originalCutoffResidueSourceDensity p c L T.val β
        (fun x => multiplierWeight 1 (φ x)) (prodModelEquiv (k + 1) d (ζ,b))) < ⊤ := by
  let F := originalCutoffResidueSourceDensity p c L T.val β (fun x => multiplierWeight 1 (φ x))
  let E := prodModelEquiv (k + 1) d
  let G : ComplexModel (k + 1) × ComplexModel d → ℝ≥0∞ := fun u => F (E u)
  have hF : Measurable F := measurable_originalCutoffResidueSourceDensity p c a ha L T.val β hβc
    (fun x => multiplierWeight 1 (φ x)) (lowerSemicontinuous_originalMultiplierWeight hφ.1)
  have hG : Measurable G := hF.comp E.continuous.measurable
  have hmass := originalCutoffResidueSource_integral_lt_top p c a ha L hC hCb β hβ hβle hsource hφ T μ hμ
  have himage : E '' (C ×ˢ (univ : Set (ComplexModel d))) =
      (fun z : ComplexModel (k + 1 + d) => (E.symm z).1) ⁻¹' C := by
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      change (E.symm (E u)).1 ∈ C
      rw [E.symm_apply_apply]
      exact hu.1
    · intro hz
      exact ⟨E.symm z,⟨hz,mem_univ _⟩,E.apply_symm_apply z⟩
  have hemb : MeasurableEmbedding E := E.toHomeomorph.measurableEmbedding
  have heq : (∫⁻ z in (fun z : ComplexModel (k + 1 + d) => (E.symm z).1) ⁻¹' C, F z) =
      ∫⁻ u, G u ∂((volume : Measure (ComplexModel (k + 1))).restrict C).prod volume := by
    rw [← himage,← (ProductMixedMeasure.measurePreserving_prodModelEquiv (k + 1) d).setLIntegral_comp_emb hemb,
      ← Measure.prod_restrict]
    simp only [Measure.restrict_univ]
    rfl
  have hprod : (∫⁻ u, G u ∂((volume : Measure (ComplexModel (k + 1))).restrict C).prod volume) < ⊤ := heq ▸ hmass
  have hiter : (∫⁻ ζ, (∫⁻ b : ComplexModel d, G (ζ,b)) ∂volume.restrict C) < ⊤ := by
    rw [← lintegral_prod _ hG.aemeasurable]
    exact hprod
  exact ae_lt_top (hG.lintegral_prod_right') (ne_top_of_lt hiter)

end SGPT.Trace.BertiniUniversal
