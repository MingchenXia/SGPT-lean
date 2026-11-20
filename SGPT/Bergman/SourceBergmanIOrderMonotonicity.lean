import SGPT.Bergman.SourceGammaIOrderEmbedding

/-!
# BergmanIOrderMonotonicity

Source `rmk:Bergman:L797`: if `φ ⪯_I ψ` then `β^k_{v,φ,μ} ≤ β^k_{v,ψ,μ}` for all `k ≥ 1`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.IdealOrderMonotonicity
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  {φ ψ : X → EReal} (hI : sourceIOrder (ofFixedModel n X) φ ψ) (k : ℕ) (hk : 0 < k)

set_option backward.isDefEq.respectTransparency false in
include hI hk in
/-- ALL original norm-admissible literal Gamma sections embed with the SAME value.
The target is the natural all-QPSH same-formula extension when psi lacks positive ordinary mass. -/
theorem sourcePartialBergmanDensity_mono (x : W.carrier) :
    sourcePartialBergmanDensity L T W μ k φ x ≤ sourcePartialBergmanDensity L T W μ k ψ x := by
  unfold sourcePartialBergmanDensity
  refine iSup_le (fun s => iSup_le (fun hs => ?_))
  let t := originalGammaIOrderInclusion L T hI k hk s
  have ht : weightedL2Norm (twistedPower L T k).Fiber k W.erealWeight μ
      (literalTwistedMultiplierSectionEquiv L T k ψ t).val ≤ 1 := by
    rw [originalGammaIOrderInclusion_L2Norm]
    exact hs
  have hd := originalGammaIOrderInclusion_density L T hI k hk W s x
  exact hd ▸ le_iSup_of_le t (le_iSup_of_le ht le_rfl)

include hI hk in
/-- The TRUE original zero extensions preserve the original density order at every point of X. -/
theorem sourcePartialBergmanDensityOnX_mono (x : X) :
    sourcePartialBergmanDensityOnX L T W μ k φ x ≤ sourcePartialBergmanDensityOnX L T W μ k ψ x := by
  by_cases hx : x ∈ W.carrier
  · exact (sourcePartialBergmanDensityOnX_in L T W μ k φ ⟨x, hx⟩).trans_le
      ((sourcePartialBergmanDensity_mono L T W μ hI k hk ⟨x, hx⟩).trans_eq
        (sourcePartialBergmanDensityOnX_in L T W μ k ψ ⟨x, hx⟩).symm)
  · rw [sourcePartialBergmanDensityOnX_out L T W μ k φ hx,
      sourcePartialBergmanDensityOnX_out L T W μ k ψ hx]

include hI hk in
/-- SAME original normalization, SAME original mu and actual withDensity give the original beta order on K. -/
theorem sourcePartialBergmanMeasureOnK_mono :
    sourcePartialBergmanMeasureOnK L T W μ k φ ≤ sourcePartialBergmanMeasureOnK L T W μ k ψ := by
  unfold sourcePartialBergmanMeasureOnK
  have h := withDensity_mono (μ := μ)
    (Filter.Eventually.of_forall (sourcePartialBergmanDensity_mono L T W μ hI k hk))
  exact _root_.smul_le_smul_left _ h


include hI hk in
/-- Source `rmk:Bergman:L797`: if `φ ⪯_I ψ` then `β^k_{v,φ,μ} ≤ β^k_{v,ψ,μ}` for every `k ≥ 1`. -/
theorem sourcePartialBergmanMeasure_mono :
    sourcePartialBergmanMeasure L T W μ k φ ≤ sourcePartialBergmanMeasure L T W μ k ψ := by
  exact Measure.map_mono (sourcePartialBergmanMeasureOnK_mono L T W μ hI k hk) measurable_subtype_coe

end SGPT.Bergman.IdealOrderMonotonicity
