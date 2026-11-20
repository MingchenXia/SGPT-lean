import SGPT.Trace.BertiniUniversalCutoffMass
import SGPT.Trace.BertiniOriginalPhysicalSliceFatou

/-! Actual whole ordinary joint cutoff physical density is measurable,
proved on the genuine original source then extended by zero. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
attribute [local instance] Classical.propDecidable
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

theorem measurable_originalCutoffResidueSourceDensity
    (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber)
    (β : X → ℝ) (hβ : Continuous β) (w : X → ℝ≥0∞) (hw : LowerSemicontinuous w) :
    Measurable (originalCutoffResidueSourceDensity p c L T β w) := by
  let U := originalQSourceDomain p c
  let H : Fin 1 → HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber := fun _ => T
  have hsingle : nativeSectionCombination (OriginalAmbientPhysicalBundle p L) H (fun _ => (1 : ℂ)) = T := by
    simp [nativeSectionCombination,H]
  have hraw : Continuous (fun z : U => (prodModelEquiv (k + 1) d).symm z.val) :=
    (prodModelEquiv (k + 1) d).symm.continuous.comp continuous_subtype_val
  have hQ : Continuous (originalQSourcePair p c) :=
    (hraw.fst.subtype_mk (fun z => z.property.1)).prodMk (hraw.snd.subtype_mk (fun z => z.property.2))
  let A : U → (((Fin 1 → ℂ) × ball c.ζ₀ c.r) × c.tangentPatch) :=
    fun z => (((fun _ => 1),(originalQSourcePair p c z).1),(originalQSourcePair p c z).2)
  have hA : Continuous A := (continuous_const.prodMk hQ.fst).prodMk hQ.snd
  let f : U → ℝ≥0∞ := fun z => c.originalPhysicalCombinationSliceDensity L H β w (A z)
  have hf : Measurable f := (c.lowerSemicontinuous_originalPhysicalCombinationSliceDensity L H a ha β hβ w hw).measurable.comp hA.measurable
  have hpre : Measurable (fun z => if hz : z ∈ (U : Set _) then f ⟨z,hz⟩ else 0) :=
    hf.dite measurable_const U.isOpen.measurableSet
  have heq : (fun z => if hz : z ∈ (U : Set _) then f ⟨z,hz⟩ else 0) =
      originalCutoffResidueSourceDensity p c L T β w := by
    funext z
    by_cases hz : z ∈ (U : Set _)
    · rw [dif_pos hz]
      let q := originalQSourcePair p c ⟨z,hz⟩
      have hs : originalMemberResidueSourceDensity p c L T w z =
          ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ •
            c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w (c.tangentPoint q) := dif_pos hz
      dsimp only [f,A,SliceChart.originalPhysicalCombinationSliceDensity]
      rw [hsingle]
      unfold originalCutoffResidueSourceDensity
      rw [hs]
      change (ENNReal.ofReal (β (c.tangentPoint q)) * _) * w (c.tangentPoint q) =
        ENNReal.ofReal (β (c.tangentPoint q)) * (_ * w (c.tangentPoint q))
      exact mul_assoc _ _ _
    · rw [dif_neg hz]
      have hs : originalMemberResidueSourceDensity p c L T w z = 0 := dif_neg hz
      unfold originalCutoffResidueSourceDensity
      rw [hs,mul_zero]
  rw [← heq]
  exact hpre

end SGPT.Trace.BertiniUniversal
