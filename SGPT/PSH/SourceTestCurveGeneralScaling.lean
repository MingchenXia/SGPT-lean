import SGPT.PSH.SourceTestCurveGeneralLaws
import SGPT.PSH.SourceTestCurveScalingAlgebra
import SGPT.PSH.SourceNAPositiveScaling

/-! # Positive scaling of arbitrary original test-curve suprema

The genuine cross-background least-upper-bound property and the intrinsic
positive-scaling adjunction give equality of entire original curves. The final
theorem combines this arbitrary-family result with the three existing finite
rescaling identities, retaining their exact full-background casts.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [ConnectedSpace M] in
/-- The original real cutoff bound manufactures the bound for the actual scaled family. -/
theorem sourceTestCurvePositiveScaledFamily_bddAbove {I : Type*}
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max))
    {c : ℝ} (hc : 0 < c) :
    BddAbove (range fun i => ((Γ i).positiveScale hc).max) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨c * B, ?_⟩
  rintro _ ⟨i, rfl⟩
  change c * (Γ i).max ≤ c * B
  exact mul_le_mul_of_nonneg_left (hB (mem_range_self i)) hc.le

omit [ConnectedSpace M] in
/-- Actual strict-slice scaling gives an adjunction across arbitrary original backgrounds. -/
theorem SourceTestCurvePOrder.positiveScale_le_iff_unscale
    {Γ : SourceTestCurve θ} {Δ : SourceTestCurve σ} {c : ℝ} (hc : 0 < c) :
    SourceTestCurvePOrder (Γ.positiveScale hc) Δ ↔
      SourceTestCurvePOrder Γ (Δ.positiveScale (inv_pos.mpr hc)) := by
  constructor
  · intro h
    have hcut : Γ.max ≤ (Δ.positiveScale (inv_pos.mpr hc)).max := by
      have hm := mul_le_mul_of_nonneg_left h.cutoff_le (inv_pos.mpr hc).le
      simpa only [SourceTestCurve.positiveScale_max, ← mul_assoc,
        inv_mul_cancel₀ hc.ne', one_mul] using hm
    refine ⟨hcut, ?_⟩
    intro r hr
    have hcr : c * r < (Γ.positiveScale hc).max :=
      mul_lt_mul_of_pos_left hr hc
    have h1 : c * r / c = r := by field_simp [hc.ne']
    have h2 : r / c⁻¹ = c * r := by rw [div_inv_eq_mul]; ring
    have hp := sourcePOrder_positiveScaling (h.slice_le (c * r) hcr) (inv_pos.mpr hc)
    simpa only [SourceTestCurve.positiveScale_potential, h1, h2, ← mul_assoc,
      ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul] using hp
  · intro h
    have hcut : (Γ.positiveScale hc).max ≤ Δ.max := by
      have hm := mul_le_mul_of_nonneg_left h.cutoff_le hc.le
      simpa only [SourceTestCurve.positiveScale_max, ← mul_assoc,
        mul_inv_cancel₀ hc.ne', one_mul] using hm
    refine ⟨hcut, ?_⟩
    intro r hr
    have hrc : r / c < Γ.max := (div_lt_iff₀ hc).mpr (by
      change r < c * Γ.max at hr
      nlinarith)
    have h1 : (r / c) / c⁻¹ = r := by
      rw [div_inv_eq_mul]
      exact div_mul_cancel₀ r hc.ne'
    have hp := sourcePOrder_positiveScaling (h.slice_le (r / c) hrc) hc
    simpa only [SourceTestCurve.positiveScale_potential, h1, ← mul_assoc,
      ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul] using hp

/-- Positive scaling commutes with the actual arbitrary-family original supremum. -/
theorem SourceTestCurve.generalSup_positiveScale {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) {c : ℝ} (hc : 0 < c) :
    (SourceTestCurve.generalSup omega Γ hb).positiveScale hc =
      SourceTestCurve.generalSup omega (fun i => (Γ i).positiveScale hc)
        (sourceTestCurvePositiveScaledFamily_bddAbove Γ hb hc) := by
  apply SourceTestCurvePOrder.antisymm omega
  · apply (SourceTestCurvePOrder.positiveScale_le_iff_unscale hc).mpr
    apply SourceTestCurve.generalSup_le_cross_background omega Γ hb
    intro i
    exact (SourceTestCurvePOrder.positiveScale_le_iff_unscale hc).mp
      (SourceTestCurve.le_generalSup omega (fun i => (Γ i).positiveScale hc)
        (sourceTestCurvePositiveScaledFamily_bddAbove Γ hb hc) i)
  · exact SourceTestCurve.generalSup_le omega (fun i => (Γ i).positiveScale hc)
      (sourceTestCurvePositiveScaledFamily_bddAbove Γ hb hc) _
      (fun i => (SourceTestCurve.le_generalSup omega Γ hb i).positiveScale hc)

/-- All FOUR original prop:resclacompat clauses, retaining the actual whole background casts. -/
theorem source_test_curve_rescaling_compatibility_whole {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (G : SourceTestCurve θ) (D : SourceTestCurve σ)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max))
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (C : ℝ) :
    (((SourceTestCurve.sum omega G D).positiveScale hc).castBackground
        (sourceTCScaledSumBackground_eq θ σ c) =
      SourceTestCurve.sum omega (G.positiveScale hc) (D.positiveScale hc)) ∧
    (((G.positiveScale hd).positiveScale hc).castBackground
        (sourceTCScaledCompositionBackground_eq θ c d) = G.positiveScale (mul_pos hc hd)) ∧
    ((G.translate C).positiveScale hc = (G.positiveScale hc).translate (c * C)) ∧
    ((SourceTestCurve.generalSup omega Γ hb).positiveScale hc =
      SourceTestCurve.generalSup omega (fun i => (Γ i).positiveScale hc)
        (sourceTestCurvePositiveScaledFamily_bddAbove Γ hb hc)) :=
  ⟨SourceTestCurve.positiveScale_sum omega G D hc,
    SourceTestCurve.positiveScale_positiveScale G hc hd,
    SourceTestCurve.positiveScale_translate G hc C,
    SourceTestCurve.generalSup_positiveScale omega Γ hb hc⟩

end SGPT.PSH.VariableComplexAtlas

#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurvePositiveScaledFamily_bddAbove
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurvePOrder.positiveScale_le_iff_unscale
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.generalSup_positiveScale
#print axioms SGPT.PSH.VariableComplexAtlas.source_test_curve_rescaling_compatibility_whole
