import SGPT.Checks.Comparison.OperationPotentialScaling
import SGPT.Checks.Comparison.SourceDXZPOrder
import SGPT.PSH.SourceNAPositiveScaling

/-! Actual open-slice analytification covariance, independent of a line
presentation of the scaled class. Blueprint: operation-correspondence-scaling.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]
local instance opCurveScalePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opCurveScalePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opCurveScalePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- Exactly the original open-slice formula, applied to an actual curve;
naPotentialAnAt is this formula on its actual component. -/
def openCurveAnAt (C : SourceTestCurve θ) (v : BerkovichPoint f) : EReal :=
  ⨆ τ : Iio C.max, potentialAn n E (C.potential τ) v + ((τ : ℝ) : EReal)

omit [BorelSpace (SchemeComplexPoint f)] in
/-- Mutual original intrinsic curve order preserves the SAME actual
multiplier-ideal analytification supremum, across different backgrounds. -/
theorem openCurveAnAt_eq_of_POrder_equivalent {C : SourceTestCurve θ}
    {D : SourceTestCurve σ} (hCD : SourceTestCurvePOrder C D)
    (hDC : SourceTestCurvePOrder D C) (v : BerkovichPoint f) :
    openCurveAnAt n E C v = openCurveAnAt n E D v := by
  unfold openCurveAnAt
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have hs : (τ : ℝ) < D.max := τ.2.trans_le hCD.cutoff_le
    rw [SGPT.NAPotential.BJ.SourceDXZPOrder.potentialAn_eq_of_curvePOrder_equivalent
      n E hCD hDC τ τ.2 hs]
    exact le_iSup (fun r : Iio D.max =>
      potentialAn n E (D.potential r) v + ((r : ℝ) : EReal)) ⟨τ,hs⟩
  · refine iSup_le fun τ => ?_
    have hs : (τ : ℝ) < C.max := τ.2.trans_le hDC.cutoff_le
    rw [SGPT.NAPotential.BJ.SourceDXZPOrder.potentialAn_eq_of_curvePOrder_equivalent
      n E hDC hCD τ τ.2 hs]
    exact le_iSup (fun r : Iio C.max =>
      potentialAn n E (C.potential r) v + ((r : ℝ) : EReal)) ⟨τ,hs⟩

omit [ConnectedSpace (SchemeComplexPoint f)] in
/-- ALL real positive rescalings of the SAME original curve have the
literal pointwise scaled formula on EVERY original Berkovich point. -/
theorem openCurveAnAt_positiveScale (C : SourceTestCurve θ)
    {c : ℝ} (hc : 0 < c) (v : BerkovichPoint f) :
    openCurveAnAt n E (C.positiveScale hc) v = (c : EReal) * openCurveAnAt n E C v := by
  let e : Iio C.max ≃ Iio (C.positiveScale hc).max := {
    toFun τ := ⟨c * τ, by change c * (τ : ℝ) < c * C.max; exact mul_lt_mul_of_pos_left τ.2 hc⟩
    invFun r := ⟨(r : ℝ) / c, by
      apply (div_lt_iff₀ hc).mpr
      have h := r.2
      change (r : ℝ) < c * C.max at h
      simpa only [mul_comm] using h⟩
    left_inv τ := by apply Subtype.ext; change c * (τ : ℝ) / c = (τ : ℝ); field_simp
    right_inv r := by apply Subtype.ext; change c * ((r : ℝ) / c) = (r : ℝ); field_simp }
  unfold openCurveAnAt
  rw [← e.iSup_comp]
  calc
    (⨆ τ : Iio C.max, potentialAn n E ((C.positiveScale hc).potential (e τ)) v +
      (((e τ : Iio (C.positiveScale hc).max) : ℝ) : EReal)) =
      ⨆ τ : Iio C.max, (c : EReal) *
        (potentialAn n E (C.potential τ) v + ((τ : ℝ) : EReal)) := by
      apply iSup_congr
      intro τ
      rw [SourceTestCurve.positiveScale_potential]
      have hindex : (⟨((e τ : Iio (C.positiveScale hc).max) : ℝ) / c,
          by have h := (e τ).2; change ((e τ : Iio (C.positiveScale hc).max) : ℝ) < c * C.max at h
             exact (div_lt_iff₀ hc).mpr (by nlinarith)⟩ : Iio C.max) = τ := by
        apply Subtype.ext
        change c * (τ : ℝ) / c = (τ : ℝ)
        field_simp
      rw [hindex, potentialAn_positiveScale n E
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (C.thetaPSH τ)) hc]
      rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top c)]
      change (c : EReal) * potentialAn n E (C.potential τ) v + ((c * (τ : ℝ) : ℝ) : EReal) = _
      rw [EReal.coe_mul]
    _ = (c : EReal) * (⨆ τ : Iio C.max,
        potentialAn n E (C.potential τ) v + ((τ : ℝ) : EReal)) := by
      exact (_root_.map_iSup (sourcePositiveERealOrderIso c hc) _).symm

end SGPT.NAPotential.OperationComparison
