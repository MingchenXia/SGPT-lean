import SGPT.IGood.DXMainTensorMetric
import SGPT.Checks.Comparison.BJAsmSectionGF
import SGPT.PSH.SourceIGoodBackground

/-! ACTUAL mixed rational tensor line/atlas/metric/Chern for original sums.
No caller tensor/class/normalization certificate.
Blueprint: operation-sum-chern-data.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard

abbrev sumTensorLine {X : Scheme.{0}} (M N : X.Modules) (m q : ℕ) : X.Modules :=
  bundleTensor (bundleTensorPower M q) (bundleTensorPower N m)

def sumTensorAtlas {X : Scheme.{0}} {M N : X.Modules}
    (b : LineBundleAtlas M) (c : LineBundleAtlas N) (m q : ℕ) :
    LineBundleAtlas (sumTensorLine M N m q) :=
  pairwiseTensorAtlas (b.tensorPower q) (c.tensorPower m)

/-- Equality in the SAME original RATIONAL Picard space, not only numerical classes. -/
theorem sumTensor_rationalClass {X : Scheme.{0}} {M N : X.Modules}
    (b : LineBundleAtlas M) (c : LineBundleAtlas N) {m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    ((m*q : ℕ) : ℚ)⁻¹ • rationalPicardClass (sumTensorAtlas b c m q) =
      (m : ℚ)⁻¹ • rationalPicardClass b + (q : ℚ)⁻¹ • rationalPicardClass c := by
  unfold sumTensorAtlas
  rw [Assembly.rationalPicardClass_pairwiseTensor,
    rationalPicardClass_atlas_independent (b.tensorPower q) (powerAtlas b q),
    rationalPicardClass_atlas_independent (c.tensorPower m) (powerAtlas c m),
    rationalPicardClass_power,rationalPicardClass_power,
    smul_add,← Nat.cast_smul_eq_nsmul ℚ,← Nat.cast_smul_eq_nsmul ℚ,smul_smul,smul_smul]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  congr 2 <;> push_cast <;> field_simp

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
variable [IsSeparated f] [QuasiCompact f]
local instance sumChernPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance sumChernPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance sumChernPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {M N : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)
  (c : LineBundleAtlas N) (HN : SchemeLineBundleMetric f n E N)

def sumTensorMetric (m q : ℕ) : SchemeLineBundleMetric f n E (sumTensorLine M N m q) :=
  (HM.tensorPower b q).tensorProduct (HN.tensorPower c m) (b.tensorPower q) (c.tensorPower m)

omit [IsSeparated f] [QuasiCompact f] in
/-- Genuine curvature of the ACTUAL original mixed tensor metric and atlas. -/
theorem sumTensorMetric_curvature (m q : ℕ) :
    ((sumTensorMetric f n E b HM c HN m q).curvature (sumTensorAtlas b c m q)).val.GeometricallyEq
      ((q : ℝ) • HM.curvature b + (m : ℝ) • HN.curvature c).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  have ht := (HM.tensorPower b q).curvature_tensorProduct (HN.tensorPower c m)
    (b.tensorPower q) (c.tensorPower m) (sumTensorAtlas b c m q) e hu
  have hM := HM.curvature_tensorPower b q e hu
  have hN := HN.curvature_tensorPower c m e hu
  change (((HM.tensorPower b q).tensorProduct (HN.tensorPower c m)
    (b.tensorPower q) (c.tensorPower m)).curvature (sumTensorAtlas b c m q)).val.coeff e u = _
  rw [ht,ClosedRealOneOneForm.coeff_add,hM,hN,ClosedRealOneOneForm.coeff_add]

/-- Original TWO primitive Chern hypotheses internally give the SAME actual
summed atlas form's tensor Chern hypothesis at denominator m*q. -/
theorem sumTensor_geometricallyEq {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (hσ : (atlasClosedFormToNative σ).val.GeometricallyEq (((q : ℝ)⁻¹) • HN.curvature c).val) :
    (atlasClosedFormToNative (θ.add σ)).val.GeometricallyEq
      ((((m*q : ℕ) : ℝ))⁻¹ •
        (sumTensorMetric f n E b HM c HN m q).curvature (sumTensorAtlas b c m q)).val := by
  intro e u hu
  have hc := sumTensorMetric_curvature f n E b HM c HN m q e hu
  have hθc := hθ e hu
  have hσc := hσ e hu
  rw [sourceNativeClosedForm_add]
  change (atlasClosedFormToNative θ + atlasClosedFormToNative σ).val.coeff e u =
    (((m*q : ℕ) : ℝ))⁻¹ •
      ((sumTensorMetric f n E b HM c HN m q).curvature (sumTensorAtlas b c m q)).val.coeff e u
  change (atlasClosedFormToNative θ).val.coeff e u =
    (((m : ℝ)⁻¹) • HM.curvature b).val.coeff e u at hθc
  change (atlasClosedFormToNative σ).val.coeff e u =
    (((q : ℝ)⁻¹) • HN.curvature c).val.coeff e u at hσc
  rw [hc,ClosedRealOneOneForm.coeff_add,hθc,hσc,
    ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_smul,ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_smul,smul_add,smul_smul,smul_smul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  congr 2 <;> push_cast <;> field_simp

end SGPT.NAPotential.OperationComparison
