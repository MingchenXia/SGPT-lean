import SGPT.Checks.Comparison.BJAsmSectionGF
import SGPT.Checks.Comparison.BJNativeLogNorm
import SGPT.IGood.DXMainTensorMetric

/-! The ACTUAL original tensor line bundles, tensor metrics and rational
Chern forms, narrowly source-ported without a second GF hull namespace.
Blueprint: trace-na-general-family.tex. No conclusion certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.GFTwist
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

private theorem actual_closed_form_roundtrip {q : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel q) Y] [IsComplexManifold q Y]
    (α : ClosedRealOneOneForm q Y) :
    atlasClosedFormToNative (nativeClosedFormToAtlas α) = α := by
  rcases α with ⟨α,hα⟩
  cases α
  rfl

section Classes

variable {X : Scheme.{0}} {M H : X.Modules} (b : LineBundleAtlas M) (bH : LineBundleAtlas H)

/-- The line bundle `M^{⊗ q} ⊗ H^{⊗ r}`. -/
abbrev twistLine (M H : X.Modules) (q r : ℕ) : X.Modules :=
  bundleTensor (bundleTensorPower M q) (bundleTensorPower H r)

/-- The atlas of `M^{⊗ q} ⊗ H^{⊗ r}` by tensor frames. -/
def twistLineAtlas (q r : ℕ) : LineBundleAtlas (twistLine M H q r) :=
  pairwiseTensorAtlas (b.tensorPower q) (bH.tensorPower r)

/-- `[M^{⊗ q} ⊗ H^{⊗ r}] = q [M] + r [H]` in `Pic(X) ⊗ ℚ`. -/
theorem rationalPicardClass_twistLineAtlas (q r : ℕ) :
    rationalPicardClass (twistLineAtlas b bH q r) =
      q • rationalPicardClass b + r • rationalPicardClass bH := by
  unfold twistLineAtlas
  rw [Assembly.rationalPicardClass_pairwiseTensor,
    rationalPicardClass_atlas_independent (b.tensorPower q) (powerAtlas b q),
    rationalPicardClass_atlas_independent (bH.tensorPower r) (powerAtlas bH r),
    rationalPicardClass_power, rationalPicardClass_power]

/-- **`L + ε [H] = (m q)⁻¹ [M^{⊗ q} ⊗ H^{⊗ m p}]`** for `L = m⁻¹ [M]` and `ε = p/q`. -/
theorem rationalPicardClass_twist {m : ℕ} (hm : 0 < m) (ε : ℚ) (hε : 0 ≤ ε) :
    (((m * ε.den : ℕ) : ℚ))⁻¹ • rationalPicardClass (twistLineAtlas b bH ε.den (m * ε.num.toNat)) =
      (m : ℚ)⁻¹ • rationalPicardClass b + ε • rationalPicardClass bH := by
  rw [rationalPicardClass_twistLineAtlas, smul_add, ← Nat.cast_smul_eq_nsmul ℚ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqQ : (ε.den : ℚ) ≠ 0 := by exact_mod_cast ε.den_pos.ne'
  have hnum : ((ε.num.toNat : ℕ) : ℚ) = (ε.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hε)
  congr 2
  · push_cast
    field_simp
  · push_cast
    rw [hnum]
    nth_rewrite 3 [← Rat.num_div_den ε]
    field_simp

end Classes

/-! ### Metrics and atlas forms -/

section Forms

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxzSurjClassesPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxzSurjClassesPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable [IsSeparated f] [QuasiCompact f]

local instance dxzSurjClassesPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {M H : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)
  (bH : LineBundleAtlas H) (HH : SchemeLineBundleMetric f n E H)

/-- The product metric `h_M^{⊗ q} ⊗ h_H^{⊗ r}` on `M^{⊗ q} ⊗ H^{⊗ r}`. -/
def twistLineMetric (q r : ℕ) : SchemeLineBundleMetric f n E (twistLine M H q r) :=
  (HM.tensorPower b q).tensorProduct (HH.tensorPower bH r) (b.tensorPower q) (bH.tensorPower r)

/-- The atlas form `θ + ε ω_H`, `ω_H = c₁(H, h_H)`. -/
def twistForm (θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))) (ε : ℝ) :
    AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f)) :=
  nativeClosedFormToAtlas (atlasClosedFormToNative θ + ε • HH.curvature bH)

theorem twistForm_native (θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f)))
    (ε : ℝ) :
    atlasClosedFormToNative (twistForm f n E bH HH θ ε) =
      atlasClosedFormToNative θ + ε • HH.curvature bH :=
  actual_closed_form_roundtrip _

/-- `c₁(M^{⊗ q} ⊗ H^{⊗ r}) = q c₁(M, h_M) + r c₁(H, h_H)` on every chart target. -/
theorem curvature_twistLineMetric (q r : ℕ) (c : LineBundleAtlas (twistLine M H q r)) :
    ((twistLineMetric f n E b HM bH HH q r).curvature c).val.GeometricallyEq
      ((q : ℝ) • HM.curvature b + (r : ℝ) • HH.curvature bH).val := by
  intro e u hu
  have h1 := (HM.tensorPower b q).curvature_tensorProduct (HH.tensorPower bH r) (b.tensorPower q)
    (bH.tensorPower r) c e hu
  have h2 := HM.curvature_tensorPower b q e hu
  have h3 := HH.curvature_tensorPower bH r e hu
  change (((HM.tensorPower b q).tensorProduct (HH.tensorPower bH r) (b.tensorPower q)
    (bH.tensorPower r)).curvature c).val.coeff e u = _
  rw [h1, ClosedRealOneOneForm.coeff_add, h2, h3, ClosedRealOneOneForm.coeff_add]

/-- **`θ + ε ω_H = (m q)⁻¹ c₁(M^{⊗ q} ⊗ H^{⊗ m p})`** on every chart target, for
`θ = m⁻¹ c₁(M, h_M)` and `ε = p/q`. -/
theorem twistForm_geometricallyEq {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (ε : ℚ) (hε : 0 ≤ ε) :
    (atlasClosedFormToNative (twistForm f n E bH HH θ (ε : ℝ))).val.GeometricallyEq
      ((((m * ε.den : ℕ) : ℝ))⁻¹ •
        (twistLineMetric f n E b HM bH HH ε.den (m * ε.num.toNat)).curvature
          (twistLineAtlas b bH ε.den (m * ε.num.toNat))).val := by
  intro e u hu
  have hc := curvature_twistLineMetric f n E b HM bH HH ε.den (m * ε.num.toNat)
    (twistLineAtlas b bH ε.den (m * ε.num.toNat)) e hu
  have ht := hθ e hu
  rw [twistForm_native]
  change (atlasClosedFormToNative θ + (ε : ℝ) • HH.curvature bH).val.coeff e u =
    (((m * ε.den : ℕ) : ℝ))⁻¹ •
      ((twistLineMetric f n E b HM bH HH ε.den (m * ε.num.toNat)).curvature
        (twistLineAtlas b bH ε.den (m * ε.num.toNat))).val.coeff e u
  change (atlasClosedFormToNative θ).val.coeff e u =
    (((m : ℝ)⁻¹) • HM.curvature b).val.coeff e u at ht
  rw [hc, ClosedRealOneOneForm.coeff_add, ht, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul, smul_add, smul_smul,
    smul_smul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqR : (ε.den : ℝ) ≠ 0 := by exact_mod_cast ε.den_pos.ne'
  have hnum : ((ε.num.toNat : ℕ) : ℝ) = (ε.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hε)
  have hεR : ((ε : ℚ) : ℝ) = (ε.num : ℝ) / (ε.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  congr 2
  · push_cast
    field_simp
  · push_cast
    rw [hnum, hεR]
    field_simp

end Forms

end SGPT.NAPotential.TraceComparison.GFTwist
