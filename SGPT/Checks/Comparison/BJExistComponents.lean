import SGPT.Checks.Comparison.BJAsmVarphian
import SGPT.NAPotential.AnTransIndependence

/-!
# Components of non-Archimedean potentials in the classes `L + ε H`

Infrastructure for the existence clause of `cor:testcurvegivepshme` (`chapter_NApotential.tex`,
*The algebraic setting*). Let `L = m⁻¹ [M]` with `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)` and let
`Γ ∈ PSH^NA(X, θ)` (`SourceNAPotential θ`). The book writes `Γ^An = (Γ^{θ + m⁻¹ω})^An` with
`ω ∈ c₁(H)` and treats the component `Γ^{θ + εω}` as a test curve in the class of the
`ℚ`-line bundle `L + εH`. Here:

* `scaledFSIndex ε`: the Kähler index `ε ω_FS` (`ω_FS = c₁(𝒪_X(1), h_FS)`).
* `isThetaPshPotential_componentTwist`: if `φ ∈ PSH(X, θ + (2mq)⁻¹ ω_FS)` (a slice of the
  component of `Γ` at the index `(2mq)⁻¹ ω_FS`), then
  `m q φ ∈ PSH(X, c₁(𝒪_X(1) ⊗ M^{⊗ q}) - ½ ω_FS)`, so Siu's theorem applies to the twisted bundle
  `𝒪_X(1) ⊗ M^{⊗ q}` with the margin `½ ω_FS`.
* `multiplierIdeal_component_potential_eq`, `multiplierIdeal_component_limit_eq`: corresponding
  slices, and the limits `Γ_{-∞} = usc sup_τ Γ_τ`, of two components have the same multiplier
  ideals (the components are related by `𝓘`-projections).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.Exist

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult SGPT.NAPotential.FSPos
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ.Assembly

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance existCompPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existCompPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
section Twist

variable [IsSeparated f] [QuasiCompact f]

local instance existCompPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The Kähler index `ε ω_FS`, `ε > 0`. -/
def scaledFSIndex {ε : ℝ} (hε : 0 < ε) : SourceKahlerForm n (SchemeComplexPoint f) :=
  sourceKahlerFormOfBackground (KahlerBackground.smul hε (fsBackground f n E))

/-- `(2 m q)⁻¹ > 0`. -/
theorem twistScale_pos {m q : ℕ} (hm : 0 < m) (hq : 0 < q) : (0 : ℝ) < ((2 * m * q : ℕ) : ℝ)⁻¹ :=
  inv_pos.mpr (by exact_mod_cast Nat.mul_pos (Nat.mul_pos two_pos hm) hq)

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)

/-- **The component in the class `L + (2mq)⁻¹ H` and the twisted bundle `𝒪_X(1) ⊗ M^{⊗ q}`.**
If `θ = m⁻¹ c₁(M, h_M)` (equal coefficients in every chart) and
`φ ∈ PSH(X, θ + (2mq)⁻¹ ω_FS)` (the component background at the index `(2mq)⁻¹ ω_FS`), then
`m q φ ∈ PSH(X, c₁(𝒪_X(1) ⊗ M^{⊗ q}, h_FS ⊗ h_M^q) - ½ ω_FS)`. -/
theorem isThetaPshPotential_componentTwist {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : (ofFixedModel n (SchemeComplexPoint f)).IsThetaPSH
      (sourceNAComponentBackground θ (scaledFSIndex f n E (twistScale_pos hm hq))) φ) :
    IsThetaPshPotential ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
      ((1 : ℝ) / 2) • (fsBackground f n E).form).val
        (fun y => (((m * q : ℕ) : ℝ) : EReal) * φ y) := by
  have h0 := (isThetaPSH_iff_nativeThetaPotential _ _).mp hφ
  have h1 := TranscendentalCore.isThetaPshPotential_nonneg_smul h0
    (Nat.cast_nonneg (α := ℝ) (m * q))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hgeq : ((((m * q : ℕ) : ℝ)) • atlasClosedFormToNative
      (sourceNAComponentBackground θ (scaledFSIndex f n E (twistScale_pos hm hq)))).val.GeometricallyEq
      ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
        ((1 : ℝ) / 2) • (fsBackground f n E).form).val := by
    intro e u hu
    have hT := (fubiniStudyMetric f E n).curvature_tensorProduct (HM.tensorPower b q)
      (hyperplaneAtlas E) (b.tensorPower q) (twistAtlas f E b q) e hu
    have hP := HM.curvature_tensorPower b q e hu
    have hK : (sourceKahlerFormRepresentative
        (scaledFSIndex f n E (twistScale_pos hm hq))).form.val.coeff e u =
        (KahlerBackground.smul (twistScale_pos hm hq) (fsBackground f n E)).form.val.coeff e u :=
      sourceKahlerFormRepresentative_geometricallyEq
        (KahlerBackground.smul (twistScale_pos hm hq) (fsBackground f n E)) e hu
    have hθe := hθ e hu
    rw [sourceNAComponentBackground_native]
    change ((((m * q : ℕ) : ℝ)) • (atlasClosedFormToNative θ +
      (sourceKahlerFormRepresentative (scaledFSIndex f n E (twistScale_pos hm hq))).form)).val.coeff
        e u = ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
          ((1 : ℝ) / 2) • (fsBackground f n E).form).val.coeff e u
    rw [SGPT.PSH.GlobalL2.coeff_sub_smul, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_add]
    change _ = (((fubiniStudyMetric f E n).tensorProduct (HM.tensorPower b q) (hyperplaneAtlas E)
      (b.tensorPower q)).curvature (twistAtlas f E b q)).val.coeff e u - _
    rw [hT, ClosedRealOneOneForm.coeff_add, hP, hθe, hK]
    change (((m * q : ℕ) : ℝ)) • ((((m : ℝ)⁻¹) • HM.curvature b).val.coeff e u +
      (KahlerBackground.smul (twistScale_pos hm hq) (fsBackground f n E)).form.val.coeff e u) =
        ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff e u +
          ((q : ℝ) • HM.curvature b).val.coeff e u -
        ((1 : ℝ) / 2) • ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff e u
    rw [KahlerBackground.smul_form, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul, smul_add, smul_smul,
      smul_smul]
    have hc1 : ((m * q : ℕ) : ℝ) * (m : ℝ)⁻¹ = q := by
      push_cast
      field_simp
    have hc2 : ((m * q : ℕ) : ℝ) * ((2 * m * q : ℕ) : ℝ)⁻¹ = 1 / 2 := by
      push_cast
      field_simp
    have hF : (fsBackground f n E).form.val.coeff e u =
        ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff e u := rfl
    rw [hc1, hc2, hF]
    module
  exact (hgeq.thetaPshPotential_iff _).mp h1

end Twist

/-! ### Multiplier ideals of different components -/

section Components

variable [IsProper f]

local instance existCompPointManifold' : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)]
  [BorelSpace (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- Corresponding slices of two components of `Γ` have the same multiplier ideals. -/
theorem multiplierIdeal_component_potential_eq (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm n (SchemeComplexPoint f)) (r : ℝ)
    (hr : r < (Γ.component ω).val.max) (hs : r < (Γ.component η).val.max) {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := n) c ((Γ.component η).val.potential ⟨r, hs⟩) =
      multiplierIdeal (n := n) c ((Γ.component ω).val.potential ⟨r, hr⟩) := by
  let ζ := sourceKahlerFormCommonUpper ω η
  have hζ : r < (Γ.component ζ).val.max := by rwa [Γ.component_max_eq ζ ω]
  rw [multiplierIdeal_eq_of_sourceIEquivalent (naComponent_potential_iEquivalent_of_le n Γ
      (sourceKahlerFormLE_commonUpper_right ω η) r hs hζ) hc,
    multiplierIdeal_eq_of_sourceIEquivalent (naComponent_potential_iEquivalent_of_le n Γ
      (sourceKahlerFormLE_commonUpper_left ω η) r hr hζ) hc]

/-- For Kähler indices `ω ≤ η`, the limit `Γ^{θ+η}_{-∞}` of the component at `η` is the
`𝓘`-envelope of the limit of the component at `ω`. -/
theorem component_limit_eq_of_le (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm n (SchemeComplexPoint f)} (h : sourceKahlerFormLE ω η) :
    sourceTestCurveLimit (Γ.component η).val.toSourceTestCurvePredata =
      sourceIEnvelope (sourceNAComponentBackground θ η)
        (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) := by
  rw [← Γ.compatible ω η h]
  exact sourceIModelTestCurveTransition_limit _ _ _

/-- For Kähler indices `ω ≤ η`, the limits of the two components are `𝓘`-equivalent. -/
theorem component_limit_iEquivalent_of_le (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm n (SchemeComplexPoint f)} (h : sourceKahlerFormLE ω η) :
    sourceIEquivalent (ofFixedModel n (SchemeComplexPoint f))
      (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata)
      (sourceTestCurveLimit (Γ.component η).val.toSourceTestCurvePredata) := by
  rw [component_limit_eq_of_le f n Γ h]
  exact sourceIEquivalent_iEnvelope (sourceThetaPSH_of_semipositive_difference
    (sourceNAComponentBackground_difference θ h) (Γ.component ω).val.limit_thetaPSH)

/-- The limits of two components of `Γ` have the same multiplier ideals. -/
theorem multiplierIdeal_component_limit_eq (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm n (SchemeComplexPoint f)) {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := n) c (sourceTestCurveLimit (Γ.component η).val.toSourceTestCurvePredata) =
      multiplierIdeal (n := n) c
        (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) := by
  let ζ := sourceKahlerFormCommonUpper ω η
  rw [multiplierIdeal_eq_of_sourceIEquivalent (component_limit_iEquivalent_of_le f n Γ
      (sourceKahlerFormLE_commonUpper_right ω η)) hc,
    multiplierIdeal_eq_of_sourceIEquivalent (component_limit_iEquivalent_of_le f n Γ
      (sourceKahlerFormLE_commonUpper_left ω η)) hc]

end Components

end SGPT.NAPotential.BJ.Exist
