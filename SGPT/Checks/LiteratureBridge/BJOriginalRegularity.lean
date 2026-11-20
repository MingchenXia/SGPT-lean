import SGPT.Checks.LiteratureBridge.BJNativeGFBridge
import SGPT.Foundations.PublishedEnvelope.AlgGeom.NativeNumericalFSContinuity

/-! Actual original rational GF continuity, all-point USC and finite
generic trivial-point values for the unchanged arbitrary-universe nets.
No singular PSH2, previous-predicate equivalence or additional whole credit. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.PublishedEnvelope
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Genuine original whole-section functions are continuous everywhere,
including common-zero poles, by the exact actual native model-norm map. -/
theorem RationalGFPackage.continuous_eval (D : RationalGFPackage X) :
    Continuous (D.eval p) := by
  have h := (D.toNative.continuous_eval p).comp (continuous_toNative p)
  apply h.congr
  intro v
  exact D.toNative_eval p v

/-- Actual nonzero original sections attain the common weight bound at
the SAME generic trivial point, without replacing the support. -/
theorem RationalGFPackage.eval_le_trivial (D : RationalGFPackage X)
    (v : BerkovichPoint p) : D.eval p v ≤ D.eval p (BerkovichPoint.trivial p) := by
  change (((1/(D.m:ℝ)):ℝ):EReal)*finiteMaximum D.atlas D.data v ≤
    (((1/(D.m:ℝ)):ℝ):EReal)*finiteMaximum D.atlas D.data (BerkovichPoint.trivial p)
  rw [finiteMaximum_trivial]
  exact mul_le_mul_of_nonneg_left (finiteMaximum_le_weightMaximum D.atlas D.data v)
    (EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg _)))

theorem DecreasingGFNet.limit_upperSemicontinuous (D : DecreasingGFNet.{u} p) :
    UpperSemicontinuous (D.limit p) :=
  upperSemicontinuous_iInf fun i => ((D.term i).continuous_eval p).upperSemicontinuous

theorem DecreasingGFNet.limit_le_trivial (D : DecreasingGFNet.{u} p)
    (v : BerkovichPoint p) : D.limit p v ≤ D.limit p (BerkovichPoint.trivial p) := by
  exact iInf_mono fun i => (D.term i).eval_le_trivial p v

/-- All-point upper semicontinuity is produced by actual original GF data;
it is not inserted as a field of the printed definition. -/
theorem IsPSHForNumericalTopology.upperSemicontinuous
    {t : TopologicalSpace (NativeRealNumericalClasses.Space p)}
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsPSHForNumericalTopology.{u} p t L φ) : UpperSemicontinuous φ := by
  obtain ⟨_,D,_,rfl⟩ := (isPSHForNumericalTopology_iff_inf p t L φ).mp h
  exact D.limit_upperSemicontinuous p

theorem IsPSHForNumericalTopology.le_trivial
    {t : TopologicalSpace (NativeRealNumericalClasses.Space p)}
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsPSHForNumericalTopology.{u} p t L φ) (v : BerkovichPoint p) :
    φ v ≤ φ (BerkovichPoint.trivial p) := by
  obtain ⟨_,D,_,rfl⟩ := (isPSHForNumericalTopology_iff_inf p t L φ).mp h
  exact D.limit_le_trivial p v

theorem IsPSHForNumericalTopology.trivial_ne_bot
    {t : TopologicalSpace (NativeRealNumericalClasses.Space p)}
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsPSHForNumericalTopology.{u} p t L φ) : φ (BerkovichPoint.trivial p) ≠ ⊥ := by
  obtain ⟨v,hv⟩ := h.1
  exact ne_bot_of_le_ne_bot hv (h.le_trivial p v)

theorem IsPSHForNumericalTopology.trivial_finite
    {t : TopologicalSpace (NativeRealNumericalClasses.Space p)}
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsPSHForNumericalTopology.{u} p t L φ) :
    ∃ r : ℝ, φ (BerkovichPoint.trivial p) = (r:EReal) := by
  exact ⟨(φ (BerkovichPoint.trivial p)).toReal,
    (EReal.coe_toReal (h.ne_top p _) (h.trivial_ne_bot p)).symm⟩

theorem IsModuleTopologyPSH.upperSemicontinuous
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) : UpperSemicontinuous φ :=
  IsPSHForNumericalTopology.upperSemicontinuous p h

theorem IsModuleTopologyPSH.le_trivial
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) (v : BerkovichPoint p) :
    φ v ≤ φ (BerkovichPoint.trivial p) :=
  IsPSHForNumericalTopology.le_trivial p h v

theorem IsModuleTopologyPSH.trivial_finite
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    ∃ r : ℝ, φ (BerkovichPoint.trivial p) = (r:EReal) :=
  IsPSHForNumericalTopology.trivial_finite p h

end SGPT.NAPotential.BJ.Printed
