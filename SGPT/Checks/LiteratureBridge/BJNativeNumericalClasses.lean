import SGPT.Checks.LiteratureBridge.BJRationalPicardPresentations
import SGPT.Foundations.PublishedEnvelope.AlgGeom.NativeRealNumericalClasses
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! Actual rational Picard-to-numerical classes, with an EXPLICIT curve-weak
class topology. No usual-topology or ample-order comparison is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory Topology Filter
open Scheme.Modules SGPT.Foundations.Schemes
open SGPT.Foundations.PublishedEnvelope
open scoped TensorProduct
variable {X : Scheme.{0}}

/-- Canonical scalar extension of the SAME actual native scheme Picard group. -/
def realifyPicard : RationalPicardSpace X →ₗ[ℤ] NativeRealPicard.Space X :=
  TensorProduct.map ((Rat.castHom ℝ).toAddMonoidHom.toIntLinearMap) LinearMap.id

theorem realifyPicard_tmul (r : ℚ) (a : Additive X.Pic) :
    realifyPicard (r⊗ₜ[ℤ] a)=(r:ℝ)⊗ₜ[ℤ] a := rfl

theorem realifyPicard_rat_smul (r : ℚ) (z : RationalPicardSpace X) :
    realifyPicard (r•z)=r•realifyPicard z := map_rat_smul realifyPicard r z

/-- The atlas-generated class is exactly the SAME native real sheaf class. -/
theorem realifyPicard_line {L : X.Modules} (a : LineBundleAtlas L) :
    realifyPicard (rationalPicardClass a)=
      NativeRealPicard.lineClass L (isInvertible_of_atlas a) := by
  change realifyPicard ((1:ℚ)⊗ₜ[ℤ] Additive.ofMul (linePicardClass a))=_
  rw [realifyPicard_tmul,Rat.cast_one]
  rfl

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Actual first numerical class: canonical scalar extension, then the true
quotient by ALL actual closed-curve degrees. -/
def numericalClass : RationalPicardSpace X →ₗ[ℤ] NativeRealNumericalClasses.Space p :=
  (NativeRealNumericalClasses.projection p).restrictScalars ℤ ∘ₗ realifyPicard

theorem numericalClass_rat_smul (r : ℚ) (z : RationalPicardSpace X) :
    numericalClass p (r•z)=r•numericalClass p z := map_rat_smul (numericalClass p) r z

theorem numericalClass_line {L : X.Modules} (a : LineBundleAtlas L) :
    numericalClass p (rationalPicardClass a)=
      NativeRealNumericalClasses.lineClass p L (isInvertible_of_atlas a) := by
  change NativeRealNumericalClasses.projection p (realifyPicard (rationalPicardClass a))=_
  rw [realifyPicard_line]
  rfl

/-- Literal normalization of the SAME actual GF section-power line. -/
theorem numericalClass_gf {L : X.Modules} {n m : ℕ} (a : LineBundleAtlas L)
    (D : SGPT.NAPotential.Berkovich.BJSections.RationalGFData L n m) :
    numericalClass p (gfPicardClass a D)=
      ((n:ℚ)/(m:ℚ))•NativeRealNumericalClasses.lineClass p L (isInvertible_of_atlas a) := by
  rw [gfPicardClass,numericalClass_rat_smul,numericalClass_line]

/-- Every TRUE original closed-integral-curve degree of the actual quotient. -/
def numericalDegreeEmbedding : NativeRealNumericalClasses.Space p →ₗ[ℝ]
    (NativeClosedCurveDegrees.ClosedIntegralCurve X → ℝ) :=
  LinearMap.pi fun C => NativeRealNumericalClasses.curveDegree p C

theorem numericalDegreeEmbedding_injective : Function.Injective (numericalDegreeEmbedding p) := by
  intro x y h
  exact NativeRealNumericalClasses.ext p x y (fun C => congrFun h C)

/-- Explicit canonical curve-WEAK topology, with no identification with the
book's usual numerical-class topology or EP ample-order convergence. -/
@[instance_reducible]
def numericalCurveWeakTopology : TopologicalSpace (NativeRealNumericalClasses.Space p) :=
  TopologicalSpace.induced (numericalDegreeEmbedding p) inferInstance

theorem numericalDegreeEmbedding_isEmbedding :
    let := numericalCurveWeakTopology p
    Topology.IsEmbedding (numericalDegreeEmbedding p) := by
  exact Function.Injective.isEmbedding_induced (numericalDegreeEmbedding_injective p)

theorem numericalCurveWeakTopology_t2 :
    @T2Space (NativeRealNumericalClasses.Space p) (numericalCurveWeakTopology p) := by
  let := numericalCurveWeakTopology p
  exact (numericalDegreeEmbedding_isEmbedding p).t2Space

/-- Every directed numerical convergence assertion reads back to the true
curve degrees, without any finite-dimensionality premise. -/
theorem tendsto_numericalCurveWeak_iff {T : Type} (g : T → NativeRealNumericalClasses.Space p)
    (l : Filter T) (θ : NativeRealNumericalClasses.Space p) :
    Tendsto g l (@nhds _ (numericalCurveWeakTopology p) θ) ↔
      ∀ C : NativeClosedCurveDegrees.ClosedIntegralCurve X,
        Tendsto (fun t => NativeRealNumericalClasses.curveDegree p C (g t)) l
          (𝓝 (NativeRealNumericalClasses.curveDegree p C θ)) := by
  let := numericalCurveWeakTopology p
  rw [(numericalDegreeEmbedding_isEmbedding p).isInducing.tendsto_nhds_iff,tendsto_pi_nhds]
  rfl

end SGPT.NAPotential.BJ.NativePicard
