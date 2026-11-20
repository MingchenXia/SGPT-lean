import SGPT.Checks.Comparison.TraceNativeImagePoint

/-! Literal stalk readback at the ACTUAL native image semi-valuation.
Blueprint: `trace-native-image-valuation.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance traceStalkImageTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceStalkImageCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceStalkImageManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {m : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)
  {E : Set Z} (Φ : DivisorFlattening (m := m) E z) (t : ℝ) (ht : 0 < t)

/-- The original stalk specialization and the ACTUAL field-point residue
embedding give EXACTLY the original composed holomorphic germ fraction map. -/
theorem nativeFieldPoint_stalk_factor :
    (BerkovichPoint.specializationMap
      (nativeImagePoint_support_specializes f n G hG z Φ t ht)) ≫
        fieldEmb (nativeFieldPoint f n G hG z) =
      CommRingCat.ofHom ((algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1))))).comp
        (stalkToPrimeGerm f n G hG z)) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (schemeComplexPointImage f (G z)))).mp
  rw [BerkovichPoint.specializationMap, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  change Spec.map (fieldEmb (nativeFieldPoint f n G hG z)) ≫
    X.fromSpecResidueField (fieldPt (nativeFieldPoint f n G hG z)) = nativeFieldPoint f n G hG z
  exact spec_fieldEmb _

/-- The value on an actual ambient stalk element, with its actual support
specialization manufactured internally, is its SAME native germ value. -/
theorem nativeImagePoint_valAt_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z))) :
    letI := nativeFieldComplexAlgebra f n G hG z
    (nativeImagePoint f n G hG z Φ t ht).valAt
      ((BerkovichPoint.specializationMap
        (nativeImagePoint_support_specializes f n G hG z Φ t ht)).hom a) =
      fractionRealValuation Φ t ht
        (algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1))))
          (stalkToPrimeGerm f n G hG z a)) := by
  let := nativeFieldComplexAlgebra f n G hG z
  change fractionRealValuation Φ t ht
    ((fieldEmb (nativeFieldPoint f n G hG z)).hom
      ((BerkovichPoint.specializationMap
        (nativeImagePoint_support_specializes f n G hG z Φ t ht)).hom a)) = _
  exact congrArg (fractionRealValuation Φ t ht)
    (congrArg (fun q : X.presheaf.stalk (schemeComplexPointImage f (G z)) ⟶
      CommRingCat.of (FractionRing (HolGerm (ComplexModel (m+1)))) => q.hom a)
        (nativeFieldPoint_stalk_factor f n G hG z Φ t ht))

/-- EXACT original scaled normal order on the entire actual ambient stalk,
including zero germs and non-dominant analytic restrictions. -/
theorem nativeImagePoint_toENNReal_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z))) :
    toENNReal ((nativeImagePoint f n G hG z Φ t ht).valAt
      ((BerkovichPoint.specializationMap
        (nativeImagePoint_support_specializes f n G hG z Φ t ht)).hom a)) =
      ENNReal.ofReal t * (normalOrder Φ (stalkToPrimeGerm f n G hG z a) : ℝ≥0∞) := by
  let := nativeFieldComplexAlgebra f n G hG z
  rw [nativeImagePoint_valAt_stalk]
  exact fractionRealValuation_algebraMap Φ t ht _

/-- The produced image valuation is nonnegative on EVERY actual ambient
stalk germ at the literal original image point. -/
theorem nativeImagePoint_valAt_stalk_nonneg
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z))) :
    0 ≤ (nativeImagePoint f n G hG z Φ t ht).valAt
      ((BerkovichPoint.specializationMap
        (nativeImagePoint_support_specializes f n G hG z Φ t ht)).hom a) := by
  let := nativeFieldComplexAlgebra f n G hG z
  rw [nativeImagePoint_valAt_stalk]
  exact fractionRealValuation_algebraMap_nonneg Φ t ht _

end SGPT.NAPotential.TraceComparison.NativeImage
