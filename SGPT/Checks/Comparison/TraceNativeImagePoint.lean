import SGPT.Checks.Comparison.TraceNativeGermValuation

/-! The ACTUAL ambient image semi-valuation of a SAME native analytic prime.
Blueprint: `trace-native-image-valuation.tex`. No target algebraization or
ambient dominance premise, and no kernel/support certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance traceImageTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceImageCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceImageManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {m : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)

/-- The original algebraic stalk, the actual holomorphic comap and the SAME
centered chart yield an actual WHOLE ring homomorphism. -/
def stalkToPrimeGerm :
    X.presheaf.stalk (schemeComplexPointImage f (G z)) →+* HolGerm (ComplexModel (m+1)) :=
  (NativeHolGerm.chartEquiv z).toRingHom.comp
    ((NativeHolGerm.comap G hG z).comp (schemeNativeStalkGerm f n (G z)))

/-- Every actual original holomorphic representative has its unchanged
literal pullback germ in the same original centered chart. -/
theorem stalkToPrimeGerm_mk
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z)))
    {u : SchemeComplexPoint f → ℂ} (hu : HolomorphicAt n u (G z))
    (ha : schemeNativeStalkGerm f n (G z) a = NativeHolGerm.mk u hu) :
    stalkToPrimeGerm f n G hG z a =
      NativeHolGerm.chartEquiv z (NativeHolGerm.mk (u ∘ G)
        (hu.comp_contMDiff (Eventually.of_forall fun w => hG w))) := by
  change NativeHolGerm.chartEquiv z
    (NativeHolGerm.comap G hG z (schemeNativeStalkGerm f n (G z) a)) = _
  rw [ha]
  rfl

/-- The actual field-valued point of the ORIGINAL ambient scheme. Its
actual support is produced by Spec; non-dominant restrictions are allowed. -/
def nativeFieldPoint : Spec (.of (FractionRing (HolGerm (ComplexModel (m+1))))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1))))).comp
      (stalkToPrimeGerm f n G hG z))) ≫ X.fromSpecStalk (schemeComplexPointImage f (G z))

/-- The ACTUAL base map endows the SAME fraction field with its genuine
complex algebra structure; no constant-map equality is assumed. -/
@[instance_reducible] def nativeFieldComplexAlgebra :
    Algebra ℂ (FractionRing (HolGerm (ComplexModel (m+1)))) :=
  (Spec.preimage (nativeFieldPoint f n G hG z ≫ f)).hom.toAlgebra

/-- The SAME original field-valued point is literally over the original
complex base. This dictionary is produced by Spec's actual full faithfulness. -/
theorem nativeFieldPoint_over :
    letI := nativeFieldComplexAlgebra f n G hG z
    nativeFieldPoint f n G hG z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (HolGerm (ComplexModel (m+1)))))) := by
  change nativeFieldPoint f n G hG z ≫ f =
    Spec.map (Spec.preimage (nativeFieldPoint f n G hG z ≫ f))
  exact (Spec.map_preimage _).symm

/-- The ACTUAL original ambient image semi-valuation. It uses the SAME
native prime flattening and positive scalar, and no algebraic target model. -/
def nativeImagePoint {E : Set Z} (Φ : DivisorFlattening (m := m) E z)
    (t : ℝ) (ht : 0 < t) : BerkovichPoint f :=
  letI := nativeFieldComplexAlgebra f n G hG z
  fieldBerkovichPoint f (nativeFieldPoint f n G hG z)
    (nativeFieldPoint_over f n G hG z) (fractionRealValuation Φ t ht)

/-- The support is the true Spec image of the same actual native field point. -/
theorem nativeImagePoint_support {E : Set Z} (Φ : DivisorFlattening (m := m) E z)
    (t : ℝ) (ht : 0 < t) :
    (nativeImagePoint f n G hG z Φ t ht).support = fieldPt (nativeFieldPoint f n G hG z) := rfl

/-- The ACTUAL support specializes to the literal image point; no supplied
center/support certificate or dominance assertion. -/
theorem nativeImagePoint_support_specializes {E : Set Z} (Φ : DivisorFlattening (m := m) E z)
    (t : ℝ) (ht : 0 < t) :
    (nativeImagePoint f n G hG z Φ t ht).support ⤳ schemeComplexPointImage f (G z) := by
  let q := (Spec.map (CommRingCat.ofHom
    ((algebraMap _ (FractionRing (HolGerm (ComplexModel (m+1))))).comp
      (stalkToPrimeGerm f n G hG z)))) (IsLocalRing.closedPoint _)
  have hs := (IsLocalRing.specializes_closedPoint q).map
    (X.fromSpecStalk (schemeComplexPointImage f (G z))).continuous
  change (X.fromSpecStalk (schemeComplexPointImage f (G z))) q ⤳ schemeComplexPointImage f (G z)
  simpa only [Scheme.fromSpecStalk_closedPoint] using hs

end SGPT.NAPotential.TraceComparison.NativeImage
