import SGPT.Checks.Comparison.TraceNativeIdealValue

/-! The ACTUAL native trivial image, in EVERY target dimension.
Blueprint: `trace-native-trivial.tex`. No target algebraization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeTrivial

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal Classical

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsProper f]
local instance traceTrivialImageTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceTrivialImageCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceTrivialImageManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {k : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)

/-- The original algebraic stalk, the actual holomorphic comap and the SAME
centered chart yield an actual WHOLE ring homomorphism. -/
def stalkToGerm :
    X.presheaf.stalk (schemeComplexPointImage f (G z)) →+* HolGerm (ComplexModel k) :=
  (NativeHolGerm.chartEquiv z).toRingHom.comp
    ((NativeHolGerm.comap G hG z).comp (schemeNativeStalkGerm f n (G z)))

/-- Every actual original holomorphic representative has its unchanged
literal pullback germ in the same original centered chart. -/
theorem stalkToGerm_mk
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z)))
    {u : SchemeComplexPoint f → ℂ} (hu : HolomorphicAt n u (G z))
    (ha : schemeNativeStalkGerm f n (G z) a = NativeHolGerm.mk u hu) :
    stalkToGerm f n G hG z a =
      NativeHolGerm.chartEquiv z (NativeHolGerm.mk (u ∘ G)
        (hu.comp_contMDiff (Eventually.of_forall fun w => hG w))) := by
  change NativeHolGerm.chartEquiv z
    (NativeHolGerm.comap G hG z (schemeNativeStalkGerm f n (G z) a)) = _
  rw [ha]
  rfl

/-- The actual field-valued point of the ORIGINAL ambient scheme. Its
actual support is produced by Spec; non-dominant restrictions are allowed. -/
def fieldPoint : Spec (.of (FractionRing (HolGerm (ComplexModel k)))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap _ (FractionRing (HolGerm (ComplexModel k)))).comp
      (stalkToGerm f n G hG z))) ≫ X.fromSpecStalk (schemeComplexPointImage f (G z))

/-- The ACTUAL base map endows the SAME fraction field with its genuine
complex algebra structure; no constant-map equality is assumed. -/
@[instance_reducible] def fieldComplexAlgebra :
    Algebra ℂ (FractionRing (HolGerm (ComplexModel k))) :=
  (Spec.preimage (fieldPoint f n G hG z ≫ f)).hom.toAlgebra

/-- The SAME original field-valued point is literally over the original
complex base. This dictionary is produced by Spec's actual full faithfulness. -/
theorem fieldPoint_over :
    letI := fieldComplexAlgebra f n G hG z
    fieldPoint f n G hG z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (HolGerm (ComplexModel k))))) := by
  change fieldPoint f n G hG z ≫ f =
    Spec.map (Spec.preimage (fieldPoint f n G hG z ≫ f))
  exact (Spec.map_preimage _).symm

/-- The ACTUAL ambient image of the native trivial valuation, in EVERY
native dimension, including zero. -/
def point : BerkovichPoint f := by
  classical
  letI := fieldComplexAlgebra f n G hG z
  exact fieldBerkovichPoint f (fieldPoint f n G hG z)
    (fieldPoint_over f n G hG z) SourceRealValuation.trivial

/-- Its support is the actual image of the same native field-valued point. -/
theorem point_support : (point f n G hG z).support = fieldPt (fieldPoint f n G hG z) := rfl

/-- The actual support specializes to the literal original image point. -/
theorem point_support_specializes :
    (point f n G hG z).support ⤳ schemeComplexPointImage f (G z) := by
  let q := (Spec.map (CommRingCat.ofHom
    ((algebraMap _ (FractionRing (HolGerm (ComplexModel k)))).comp
      (stalkToGerm f n G hG z)))) (IsLocalRing.closedPoint _)
  have hs := (IsLocalRing.specializes_closedPoint q).map
    (X.fromSpecStalk (schemeComplexPointImage f (G z))).continuous
  change (X.fromSpecStalk (schemeComplexPointImage f (G z))) q ⤳ schemeComplexPointImage f (G z)
  simpa only [Scheme.fromSpecStalk_closedPoint] using hs

/-- The actual Spec residue embedding and original stalk map compose to
precisely the actual native holomorphic germ fraction map. -/
theorem fieldPoint_stalk_factor :
    (BerkovichPoint.specializationMap (point_support_specializes f n G hG z)) ≫
      fieldEmb (fieldPoint f n G hG z) =
      CommRingCat.ofHom ((algebraMap _ (FractionRing (HolGerm (ComplexModel k)))).comp
        (stalkToGerm f n G hG z)) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (schemeComplexPointImage f (G z)))).mp
  rw [BerkovichPoint.specializationMap, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  change Spec.map (fieldEmb (fieldPoint f n G hG z)) ≫
    X.fromSpecResidueField (fieldPt (fieldPoint f n G hG z)) = fieldPoint f n G hG z
  exact spec_fieldEmb _

/-- EXACT original stalk readback at the actual native trivial image. -/
theorem point_valAt_stalk
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z))) :
    (point f n G hG z).valAt
      ((BerkovichPoint.specializationMap (point_support_specializes f n G hG z)).hom a) =
      if stalkToGerm f n G hG z a = 0 then (⊤ : WithTop ℝ) else 0 := by
  classical
  let := fieldComplexAlgebra f n G hG z
  change SourceRealValuation.trivial
    ((fieldEmb (fieldPoint f n G hG z)).hom
      ((BerkovichPoint.specializationMap (point_support_specializes f n G hG z)).hom a)) = _
  rw [show (fieldEmb (fieldPoint f n G hG z)).hom
      ((BerkovichPoint.specializationMap (point_support_specializes f n G hG z)).hom a) =
    algebraMap _ (FractionRing (HolGerm (ComplexModel k))) (stalkToGerm f n G hG z a) from
      congrArg (fun q : X.presheaf.stalk (schemeComplexPointImage f (G z)) ⟶
        CommRingCat.of (FractionRing (HolGerm (ComplexModel k))) => q.hom a)
          (fieldPoint_stalk_factor f n G hG z)]
  simp only [SourceRealValuation.trivial, map_eq_zero_iff _ (IsFractionRing.injective _ _)]

/-- Every original stalk element has a nonnegative actual trivial value. -/
theorem point_valAt_stalk_nonneg
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z))) :
    0 ≤ (point f n G hG z).valAt
      ((BerkovichPoint.specializationMap (point_support_specializes f n G hG z)).hom a) := by
  classical
  rw [point_valAt_stalk]
  split_ifs <;> simp


/-- The produced actual center is an actual generization of the native image. -/
theorem point_center_specializes :
    (point f n G hG z).center ⤳ schemeComplexPointImage f (G z) :=
  NativeImage.center_specializes_of_nonneg _ (point_support_specializes f n G hG z)
    (point_valAt_stalk_nonneg f n G hG z)

/-- Every affine section has its exact zero-or-infinite trivial image value. -/
theorem point_idealVal (U : X.affineOpens)
    (hU : schemeComplexPointImage f (G z) ∈ (U : X.Opens)) (J : X.IdealSheafData) :
    (point f n G hG z).idealVal J =
      ⨅ r ∈ J.ideal U, if stalkToGerm f n G hG z
        ((X.presheaf.germ (U : X.Opens) _ hU).hom r) = 0 then ⊤ else 0 := by
  classical
  have hc : (point f n G hG z).center ∈ (U : X.Opens) :=
    (point_center_specializes f n G hG z).mem_open (U : X.Opens).isOpen hU
  rw [BerkovichPoint.idealVal_eq_iInf_sectionVal _ J U hc]
  refine iInf_congr fun r => iInf_congr fun _ => ?_
  rw [← BerkovichPoint.valAt_specializationMap_germ _
    (point_support_specializes f n G hG z) _ hU r, point_valAt_stalk]
  split_ifs <;> simp

end SGPT.NAPotential.TraceComparison.NativeTrivial
