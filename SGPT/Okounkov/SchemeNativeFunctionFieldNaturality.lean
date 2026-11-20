import SGPT.NAPotential.ProjectiveGraphStalkNaturality
import SGPT.Okounkov.OF9RationalEmbedding
import SGPT.Okounkov.SchemeNativeStalkNaturality

/-! The algebraic function-field pullback and the analytic meromorphic-germ pullback agree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

variable {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X]
  (f : X ⟶ Spec (.of ℂ)) (p : V ⟶ X) (n : ℕ)
  [SmoothOfRelativeDimension n (p ≫ f)] [SmoothOfRelativeDimension n f]
  [IsSeparated (p ≫ f)] [QuasiCompact (p ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint (p ≫ f)) :=
  schemeAnalyticPointTopology (p ≫ f)

local instance targetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (p ≫ f)) :=
  schemeAnalyticTNChartedSpace (p ≫ f) n

local instance targetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance sourceManifold : IsComplexManifold n (SchemeComplexPoint (p ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (p ≫ f) n

local instance targetManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The algebraic pullback of a rational function has the same germ as its analytic pullback. -/
theorem schemeNativeFunctionFieldGerm_genericPullback
    (hη : p (genericPoint V) = genericPoint X)
    (hmod : IsAnalyticModification (n := n) (schemeComplexPointMap (p ≫ f) f p rfl))
    (v : SchemeComplexPoint (p ≫ f)) (q : X.functionField) :
    schemeNativeFunctionFieldGerm (p ≫ f) n v (genericPullback p hη q) =
      OF9.ratGerm f hmod v q := by
  have h :
      (schemeNativeFunctionFieldGerm (p ≫ f) n v).comp (genericPullback p hη) =
        OF9.ratGerm f hmod v := by
    let x := schemeComplexPointImage f (schemeComplexPointMap (p ≫ f) f p rfl v)
    apply IsLocalization.ringHom_ext (nonZeroDivisors (X.presheaf.stalk x))
    apply RingHom.ext
    intro a
    change schemeNativeFunctionFieldGerm (p ≫ f) n v
        (genericPullback p hη (algebraMap (X.presheaf.stalk x) X.functionField a)) =
      OF9.ratGerm f hmod v (algebraMap (X.presheaf.stalk x) X.functionField a)
    have hpull := genericPullback_stalk p hη (schemeComplexPointImage (p ≫ f) v) a
    change genericPullback p hη (algebraMap (X.presheaf.stalk x) X.functionField a) =
      algebraMap (V.presheaf.stalk (schemeComplexPointImage (p ≫ f) v)) V.functionField
        ((p.stalkMap (schemeComplexPointImage (p ≫ f) v)).hom a) at hpull
    rw [hpull, schemeNativeFunctionFieldGerm_stalk, OF9.ratGerm_apply,
      schemeNativeFunctionFieldGerm_stalk, OF9.fracComap_algebraMap]
    exact congrArg (algebraMap _ _) (schemeNativeStalkGerm_naturality f p n n v a)
  exact RingHom.congr_fun h q

end SGPT.Okounkov
