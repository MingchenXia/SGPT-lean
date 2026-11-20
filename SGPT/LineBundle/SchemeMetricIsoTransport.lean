import SGPT.Okounkov.SchemeLineBundleMetricGeometry

/-! Actual original sheaf isomorphisms transport actual smooth physical
metrics, with exact original frame transitions and Chern coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov

variable {X : Scheme.{0}} {L Q : X.Modules}

/-- The actual original local frame transferred through a literal original
sheaf isomorphism, on the same original scheme open. -/
def isoFrame (Φ : L ≅ Q) {U : X.Opens} (α : LocalBundleFrame L U) : LocalBundleFrame Q U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso Φ.symm ≪≫ α

/-- Every actual smaller-open coefficient is read through the literal
original inverse sheaf map. -/
theorem isoFrame_coefficients (Φ : L ≅ Q) {U W : X.Opens}
    (α : LocalBundleFrame L U) (i : W ⟶ U) (s : bundleSections Q W) :
    (isoFrame Φ α).coefficients i s = α.coefficients i (Φ.inv.val.app (op W) s) := rfl

/-- The whole original unit transition is unchanged by the actual sheaf
isomorphism, including all original regular functions on every smaller open. -/
theorem isoFrame_transition (Φ : L ≅ Q) {U V W : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition (isoFrame Φ α) (isoFrame Φ β) i j =
      localBundleFrameTransition α β i j := by
  apply Units.ext
  change ((isoFrame Φ β).coefficients j) (((isoFrame Φ α).coefficients i).symm 1) =
    β.coefficients j ((α.coefficients i).symm 1)
  let s := (α.coefficients i).symm 1
  have hinv : Φ.inv.val.app (op W) (Φ.hom.val.app (op W) s) = s := by
    have h := congrArg (fun t => t.val.app (op W) s) Φ.hom_inv_id
    exact h
  have hframe : ((isoFrame Φ α).coefficients i).symm 1 = Φ.hom.val.app (op W) s := by
    apply ((isoFrame Φ α).coefficients i).injective
    rw [LinearEquiv.apply_symm_apply, isoFrame_coefficients, hinv, LinearEquiv.apply_symm_apply]
  rw [hframe, isoFrame_coefficients, hinv]

variable (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f]

local instance isoMetricTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance isoMetricCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance isoMetricManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The actual analytic frame transition is the same original unit after
transport, on the whole actual original overlap. -/
theorem isoFrame_schemeTransition (Φ : L ≅ Q) {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) :
    schemeFrameTransition f n E (isoFrame Φ α) (isoFrame Φ β) = schemeFrameTransition f n E α β := by
  unfold schemeFrameTransition
  rw [isoFrame_transition]

/-- Literal original bundle isomorphisms manufacture actual smooth physical
metrics on the original source bundle, rather than assume a Chern reader. -/
def transportMetric (H : SchemeLineBundleMetric f n E Q) (Φ : L ≅ Q) :
    SchemeLineBundleMetric f n E L where
  frameNormSq α := H.frameNormSq (isoFrame Φ α)
  smooth α := H.smooth (isoFrame Φ α)
  positive α := H.positive (isoFrame Φ α)
  transition α β p hp hq := by
    rw [H.transition (isoFrame Φ α) (isoFrame Φ β) p hp hq,
      isoFrame_schemeTransition f n E Φ α β]

/-- The transported metric has the exact same original chart Chern
coefficients, for arbitrary original atlases on the two actual bundles. -/
theorem transportMetric_curvature (H : SchemeLineBundleMetric f n E Q) (Φ : L ≅ Q)
    (a : LineBundleAtlas L) (b : LineBundleAtlas Q) :
    let := E.isSeparated
    let := E.quasiCompact
    ((transportMetric f n E H Φ).curvature a).val.GeometricallyEq (H.curvature b).val := by
  let := E.isSeparated
  let := E.quasiCompact
  dsimp only
  intro c z hz
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (c.val.symm z))
  rw [(transportMetric f n E H Φ).curvature_coeff_frame a (a.frame i) c hz hi,
    H.curvature_coeff_frame b (isoFrame Φ (a.frame i)) c hz hi]
  rfl

/-- The same original physical frame norms, with another auxiliary
projective embedding. Genuine regular transitions have identical values. -/
def reembedMetric {L : X.Modules} (H : SchemeLineBundleMetric f n E L)
    (E' : ClosedProjectiveEmbedding f) : SchemeLineBundleMetric f n E' L where
  frameNormSq := H.frameNormSq
  smooth := H.smooth
  positive := H.positive
  transition := H.transition

/-- Re-embedding preserves every actual original Chern coefficient. -/
theorem reembedMetric_curvature {L : X.Modules} (H : SchemeLineBundleMetric f n E L)
    (E' : ClosedProjectiveEmbedding f) (a b : LineBundleAtlas L) :
    let := E.isSeparated
    let := E.quasiCompact
    ((reembedMetric f n E H E').curvature b).val.GeometricallyEq (H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  dsimp only
  intro c z hz
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (c.val.symm z))
  rw [(reembedMetric f n E H E').curvature_coeff_frame b (a.frame i) c hz hi,
    H.curvature_coeff_frame a (a.frame i) c hz hi]
  rfl

end SGPT.LineBundle.AmpleChern
