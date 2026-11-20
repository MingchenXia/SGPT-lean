import SGPT.Projective.OkounkovOriginalCancellationPolytopes
import SGPT.Projective.OkounkovOriginalQuotientMetric
import SGPT.Projective.OkounkovOriginalTwistedPolytopeGeometry
import SGPT.Convex.HausdorffSubsetLimit
import SGPT.NAPotential.FSPosKahler

/-! SAME literal original bodies for arbitrary valuations under genuine original Chern-class equality.
Blueprint: okounkov-original-body-class-invariance.tex. Numerical kernel separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open SGPT.Okounkov.OriginalCancellation SGPT.Okounkov.OriginalDifference
open SGPT.NAPotential.FSPos

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)] [IsSeparated f] [QuasiCompact f]
  {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (b : LineBundleAtlas L') (K : SchemeLineBundleMetric f n E L')
  (hbig : SGPT.LineBundle.IsBig f L n) (hbig' : SGPT.LineBundle.IsBig f L' n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
  (c : X) (hc : IsNonnegAt v c)

local instance bodyClassTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bodyClassCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bodyClassManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

include hbig hbig' hv hc

/-- Actual original sections/geometry/limits manufacture SAME original body inclusion, with a genuine positive line. -/
theorem okounkovBody_subset_of_chernClass_eq_with_positive_line
    {A : X.Modules} (d : LineBundleAtlas A) (J : SchemeLineBundleMetric f n E A)
    (hJ : (J.curvature d).val.IsKahler)
    (hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b)) :
    okounkovBody v c a ⊆ okounkovBody v c b := by
  let q := originalDifferenceAtlas a b
  let Q := originalDifferenceMetric a b f n E H K
  have hzero := originalDifferenceMetric_class_zero a b f n E H K hclass
  obtain ⟨k,hk,hpoly⟩ := exists_fixed_positive_twist_raw_polytope_inclusions a b d f n E q Q J hJ hzero
  let R (m : ℕ) := pairwiseTensorAtlas (d.tensorPower k) (b.tensorPower m)
  obtain ⟨C,hS,hG⟩ := exists_original_admissibleCone_allDimensions f a n E hbig v hv c
  obtain ⟨D,hT,hGT⟩ := exists_original_admissibleCone_allDimensions f b n E hbig' v hv c
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hAc : IsCompact (e '' okounkovBody v c a) :=
    (isCompact_body C (sectionSemigroup v c a) hS
      (nonempty_of_generatedGroup_eq_top _ hG)).image e.continuous
  have hBc : IsCompact (e '' okounkovBody v c b) :=
    (isCompact_body D (sectionSemigroup v c b) hT
      (nonempty_of_generatedGroup_eq_top _ hGT)).image e.continuous
  have hAn : (e '' okounkovBody v c a).Nonempty := BodyGeometry.euclideanBody_nonempty C _ hS hG
  have hBn : (e '' okounkovBody v c b).Nonempty := BodyGeometry.euclideanBody_nonempty D _ hT hGT
  have hleft := ValGen.tendsto_hausdorffDist_lineBundleDegreePolytope a c v hS hG
  have hright := tendsto_hausdorffDist_twistedDegreePolytope_allDimensions f n E b hbig' v hv c hc
    (d.tensorPower k) R
  have hsub : ∀ᶠ m : ℕ in atTop,
      e '' lineBundleDegreePolytope v c a m ⊆ e '' AlgebraicValuation.twistedDegreePolytope v c m (R m) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact Set.image_mono (hpoly m hm v c hc (R m))
  have hleftcompact (m : ℕ) : IsCompact (e '' lineBundleDegreePolytope v c a m) := by
    rw [lineBundleDegreePolytope,ValGen.image_degreePolytope]
    exact BodyGeometry.isCompact_euclideanDegreeBody C _ hS m
  have hleftne : ∀ᶠ m : ℕ in atTop, (e '' lineBundleDegreePolytope v c a m).Nonempty := by
    have hn := BodyGeometry.eventually_euclideanDegreeBody_nonempty C _ hS hG
    filter_upwards [hn] with m hm
    change ((EuclideanSpace.equiv (Fin n) ℝ).symm '' degreePolytope n
      (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) m).Nonempty
    rw [ValGen.image_degreePolytope]
    exact hm
  have hgood : ∀ᶠ m : ℕ in atTop, IsCompact (e '' lineBundleDegreePolytope v c a m) ∧
      IsCompact (e '' AlgebraicValuation.twistedDegreePolytope v c m (R m)) ∧
      (e '' lineBundleDegreePolytope v c a m).Nonempty ∧
      (e '' AlgebraicValuation.twistedDegreePolytope v c m (R m)).Nonempty := by
    filter_upwards [hleftne,hsub] with m hn hs
    exact ⟨hleftcompact m,original_twistedDegreePolytope_isCompact_allDimensions f n E b hbig' v hv c hc
      (d.tensorPower k) m (R m),hn,hn.mono hs⟩
  have hinc := SGPT.Convex.subset_of_tendsto_hausdorffDist_of_isCompact hAc hBc hAn hBn hgood hsub hleft hright
  intro x hx
  obtain ⟨y,hy,heq⟩ := hinc ⟨x,hx,rfl⟩
  exact e.injective heq ▸ hy

/-- NO auxiliary positive line: the SAME original hyperplane/FS metric gives equality of literal original bodies. -/
theorem okounkovBody_eq_of_chernClass_eq_allDimensions
    (hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b)) :
    okounkovBody v c a = okounkovBody v c b := by
  apply Set.Subset.antisymm
  · exact okounkovBody_subset_of_chernClass_eq_with_positive_line f n E a H b K hbig hbig' v hv c hc
      (hyperplaneAtlas E) (fubiniStudyMetric f E n) (fubiniStudy_isKahler f E n) hclass
  · exact okounkovBody_subset_of_chernClass_eq_with_positive_line f n E b K a H hbig' hbig v hv c hc
      (hyperplaneAtlas E) (fubiniStudyMetric f E n) (fubiniStudy_isKahler f E n) hclass.symm

omit c hc in
/-- Actual original canonical center/nonnegativity manufactured internally; no auxiliary flag/cone/body certificate. -/
theorem centreOkounkovBody_eq_of_chernClass_eq_allDimensions
    (hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b)) :
    haveI := E.isProper
    centreOkounkovBody f v a = centreOkounkovBody f v b := by
  let := E.isProper
  exact okounkovBody_eq_of_chernClass_eq_allDimensions f n E a H b K hbig hbig' v hv
    (valuationCenter f v) (isNonnegAt_valuationCenter f v) hclass

end SGPT.Okounkov.OriginalBook
