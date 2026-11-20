import SGPT.Okounkov.SchemeNativeFunctionFieldNaturality
import SGPT.Okounkov.OF13Final
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

/-! A rational algebraization identifies the generic stalk map of the actual projection. -/

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

local instance modelTopology {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance modelCharts {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance modelManifold {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X]
  (f : X ⟶ Spec (.of ℂ)) (p : V ⟶ X) (n : ℕ)
  [SmoothOfRelativeDimension n (p ≫ f)] [SmoothOfRelativeDimension n f]
  [IsSeparated (p ≫ f)] [QuasiCompact (p ≫ f)] [IsSeparated f] [QuasiCompact f]

/-- Meromorphic pullback depends only on the map of complex manifolds. -/
private theorem ratGerm_congr
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {a b : Y → SchemeComplexPoint f} (hab : a = b)
    (ha : IsAnalyticModification (n := n) a) (hb : IsAnalyticModification (n := n) b)
    (y : Y) (q : X.functionField) :
    OF9.ratGerm f ha y q = OF9.ratGerm f hb y q := by
  cases hab
  rfl

/-- For a rational algebraization, the actual projection induces an isomorphism at the generic
point. The field equivalence is used through its meromorphic pullback property at one point. -/
theorem isIso_genericStalkMap_of_rationalAlgebraization
    (hη : p (genericPoint V) = genericPoint X)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (φ : SchemeComplexPoint (p ≫ f) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hprojection : schemeComplexPointMap (p ≫ f) f p rfl = π ∘ φ)
    (v : SchemeComplexPoint (p ≫ f)) (e : X.functionField ≃+* V.functionField)
    (he : ∀ q, schemeNativeFunctionFieldGerm (p ≫ f) n v (e q) =
      OF9.fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v
        (OF9.ratGerm f hπ (φ v) q)) :
    IsIso (p.stalkMap (genericPoint V)) := by
  have hφ := OF13.isAnalyticModification_of_diffeomorph φ
  have hcomp := AnalyticModificationComposition.isAnalyticModification_comp hπ hφ
  have hp : IsAnalyticModification (n := n) (schemeComplexPointMap (p ≫ f) f p rfl) :=
    hprojection.symm ▸ hcomp
  have hfield : genericPullback p hη = e.toRingHom := by
    apply RingHom.ext
    intro q
    apply schemeNativeFunctionFieldGerm_injective (p ≫ f) n v
    rw [schemeNativeFunctionFieldGerm_genericPullback f p n hη hp v q]
    exact (ratGerm_congr f n hprojection hp hcomp v q).trans
      ((OF9.ratGerm_comp f hπ hφ hcomp v q).trans (he q).symm)
  let c := X.presheaf.stalkCongr (.of_eq hη.symm)
  have hc : c.hom ≫ p.stalkMap (genericPoint V) = e.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    exact hfield
  have hi : IsIso (c.hom ≫ p.stalkMap (genericPoint V)) := by
    rw [hc]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

end SGPT.Okounkov
