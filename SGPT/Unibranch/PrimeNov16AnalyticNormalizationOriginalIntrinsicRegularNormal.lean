import SGPT.Unibranch.OriginalIntrinsicSingularLocus
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
import SGPT.Foundations.Analysis.Pending.GermIntegrallyClosed

/-! Actual original regular-point stalks are normal through genuine manifold charts.
Blueprint: prime-nov16-analytic-normalization-original-intrinsic-regular-normal.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
open HironakaSmoothCentreRealDomainActualSheafStalk
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntrinsicRegularNormal

theorem normal_stalk_of_intrinsicRegular (X : SourceReducedComplexSpace) (x : X.obj.left)
    (hx : x ∈ intrinsicRegularLocus X.obj) :
    IsDomain (X.obj.left.presheaf.stalk x).carrier ∧
      IsIntegrallyClosed (X.obj.left.presheaf.stalk x).carrier := by
  obtain ⟨d,O,i,hi,_hscalar,v,hv⟩ := hx
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let E₀ := (asIso (i.stalkMap v)).commRingCatIsoToRingEquiv
  let E : (X.obj.left.presheaf.stalk (i.base v)).carrier ≃+* HolGerm (ComplexModel d) :=
    E₀.trans (actualStalkChartEquiv (n := d) (M := O) (show O from v))
  have h : IsDomain (X.obj.left.presheaf.stalk (i.base v)).carrier ∧
      IsIntegrallyClosed (X.obj.left.presheaf.stalk (i.base v)).carrier :=
    ⟨Function.Injective.isDomain E E.injective,IsIntegrallyClosed.of_equiv E.symm⟩
  exact Eq.ndrec (motive := fun y : X.obj.left =>
    IsDomain (X.obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (X.obj.left.presheaf.stalk y).carrier) h hv
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntrinsicRegularNormal
