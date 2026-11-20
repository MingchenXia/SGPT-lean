import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceManifoldCharts
import SGPT.Foundations.Analysis.Pending.GermIntegrallyClosed

/-! Genuine regularity implies normality of the ENTIRE actual original stalk.
Blueprint: prime-nov16-analytic-normalization-regular-original-stalk.tex. -/
set_option autoImplicit false
noncomputable section
open Set CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularOriginalStalk
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
open HironakaSmoothCentreRealDomainActualSheafStalk

theorem actual_regular_original_stalk_normal {d t : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d) :
    IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier := by
  obtain ⟨V,i,hi,_hpoint,v,hv⟩ := exists_actual_regular_subspace_manifold_chart C x hreg
  let : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion i := hi
  let : IsIso (i.stalkMap v) := AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso i v
  let e := ((asIso (i.stalkMap v)).commRingCatIsoToRingEquiv).trans
    (actualStalkChartEquiv (n := d) (M := V) (show V from v))
  have hd : IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk (i.base v)).carrier :=
    Function.Injective.isDomain e e.injective
  have hn : IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk (i.base v)).carrier :=
    IsIntegrallyClosed.of_equiv e.symm
  exact Eq.mp (congrArg (fun q : C =>
    IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk q).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk q).carrier) hv) ⟨hd,hn⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularOriginalStalk
