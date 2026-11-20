import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent
import SGPT.Unibranch.HironakaG10ChowNativeIsoCriterion

/-! Actual inverse witnesses manufacture common denominator density; actual coproduct descent retains it.
Blueprint: prime-nov16-analytic-normalization-original-good-density.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodDensity
open SourceReducedComplexSpace
open HironakaG1NativeDisjointCoproduct

theorem dense_preimage_of_actual_good_inverse {Y X : SourceReducedComplexSpace}
    (f : Y ⟶ X) (G : Set X.obj.left) (hIso : IsIsoOver f G)
    (hG : Dense (f.hom.left.base ⁻¹' G)) (Q : Set X.obj.left) (hQ : Dense Q) :
    Dense (f.hom.left.base ⁻¹' Q) := by
  obtain ⟨V,j,_hj,hjr,hjf,_hr⟩ := hIso
  intro p
  apply mem_closure_iff.mpr
  intro U hU hpU
  obtain ⟨q,hqU,hqG⟩ := mem_closure_iff.mp (hG p) U hU hpU
  rw [← hjr] at hqG
  obtain ⟨a,rfl⟩ := hqG
  let O : Set V := j.base ⁻¹' U
  have hO : IsOpen O := hU.preimage j.base.hom.continuous
  have haO : a ∈ O := hqU
  have hT : IsOpen ((j ≫ f.hom.left).base '' O) := hjf.base_open.isOpenMap _ hO
  obtain ⟨x,⟨b,hbO,hbx⟩,hxQ⟩ := mem_closure_iff.mp (hQ ((j ≫ f.hom.left).base a))
    _ hT ⟨a,haO,rfl⟩
  refine ⟨j.base b,hbO,?_⟩
  change f.hom.left.base (j.base b) ∈ Q
  exact hbx.symm ▸ hxQ

theorem dense_preimage_coproduct {k : ℕ} (Y : Fin k → SourceReducedComplexSpace)
    {X : SourceReducedComplexSpace} (F : ∀ i,Y i ⟶ X) (Q : Set X.obj.left)
    (hQ : ∀ i,Dense ((F i).hom.left.base ⁻¹' Q)) :
    Dense ((desc Y F).hom.left.base ⁻¹' Q) := by
  intro p
  obtain ⟨i,a,rfl⟩ := inclusion_jointly_surjective Y p
  apply mem_closure_iff.mpr
  intro U hU hpU
  obtain ⟨b,hbU,hbQ⟩ := mem_closure_iff.mp (hQ i a)
    ((inclusion Y i).hom.left.base ⁻¹' U)
    (hU.preimage (inclusion Y i).hom.left.base.hom.continuous) hpU
  refine ⟨(inclusion Y i).hom.left.base b,hbU,?_⟩
  have he := congrArg (fun m : Y i ⟶ X => m.hom.left.base b) (inclusion_desc Y F i)
  change (desc Y F).hom.left.base ((inclusion Y i).hom.left.base b) ∈ Q
  exact he.symm ▸ hbQ

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodDensity
