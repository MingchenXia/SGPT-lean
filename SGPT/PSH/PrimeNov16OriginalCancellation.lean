import SGPT.PSH.PrimeNov16IsoOverLift
import SGPT.Unibranch.SourceMorphismExt
import SGPT.Unibranch.HironakaG11ModificationCalculus

/-! Actual original full-map cancellation over a genuine common projection.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.PSH.PrimeNov16OriginalCancellation
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending HironakaResolutionSpaceComplex
open SGPT.Unibranch SourceReducedComplexSpace

theorem eq_of_actual_common_projection {X Y S : SourceReducedComplexSpace}
    (p : Y ⟶ X) (hp : IsProperBimeromorphic p) (a b : S ⟶ Y)
    (hcomp : a ≫ p = b ≫ p) (hactual : IsProperBimeromorphic (a ≫ p)) : a = b := by
  obtain ⟨_hpp, B, _hBa, hBt, _hpre, hi⟩ := hp
  obtain ⟨_hHp, _C, _hCa, _hCt, hHpre, hiH⟩ := hactual
  have hthin : interior ((a ≫ p).hom.left.base ⁻¹' B) = ∅ :=
    hiH.interior_preimage_eq_empty hHpre hBt
  have hd : Dense (((a ≫ p).hom.left.base ⁻¹' B)ᶜ) :=
    interior_eq_empty_iff_dense_compl.mp hthin
  have hpoint (x : S.obj.left) : p.hom.left.base (a.hom.left.base x) = p.hom.left.base (b.hom.left.base x) :=
    congrArg (fun F : S ⟶ X => F.hom.left.base x) hcomp
  let : T2Space Y.obj.left := Y.property.1
  have heq : (a.hom.left.base : S.obj.left → Y.obj.left) = b.hom.left.base := by
    have hca : Continuous (fun x : S.obj.left => (a.hom.left.base x : Y.obj.left)) := a.hom.left.base.hom.continuous
    have hcb : Continuous (fun x : S.obj.left => (b.hom.left.base x : Y.obj.left)) := b.hom.left.base.hom.continuous
    apply Continuous.ext_on (X := Y.obj.left) (Y := S.obj.left) hd hca hcb
    intro x hx
    have ha : p.hom.left.base (a.hom.left.base x) ∈ Bᶜ := hx
    have hb : p.hom.left.base (b.hom.left.base x) ∈ Bᶜ := (hpoint x) ▸ ha
    exact PrimeNov16IsoOverLift.injOn_preimage hi ha hb (hpoint x)
  exact SourceReducedComplexSpace.morphism_eq_of_pointwise_eq a b (fun x => congrFun heq x)

end SGPT.PSH.PrimeNov16OriginalCancellation
