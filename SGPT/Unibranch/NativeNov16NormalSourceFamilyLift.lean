import SGPT.Unibranch.NativeNov16RegularNormalGraphLift
import SGPT.Unibranch.NativeNov16DisjointSourceCoverGluing
import SGPT.Unibranch.NativeNov16NormalizationOverlapUniqueness
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion

/-! Actual component graph lifts assemble on the SAME original normal source.
Blueprint: native-nov16-normal-source-family-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16NormalSourceFamilyLift
open SourceReducedComplexSpace HironakaActualAnalyticSubspace
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open PrimeNov16AnalyticNormalizationLocalGraph PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalSourceScalarRelations
open HironakaG1NativeDisjointCoproduct

theorem exists_unique_family_lift {n m k : ℕ} {B : Fin k → Set (ComplexModel n)}
    (d : ∀ i,GraphPresentation n (B i)) {X : SourceReducedComplexSpace}
    (c : ∀ i,(d i).target ⟶ X)
    (P : Opens (ComplexModel m)) (C : Set P) (hC : IsComplexAnalyticSubset (n := m) C)
    (W : Opens (TopCat.of C)) (f : coordinateSource P C hC W ⟶ X)
    (hn : ∀ x ∈ W,IsDomain ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier)
    (V : Fin k → Opens (TopCat.of C)) (hVW : ∀ i,V i ≤ W)
    (hcover : ∀ x : W,∃ i,x.val ∈ V i)
    (hdisj : Pairwise (fun i j => Disjoint (V i : Set C) (V j : Set C)))
    (s : ∀ i,coordinateSource P C hC (V i) ⟶ (d i).target)
    (htri : ∀ i,s i ≫ c i=windowInclusion P C hC (V i) W (hVW i) ≫ f)
    (hr : ∀ i,∀ (x : C) (hx : x ∈ V i),
      (actualSubspaceSheaf (n := m) C).presheaf.germ (V i) x hx
        (pulledBaseScalar (d i) P C hC (V i) (s i) (d i).denominator (d i).denominator_holo) ≠ 0)
    (deg : ∀ i,Fin (d i).arity → ℕ)
    (a : ∀ i,Fin (d i).arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j l,l < deg i j → DifferentiableOn ℂ (a i j l) (ballDomain (n := n) (d i).radius))
    (hm : ∀ i,∀ p : (d i).graph.obj.left,∀ j,
      GermParametrizationData.monicEval (deg i j) (a i j)
        (baseProjection n (d i).arity p.val.val) (fibreProjection n (d i).arity p.val.val j)=0)
    (hs : ∀ i,Function.Surjective (d i).map.hom.left.base)
    (G : Set X.obj.left)
    (hIso : IsIsoOver (desc (fun i => (d i).source) (fun i => (d i).map ≫ c i)) G)
    (hd : Dense (f.hom.left.base ⁻¹' G)) :
    ∃! L : coordinateSource P C hC W ⟶ coproduct (fun i => (d i).source),
      L ≫ desc (fun i => (d i).source) (fun i => (d i).map ≫ c i)=f := by
  classical
  have hlocal (i : Fin k) : ∃! L : coordinateSource P C hC (V i) ⟶ (d i).source,
      L ≫ (d i).map=s i :=
    NativeNov16RegularNormalGraphLift.exists_unique_graph_lift_of_regular_pullback
      (d i) P C hC (V i) (s i) (fun x hx => hn x (hVW i hx))
      (hr i) (deg i) (a i) (ha i) (hm i) (hs i)
  choose L hL huniq using hlocal
  let T := fun i => coordinateSource P C hC (V i)
  let j := fun i => windowInclusion P C hC (V i) W (hVW i)
  let Y := fun i => (d i).source
  let p := desc Y (fun i => (d i).map ≫ c i)
  have hc : ∀ x : (coordinateSource P C hC W).obj.left,
      ∃ (i : Fin k) (t : (T i).obj.left),(j i).hom.left.base t=x := by
    intro x
    obtain ⟨i,hi⟩ := hcover x
    refine ⟨i,(⟨x.val,hi⟩ : V i),?_⟩
    apply Subtype.ext
    exact windowInclusion_point P C hC (V i) W (hVW i) _
  have hDj : Pairwise (fun i l => Disjoint (range (j i).hom.left.base)
      (range (j l).hom.left.base)) := by
    intro i l hil
    apply disjoint_left.mpr
    rintro x ⟨u,hu⟩ ⟨v,hv⟩
    have he : u.val=v.val := by
      have hh := congrArg (fun t : (coordinateSource P C hC W).obj.left => t.val)
        (hu.trans hv.symm)
      exact (windowInclusion_point P C hC (V i) W (hVW i) u).symm.trans
        (hh.trans (windowInclusion_point P C hC (V l) W (hVW l) v))
    exact disjoint_left.mp (hdisj hil) u.property (he.symm ▸ v.property)
  obtain ⟨F,hF,_hFu⟩ := NativeNov16DisjointSourceCoverGluing.exists_unique_morphism T j
    (fun i => windowInclusion_isOpenImmersion P C hC (V i) W (hVW i)) hc hDj
    (fun i => L i ≫ inclusion Y i)
  have hFp : F ≫ p=f := by
    apply morphism_eq_of_pointwise_eq
    intro x
    obtain ⟨i,t,rfl⟩ := hc x
    have he : j i ≫ (F ≫ p)=j i ≫ f := by
      rw [← Category.assoc,hF,Category.assoc,inclusion_desc,← Category.assoc,hL,htri]
    exact congrArg (fun q : T i ⟶ X => q.hom.left.base t) he
  refine ⟨F,hFp,?_⟩
  intro K hK
  exact NativeNov16NormalizationOverlapUniqueness.hom_ext_of_dense_good p G hIso f hd K F hK hFp

end SGPT.Unibranch.NativeNov16NormalSourceFamilyLift
