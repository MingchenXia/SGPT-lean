import SGPT.Unibranch.NativeNov16NormalGraphLift

/-! Actual normal integral quotients construct full original graph-coordinate morphisms.
Blueprint: native-nov16-normal-graph-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16NormalGraphLift
open SourceReducedComplexSpace HironakaActualAnalyticSubspace
open HironakaActualAnalyticSubspaceResidue
open NativeNov16SectionCoordinateMorphism NativeNov16NormalSectionDivision
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation

theorem baseProjection_coordinate {n k : ℕ} (z : ComplexModel (n+k)) (i : Fin n) :
    baseProjection n k z i=z (i.castAdd k) := rfl

theorem fibreProjection_coordinate {n k : ℕ} (z : ComplexModel (n+k)) (i : Fin k) :
    fibreProjection n k z i=z (i.natAdd n) := rfl

abbrev sectionRing {m : ℕ} (P : Opens (ComplexModel m)) (C : Set P)
    (W : Opens (TopCat.of C)) :=
  ((actualSubspaceSheaf (n := m) C).presheaf.obj (Opposite.op W)).carrier

def evaluate {m : ℕ} (P : Opens (ComplexModel m)) (C : Set P)
    (W : Opens (TopCat.of C)) (x : W) : sectionRing P C W →+* ℂ :=
  (actualSubspaceStalkEval (n := m) C x.val).comp
    ((actualSubspaceSheaf (n := m) C).presheaf.germ W x.val x.property).hom

theorem exists_normal_graph_coordinates {m n : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (P : Opens (ComplexModel m)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target)
    (hnormal : ∀ x ∈ W, IsDomain ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier)
    (b : Fin n → sectionRing P C W) (h : sectionRing P C W)
    (g : Fin d.arity → sectionRing P C W)
    (hb : ∀ (x : W) (i : Fin n),evaluate P C W x (b i)=(f.hom.left.base x).val.val.val i)
    (hreg : ∀ (x : C) (hx : x ∈ W),
      (actualSubspaceSheaf (n := m) C).presheaf.germ W x hx h ≠ 0)
    (deg : Fin d.arity → ℕ) (c : ∀ i,Fin (deg i) → sectionRing P C W)
    (hrel : ∀ i,(g i)^(deg i)+∑ j : Fin (deg i),c i j*h^(deg i-j.val)*(g i)^j.val=0) :
    ∃ (q : Fin d.arity → sectionRing P C W)
      (F : coordinateSource P C hC W ⟶ domainSpace (⊤ : Opens (ComplexModel (n+d.arity)))),
      (∀ i,g i=h*q i) ∧
      (∀ x : W,baseProjection n d.arity (F.hom.left.base x).val.val=
        (f.hom.left.base x).val.val.val) ∧
      ∀ (x : W) (i : Fin d.arity),fibreProjection n d.arity (F.hom.left.base x).val.val i=
        evaluate P C W x (q i) := by
  classical
  have hdiv (i : Fin d.arity) := exists_unique_divisor_of_cleared_relation
    (actualSubspaceSheaf (n := m) C) W (c i) (g i) h hnormal hreg (hrel i)
  choose q hq using fun i => (hdiv i).exists
  let s : Fin (n+d.arity) → sectionRing P C W := Fin.addCases b q
  obtain ⟨F,hF,_huniq⟩ := exists_unique_coordinate_morphism P C hC W s
  refine ⟨q,F,hq,?_,?_⟩
  · intro x
    ext i
    rw [baseProjection_coordinate]
    have he := hF x (i.castAdd d.arity)
    have hi : (F.hom.left.base x).val.val (i.castAdd d.arity)=evaluate P C W x (b i) := by
      simpa [s,evaluate] using he
    exact hi.trans (hb x i)
  · intro x i
    rw [fibreProjection_coordinate]
    have he := hF x (i.natAdd n)
    simpa [s,evaluate] using he

end SGPT.Unibranch.NativeNov16NormalGraphLift
