import SGPT.Unibranch.NativeNov16WindowSectionValues
import SGPT.Unibranch.NativeNov16PartialBaseScalarSections
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorRelations
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorFactors
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorDenominator

/-! Actual full normal-source morphisms internally manufacture selectors, original component factors, and whole-germ regularity.
Blueprint: prime-nov16-analytic-normalization-original-normal-source-selectors.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
open NativeNov16SectionCoordinateMorphism NativeNov16PartialBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalWindowSectionPullback
open PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationOriginalSelectorRelations
open PrimeNov16AnalyticNormalizationOriginalSelectorFactors
open PrimeNov16AnalyticNormalizationOriginalSelectorDenominator
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaActualAnalyticSubspaceLocalFunctions
open SourceReducedComplexSpace

def pulledPartialScalar {m n : ℕ} (Ps : Opens (ComplexModel m)) (Cs : Set Ps)
    (hCs : IsComplexAnalyticSubset (n := m) Cs) (Ws : Opens (TopCat.of Cs))
    (Pt : Opens (ComplexModel n)) (Ct : Set Pt) (hCt : IsComplexAnalyticSubset (n := n) Ct)
    (Ut : Opens (TopCat.of Ct)) (f : coordinateSource Ps Cs hCs Ws ⟶ coordinateSource Pt Ct hCt Ut)
    (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F Ω)
    (hland : ∀ b : Ct,b ∈ Ut → b.val.val ∈ Ω) :
    ((actualSubspaceSheaf (n := m) Cs).presheaf.obj (op Ws)).carrier :=
  pullWindowRingHom f.hom.left (scalarSection Pt Ct Ut Ω F hF hland)

theorem pulledPartialScalar_value {m n : ℕ} (Ps : Opens (ComplexModel m)) (Cs : Set Ps)
    (hCs : IsComplexAnalyticSubset (n := m) Cs) (Ws : Opens (TopCat.of Cs))
    (Pt : Opens (ComplexModel n)) (Ct : Set Pt) (hCt : IsComplexAnalyticSubset (n := n) Ct)
    (Ut : Opens (TopCat.of Ct)) (f : coordinateSource Ps Cs hCs Ws ⟶ coordinateSource Pt Ct hCt Ut)
    (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F Ω)
    (hland : ∀ b : Ct,b ∈ Ut → b.val.val ∈ Ω) (p : Ws) :
    original_value_hom Cs Ws p (pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω F hF hland)=
      F (f.hom.left.base p).val.val.val := by
  have hp : (f.hom.left ≫ (actualSubspaceLocallyRingedSpace (n := n) Ct).ofRestrict Ut.isOpenEmbedding) ≫
      subspacePointMap (n := n) Ct=
      (actualSubspaceLocallyRingedSpace (n := m) Cs).ofRestrict Ws.isOpenEmbedding ≫
        subspacePointMap (n := m) Cs := by
    rw [Category.assoc]
    exact Over.w f.hom
  exact (NativeNov16WindowSectionValues.pullWindow_value Cs Ct Ws Ut f.hom.left hp p
    (scalarSection Pt Ct Ut Ω F hF hland)).trans (scalarSection_value Pt Ct Ut Ω F hF hland (f.hom.left.base p))

theorem exists_actual_normal_source_selectors {m n k : ℕ}
    (Ps : Opens (ComplexModel m)) (Cs : Set Ps) (hCs : IsComplexAnalyticSubset (n := m) Cs)
    (Ws : Opens (TopCat.of Cs)) (Pt : Opens (ComplexModel n)) (Ct : Set Pt)
    (hCt : IsComplexAnalyticSubset (n := n) Ct) (Ut : Opens (TopCat.of Ct))
    (f : coordinateSource Ps Cs hCs Ws ⟶ coordinateSource Pt Ct hCt Ut)
    (B : Fin k → Set Pt) (hB : ∀ i,IsComplexAnalyticSubset (n := n) (B i))
    (hBC : ∀ i,B i ⊆ Ct) (hcover : ∀ b ∈ Ct,∃ i,b ∈ B i)
    (Ω : Opens (ComplexModel n)) (Q : ComplexModel n → ℂ)
    (T H : Fin k → ComplexModel n → ℂ) (hQ : DifferentiableOn ℂ Q Ω)
    (hT : ∀ i,DifferentiableOn ℂ (T i) Ω) (hH : ∀ i,DifferentiableOn ℂ (H i) Ω)
    (hland : ∀ b : Ct,b ∈ Ut → b.val.val ∈ Ω)
    (hvan : ∀ i j,i ≠ j → ∀ b ∈ B j,b.val ∈ Ω → T i b.val=0)
    (hbranch : ∀ i,∀ b ∈ B i,b.val ∈ Ω → Q b.val=T i b.val*H i b.val)
    (hnormal : ∀ x ∈ Ws,IsDomain ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier)
    (hreg : ∀ x (hx : x ∈ Ws),(actualSubspaceSheaf (n := m) Cs).presheaf.germ Ws x hx
      (pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω Q hQ hland) ≠ 0) :
    let q := pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω Q hQ hland
    let t := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω (T i) (hT i) hland
    let h := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω (H i) (hH i) hland
    let num := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω
      (fun z => T i z*H i z) ((hT i).mul (hH i)) hland
    ∃ (e : Fin k → ((actualSubspaceSheaf (n := m) Cs).presheaf.obj (op Ws)).carrier)
      (V : Fin k → Opens (TopCat.of Cs)) (hVW : ∀ i,V i ≤ Ws),
      (∀ i,num i=q*e i) ∧ (∀ i,(e i)^2=e i) ∧ (∑ i,e i=1) ∧
      (∀ i j,i ≠ j → e i*e j=0) ∧ (∀ i,num i=t i*h i) ∧
      (∀ i,IsClosed ((Subtype.val : Ws → Cs) ⁻¹' (V i : Set Cs))) ∧
      (∀ p : Ws,∃ i,p.val ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i : Set Cs) (V j : Set Cs)) ∧
      (∀ i,(actualSubspaceSheaf (n := m) Cs).presheaf.map (homOfLE (hVW i)).op (e i)=1) ∧
      (∀ i,∀ x (hx : x ∈ V i),(actualSubspaceSheaf (n := m) Cs).presheaf.germ (V i) x hx
        ((actualSubspaceSheaf (n := m) Cs).presheaf.map (homOfLE (hVW i)).op (h i)) ≠ 0) ∧
      ∀ i,∃! G : coordinateSource Ps Cs hCs (V i) ⟶ ofClosedAnalytic (B i) (hB i),
        G ≫ OriginalClosedSubspaceFactorization.inclusion (hB i) hCt (hBC i)=
          windowInclusion Ps Cs hCs (V i) Ws (hVW i) ≫ f ≫ coordinateInclusion Pt Ct hCt Ut := by
  classical
  let q := pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω Q hQ hland
  let t := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω (T i) (hT i) hland
  let h := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω (H i) (hH i) hland
  let num := fun i => pulledPartialScalar Ps Cs hCs Ws Pt Ct hCt Ut f Ω
    (fun z => T i z*H i z) ((hT i).mul (hH i)) hland
  let F := f ≫ coordinateInclusion Pt Ct hCt Ut
  let D : Ct → ℂ := fun b => if b.val.val ∈ Ω then Q b.val.val else 0
  let N : Fin k → Ct → ℂ := fun i b => if b.val.val ∈ Ω then T i b.val.val*H i b.val.val else 0
  have hNvan : ∀ i j,i ≠ j → ∀ b : Ct,b.val ∈ B j → N i b=0 := by
    intro i j hij b hb
    dsimp only [N]
    split_ifs with hΩ
    · rw [hvan i j hij b.val hb hΩ,zero_mul]
    · rfl
  have hND : ∀ i,∀ b : Ct,b.val ∈ B i → D b=N i b := by
    intro i b hb
    dsimp only [D,N]
    split_ifs with hΩ
    · exact hbranch i b.val hb hΩ
    · rfl
  have hqVal (p : Ws) : original_value_hom Cs Ws p q=D (F.hom.left.base p) := by
    change _=if (F.hom.left.base p).val.val ∈ Ω then Q (F.hom.left.base p).val.val else 0
    have hΩ : (F.hom.left.base p).val.val ∈ Ω := hland (f.hom.left.base p).val (f.hom.left.base p).property
    have hv : original_value_hom Cs Ws p q=Q (F.hom.left.base p).val.val :=
      pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hCt Ut f Ω Q hQ hland p
    exact hv.trans (if_pos hΩ).symm
  have hnVal (i : Fin k) (p : Ws) : original_value_hom Cs Ws p (num i)=N i (F.hom.left.base p) := by
    change _=if (F.hom.left.base p).val.val ∈ Ω then T i (F.hom.left.base p).val.val*H i (F.hom.left.base p).val.val else 0
    have hΩ : (F.hom.left.base p).val.val ∈ Ω := hland (f.hom.left.base p).val (f.hom.left.base p).property
    have hv : original_value_hom Cs Ws p (num i)=T i (F.hom.left.base p).val.val*H i (F.hom.left.base p).val.val :=
      pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hCt Ut f Ω _ ((hT i).mul (hH i)) hland p
    exact hv.trans (if_pos hΩ).symm
  obtain ⟨hid,hsum,horth⟩ := actual_whole_selector_numerator_relations Cs Ws F.hom.left.base
    (fun i => (Subtype.val : Ct → Pt) ⁻¹' B i)
    (fun p => hcover _ (F.hom.left.base p).property) D N hNvan hND q num hqVal hnVal
  obtain ⟨e,heq,hei,heSum,heOrth⟩ := exists_actual_selector_sections (actualSubspaceSheaf (n := m) Cs)
    Ws q num hnormal hreg hid hsum horth
  have hFactor (i : Fin k) : num i=t i*h i := by
    apply actualSubspaceSection_ext_eval Cs Ws
    intro x hx
    let p : Ws := ⟨x,hx⟩
    change original_value_hom Cs Ws p (num i)=original_value_hom Cs Ws p (t i*h i)
    rw [map_mul]
    exact (pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hCt Ut f Ω _ ((hT i).mul (hH i)) hland p).trans
      (congrArg₂ (·*·) (pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hCt Ut f Ω (T i) (hT i) hland p)
        (pulledPartialScalar_value Ps Cs hCs Ws Pt Ct hCt Ut f Ω (H i) (hH i) hland p)).symm
  obtain ⟨V,hVW,hClosed,hCover,hDisjoint,hOne,hG⟩ := exists_actual_component_factors
    Ps Cs hCs Ws Pt Ct hCt B hB hBC hcover F N hNvan q e hreg hei heSum heOrth (by
      intro i p
      have he := congrArg (original_value_hom Cs Ws p) (heq i)
      rw [map_mul] at he
      exact he.symm.trans (hnVal i p))
  refine ⟨e,V,hVW,heq,hei,heSum,heOrth,hFactor,hClosed,hCover,hDisjoint,hOne,?_,?_⟩
  · intro i
    exact original_selector_denominator_nonzero (actualSubspaceSheaf (n := m) Cs) Ws (V i) (hVW i)
      q (e i) (t i) (h i) hreg ((heq i).symm.trans (hFactor i)) (hOne i)
  · intro i
    exact hG i

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
