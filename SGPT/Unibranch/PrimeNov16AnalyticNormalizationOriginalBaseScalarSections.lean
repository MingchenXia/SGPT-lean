import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
import SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives

/-! SAME primitive base functions manufacture actual entire target and source sections and whole monic identities.
Blueprint: prime-nov16-analytic-normalization-original-base-scalar-sections.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationLocalGraph
open NativeNov16SectionCoordinateMorphism
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceLocalFunctions
open HironakaSmoothCentreRealDomainActualSheafStalk

private theorem scalar_smooth {n : ℕ} (P : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F P) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (F ∘ Subtype.val : P → ℂ) :=
  (contDiffOn_of_differentiableOn_complex hF P.isOpen).contMDiffOn.comp_contMDiff
    contMDiff_subtype_val (fun z => z.property)

def ambientScalarSection {n : ℕ} (P : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F P) : actualComplexSection (n := n) (⊤ : Opens P) :=
  ⟨fun z => F z.val.val,(scalar_smooth P F hF).comp contMDiff_subtype_val⟩

variable {n : ℕ} {Z : Set (ComplexModel n)}

def baseAmbientMap (d : GraphPresentation n Z) : d.target.obj.left ⟶
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) (ballDomain (n := n) d.radius) :=
  d.baseInclusion.hom.left ≫ actualSubspaceInclusion (n := n)
    {z : ballDomain (n := n) d.radius | z.val ∈ Z}

def baseScalarSection (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) :
    (d.target.obj.left.presheaf.obj (op ⊤)).carrier :=
  pullTopRingHom (baseAmbientMap d) (ambientScalarSection (ballDomain (n := n) d.radius) F hF)

def fullBaseScalarSection (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) :
    (d.base.obj.left.presheaf.obj (op ⊤)).carrier :=
  pullTopRingHom (actualSubspaceInclusion (n := n)
    {z : ballDomain (n := n) d.radius | z.val ∈ Z})
    (ambientScalarSection (ballDomain (n := n) d.radius) F hF)

theorem baseScalar_eq_pullFull (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) :
    baseScalarSection d F hF=pullTopRingHom d.baseInclusion.hom.left (fullBaseScalarSection d F hF) :=
  pullTop_comp d.baseInclusion.hom.left
    (actualSubspaceInclusion (n := n) {z : ballDomain (n := n) d.radius | z.val ∈ Z}) _

theorem fullBaseScalar_value (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) (b : d.base.obj.left) :
    HironakaActualAnalyticSubspaceResidue.actualSubspaceStalkEval (n := n)
      {z : ballDomain (n := n) d.radius | z.val ∈ Z} b
      (d.base.obj.left.presheaf.germ ⊤ b (by trivial) (fullBaseScalarSection d F hF))=F b.val.val := by
  change HironakaActualAnalyticSubspaceResidue.actualSubspaceStalkEval _ b
    (d.base.obj.left.presheaf.germ ⊤ b (by trivial) (pullTopRingHom (actualSubspaceInclusion (n := n)
      {z : ballDomain (n := n) d.radius | z.val ∈ Z})
      (ambientScalarSection (ballDomain (n := n) d.radius) F hF)))=_
  exact (congrArg (HironakaActualAnalyticSubspaceResidue.actualSubspaceStalkEval _ b)
    (pullTop_germ (actualSubspaceInclusion (n := n)
      {z : ballDomain (n := n) d.radius | z.val ∈ Z})
      (ambientScalarSection (ballDomain (n := n) d.radius) F hF) b)).trans
    (actualSubspaceStalkEval_inclusion_germ
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} ⊤
    (ambientScalarSection (ballDomain (n := n) d.radius) F hF) b (by trivial))

private theorem baseAmbientSection_germ (d : GraphPresentation n Z)
    (s : actualComplexSection (n := n) (⊤ : Opens (ballDomain (n := n) d.radius)))
    (b : d.target.obj.left) :
    d.target.obj.left.presheaf.germ ⊤ b (by trivial) (pullTopRingHom (baseAmbientMap d) s)=
      d.baseInclusion.hom.left.stalkMap b
        ((actualSubspaceInclusion (n := n) {z : ballDomain (n := n) d.radius | z.val ∈ Z}).stalkMap b.val
          ((actualComplexStructureSheaf (n := n) (ballDomain (n := n) d.radius)).presheaf.germ
            ⊤ b.val.val (by trivial) s)) := by
  rw [pullTop_germ]
  exact ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp d.baseInclusion.hom.left
    (actualSubspaceInclusion (n := n) {z : ballDomain (n := n) d.radius | z.val ∈ Z}) b)
    ((actualComplexStructureSheaf (n := n) (ballDomain (n := n) d.radius)).presheaf.germ
      ⊤ b.val.val (by trivial) s)

theorem baseScalar_germ (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) (b : d.target.obj.left)
    (hFb : HolomorphicAt n (F ∘ Subtype.val) b.val.val) :
    d.target.obj.left.presheaf.germ ⊤ b (by trivial) (baseScalarSection d F hF)=
      d.baseInclusion.hom.left.stalkMap b (originalFunctionImage
        {z : ballDomain (n := n) d.radius | z.val ∈ Z} b.val (F ∘ Subtype.val) hFb) := by
  let s := ambientScalarSection (ballDomain (n := n) d.radius) F hF
  have hr := actualOriginalFunctionGerm_eq_section (⊤ : Opens (ballDomain (n := n) d.radius))
    b.val.val (by trivial) s (F ∘ Subtype.val) hFb (Eventually.of_forall fun y => by
      rw [sectionExtension_apply _ _ _ (by trivial)]
      rfl)
  have hi := intrinsicGermMap_original_function
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} b.val (F ∘ Subtype.val) hFb
  have he : originalFunctionImage {z : ballDomain (n := n) d.radius | z.val ∈ Z}
      b.val (F ∘ Subtype.val) hFb=
      (actualSubspaceInclusion (n := n) {z : ballDomain (n := n) d.radius | z.val ∈ Z}).stalkMap b.val
        ((actualComplexStructureSheaf (n := n) (ballDomain (n := n) d.radius)).presheaf.germ
          ⊤ b.val.val (by trivial) s) := hi.trans (congrArg _ hr)
  exact (baseAmbientSection_germ d s b).trans (congrArg _ he.symm)

theorem baseScalar_germ_nonzero (d : GraphPresentation n Z) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) (b : d.target.obj.left)
    (hFb : HolomorphicAt n (F ∘ Subtype.val) b.val.val)
    (hn : originalFunctionImage {z : ballDomain (n := n) d.radius | z.val ∈ Z}
      b.val (F ∘ Subtype.val) hFb ≠ 0) :
    d.target.obj.left.presheaf.germ ⊤ b (by trivial) (baseScalarSection d F hF) ≠ 0 := by
  rw [baseScalar_germ d F hF b hFb]
  let E := (asIso (d.baseInclusion.hom.left.stalkMap b)).commRingCatIsoToRingEquiv
  intro hz
  apply hn
  apply E.injective
  rw [map_zero]
  exact hz

theorem baseAmbientSection_zero_of_values (d : GraphPresentation n Z)
    (s : actualComplexSection (n := n) (⊤ : Opens (ballDomain (n := n) d.radius)))
    (hs : ∀ b : d.base.obj.left,b ∈ d.baseOpen → s ⟨b.val,by trivial⟩=0) :
    pullTopRingHom (baseAmbientMap d) s=0 := by
  apply TopCat.Presheaf.section_ext d.target.obj.left.toSheafedSpace.sheaf ⊤ _ 0
  intro b _hb
  change d.target.obj.left.presheaf.germ ⊤ b (by trivial)
    (pullTopRingHom (baseAmbientMap d) s)=_
  rw [map_zero,baseAmbientSection_germ]
  let C := {z : ballDomain (n := n) d.radius | z.val ∈ Z}
  let p : C := b.val
  let F := sectionExtension (⊤ : Opens (ballDomain (n := n) d.radius)) s
  have hF : HolomorphicAt n F p.val := sectionExtension_holomorphicAt _ s _ (by trivial)
  let V0 : Set C := fun q => (show d.base.obj.left from q) ∈ d.baseOpen
  have hV0 : IsOpen V0 := d.baseOpen.isOpen
  obtain ⟨O,hO,hOV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV0
  have hpO : p.val ∈ O := by
    change p ∈ Subtype.val ⁻¹' O
    rw [hOV]
    exact b.property
  have hFI : (vanishingIdeal (n := n) C).mem p.val F := by
    refine ⟨hF,?_⟩
    filter_upwards [hO.mem_nhds hpO] with y hy hyC
    have hyV : (show d.base.obj.left from (⟨y,hyC⟩ : C)) ∈ d.baseOpen := by
      change (⟨y,hyC⟩ : C) ∈ V0
      rw [← hOV]
      exact hy
    change sectionExtension (⊤ : Opens (ballDomain (n := n) d.radius)) s y=0
    rw [sectionExtension_apply _ _ _ (by trivial)]
    exact hs (⟨y,hyC⟩ : C) hyV
  have hz := (original_function_image_zero_iff C d.carrier_analytic p F hF).mpr hFI
  have hr := actualOriginalFunctionGerm_eq_section (⊤ : Opens (ballDomain (n := n) d.radius))
    p.val (by trivial) s F hF (Eventually.of_forall fun _ => rfl)
  have hi := intrinsicGermMap_original_function C p F hF
  have hz' : (actualSubspaceInclusion (n := n) C).stalkMap p
      ((actualComplexStructureSheaf (n := n) (ballDomain (n := n) d.radius)).presheaf.germ
        ⊤ p.val (by trivial) s)=0 := by
    rw [← hr]
    exact hi.symm.trans hz
  rw [hz',map_zero]

theorem baseScalar_cleared_relation (d : GraphPresentation n Z) {k : ℕ}
    (c : Fin k → ComplexModel n → ℂ) (G H : ComplexModel n → ℂ)
    (hc : ∀ i,DifferentiableOn ℂ (c i) (ballDomain (n := n) d.radius))
    (hG : DifferentiableOn ℂ G (ballDomain (n := n) d.radius))
    (hH : DifferentiableOn ℂ H (ballDomain (n := n) d.radius))
    (hv : ∀ b : d.base.obj.left,b ∈ d.baseOpen →
      (G b.val.val)^k+∑ i : Fin k,c i b.val.val*(H b.val.val)^(k-i.val)*(G b.val.val)^i.val=0) :
    (baseScalarSection d G hG)^k+∑ i : Fin k,baseScalarSection d (c i) (hc i)*
      (baseScalarSection d H hH)^(k-i.val)*(baseScalarSection d G hG)^i.val=0 := by
  let sg := ambientScalarSection (ballDomain (n := n) d.radius) G hG
  let sh := ambientScalarSection (ballDomain (n := n) d.radius) H hH
  let sc := fun i => ambientScalarSection (ballDomain (n := n) d.radius) (c i) (hc i)
  let r := sg^k+∑ i : Fin k,sc i*sh^(k-i.val)*sg^i.val
  have hz : pullTopRingHom (baseAmbientMap d) r=0 := by
    apply baseAmbientSection_zero_of_values d r
    intro b hb
    let ev := ContMDiffMap.evalRingHom (I := 𝓘(ℂ,ComplexModel n)) (I' := 𝓘(ℂ,ℂ)) (n := ∞) (R := ℂ) (⟨b.val,by trivial⟩ : (⊤ : Opens (ballDomain (n := n) d.radius)))
    change ev r=0
    simp only [r,map_add,map_pow,map_sum,map_mul]
    exact hv b hb
  simpa only [r,sg,sh,sc,baseScalarSection,map_add,map_pow,map_sum,map_mul] using hz

theorem baseScalar_graph_monic (d : GraphPresentation n Z) (deg : Fin d.arity → ℕ)
    (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius))
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (PrimeNov16AnalyticNormalizationDenominatorGraph.baseProjection n d.arity p.val.val)
      (PrimeNov16AnalyticNormalizationDenominatorGraph.fibreProjection n d.arity p.val.val i)=0)
    (hs : Function.Surjective d.map.hom.left.base) (i : Fin d.arity) :
    (baseScalarSection d (d.numerator i) (d.numerator_holo i))^(deg i)+∑ j : Fin (deg i),
      baseScalarSection d (a i j.val) (ha i j.val j.isLt)*
      (baseScalarSection d d.denominator d.denominator_holo)^(deg i-j.val)*
      (baseScalarSection d (d.numerator i) (d.numerator_holo i))^j.val=0 := by
  apply baseScalar_cleared_relation d (fun j : Fin (deg i) => a i j.val) (d.numerator i) d.denominator
    (fun j => ha i j.val j.isLt) (d.numerator_holo i) d.denominator_holo
  intro b hb
  have he := actual_whole_base_cleared d deg a hm hs (⟨b,hb⟩ : d.target.obj.left) i
  simpa only [Finset.sum_range] using he

def pulledBaseScalar {m : ℕ} (d : GraphPresentation n Z) (P : Opens (ComplexModel m))
    (C : Set P) (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) :
    ((actualSubspaceSheaf (n := m) C).presheaf.obj (op W)).carrier :=
  openTopEquiv (sourceReducedComplexSpaceModel P C hC).obj.left W
    (pullTopRingHom f.hom.left (baseScalarSection d F hF))

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
