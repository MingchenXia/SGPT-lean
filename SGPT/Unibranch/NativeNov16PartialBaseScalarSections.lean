import SGPT.Unibranch.NativeNov16OriginalPullbackValues
import SGPT.Unibranch.NativeNov16SectionGermValues
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections

/-! Partial ambient holomorphic functions produce actual sections and germs on the SAME old carrier.
Blueprint: native-nov16-partial-base-scalar-sections.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.NativeNov16PartialBaseScalarSections
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspaceResidue
open HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces
open HironakaSmoothCentreRealDomainActualSheafStalk
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal

def localAmbient {n : ℕ} (P Ω : Opens (ComplexModel n)) : Opens P :=
  ⟨(Subtype.val : P → ComplexModel n) ⁻¹' Ω,Ω.isOpen.preimage continuous_subtype_val⟩

abbrev localCarrier {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (Ω : Opens (ComplexModel n)) : Set (localAmbient P Ω) :=
  (Subtype.val : localAmbient P Ω → P) ⁻¹' C

def intoOmega {n : ℕ} (P Ω : Opens (ComplexModel n)) : localAmbient P Ω → Ω :=
  fun z => ⟨z.val.val,z.property⟩

theorem intoOmega_contMDiff {n : ℕ} (P Ω : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (intoOmega P Ω) := by
  apply (ContMDiff.subtypeVal_comp_iff Ω (intoOmega P Ω)).mp
  change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
    (fun z : localAmbient P Ω => z.val.val)
  exact (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
    (Subtype.val : P → ComplexModel n)).comp
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : localAmbient P Ω → P))

def ambientOnLocal {n : ℕ} (P Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F Ω) :
    actualComplexSection (n := n) (⊤ : Opens (localAmbient P Ω)) := by
  let a : localAmbient P Ω → (⊤ : Opens Ω) := fun z => ⟨intoOmega P Ω z,by trivial⟩
  have ha : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff ⊤ a).mp (intoOmega_contMDiff P Ω)
  exact ⟨fun z => F z.val.val.val,
    (smoothSheaf.contMDiff_section (ambientScalarSection Ω F hF)).comp
      (ha.comp contMDiff_subtype_val)⟩

private theorem lift_lands {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n))
    (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) :
    range ((actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict U.isOpenEmbedding).base ⊆
      range (actualOpenSubspaceMap (n := n) C (localAmbient P Ω)).base := by
  rintro _ ⟨x,rfl⟩
  exact ⟨⟨⟨x.val.val,hland x.val x.property⟩,x.val.property⟩,rfl⟩

def toLocalCarrier {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n))
    (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) :
    (actualSubspaceLocallyRingedSpace (n := n) C).restrict U.isOpenEmbedding ⟶
      actualSubspaceLocallyRingedSpace (n := n) (localCarrier P C Ω) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (actualOpenSubspaceMap (n := n) C (localAmbient P Ω))
    ((actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict U.isOpenEmbedding)
    (lift_lands P C U Ω hland)

theorem toLocalCarrier_fac {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n))
    (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) :
    toLocalCarrier P C U Ω hland ≫ actualOpenSubspaceMap (n := n) C (localAmbient P Ω)=
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

theorem toLocalCarrier_point {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n))
    (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) (x : U) :
    ((toLocalCarrier P C U Ω hland).base x).val.val=x.val.val :=
  congrArg (fun t : (actualSubspaceLocallyRingedSpace (n := n) C).restrict U.isOpenEmbedding ⟶
    actualSubspaceLocallyRingedSpace (n := n) C => (t.base x).val)
    (toLocalCarrier_fac P C U Ω hland)

def scalarSection {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F Ω) (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) :
    ((actualSubspaceSheaf (n := n) C).presheaf.obj (op U)).carrier :=
  openTopEquiv (actualSubspaceLocallyRingedSpace (n := n) C) U
    (pullTopRingHom (toLocalCarrier P C U Ω hland)
      (pullTopRingHom (actualSubspaceInclusion (n := n) (localCarrier P C Ω))
        (ambientOnLocal P Ω F hF)))

theorem function_holomorphicAt {n : ℕ} (P Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F Ω) (x : P) (hx : x.val ∈ Ω) :
    HolomorphicAt n (fun y : P => F y.val) x := by
  have hNear : ∀ᶠ y : P in 𝓝 x,y.val ∈ Ω := (localAmbient P Ω).isOpen.mem_nhds hx
  filter_upwards [hNear] with y hy
  exact (hF.differentiableAt (Ω.isOpen.mem_nhds hy)).mdifferentiableAt.comp y
    ((contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : P → ComplexModel n)).mdifferentiable (by simp) y)

theorem scalarSection_value {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F Ω) (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) (x : U) :
    actualSubspaceStalkEval (n := n) C x.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ U x.val x.property
        (scalarSection P C U Ω F hF hland))=F x.val.val.val := by
  let R := toLocalCarrier P C U Ω hland
  let D := localCarrier P C Ω
  let t := ambientOnLocal P Ω F hF
  have hj : actualOpenSubspaceMap (n := n) C (localAmbient P Ω) ≫ subspacePointMap (n := n) C=
      subspacePointMap (n := n) D :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
  have hp : R ≫ subspacePointMap (n := n) D=
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict U.isOpenEmbedding ≫
        subspacePointMap (n := n) C := by
    rw [← hj,← Category.assoc,toLocalCarrier_fac]
  calc
    _=actualSubspaceStalkEval (n := n) D (R.base x)
        ((actualSubspaceSheaf (n := n) D).presheaf.germ ⊤ (R.base x) (by trivial)
          (pullTopRingHom (actualSubspaceInclusion (n := n) D) t)) :=
      NativeNov16OriginalPullbackValues.pullTop_value C D U R hp x _
    _=actualSubspaceStalkEval (n := n) D (R.base x)
        ((actualSubspaceInclusion (n := n) D).stalkMap (R.base x)
          ((actualComplexStructureSheaf (n := n) (localAmbient P Ω)).presheaf.germ
            ⊤ (R.base x).val (by trivial) t)) :=
      congrArg (actualSubspaceStalkEval (n := n) D (R.base x))
        (pullTop_germ (actualSubspaceInclusion (n := n) D) t (R.base x))
    _=F (R.base x).val.val.val :=
      actualSubspaceStalkEval_inclusion_germ D ⊤ t (R.base x) (by trivial)
    _= _ := congrArg (fun z : P => F z.val) (toLocalCarrier_point P C U Ω hland x)

theorem scalarSection_germ {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := n) C) (U : Opens (TopCat.of C))
    (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F Ω)
    (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω) (x : C) (hx : x ∈ U) :
    (actualSubspaceSheaf (n := n) C).presheaf.germ U x hx (scalarSection P C U Ω F hF hland)=
      originalFunctionImage C x (fun y : P => F y.val)
        (function_holomorphicAt P Ω F hF x.val (hland x hx)) := by
  exact NativeNov16SectionGermValues.germ_eq_original_function_of_values C hC U _
    (fun y : P => F y.val) (fun y hy => scalarSection_value P C U Ω F hF hland ⟨y,hy⟩)
    x hx (function_holomorphicAt P Ω F hF x.val (hland x hx))

theorem scalarSection_unique {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
    (U : Opens (TopCat.of C)) (Ω : Opens (ComplexModel n)) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F Ω) (hland : ∀ (b : C),b ∈ U → b.val.val ∈ Ω)
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op U)).carrier)
    (hs : ∀ (y : C) (hy : y ∈ U),actualSubspaceStalkEval (n := n) C y
      ((actualSubspaceSheaf (n := n) C).presheaf.germ U y hy s)=F y.val.val) :
    s=scalarSection P C U Ω F hF hland := by
  apply actualSubspaceSection_ext_eval C U s
  intro y hy
  exact (hs y hy).trans (scalarSection_value P C U Ω F hF hland ⟨y,hy⟩).symm

end SGPT.Unibranch.NativeNov16PartialBaseScalarSections
