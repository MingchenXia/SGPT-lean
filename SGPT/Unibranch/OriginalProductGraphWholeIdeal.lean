import SGPT.Foundations.Analysis.Pending.HironakaGraphBaseChangeElimination
import SGPT.Foundations.Analysis.Pending.HironakaVanishingQuotientOriginalSubspaceBridge
import SGPT.Foundations.Analysis.Pending.HironakaFiniteSectionProductGraph
import SGPT.Foundations.Analysis.Pending.HironakaSmoothSubmersionRelativeRestriction
import SGPT.Foundations.Analysis.Pending.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! The WHOLE original ideal of the literal product graph on its real open.
BP FIRST: `original-product-graph-whole-ideal.tex`. Native product/M2 ambient
order and full original maps are constructed, never supplied. Ambient quotient
PRESHEAF stalks exist also off support; no offgraph LRS point is manufactured.
No Qsat, P0/Q0, raw-fibre comparison or nonreduced representability is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalProductGraphWholeIdeal
noncomputable section
open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualIntrinsicStableAmbientIso HironakaActualJointBaseFibre
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaGraphBaseChangeElimination HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaFiniteSectionProductGraph
  HironakaReducedComplexAnalyticSpaces HironakaNonreducedAnalyticQuotientModel
  HironakaVanishingQuotientOriginalSubspaceBridge
  HironakaSmoothCentreRealDomainActualSheafStalk
open scoped ProductComplexManifold

variable {n r : ℕ}

/-- The genuine target coordinate open, without extending the functions on P. -/
def targetOpen (r : ℕ) : Opens (ComplexModel r) := ⊤

/-- Actual source-normal product versus the base-first M2 coordinate open. -/
def productGraphAmbientOrderDiffeomorph (P : Opens (ComplexModel n)) (r : ℕ) :
    (P × ComplexModel r) ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (r+n))⟯
      graphOpen P (targetOpen r) where
  toFun p := ⟨join p.2 p.1.val,by
    change tangentProjection r n (join p.2 p.1.val) ∈ targetOpen r ∧
      actualJointNormalProjection r n (join p.2 p.1.val) ∈ P
    rw [first_join,second_join]
    exact ⟨mem_univ _,p.1.property⟩⟩
  invFun w := (graphSource P (targetOpen r) w,(graphTarget P (targetOpen r) w).val)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact second_join _ _
    · exact first_join _ _
  right_inv w := by
    apply Subtype.ext
    exact join_projections w.val
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (graphOpen P (targetOpen r)) _).mp
    exact ((tangentInclusion r n).contDiff.contMDiff.comp
      ProductComplexManifold.contMDiff_snd).add
        ((actualJointNormalInclusion r n).contDiff.contMDiff.comp
          (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst))
  contMDiff_invFun :=
    ProductComplexManifold.contMDiff_prodMk (graphSource_holomorphic P (targetOpen r))
      (contMDiff_subtype_val.comp (graphTarget_holomorphic P (targetOpen r)))

/-- The literal same function, with only its target-open subtype attached. -/
def targetFunction (P : Opens (ComplexModel n)) (G : P → ComplexModel r) : P → targetOpen r :=
  fun p => ⟨G p,mem_univ _⟩

theorem targetFunction_holomorphic (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ (targetFunction P G) :=
  (ContMDiff.subtypeVal_comp_iff (targetOpen r) _).mp hG

theorem ambientOrder_graphMap (P : Opens (ComplexModel n)) (G : P → ComplexModel r) :
    (fun p => productGraphAmbientOrderDiffeomorph P r (p,G p)) =
      graphMap P (targetOpen r) (targetFunction P G) := rfl

theorem ambientOrder_source (P : Opens (ComplexModel n)) :
    graphSource P (targetOpen r) ∘ productGraphAmbientOrderDiffeomorph P r =
      (Prod.fst : P × ComplexModel r → P) := by
  funext p
  apply Subtype.ext
  exact second_join _ _

theorem ambientOrder_target (P : Opens (ComplexModel n)) :
    (fun p : P × ComplexModel r =>
      (graphTarget P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r p)).val) =
        Prod.snd := by
  funext p
  exact first_join _ _

def ambientOrderMorphism (P : Opens (ComplexModel n)) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (r+n)) (graphOpen P (targetOpen r)) :=
  ChartedSpace.locallyRingedSpaceMap (productGraphAmbientOrderDiffeomorph P r)
    (productGraphAmbientOrderDiffeomorph P r).contMDiff

theorem ambientOrderMorphism_graph (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    ChartedSpace.locallyRingedSpaceMap (fun p : P => (p,G p))
        (ProductComplexManifold.contMDiff_prodMk contMDiff_id hG) ≫ ambientOrderMorphism P =
      ChartedSpace.locallyRingedSpaceMap (graphMap P (targetOpen r) (targetFunction P G))
        (graphMap_holomorphic P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)) := by
  exact (ChartedSpace.locallyRingedSpace_comp
    (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel (n+r)))
    (IP := 𝓘(ℂ,ComplexModel (r+n)))
    (ProductComplexManifold.contMDiff_prodMk contMDiff_id hG)
    (productGraphAmbientOrderDiffeomorph P r).contMDiff).symm

theorem ambientOrderMorphism_source (P : Opens (ComplexModel n)) :
    ambientOrderMorphism (r := r) P ≫
      ChartedSpace.locallyRingedSpaceMap (graphSource P (targetOpen r))
        (graphSource_holomorphic P (targetOpen r)) =
      ChartedSpace.locallyRingedSpaceMap (Prod.fst : P × ComplexModel r → P)
        ProductComplexManifold.contMDiff_fst := by
  rw [ambientOrderMorphism,←ChartedSpace.locallyRingedSpace_comp]
  have he := ambientOrder_source (r := r) P
  simp only [he]

theorem ambientOrderMorphism_target (P : Opens (ComplexModel n)) :
    ambientOrderMorphism (r := r) P ≫
      ChartedSpace.locallyRingedSpaceMap (fun w : graphOpen P (targetOpen r) => (graphTarget P (targetOpen r) w).val)
        (contMDiff_subtype_val.comp (graphTarget_holomorphic P (targetOpen r))) =
      ChartedSpace.locallyRingedSpaceMap (Prod.snd : P × ComplexModel r → ComplexModel r)
        ProductComplexManifold.contMDiff_snd := by
  rw [ambientOrderMorphism,←ChartedSpace.locallyRingedSpace_comp]
  have he : (fun w : graphOpen P (targetOpen r) => (graphTarget P (targetOpen r) w).val) ∘
      productGraphAmbientOrderDiffeomorph P r = (Prod.snd : P × ComplexModel r → ComplexModel r) :=
    ambientOrder_target P
  simp only [he]

theorem ambientOrderMorphism_point (P : Opens (ComplexModel n)) :
    ambientOrderMorphism (r := r) P ≫ ambientPointMap (r+n) (graphOpen P (targetOpen r)) =
      ambientPointMap (n+r) (P × ComplexModel r) := by
  unfold ambientOrderMorphism ambientPointMap
  exact (ChartedSpace.locallyRingedSpace_comp
    (IM := 𝓘(ℂ,ComplexModel (n+r))) (IN := 𝓘(ℂ,ComplexModel (r+n)))
    (IP := 𝓘(ℂ,ComplexModel 0))
    (productGraphAmbientOrderDiffeomorph P r).contMDiff
    (show ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel 0) ∞
      (fun _ : graphOpen P (targetOpen r) => (0 : ComplexModel 0)) from contMDiff_const)).symm

open RestrictedIdealExtension GermIdealPullbackCalculus RelativePrincipalizationSpan
  HironakaNonreducedQuotientNeighborhoodLifting

/-- The literal finite differences on the SAME native product ambient. -/
def productGraphEquation (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (i : Fin r) (w : P × ComplexModel r) : ℂ := w.2 i-G w.1 i

theorem productGraphEquation_holomorphic (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ℂ) ∞ (productGraphEquation P G i) :=
  ((EuclideanSpace.proj i).contDiff.contMDiff.comp ProductComplexManifold.contMDiff_snd).sub
    ((EuclideanSpace.proj i).contDiff.contMDiff.comp (hG.comp ProductComplexManifold.contMDiff_fst))

def productGraphEquations (P : Opens (ComplexModel n)) (G : P → ComplexModel r) :
    GermIdeal (n+r) (P × ComplexModel r) where
  mem w a := IsInSpanAt (n := n+r) (· ∈ range (productGraphEquation P G)) w a

theorem productGraphEquations_coherent (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (productGraphEquations P G).IsCoherent := by
  intro w
  refine ⟨univ,isOpen_univ,mem_univ _,r,productGraphEquation P G,?_,?_⟩
  · intro i
    exact ((productGraphEquation_holomorphic P G hG i).mdifferentiable (by simp)).mdifferentiableOn
  · intro z _ a
    rfl

/-- The ENTIRE original source pull and the SAME literal graph equations. -/
def productGraphIdeal (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    GermIdeal (n+r) (P × ComplexModel r) :=
  sumIdeal (GermIdeal.pullback (m := n+r) (Prod.fst : P × ComplexModel r → P)
    (vanishingIdeal (n := n) S)) (productGraphEquations P G)

theorem productGraphIdeal_coherent (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (productGraphIdeal P S G).IsCoherent :=
  isCoherent_sumIdeal
    (isCoherent_pullback ProductComplexManifold.contMDiff_fst (CartanIrreducible.cartanCoherence S hS))
    (productGraphEquations_coherent P G hG)

/-- Genuine ambient PRESHEAF stalk map, also where the quotient ring is zero. -/
def productGraphAmbientStalkHom (P : Opens (ComplexModel n)) (S : Set P)
    (G : P → ComplexModel r) (w : P × ComplexModel r) :
    actualComplexStructureStalk (n := n+r) w →+*
      ((quotientPresheaf (productGraphIdeal P S G)).stalk w).carrier :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (P × ComplexModel r)) CommRingCat w).map
    (quotientAmbientPresheafMap (productGraphIdeal P S G))).hom

theorem productGraphAmbientStalkHom_all_numerators (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : P × ComplexModel r) (a : actualComplexStructureStalk (n := n+r) w) :
    rawStalkWholeEquiv (productGraphIdeal P S G) (productGraphIdeal_coherent P S hS G hG) w
      (productGraphAmbientStalkHom P S G w a) =
        Ideal.Quotient.mk (actualWholeSheafStalkIdeal (productGraphIdeal P S G) w) a := by
  obtain ⟨U,hw,s,rfl⟩ := (actualComplexStructureSheaf (n := n+r) (P × ComplexModel r)).presheaf.exists_germ_eq a
  change rawStalkWholeEquiv (productGraphIdeal P S G) (productGraphIdeal_coherent P S hS G hG) w
    (((TopCat.Presheaf.stalkFunctor CommRingCat w).map
      (quotientAmbientPresheafMap (productGraphIdeal P S G)))
        ((actualComplexStructureSheaf (n := n+r) (P × ComplexModel r)).presheaf.germ U w hw s)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact rawStalkWholeEquiv_germ_mk (productGraphIdeal P S G)
    (productGraphIdeal_coherent P S hS G hG) U w hw s

theorem productGraphAmbientStalkHom_kernel_ideal (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : P × ComplexModel r) :
    RingHom.ker (productGraphAmbientStalkHom P S G w) =
      actualWholeSheafStalkIdeal (productGraphIdeal P S G) w := by
  ext a
  change productGraphAmbientStalkHom P S G w a=0 ↔ _
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (productGraphAmbientStalkHom_all_numerators P S hS G hG w a).symm.trans
      ((congrArg (rawStalkWholeEquiv (productGraphIdeal P S G)
        (productGraphIdeal_coherent P S hS G hG) w) h).trans (map_zero _))
  · intro h
    apply (rawStalkWholeEquiv (productGraphIdeal P S G)
      (productGraphIdeal_coherent P S hS G hG) w).injective
    rw [productGraphAmbientStalkHom_all_numerators P S hS G hG w a,map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- The FULL original graph map to its actual ambient. -/
def productGraphAmbientMorphism (P : Opens (ComplexModel n)) (S : Set P)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    actualSubspaceLocallyRingedSpace (n := n) S ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) :=
  actualSubspaceInclusion S ≫ ChartedSpace.locallyRingedSpaceMap (fun p : P => (p,G p))
    (ProductComplexManifold.contMDiff_prodMk contMDiff_id hG)

theorem productGraphAmbientMorphism_point (P : Opens (ComplexModel n)) (S : Set P)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    productGraphAmbientMorphism P S G hG ≫ ambientPointMap (n+r) (P × ComplexModel r) =
      subspacePointMap (n := n) S := by
  have hp : ChartedSpace.locallyRingedSpaceMap (fun p : P => (p,G p))
      (ProductComplexManifold.contMDiff_prodMk contMDiff_id hG) ≫
        ambientPointMap (n+r) (P × ComplexModel r) = ambientPointMap n P := by
    exact (ChartedSpace.locallyRingedSpace_comp
      (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel (n+r)))
      (IP := 𝓘(ℂ,ComplexModel 0))
      (ProductComplexManifold.contMDiff_prodMk contMDiff_id hG)
      (show ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel 0) ∞
        (fun _ : P × ComplexModel r => (0 : ComplexModel 0)) from contMDiff_const)).symm
  exact (Category.assoc _ _ _).trans (congrArg (fun f => actualSubspaceInclusion S ≫ f) hp)

theorem productGraphAmbientMorphism_stalk_kernel_vanishing
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (s : S) :
    RingHom.ker ((productGraphAmbientMorphism P S G hG).stalkMap s).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) (productGraph S G))
        ((s.val,G s.val) : P × ComplexModel r) := by
  let E := productGraphIso S G hG
  let i := actualSubspaceInclusion (n := n+r) (productGraph S G)
  have hs := LocallyRingedSpace.stalkMap_congr_hom (E.hom ≫ i)
    (productGraphAmbientMorphism P S G hG) (productGraphIso_inclusion S G hG) s
  change (E.hom ≫ i).stalkMap s =
    (actualComplexStructureSheaf (n := n+r) (P × ComplexModel r)).presheaf.stalkSpecializes
      (specializes_of_eq (rfl : ((s.val,G s.val) : P × ComplexModel r)=(s.val,G s.val))) ≫
        (productGraphAmbientMorphism P S G hG).stalkMap s at hs
  rw [TopCat.Presheaf.stalkSpecializes_refl] at hs
  have he := hs.trans (Category.id_comp _)
  have hk := congrArg (fun f => RingHom.ker f.hom) he
  rw [LocallyRingedSpace.stalkMap_comp] at hk
  change RingHom.ker ((E.hom.stalkMap s).hom.comp (i.stalkMap (E.hom.base s)).hom) =
    RingHom.ker ((productGraphAmbientMorphism P S G hG).stalkMap s).hom at hk
  have hi : Function.Injective (E.hom.stalkMap s).hom :=
    (asIso (E.hom.stalkMap s)).commRingCatIsoToRingEquiv.injective
  have hc := RingHom.ker_comp_of_injective (i.stalkMap (E.hom.base s)).hom hi
  exact hk.symm.trans (hc.trans (actualSubspaceInclusion_stalk_kernel (productGraph S G) (E.hom.base s)))

private def baseFirstCarrier (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    Set (graphOpen P (targetOpen r)) :=
  {w | graphSource P (targetOpen r) w ∈ S ∧
    (graphTarget P (targetOpen r) w).val=G (graphSource P (targetOpen r) w)}

private theorem ambientOrder_carrier (P : Opens (ComplexModel n)) (S : Set P)
    (G : P → ComplexModel r) (w : P × ComplexModel r) :
    w ∈ productGraph S G ↔ productGraphAmbientOrderDiffeomorph P r w ∈ baseFirstCarrier P S G := by
  change w.1∈S ∧ w.2=G w.1 ↔ _
  change _ ↔ graphSource P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w) ∈ S ∧
    (graphTarget P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)).val=
      G (graphSource P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w))
  have hs : graphSource P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)=w.1 :=
    congrFun (ambientOrder_source (r := r) P) w
  have ht : (graphTarget P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)).val=w.2 :=
    congrFun (ambientOrder_target (r := r) P) w
  rw [hs,ht]

private def ambientOrderSubspaceIso (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    actualSubspaceLocallyRingedSpace (n := n+r) (productGraph S G) ≅
      actualSubspaceLocallyRingedSpace (n := r+n) (baseFirstCarrier P S G) :=
  actualSubspaceBiholomorphicIso (productGraphAmbientOrderDiffeomorph P r)
    (productGraph S G) (baseFirstCarrier P S G) (ambientOrder_carrier P S G)

private theorem ambientOrderSubspaceIso_inclusion
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    (ambientOrderSubspaceIso P S G).hom ≫ actualSubspaceInclusion (n := r+n) (baseFirstCarrier P S G) =
      actualSubspaceInclusion (n := n+r) (productGraph S G) ≫ ambientOrderMorphism P :=
  (actualSubspaceMap_inclusion (productGraphAmbientOrderDiffeomorph P r).contMDiff
    (fun w hw => (ambientOrder_carrier P S G w).mp hw)).symm

private def sourceToActualBaseFirstGraphIso (P : Opens (ComplexModel n)) (S : Set P)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    actualSubspaceLocallyRingedSpace (n := n) S ≅
      actualSubspaceLocallyRingedSpace (n := r+n) (baseFirstCarrier P S G) :=
  (productGraphIso S G hG).trans (ambientOrderSubspaceIso P S G)

private theorem sourceToActualBaseFirstGraphIso_inclusion
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (sourceToActualBaseFirstGraphIso P S G hG).hom ≫
        actualSubspaceInclusion (n := r+n) (baseFirstCarrier P S G) =
      actualSubspaceInclusion (n := n) S ≫
        ChartedSpace.locallyRingedSpaceMap (graphMap P (targetOpen r) (targetFunction P G))
          (graphMap_holomorphic P (targetOpen r) (targetFunction P G)
            (targetFunction_holomorphic P G hG)) := by
  change ((productGraphIso S G hG).hom ≫ (ambientOrderSubspaceIso P S G).hom) ≫ _ = _
  rw [Category.assoc,ambientOrderSubspaceIso_inclusion,←Category.assoc,
    productGraphIso_inclusion S G hG,Category.assoc,ambientOrderMorphism_graph P G hG]

private def baseFirstIdeal (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    GermIdeal (r+n) (graphOpen P (targetOpen r)) :=
  graphIdeal P (targetOpen r) (targetFunction P G) (vanishingIdeal (n := n) S)

private theorem baseFirstIdeal_coherent (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (baseFirstIdeal P S G).IsCoherent :=
  graphIdeal_coherent P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)
    (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS)

-- Rebase the COMMON Q(I_S) by its actual bridge only to make native source
-- points literal; the two independent full source isomorphisms are unchanged.
private def sourceToM2GraphIso (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    actualSubspaceLocallyRingedSpace (n := n) S ≅
      quotientLocallyRingedSpace (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) :=
  (vanishingQuotientOriginalSubspaceIso S hS).symm.trans
    (graphQuotientIso P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)
      (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS))

private theorem sourceToM2GraphIso_inclusion
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (sourceToM2GraphIso P S hS G hG).hom ≫
        quotientInclusion (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) =
      actualSubspaceInclusion (n := n) S ≫
        ChartedSpace.locallyRingedSpaceMap (graphMap P (targetOpen r) (targetFunction P G))
          (graphMap_holomorphic P (targetOpen r) (targetFunction P G)
            (targetFunction_holomorphic P G hG)) := by
  change ((vanishingQuotientOriginalSubspaceIso S hS).inv ≫
    (graphQuotientIso P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)
      (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS)).hom) ≫ _ = _
  calc
    _ = (vanishingQuotientOriginalSubspaceIso S hS).inv ≫
        ((graphQuotientIso P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)
          (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS)).hom ≫
            quotientInclusion (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG)) :=
      Category.assoc _ _ _
    _ = (vanishingQuotientOriginalSubspaceIso S hS).inv ≫
        (quotientInclusion (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS) ≫
          ChartedSpace.locallyRingedSpaceMap (graphMap P (targetOpen r) (targetFunction P G))
            (graphMap_holomorphic P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG))) :=
      congrArg (fun f => (vanishingQuotientOriginalSubspaceIso S hS).inv ≫ f)
        (graphQuotientIso_ambient P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)
          (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS))
    _ = ((vanishingQuotientOriginalSubspaceIso S hS).inv ≫
        quotientInclusion (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS)) ≫
          ChartedSpace.locallyRingedSpaceMap (graphMap P (targetOpen r) (targetFunction P G))
            (graphMap_holomorphic P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ ChartedSpace.locallyRingedSpaceMap
      (graphMap P (targetOpen r) (targetFunction P G))
        (graphMap_holomorphic P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)))
      (bridge_inv_inclusion S hS)

private def baseFirstGraphComparisonIso (P : Opens (ComplexModel n)) (S : Set P)
    (hS : IsComplexAnalyticSubset (n := n) S) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    quotientLocallyRingedSpace (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) ≅
      actualSubspaceLocallyRingedSpace (n := r+n) (baseFirstCarrier P S G) :=
  (sourceToM2GraphIso P S hS G hG).symm.trans (sourceToActualBaseFirstGraphIso P S G hG)

private theorem baseFirstGraphComparisonIso_inclusion
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (baseFirstGraphComparisonIso P S hS G hG).hom ≫
        actualSubspaceInclusion (n := r+n) (baseFirstCarrier P S G) =
      quotientInclusion (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) := by
  apply (cancel_epi (sourceToM2GraphIso P S hS G hG).hom).mp
  change (sourceToM2GraphIso P S hS G hG).hom ≫
    ((sourceToM2GraphIso P S hS G hG).inv ≫ (sourceToActualBaseFirstGraphIso P S G hG).hom) ≫ _ = _
  have hi := congrArg (fun f => f ≫ (sourceToActualBaseFirstGraphIso P S G hG).hom ≫
    actualSubspaceInclusion (baseFirstCarrier P S G)) (sourceToM2GraphIso P S hS G hG).hom_inv_id
  have hh : (sourceToM2GraphIso P S hS G hG).hom ≫
      ((sourceToM2GraphIso P S hS G hG).inv ≫ (sourceToActualBaseFirstGraphIso P S G hG).hom) ≫
        actualSubspaceInclusion (baseFirstCarrier P S G) =
      (sourceToActualBaseFirstGraphIso P S G hG).hom ≫ actualSubspaceInclusion (baseFirstCarrier P S G) :=
    (Category.assoc _ _ _).trans ((Category.assoc _ _ _).symm.trans
      (hi.trans (Category.id_comp _)))
  exact hh.trans ((sourceToActualBaseFirstGraphIso_inclusion P S G hG).trans
    (sourceToM2GraphIso_inclusion P S hS G hG).symm)

private theorem baseFirstGraphComparisonIso_point
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (baseFirstGraphComparisonIso P S hS G hG).hom ≫ subspacePointMap (n := r+n) (baseFirstCarrier P S G) =
      quotientPointMap (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) := by
  have h := congrArg (fun f => f ≫ ambientPointMap (r+n) (graphOpen P (targetOpen r)))
    (baseFirstGraphComparisonIso_inclusion P S hS G hG)
  exact (Category.assoc _ _ _).symm.trans h

open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback

-- Conjugating native kernels to the SAME preferred chart ring makes full-map
-- congruence honest even when their native ambient image points are dependent.
private def ambientKernelChart {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {A : LocallyRingedSpace.{0}}
    (f : A ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k) M) (x : A) :
    Ideal (HolGerm (ComplexModel k)) :=
  Ideal.comap (actualStalkChartEquiv (n := k) (show M from f.base x)).symm.toRingHom
    (RingHom.ker (f.stalkMap x).hom)

private theorem ambientKernelChart_precomp_iso {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {A B : LocallyRingedSpace.{0}}
    (E : A ≅ B) (f : B ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k) M) (x : A) :
    ambientKernelChart (E.hom ≫ f) x = ambientKernelChart f (E.hom.base x) := by
  have hs := LocallyRingedSpace.stalkMap_comp E.hom f x
  have hk := congrArg (fun h => RingHom.ker h.hom) hs
  change RingHom.ker ((E.hom ≫ f).stalkMap x).hom =
    RingHom.ker ((E.hom.stalkMap x).hom.comp (f.stalkMap (E.hom.base x)).hom) at hk
  have hi : Function.Injective (E.hom.stalkMap x).hom :=
    (asIso (E.hom.stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact congrArg (Ideal.comap (actualStalkChartEquiv (n := k) (show M from f.base (E.hom.base x))).symm.toRingHom)
    (hk.trans (RingHom.ker_comp_of_injective _ hi))

private theorem ambientKernelChart_quotient {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (I : GermIdeal k M) (hI : I.IsCoherent) (x : I.zeroLocus) :
    ambientKernelChart (quotientInclusion I hI) x =
      wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val) := by
  unfold ambientKernelChart
  rw [quotientInclusion_stalk_kernel]
  exact (Ideal.comap_symm (actualStalkChartEquiv (n := k) x.val)).trans
    (map_actualWholeSheafStalkIdeal I x.val)

private theorem ambientKernelChart_actual {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] (C : Set M) (x : C) :
    ambientKernelChart (actualSubspaceInclusion (n := k) C) x =
      wholeChartStalkIdeal (vanishingIdeal (n := k) C) x.val x.val (mem_chart_source _ x.val) := by
  unfold ambientKernelChart
  rw [actualSubspaceInclusion_stalk_kernel]
  exact (Ideal.comap_symm (actualStalkChartEquiv (n := k) x.val)).trans
    (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := k) C) x.val)

private theorem sourceToM2GraphIso_base
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (s : S) :
    ((sourceToM2GraphIso P S hS G hG).hom.base s).val =
      graphMap P (targetOpen r) (targetFunction P G) s.val := rfl

private theorem sourceToActualBaseFirstGraphIso_base
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (s : S) :
    ((sourceToActualBaseFirstGraphIso P S G hG).hom.base s).val =
      graphMap P (targetOpen r) (targetFunction P G) s.val := rfl

private theorem baseFirst_whole_ideal_at_graph_point
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (s : S) :
    wholeChartStalkIdeal (baseFirstIdeal P S G)
        (graphMap P (targetOpen r) (targetFunction P G) s.val)
        (graphMap P (targetOpen r) (targetFunction P G) s.val) (mem_chart_source _ _) =
      wholeChartStalkIdeal (vanishingIdeal (n := r+n) (baseFirstCarrier P S G))
        (graphMap P (targetOpen r) (targetFunction P G) s.val)
        (graphMap P (targetOpen r) (targetFunction P G) s.val) (mem_chart_source _ _) := by
  let E := sourceToM2GraphIso P S hS G hG
  let D := sourceToActualBaseFirstGraphIso P S G hG
  let q := quotientInclusion (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG)
  let i := actualSubspaceInclusion (n := r+n) (baseFirstCarrier P S G)
  have hs : E.hom ≫ q = D.hom ≫ i :=
    (sourceToM2GraphIso_inclusion P S hS G hG).trans (sourceToActualBaseFirstGraphIso_inclusion P S G hG).symm
  have hk := congrArg (fun f : actualSubspaceLocallyRingedSpace (n := n) S ⟶
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (r+n)) (graphOpen P (targetOpen r)) =>
      ambientKernelChart f s) hs
  have h := (ambientKernelChart_quotient (baseFirstIdeal P S G)
    (baseFirstIdeal_coherent P S hS G hG) (E.hom.base s)).symm.trans
      ((ambientKernelChart_precomp_iso E q s).symm.trans
        (hk.trans ((ambientKernelChart_precomp_iso D i s).trans
          (ambientKernelChart_actual (baseFirstCarrier P S G) (D.hom.base s)))))
  exact h

private theorem baseFirstCarrier_graphMap
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r)
    (w : graphOpen P (targetOpen r)) (hw : w ∈ baseFirstCarrier P S G) :
    graphMap P (targetOpen r) (targetFunction P G) (graphSource P (targetOpen r) w)=w := by
  apply Subtype.ext
  change join (G (graphSource P (targetOpen r) w)) (actualJointNormalProjection r n w.val)=w.val
  rw [←hw.2]
  exact join_projections w.val

private theorem baseFirstCarrier_analytic
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    IsComplexAnalyticSubset (n := r+n) (baseFirstCarrier P S G) := by
  have he : baseFirstCarrier P S G =
      (productGraphAmbientOrderDiffeomorph P r).symm ⁻¹' productGraph S G := by
    ext w
    exact ((ambientOrder_carrier P S G ((productGraphAmbientOrderDiffeomorph P r).symm w)).trans
      (by rw [(productGraphAmbientOrderDiffeomorph P r).apply_symm_apply])).symm
  rw [he]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (productGraphAmbientOrderDiffeomorph P r).symm.contMDiff (productGraph_analytic S hS G hG)

private theorem baseFirst_unit_off_graph
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : graphOpen P (targetOpen r))
    (hw : (graphTarget P (targetOpen r) w).val ≠ G (graphSource P (targetOpen r) w)) :
    wholeChartStalkIdeal (baseFirstIdeal P S G) w w (mem_chart_source _ w) = ⊤ := by
  classical
  have hi : ∃ i : Fin r, graphEquation P (targetOpen r) (targetFunction P G) i w ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    ext i
    exact sub_eq_zero.mp (h i)
  obtain ⟨i,hi⟩ := hi
  have hh (j : Fin r) : HolomorphicAt (r+n)
      (graphEquation P (targetOpen r) (targetFunction P G) j) w :=
    Eventually.of_forall fun _ =>
      ((graphEquation_holomorphic P (targetOpen r) (targetFunction P G)
        (targetFunction_holomorphic P G hG) j).mdifferentiable (by simp)).mdifferentiableAt
  have hm : (graphEquations P (targetOpen r) (targetFunction P G)).mem w
      (graphEquation P (targetOpen r) (targetFunction P G) i) :=
    CoherentIdealColon.isInSpanAt_range_self hh i
  have hmA : (baseFirstIdeal P S G).mem w
      (graphEquation P (targetOpen r) (targetFunction P G) i) :=
    le_sumIdeal_right (graphEquations_coherent P (targetOpen r) (targetFunction P G)
      (targetFunction_holomorphic P G hG)) _ _ hm
  exact chartIdeal_eq_top_off_support (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) w
    (fun h => hi (h _ hmA))

private theorem baseFirst_unit_off_source
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : graphOpen P (targetOpen r)) (hw : graphSource P (targetOpen r) w ∉ S) :
    wholeChartStalkIdeal (baseFirstIdeal P S G) w w (mem_chart_source _ w) = ⊤ := by
  have hone : (vanishingIdeal (n := n) S).mem (graphSource P (targetOpen r) w)
      (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hw] with p hp hpS
    exact False.elim (hp hpS)
  have hpull : (GermIdeal.pullback (m := r+n) (graphSource P (targetOpen r))
      (vanishingIdeal (n := n) S)).mem w ((fun _ : P => (1 : ℂ)) ∘ graphSource P (targetOpen r)) :=
    GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨fun _ : P => (1 : ℂ),hone,rfl⟩ (holomorphicAt_const 1))
  have hmA : (baseFirstIdeal P S G).mem w ((fun _ : P => (1 : ℂ)) ∘ graphSource P (targetOpen r)) :=
    le_sumIdeal_left (isCoherent_pullback (graphSource_holomorphic P (targetOpen r))
      (CartanIrreducible.cartanCoherence S hS)) _ _ hpull
  exact chartIdeal_eq_top_off_support (baseFirstIdeal P S G) (baseFirstIdeal_coherent P S hS G hG) w
    (fun h => one_ne_zero (h _ hmA))

private theorem baseFirst_vanishing_unit_off_carrier
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : graphOpen P (targetOpen r)) (hw : w ∉ baseFirstCarrier P S G) :
    wholeChartStalkIdeal (vanishingIdeal (n := r+n) (baseFirstCarrier P S G)) w w
      (mem_chart_source _ w) = ⊤ := by
  have hC := baseFirstCarrier_analytic P S hS G hG
  have hz := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := r+n) hC.isClosed
  apply chartIdeal_eq_top_off_support _ (CartanIrreducible.cartanCoherence _ hC) w
  rwa [hz]

private theorem baseFirst_whole_ideal_all_points
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : graphOpen P (targetOpen r)) :
    wholeChartStalkIdeal (baseFirstIdeal P S G) w w (mem_chart_source _ w) =
      wholeChartStalkIdeal (vanishingIdeal (n := r+n) (baseFirstCarrier P S G)) w w (mem_chart_source _ w) := by
  classical
  by_cases hg : (graphTarget P (targetOpen r) w).val = G (graphSource P (targetOpen r) w)
  · by_cases hs : graphSource P (targetOpen r) w ∈ S
    · let s : S := ⟨graphSource P (targetOpen r) w,hs⟩
      have h := baseFirst_whole_ideal_at_graph_point P S hS G hG s
      have he := baseFirstCarrier_graphMap P S G w ⟨hs,hg⟩
      simpa only [s,he] using h
    · exact (baseFirst_unit_off_source P S hS G hG w hs).trans
        (baseFirst_vanishing_unit_off_carrier P S hS G hG w (fun h => hs h.1)).symm
  · exact (baseFirst_unit_off_graph P S hS G hG w hg).trans
      (baseFirst_vanishing_unit_off_carrier P S hS G hG w (fun h => hg h.2)).symm

private theorem baseFirst_ideal_eq_vanishing
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    baseFirstIdeal P S G = vanishingIdeal (n := r+n) (baseFirstCarrier P S G) := by
  have hA := baseFirstIdeal_coherent P S hS G hG
  have hC := CartanIrreducible.cartanCoherence _ (baseFirstCarrier_analytic P S hS G hG)
  apply GermIdeal.ext
  funext w a
  apply propext
  constructor
  · intro ha
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hA ha
    apply (coherent_mem_iff_whole_chart _ hC w a hh).mpr
    exact (baseFirst_whole_ideal_all_points P S hS G hG w) ▸
      (coherent_mem_iff_whole_chart _ hA w a hh).mp ha
  · intro ha
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hC ha
    apply (coherent_mem_iff_whole_chart _ hA w a hh).mpr
    exact (baseFirst_whole_ideal_all_points P S hS G hG w).symm ▸
      (coherent_mem_iff_whole_chart _ hC w a hh).mp ha

private theorem ambientOrder_pull_source_ideal
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S) :
    GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r)
        (GermIdeal.pullback (m := r+n) (graphSource P (targetOpen r)) (vanishingIdeal (n := n) S)) =
      GermIdeal.pullback (m := n+r) (Prod.fst : P × ComplexModel r → P) (vanishingIdeal (n := n) S) :=
  (HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp
    (graphSource_holomorphic P (targetOpen r)) (productGraphAmbientOrderDiffeomorph P r).contMDiff
    (vanishingIdeal (n := n) S) (CartanIrreducible.cartanCoherence S hS)).symm.trans
      (congrArg (fun f => GermIdeal.pullback (m := n+r) f (vanishingIdeal (n := n) S))
        (ambientOrder_source (r := r) P))

private theorem ambientOrder_pull_graph_equations
    (P : Opens (ComplexModel n)) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r)
        (graphEquations P (targetOpen r) (targetFunction P G)) = productGraphEquations P G := by
  have he : (fun i : Fin r => graphEquation P (targetOpen r) (targetFunction P G) i ∘
      productGraphAmbientOrderDiffeomorph P r) = productGraphEquation P G := by
    funext i w
    have hs : graphSource P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)=w.1 :=
      congrFun (ambientOrder_source (r := r) P) w
    have ht : (graphTarget P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)).val=w.2 :=
      congrFun (ambientOrder_target (r := r) P) w
    change (graphTarget P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)).val i-
      G (graphSource P (targetOpen r) (productGraphAmbientOrderDiffeomorph P r w)) i=w.2 i-G w.1 i
    rw [hs,ht]
  apply GermIdeal.ext
  funext w a
  apply propext
  have hh (i : Fin r) : HolomorphicAt (r+n)
      (graphEquation P (targetOpen r) (targetFunction P G) i) (productGraphAmbientOrderDiffeomorph P r w) :=
    Eventually.of_forall fun _ =>
      ((graphEquation_holomorphic P (targetOpen r) (targetFunction P G)
        (targetFunction_holomorphic P G hG) i).mdifferentiable (by simp)).mdifferentiableAt
  have h := HironakaSmoothSubmersionRelativeRestriction.pullback_mem_iff_finite_family
    (I := graphEquations P (targetOpen r) (targetFunction P G)) (y := w)
    (productGraphAmbientOrderDiffeomorph P r).contMDiff
    (graphEquation P (targetOpen r) (targetFunction P G)) hh (fun _ => Iff.rfl) a
  rw [he] at h
  exact h

private theorem ambientOrder_pull_ideal
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r) (baseFirstIdeal P S G) =
      productGraphIdeal P S G := by
  change GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r)
    (sumIdeal (GermIdeal.pullback (m := r+n) (graphSource P (targetOpen r)) (vanishingIdeal (n := n) S))
      (graphEquations P (targetOpen r) (targetFunction P G))) = _
  rw [HironakaSmoothSubmersionRelativeRestriction.pullback_sumIdeal_dimensions
    (productGraphAmbientOrderDiffeomorph P r).contMDiff
      (isCoherent_pullback (graphSource_holomorphic P (targetOpen r)) (CartanIrreducible.cartanCoherence S hS))
      (graphEquations_coherent P (targetOpen r) (targetFunction P G) (targetFunction_holomorphic P G hG)),
    ambientOrder_pull_source_ideal P S hS,ambientOrder_pull_graph_equations P G hG]
  rfl

-- Thin whole-vanishing transport for this ACTUAL inverse pair. Existing same-
-- dimension engines have different model indices n+r/r+n; no dimension cast,
-- nonreduced point faithfulness or generic new engine credit is introduced.
private theorem ambientOrder_pull_vanishing
    (P : Opens (ComplexModel n)) (S : Set P) (G : P → ComplexModel r) :
    GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r)
        (vanishingIdeal (n := r+n) (baseFirstCarrier P S G)) =
      vanishingIdeal (n := n+r) (productGraph S G) := by
  let β := productGraphAmbientOrderDiffeomorph P r
  apply GermIdeal.ext
  funext w a
  apply propext
  constructor
  · intro ha
    obtain ⟨hhol,N,s,c,hs,_hc,he⟩ := GermIdeal.mem_pullback_iff.mp ha
    refine ⟨hhol,?_⟩
    have hz : ∀ i, ∀ᶠ q in 𝓝 w, q ∈ productGraph S G → s i q=0 := by
      intro i
      obtain ⟨b,hb,hsb⟩ := hs i
      filter_upwards [(β.continuous.tendsto w).eventually hb.2] with q hq hΓ
      rw [hsb]
      exact hq ((ambientOrder_carrier P S G q).mp hΓ)
    filter_upwards [he,eventually_all.mpr hz] with q he hz hΓ
    rw [he]
    exact Finset.sum_eq_zero fun i _ => by rw [hz i hΓ,mul_zero]
  · intro ha
    let b : graphOpen P (targetOpen r) → ℂ := a ∘ β.symm
    have hh : HolomorphicAt (n+r) a (β.symm (β w)) := by
      rw [β.symm_apply_apply]
      exact ha.1
    have hbh : HolomorphicAt (r+n) b (β w) :=
      hh.comp_contMDiff (Eventually.of_forall fun _ => β.symm.contMDiffAt)
    have hv : ∀ᶠ q in 𝓝 (β.symm (β w)), q∈productGraph S G → a q=0 := by
      rw [β.symm_apply_apply]
      exact ha.2
    have hb : (vanishingIdeal (n := r+n) (baseFirstCarrier P S G)).mem (β w) b := by
      refine ⟨hbh,?_⟩
      filter_upwards [(β.symm.continuous.tendsto (β w)).eventually hv] with u hu huΓ
      apply hu
      apply (ambientOrder_carrier P S G (β.symm u)).mpr
      exact (β.apply_symm_apply u).symm ▸ huΓ
    have hm := GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨b,hb,rfl⟩ (hbh.comp_contMDiff (Eventually.of_forall fun _ => β.contMDiffAt)))
    have he : b ∘ β=a := by
      funext q
      exact congrArg a (β.symm_apply_apply q)
    exact he ▸ hm

/-- The ENTIRE original graph ideal, including ALL offgraph/offsource unit stalks. -/
theorem productGraph_whole_ideal
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    vanishingIdeal (n := n+r) (productGraph S G)=productGraphIdeal P S G :=
  (ambientOrder_pull_vanishing P S G).symm.trans
    ((congrArg (fun I => GermIdeal.pullback (m := n+r) (productGraphAmbientOrderDiffeomorph P r) I)
      (baseFirst_ideal_eq_vanishing P S hS G hG)).symm.trans (ambientOrder_pull_ideal P S hS G hG))

theorem productGraph_native_whole_ideal
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : P × ComplexModel r) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) (productGraph S G)) w =
      actualWholeSheafStalkIdeal (productGraphIdeal P S G) w :=
  congrArg (fun I => actualWholeSheafStalkIdeal I w) (productGraph_whole_ideal P S hS G hG)

/-- Native ambient PRESHEAF kernel at EVERY actual ambient point. -/
theorem productGraphAmbientStalkHom_kernel
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G)
    (w : P × ComplexModel r) :
    RingHom.ker (productGraphAmbientStalkHom P S G w) =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) (productGraph S G)) w :=
  (productGraphAmbientStalkHom_kernel_ideal P S hS G hG w).trans
    (productGraph_native_whole_ideal P S hS G hG w).symm

/-- Genuine ORIGINAL graph LRS kernel, only at actual graph points. -/
theorem productGraphAmbientMorphism_stalk_kernel
    (P : Opens (ComplexModel n)) (S : Set P) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : P → ComplexModel r) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) (s : S) :
    RingHom.ker ((productGraphAmbientMorphism P S G hG).stalkMap s).hom =
      actualWholeSheafStalkIdeal (productGraphIdeal P S G) ((s.val,G s.val) : P × ComplexModel r) :=
  (productGraphAmbientMorphism_stalk_kernel_vanishing P S G hG s).trans
    (productGraph_native_whole_ideal P S hS G hG (s.val,G s.val))

end
end SGPT.Unibranch.OriginalProductGraphWholeIdeal
