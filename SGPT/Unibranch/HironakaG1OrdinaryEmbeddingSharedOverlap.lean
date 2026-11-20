import SGPT.Unibranch.EmbeddedBlowupOverlap
import SGPT.Foundations.Analysis.Pending.HironakaActualVanishingIntrinsicHSTransport
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowGermIdealDictionary
import SGPT.Foundations.Analysis.Pending.NormalCrossingsInvariance
import SGPT.Foundations.Analysis.Pending.HironakaActualIntrinsicLabelledBoundaryIdeals

/-!
# Actual shared overlap and common ambient from ordinary original embeddings

No equal-full-image, normalized reader, overlap-compatibility or graph
packet is an input. The ordinary old data are actual native modules and
their original whole window readouts. BP FIRST:
`hironaka-g1-ordinary-embedding-shared-overlap.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1OrdinaryEmbeddingSharedOverlap

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers NormalCrossings NormalCrossingsInvariance
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaActualWholeStalkHolomorphicPullback HironakaActualVanishingIntrinsicHSTransport
  HironakaActualOpenIntrinsicHS
  HironakaG10ChowGermIdealDictionary HironakaNativePulledIdealSheaf HironakaSingularModuleSheafStalk
  EmbeddedBlowupOverlap EmbeddedBlowupOpenRestriction
  SourceReducedComplexSpace

noncomputable section

private theorem idealMap_injective {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Function.Injective (Ideal.map e.toRingHom) := by
  intro I J h
  have hh := congrArg (Ideal.map e.symm.toRingHom) h
  have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := RingHom.ext e.symm_apply_apply
  rw [Ideal.map_map,Ideal.map_map,hc,Ideal.map_id,Ideal.map_id] at hh
  exact hh

private theorem wholeAmbient_open {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (U : Opens M) (A : Set M) (y : U) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → M) contMDiff_subtype_val).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) y.val) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' A)) y := by
  apply idealMap_injective (actualStalkChartEquiv (n := n) y)
  let f := ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → M) contMDiff_subtype_val).stalkMap y).hom
  have hs : (actualStalkChartEquiv (n := n) y).toRingHom.comp f =
      (actualStalkChartEquiv (n := n) y.val).toRingHom := by
    apply RingHom.ext
    intro a
    exact (actualNativeStalk_chart_pullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y a).trans
      (congrArg (fun g => g (actualStalkChartEquiv (n := n) y.val a)) (actualHolomorphicGermPullback_val (n := n) U y))
  calc
    _ = Ideal.map ((actualStalkChartEquiv (n := n) y).toRingHom.comp f)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) y.val) := Ideal.map_map f _
    _ = Ideal.map (actualStalkChartEquiv (n := n) y.val).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) y.val) := congrArg (fun g => Ideal.map g _) hs
    _ = _ := map_actualWholeSheafStalkIdeal _ _
    _ = _ := (wholeChartStalkIdeal_vanishing_actual_open (n := n) U A y).symm
    _ = _ := (map_actualWholeSheafStalkIdeal _ _).symm

private theorem nativeTrace_open {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (U : Opens M) (C A : Set M) (x : ((Subtype.val : U → M) ⁻¹' C)) :
    Ideal.map ((actualOpenSubspaceMap (n := n) C U).stalkMap x).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap ((actualOpenSubspaceMap (n := n) C U).base x)).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x.val.val)) =
      Ideal.map ((actualSubspaceInclusion (n := n) ((Subtype.val : U → M) ⁻¹' C)).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' A)) x.val) := by
  let j := ((actualOpenSubspaceMap (n := n) C U).stalkMap x).hom
  let i := ((actualSubspaceInclusion (n := n) C).stalkMap ((actualOpenSubspaceMap (n := n) C U).base x)).hom
  let j' := ((actualSubspaceInclusion (n := n) ((Subtype.val : U → M) ⁻¹' C)).stalkMap x).hom
  let f := ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n)) (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → M) contMDiff_subtype_val).stalkMap x.val).hom
  have hs : j.comp i = j'.comp f := by
    apply RingHom.ext
    intro a
    exact ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square
      (f := (Subtype.val : U → M)) contMDiff_subtype_val (fun _ hx => hx) x) a
  calc
    _ = Ideal.map (j.comp i) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x.val.val) := Ideal.map_map i j
    _ = Ideal.map (j'.comp f) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x.val.val) := congrArg (fun g => Ideal.map g _) hs
    _ = Ideal.map j' (Ideal.map f (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x.val.val)) := (Ideal.map_map f j').symm
    _ = _ := congrArg (Ideal.map j') (wholeAmbient_open U A x.val)

/-- Literal length transport retains EVERY original old label on the open. -/
def openLabel {n : ℕ} {M : CMfd.{0} n} (U : Opens M) (E : List (Set M)) (i : Fin E.length) :
    Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length :=
  Fin.cast (List.length_map _).symm i

/-- ENTIRE original native Cartier IMAGE restriction, with all labels retained. -/
theorem boundaryTrace_open {n : ℕ} {M : CMfd.{0} n} (U : Opens M) (C : Set M) (E : List (Set M))
    (i : Fin E.length) (x : ((Subtype.val : U → M) ⁻¹' C)) :
    Ideal.map ((actualOpenSubspaceMap (n := n) C U).stalkMap x).hom
      (actualLabelledBoundaryTraceIdeal C E i ((actualOpenSubspaceMap (n := n) C U).base x)) =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := n) U) ((Subtype.val : U → M) ⁻¹' C)
        (E.map ((Subtype.val : U → M) ⁻¹' ·)) (openLabel U E i) x := by
  have he : (E.map ((Subtype.val : U → M) ⁻¹' ·)).get (openLabel U E i) =
      (Subtype.val : U → M) ⁻¹' E.get i := by
    rw [get_map_preimage]
    congr 2
  unfold actualLabelledBoundaryTraceIdeal
  rw [he]
  exact nativeTrace_open U C (E.get i) x

private theorem original_readout_open {X : SourceReducedComplexSpace} (w : LocalEmbedding X)
    (E : List (Set w.ambient))
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit _) (i : Fin E.length)
    (hr : ∀ y : w.carrier, nativePulledIdealStalkIdeal w.map B b y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (U : Opens w.ambient) (x : ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)) :
    nativePulledIdealStalkIdeal (actualOpenSubspaceMap (n := w.dim) w.carrier U ≫ w.map) B b x =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) U) ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)
        (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) (openLabel (M := CMfd.of (n := w.dim) w.ambient) U E i) x :=
  (nativePulledIdealStalkIdeal_comp B b (actualOpenSubspaceMap (n := w.dim) w.carrier U) w.map x).trans
    ((congrArg (Ideal.map ((actualOpenSubspaceMap (n := w.dim) w.carrier U).stalkMap x).hom)
      (hr ((actualOpenSubspaceMap (n := w.dim) w.carrier U).base x))).trans
      (boundaryTrace_open (M := CMfd.of (n := w.dim) w.ambient) U w.carrier E i x))

/-- Ordinary global native old ideals/readouts derive the actual shared overlap
and EVERY full original old-slot pullback, without an overlap packet premise. -/
theorem exists_shared_boundary_overlap {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (hpq : w.toPoint p = v.toPoint q)
    (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (hE : IsSNCDivisor w.dim E) (hF : IsSNCDivisor v.dim F)
    (τ : Fin E.length ≃ Fin F.length)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _) (_hb : ∀ i, Mono (b i))
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y) :
    ∃ (U : Opens w.ambient) (V : Opens v.ambient)
      (L : ofClosedAnalytic ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val w.analytic U) ≅
        ofClosedAnalytic ((Subtype.val : V → v.ambient) ⁻¹' v.carrier)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val v.analytic V)),
      p.val ∈ U ∧ q.val ∈ V ∧
      ((Subtype.val : w.carrier → w.ambient) ⁻¹' (U : Set w.ambient) = (overlapOpen w v : Set w.carrier)) ∧
      ((Subtype.val : v.carrier → v.ambient) ⁻¹' (V : Set v.ambient) = (overlapOpen v w : Set v.carrier)) ∧
      IsSNCDivisor w.dim (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) ∧
      IsSNCDivisor v.dim (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·)) ∧
      L.hom ≫ (ambientOpenInclusion v.analytic V ≫ chartMorphism v) =
        ambientOpenInclusion w.analytic U ≫ chartMorphism w ∧
      ∀ (x : ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)) (i : Fin E.length),
        Ideal.map (L.hom.hom.left.stalkMap x).hom
          (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) V)
            ((Subtype.val : V → v.ambient) ⁻¹' v.carrier)
            (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·)) (openLabel (M := CMfd.of (n := v.dim) v.ambient) V F (τ i)) (L.hom.hom.left.base x)) =
          actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) U)
            ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)
            (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) (openLabel (M := CMfd.of (n := w.dim) w.ambient) U E i) x := by
  obtain ⟨U,V,hU,hV,L,hL,_hc⟩ := exists_base_overlap_iso w v
    (C := (∅ : Set w.ambient)) (D := (∅ : Set v.ambient)) (Z := (∅ : Set X.obj.left))
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have hpU : p.val ∈ U := (Set.ext_iff.mp hU p).mpr ⟨q,hpq.symm⟩
  have hqV : q.val ∈ V := (Set.ext_iff.mp hV q).mpr ⟨p,hpq⟩
  have hNative : L.hom.hom.left ≫ (actualOpenSubspaceMap (n := v.dim) v.carrier V ≫ v.map) =
      actualOpenSubspaceMap (n := w.dim) w.carrier U ≫ w.map :=
    congrArg (fun f => f.hom.left) hL
  refine ⟨U,V,L,hpU,hqV,hU,hV,
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := w.dim) U) continuous_subtype_val hE,
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := v.dim) V) continuous_subtype_val hF,hL,?_⟩
  intro x i
  have hrw := original_readout_open w E (B i) (b i) i (hw i) U x
  have hrv := original_readout_open v F (B i) (b i) (τ i) (hv i) V (L.hom.hom.left.base x)
  exact (congrArg (Ideal.map (L.hom.hom.left.stalkMap x).hom) hrv.symm).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) L.hom.hom.left
      (actualOpenSubspaceMap (n := v.dim) v.carrier V ≫ v.map) x).symm.trans
        ((congrArg (fun f : actualSubspaceLocallyRingedSpace (n := w.dim) ((Subtype.val : U → w.ambient) ⁻¹' w.carrier) ⟶ X.obj.left =>
          nativePulledIdealStalkIdeal f (B i) (b i) x) hNative).trans hrw))

end
end SGPT.Unibranch.HironakaG1OrdinaryEmbeddingSharedOverlap
