import SGPT.Unibranch.HironakaG1NormalizedSNCNativeWindows
import SGPT.Unibranch.HironakaG1SymmetricGraphWholeIdeal
import SGPT.Unibranch.HironakaG1OrdinaryEmbeddingSharedOverlap
import SGPT.Foundations.Analysis.Pending.HironakaActualVanishingIntrinsicHSTransport
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowGermIdealDictionary
import SGPT.Foundations.Analysis.Pending.NormalCrossingsInvariance

/-!
# Actual shared overlap and common ambient from ordinary original embeddings

No equal-full-image, normalized reader, overlap-compatibility or graph
packet is an input. The ordinary old data are actual native modules and
their original whole window readouts. BP FIRST:
`hironaka-g1-ordinary-embedding-common-ambient.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1OrdinaryEmbeddingCommonAmbient

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers NormalCrossings NormalCrossingsInvariance
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceIntrinsicLifting
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaActualWholeStalkHolomorphicPullback HironakaActualVanishingIntrinsicHSTransport
  HironakaActualOpenIntrinsicHS
  HironakaG10ChowGermIdealDictionary HironakaNativePulledIdealSheaf HironakaSingularModuleSheafStalk
  EmbeddedBlowupOverlap EmbeddedBlowupOpenRestriction HironakaG1OrdinaryEmbeddingSharedOverlap
  SourceReducedComplexSpace
  HironakaG1SNCReaderNormalization HironakaG1NormalizedSNCNativeWindows

open scoped ProductComplexManifold

noncomputable section

/-- The whole original label list is retyped only by its actual map-length equality. -/
def openLabelEquiv {n : ℕ} {M : CMfd.{0} n} (U : Opens M) (E : List (Set M)) :
    Fin E.length ≃ Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length :=
  finCongr (List.length_map _).symm

@[simp] theorem openLabelEquiv_apply {n : ℕ} {M : CMfd.{0} n} (U : Opens M) (E : List (Set M)) (i : Fin E.length) :
    openLabelEquiv U E i = openLabel U E i := rfl

def restrictedLabelEquiv {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
    (U : Opens M) (V : Opens N) (E : List (Set M)) (F : List (Set N)) (τ : Fin E.length ≃ Fin F.length) :
    Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length ≃
      Fin (F.map ((Subtype.val : V → N) ⁻¹' ·)).length :=
  (openLabelEquiv U E).symm.trans (τ.trans (openLabelEquiv V F))

theorem restrictedLabelEquiv_apply {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
    (U : Opens M) (V : Opens N) (E : List (Set M)) (F : List (Set N)) (τ : Fin E.length ≃ Fin F.length) (i : Fin E.length) :
    restrictedLabelEquiv U V E F τ (openLabel U E i) = openLabel V F (τ i) :=
  congrArg (fun j => openLabel V F (τ j)) ((openLabelEquiv U E).symm_apply_apply i)

private def nativeIso {A B : SourceReducedComplexSpace} (L : A ≅ B) : A.obj.left ≅ B.obj.left :=
  (Over.forget complexPoint).mapIso (sourceReducedComplexSpaceProperty.ι.mapIso L)

private def readerLocalEmbedding {X : SourceReducedComplexSpace} {n r a : ℕ} {M : CMfd.{0} n} {p : M}
    (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (j : actualSubspaceLocallyRingedSpace (n := n) C ⟶ X.obj.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j) (hp : j ≫ X.obj.hom = subspacePointMap (n := n) C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target) (σ : Fin (r+a) ≃ Fin n) : LocalEmbedding X where
  dim := r+a
  ambient := readerTarget Φ σ
  carrier := normalizedCarrier C Φ hsrc σ
  analytic := normalizedCarrier_analytic C Φ hsrc σ hC
  map := normalizedWindowMap C Φ hsrc σ ≫ j
  isOpenImmersion := by
    let : LocallyRingedSpace.IsOpenImmersion j := hj
    exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (normalizedWindowMap C Φ hsrc σ ≫ j))
  overPoint :=
    (Category.assoc (normalizedWindowMap C Φ hsrc σ) j X.obj.hom).trans
      ((congrArg (fun f : actualSubspaceLocallyRingedSpace (n := n) C ⟶ complexPoint =>
        normalizedWindowMap C Φ hsrc σ ≫ f) hp).trans (normalizedWindowMap_point C Φ hsrc σ))

private theorem reader_readout_comp {X : SourceReducedComplexSpace} {n r a : ℕ} {M : CMfd.{0} n} {p : M}
    (C : Set M) (E : List (Set M)) (j : actualSubspaceLocallyRingedSpace (n := n) C ⟶ X.obj.left)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf)) (b : B ⟶ SheafOfModules.unit _)
    (i : Fin E.length)
    (hr : ∀ x : C, nativePulledIdealStalkIdeal j B b x = actualLabelledBoundaryTraceIdeal C E i x)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target) (σ : Fin (r+a) ≃ Fin n)
    (slot : Fin E.length → Option (Fin r))
    (hm : ∀ x ∈ BlowupFlatCoordinates.flatDomain Φ, ∀ i : Fin E.length,
      x ∈ E.get i ↔ ∃ k, slot i = some k ∧ BlowupFlatCoordinates.flatCoord Φ (σ (k.castAdd a)) x = 0)
    (y : normalizedCarrier C Φ hsrc σ) :
    nativePulledIdealStalkIdeal (normalizedWindowMap C Φ hsrc σ ≫ j) B b y =
      normalizedSlotIdeal C Φ hsrc σ slot y i :=
  (nativePulledIdealStalkIdeal_comp B b (normalizedWindowMap C Φ hsrc σ) j y).trans
    ((congrArg (Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom)
      (hr ((normalizedWindowMap C Φ hsrc σ).base y))).trans
        (whole_slot_calibration C Φ hsrc σ slot hm y i))

def slotImageIdeal {r a : ℕ} (P : Opens (ComplexModel (r+a))) (C : Set P) (x : C) (s : Option (Fin r)) :
    Ideal (((actualSubspaceSheaf (n := r+a) C).presheaf.stalk x).carrier) :=
  match s with
  | none => ⊤
  | some j => HironakaG1PrimaryNativeGraph.coordinateImageIdeal P C x (j.castAdd a)

private theorem coordinate_holomorphic {n : ℕ} (P : Opens (ComplexModel n)) (j : Fin n) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun x : P => x.val j) :=
  (EuclideanSpace.proj (𝕜 := ℂ) j : ComplexModel n →L[ℂ] ℂ).contMDiff.comp (contMDiff_subtype_val (U := P))

private theorem coordinate_section {n : ℕ} (P : Opens (ComplexModel n)) (x : P) (j : Fin n) :
    actualOriginalFunctionGerm (n := n) x (fun y : P => y.val j)
      (Eventually.of_forall fun _ => (coordinate_holomorphic P j).contMDiffAt.mdifferentiableAt (by simp)) =
      (actualComplexStructureSheaf (n := n) P).presheaf.germ ⊤ x (by trivial) (actualCoordinateSection P j) := by
  apply actualOriginalFunctionGerm_eq_section ⊤ x (by trivial) (actualCoordinateSection P j)
  exact Eventually.of_forall fun y => (sectionExtension_apply ⊤ (actualCoordinateSection P j) y (by trivial)).trans rfl

private theorem native_function {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (f : M → N) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (x : M) (g : N → ℂ) (hg : HolomorphicAt m g (f x)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x (actualOriginalFunctionGerm (f x) g hg) =
      actualOriginalFunctionGerm x (g ∘ f) (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem coordinateIdeal_inclusion {n : ℕ} (P Q : Opens (ComplexModel n)) (hPQ : P ≤ Q)
    (C : Set Q) (x : (Set.inclusion hPQ) ⁻¹' C) (j : Fin n) :
    Ideal.map ((actualSubspaceMap (contMDiff_inclusion hPQ) (fun _ hx => hx)).stalkMap x).hom
      (HironakaG1PrimaryNativeGraph.coordinateImageIdeal Q C
        ((actualSubspaceMap (contMDiff_inclusion hPQ) (fun _ hx => hx)).base x) j) =
      HironakaG1PrimaryNativeGraph.coordinateImageIdeal P ((Set.inclusion hPQ) ⁻¹' C) x j := by
  let f : P → Q := Set.inclusion hPQ
  let hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f := contMDiff_inclusion hPQ
  let sq := (actualComplexStructureSheaf (n := n) Q).presheaf.germ ⊤ (f x.val) (by trivial) (actualCoordinateSection Q j)
  have hq : HolomorphicAt n (fun y : Q => y.val j) (f x.val) :=
    Eventually.of_forall fun _ => (coordinate_holomorphic Q j).contMDiffAt.mdifferentiableAt (by simp)
  have hfSection := (congrArg ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val)
      (coordinate_section Q (f x.val) j).symm).trans
    ((native_function f hf x.val (fun y : Q => y.val j) hq).trans (coordinate_section P x.val j))
  have hs := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf (fun _ hx => hx) x) sq
  have he := hs.trans (congrArg ((actualSubspaceInclusion (n := n) (M := P) ((Set.inclusion hPQ) ⁻¹' C)).stalkMap x) hfSection)
  rw [HironakaG1PrimaryNativeGraph.coordinateImageIdeal,Ideal.map_span,Set.image_singleton]
  exact congrArg (fun y => Ideal.span {y}) he

private theorem slotIdeal_inclusion {r a : ℕ} (P Q : Opens (ComplexModel (r+a))) (hPQ : P ≤ Q)
    (C : Set Q) (x : (Set.inclusion hPQ) ⁻¹' C) (s : Option (Fin r)) :
    Ideal.map ((actualSubspaceMap (contMDiff_inclusion hPQ) (fun _ hx => hx)).stalkMap x).hom
      (slotImageIdeal Q C ((actualSubspaceMap (contMDiff_inclusion hPQ) (fun _ hx => hx)).base x) s) =
      slotImageIdeal P ((Set.inclusion hPQ) ⁻¹' C) x s := by
  cases s with
  | none => exact Ideal.map_top _
  | some j => exact coordinateIdeal_inclusion P Q hPQ C x (j.castAdd a)

private theorem restricted_readout {X : SourceReducedComplexSpace} (w : LocalEmbedding X)
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

private def cutPoint {X : SourceReducedComplexSpace} (w : LocalEmbedding X) (p : w.carrier)
    (U : Opens w.ambient) (hp : p.val ∈ U) : ((Subtype.val : U → w.ambient) ⁻¹' w.carrier) :=
  ⟨⟨p.val,hp⟩,p.property⟩

private structure Prepared {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (τ : Fin E.length ≃ Fin F.length) where
  U : Opens w.ambient
  V : Opens v.ambient
  hp : p.val ∈ U
  hq : q.val ∈ V
  samePoint : w.toPoint p = v.toPoint q
  L : ofClosedAnalytic ((Subtype.val : U → w.ambient) ⁻¹' w.carrier)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val w.analytic U) ≅
    ofClosedAnalytic ((Subtype.val : V → v.ambient) ⁻¹' v.carrier)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val v.analytic V)
  overX : L.hom ≫ (ambientOpenInclusion v.analytic V ≫ chartMorphism v) =
    ambientOpenInclusion w.analytic U ≫ chartMorphism w
  R : RelativeReaders (M₁ := CMfd.of (n := w.dim) U) (M₂ := CMfd.of (n := v.dim) V)
    (cutPoint w p U hp).val (((nativeIso L).hom.base (cutPoint w p U hp)).val)
    (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·))
    (restrictedLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) (N := CMfd.of (n := v.dim) v.ambient) U V E F τ)

private theorem prepared_nonempty {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (hpq : w.toPoint p = v.toPoint q)
    (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (hE : IsSNCDivisor w.dim E) (hF : IsSNCDivisor v.dim F)
    (τ : Fin E.length ≃ Fin F.length)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _) (hb : ∀ i, Mono (b i))
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y) :
    Nonempty (Prepared w v p q E F τ) := by
  obtain ⟨U,V,L,hp,hq,_hU,_hV,hEU,hFV,hL,hOld⟩ :=
    exists_shared_boundary_overlap w v p q hpq E F hE hF τ B b hb hw hv
  let e := nativeIso L
  let x := cutPoint w p U hp
  let τ₀ := restrictedLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) (N := CMfd.of (n := v.dim) v.ambient) U V E F τ
  have hI : ∀ i : Fin (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)).length,
      Ideal.map (e.hom.stalkMap x).hom
        (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) V)
          ((Subtype.val : V → v.ambient) ⁻¹' v.carrier) (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·)) (τ₀ i) (e.hom.base x)) =
        actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) U)
          ((Subtype.val : U → w.ambient) ⁻¹' w.carrier) (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) i x := by
    intro i
    let j := (openLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) U E).symm i
    have hj : openLabel (M := CMfd.of (n := w.dim) w.ambient) U E j = i :=
      (openLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) U E).apply_symm_apply i
    have ht : τ₀ i = openLabel (M := CMfd.of (n := v.dim) v.ambient) V F (τ j) :=
      (congrArg τ₀ hj.symm).trans (restrictedLabelEquiv_apply (M := CMfd.of (n := w.dim) w.ambient)
        (N := CMfd.of (n := v.dim) v.ambient) U V E F τ j)
    have htarget := congrArg (fun k : Fin (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·)).length =>
      Ideal.map (e.hom.stalkMap x).hom
        (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) V)
          ((Subtype.val : V → v.ambient) ⁻¹' v.carrier) (F.map ((Subtype.val : V → v.ambient) ⁻¹' ·)) k (e.hom.base x))) ht
    have hsource := congrArg (fun k : Fin (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)).length =>
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) U)
        ((Subtype.val : U → w.ambient) ⁻¹' w.carrier) (E.map ((Subtype.val : U → w.ambient) ⁻¹' ·)) k x) hj
    exact htarget.trans ((hOld x j).trans hsource)
  obtain ⟨R⟩ := exists_relative_readers (M₁ := CMfd.of (n := w.dim) U) (M₂ := CMfd.of (n := v.dim) V)
    ((Subtype.val : U → w.ambient) ⁻¹' w.carrier) ((Subtype.val : V → v.ambient) ⁻¹' v.carrier)
    e x hEU hFV τ₀ hI
  exact ⟨⟨U,V,hp,hq,hpq,L,hL,R⟩⟩

namespace Prepared

variable {X : SourceReducedComplexSpace} {w v : LocalEmbedding X} {p : w.carrier} {q : v.carrier}
  {E : List (Set w.ambient)} {F : List (Set v.ambient)} {τ : Fin E.length ≃ Fin F.length}
  (z : Prepared w v p q E F τ)

private abbrev leftCarrier := (Subtype.val : z.U → w.ambient) ⁻¹' w.carrier
private abbrev rightCarrier := (Subtype.val : z.V → v.ambient) ⁻¹' v.carrier

private def leftToX : actualSubspaceLocallyRingedSpace (n := w.dim) z.leftCarrier ⟶ X.obj.left :=
  actualOpenSubspaceMap (n := w.dim) w.carrier z.U ≫ w.map

private def rightToX : actualSubspaceLocallyRingedSpace (n := v.dim) z.rightCarrier ⟶ X.obj.left :=
  actualOpenSubspaceMap (n := v.dim) v.carrier z.V ≫ v.map

private theorem leftToX_oi : LocallyRingedSpace.IsOpenImmersion z.leftToX :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (actualOpenSubspaceMap (n := w.dim) w.carrier z.U)
    (actualOpenSubspaceMap_isOpenImmersion (n := w.dim) w.carrier z.U) w.map w.isOpenImmersion

private theorem rightToX_oi : LocallyRingedSpace.IsOpenImmersion z.rightToX :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (actualOpenSubspaceMap (n := v.dim) v.carrier z.V)
    (actualOpenSubspaceMap_isOpenImmersion (n := v.dim) v.carrier z.V) v.map v.isOpenImmersion

private theorem leftToX_point : z.leftToX ≫ X.obj.hom = subspacePointMap (n := w.dim) z.leftCarrier :=
  (Category.assoc (actualOpenSubspaceMap (n := w.dim) w.carrier z.U) w.map X.obj.hom).trans
    ((congrArg (fun f : actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier ⟶ complexPoint =>
      actualOpenSubspaceMap (n := w.dim) w.carrier z.U ≫ f) w.overPoint).trans
        (actualSubspaceMap_point (f := (Subtype.val : z.U → w.ambient)) contMDiff_subtype_val (fun _ hx => hx)))

private theorem rightToX_point : z.rightToX ≫ X.obj.hom = subspacePointMap (n := v.dim) z.rightCarrier :=
  (Category.assoc (actualOpenSubspaceMap (n := v.dim) v.carrier z.V) v.map X.obj.hom).trans
    ((congrArg (fun f : actualSubspaceLocallyRingedSpace (n := v.dim) v.carrier ⟶ complexPoint =>
      actualOpenSubspaceMap (n := v.dim) v.carrier z.V ≫ f) v.overPoint).trans
        (actualSubspaceMap_point (f := (Subtype.val : z.V → v.ambient)) contMDiff_subtype_val (fun _ hx => hx)))

private abbrev leftChart : LocalEmbedding X :=
  readerLocalEmbedding (M := CMfd.of (n := w.dim) z.U) z.leftCarrier
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val w.analytic z.U)
    z.leftToX z.leftToX_oi z.leftToX_point z.R.Φ₁ z.R.hsrc₁ z.R.σ₁

private abbrev rightChart : LocalEmbedding X :=
  readerLocalEmbedding (M := CMfd.of (n := v.dim) z.V) z.rightCarrier
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val v.analytic z.V)
    z.rightToX z.rightToX_oi z.rightToX_point z.R.Φ₂ z.R.hsrc₂ z.R.σ₂

private def leftCenter : z.leftChart.carrier :=
  normalizedZero (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁ (cutPoint w p z.U z.hp).property z.R.zero₁

private def rightCenter : z.rightChart.carrier :=
  normalizedZero (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂
    (((nativeIso z.L).hom.base (cutPoint w p z.U z.hp))).property z.R.zero₂

private theorem leftCenter_zero : z.leftCenter.val.val = 0 := rfl
private theorem rightCenter_zero : z.rightCenter.val.val = 0 := rfl

private theorem leftCenter_global : z.leftChart.toPoint z.leftCenter = w.toPoint p :=
  congrArg (fun y : z.leftCarrier => z.leftToX.base y)
    (normalizedZero_original (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁ (cutPoint w p z.U z.hp).property z.R.zero₁)

private theorem rightCut_global : z.rightToX.base ((nativeIso z.L).hom.base (cutPoint w p z.U z.hp)) = w.toPoint p := by
  have hs : (nativeIso z.L).hom ≫ z.rightToX = z.leftToX :=
    congrArg (fun f => f.hom.left) z.overX
  exact congrArg (fun f : actualSubspaceLocallyRingedSpace (n := w.dim) z.leftCarrier ⟶ X.obj.left =>
    f.base (cutPoint w p z.U z.hp)) hs

private theorem rightCenter_global : z.rightChart.toPoint z.rightCenter = v.toPoint q :=
  (congrArg (fun y : z.rightCarrier => z.rightToX.base y)
    (normalizedZero_original (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂
      (((nativeIso z.L).hom.base (cutPoint w p z.U z.hp))).property z.R.zero₂)).trans
        (z.rightCut_global.trans z.samePoint)

private theorem centers_same : z.leftChart.toPoint z.leftCenter = z.rightChart.toPoint z.rightCenter :=
  z.leftCenter_global.trans (z.samePoint.trans z.rightCenter_global.symm)

private def oldSlot (i : Fin E.length) : Option (Fin z.R.r) :=
  z.R.slot (openLabel (M := CMfd.of (n := w.dim) w.ambient) z.U E i)

private theorem oldSlot_surjective (j : Fin z.R.r) : ∃ i : Fin E.length, z.oldSlot i = some j := by
  obtain ⟨k,hk⟩ := z.R.slot_surjective j
  let i := (openLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) z.U E).symm k
  refine ⟨i,?_⟩
  exact (congrArg z.R.slot ((openLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) z.U E).apply_symm_apply k)).trans hk

private theorem left_readout
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (i : Fin E.length) (y : normalizedCarrier (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁) :
    nativePulledIdealStalkIdeal z.leftChart.map (B i) (b i) y =
      slotImageIdeal (r := z.R.r) (a := z.R.a) z.R.sourceCoordinateOpen (normalizedCarrier (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁)
        y (z.oldSlot i) :=
  reader_readout_comp (M := CMfd.of (n := w.dim) z.U) z.leftCarrier
    (E.map ((Subtype.val : z.U → w.ambient) ⁻¹' ·)) z.leftToX (B i) (b i)
    (openLabel (M := CMfd.of (n := w.dim) w.ambient) z.U E i)
    (restricted_readout w E (B i) (b i) i (hw i) z.U) z.R.Φ₁ z.R.hsrc₁ z.R.σ₁ z.R.slot z.R.member₁ y

private theorem right_readout
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y)
    (i : Fin E.length) (y : normalizedCarrier (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂) :
    nativePulledIdealStalkIdeal z.rightChart.map (B i) (b i) y =
      slotImageIdeal (r := z.R.r) (a := z.R.b) z.R.targetCoordinateOpen (normalizedCarrier (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂)
        y (z.oldSlot i) := by
  let τ₀ := restrictedLabelEquiv (M := CMfd.of (n := w.dim) w.ambient) (N := CMfd.of (n := v.dim) v.ambient) z.U z.V E F τ
  let slot : Fin (F.map ((Subtype.val : z.V → v.ambient) ⁻¹' ·)).length → Option (Fin z.R.r) := fun j => z.R.slot (τ₀.symm j)
  have hm : ∀ x ∈ BlowupFlatCoordinates.flatDomain z.R.Φ₂, ∀ j,
      x ∈ (F.map ((Subtype.val : z.V → v.ambient) ⁻¹' ·)).get j ↔
        ∃ k, slot j = some k ∧ BlowupFlatCoordinates.flatCoord z.R.Φ₂ (z.R.σ₂ (k.castAdd z.R.b)) x = 0 := by
    intro x hx j
    have h := z.R.member₂ x hx (τ₀.symm j)
    change x ∈ (F.map ((Subtype.val : z.V → v.ambient) ⁻¹' ·)).get (τ₀ (τ₀.symm j)) ↔
      ∃ k, slot j = some k ∧ BlowupFlatCoordinates.flatCoord z.R.Φ₂ (z.R.σ₂ (k.castAdd z.R.b)) x = 0 at h
    rw [τ₀.apply_symm_apply] at h
    exact h
  have h := reader_readout_comp (M := CMfd.of (n := v.dim) z.V) z.rightCarrier
    (F.map ((Subtype.val : z.V → v.ambient) ⁻¹' ·)) z.rightToX (B i) (b i)
    (openLabel (M := CMfd.of (n := v.dim) v.ambient) z.V F (τ i))
    (restricted_readout v F (B i) (b i) (τ i) (hv i) z.V) z.R.Φ₂ z.R.hsrc₂ z.R.σ₂ slot hm y
  have he := restrictedLabelEquiv_apply (M := CMfd.of (n := w.dim) w.ambient) (N := CMfd.of (n := v.dim) v.ambient) z.U z.V E F τ i
  have hi : τ₀.symm (openLabel (M := CMfd.of (n := v.dim) v.ambient) z.V F (τ i)) =
      openLabel (M := CMfd.of (n := w.dim) w.ambient) z.U E i :=
    (congrArg τ₀.symm he).symm.trans (τ₀.symm_apply_apply _)
  exact h.trans (congrArg (fun s : Option (Fin z.R.r) =>
    slotImageIdeal (r := z.R.r) (a := z.R.b) z.R.targetCoordinateOpen (normalizedCarrier (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂) y s)
    (congrArg z.R.slot hi))

end Prepared

namespace AmbientTrace

variable {X : SourceReducedComplexSpace} (w : LocalEmbedding X) (O : Opens w.ambient)

private def coordinateOpen : Opens (ComplexModel w.dim) :=
  ⟨(Subtype.val : w.ambient → ComplexModel w.dim) '' (O : Set w.ambient),
    w.ambient.isOpen.isOpenMap_subtype_val _ O.isOpen⟩

private theorem coordinateOpen_le : coordinateOpen w O ≤ w.ambient := by
  rintro _ ⟨y,_,rfl⟩
  exact y.property

private theorem point_mem (x : coordinateOpen w O) : Set.inclusion (coordinateOpen_le w O) x ∈ O := by
  obtain ⟨y,hy,hyx⟩ := x.property
  have heq : y = Set.inclusion (coordinateOpen_le w O) x := Subtype.ext hyx
  exact heq ▸ hy

/-- The literal held coordinate-open coercion, realizing THIS actual trace open. -/
private def flatten : coordinateOpen w O ≃ₘ⟮𝓘(ℂ,ComplexModel w.dim),𝓘(ℂ,ComplexModel w.dim)⟯ O where
  toFun x := ⟨Set.inclusion (coordinateOpen_le w O) x,point_mem w O x⟩
  invFun y := ⟨y.val.val,⟨y.val,y.property,rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff O _).mp (contMDiff_inclusion (coordinateOpen_le w O))
  contMDiff_invFun := by
    show ContMDiff 𝓘(ℂ,ComplexModel w.dim) 𝓘(ℂ,ComplexModel w.dim) ∞
      (fun y : O => (⟨y.val.val,⟨y.val,y.property,rfl⟩⟩ : coordinateOpen w O))
    apply (ContMDiff.subtypeVal_comp_iff (coordinateOpen w O) _).mp
    have h : ContMDiff 𝓘(ℂ,ComplexModel w.dim) 𝓘(ℂ,ComplexModel w.dim) ∞
        (fun y : O => y.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
    exact h

private def carrier : Set (coordinateOpen w O) := w.restrictCarrier (coordinateOpen w O) (coordinateOpen_le w O)

private def nativeFlatten : actualSubspaceLocallyRingedSpace (n := w.dim) (carrier w O) ≅
    actualSubspaceLocallyRingedSpace (n := w.dim) ((Subtype.val : O → w.ambient) ⁻¹' w.carrier) :=
  actualSubspaceBiholomorphicIso (flatten w O) (carrier w O)
    ((Subtype.val : O → w.ambient) ⁻¹' w.carrier) (fun _ => Iff.rfl)

private def canonicalMap : actualSubspaceLocallyRingedSpace (n := w.dim) (carrier w O) ⟶
    actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier :=
  actualSubspaceMap (contMDiff_inclusion (coordinateOpen_le w O)) (fun _ hx => hx)

private theorem nativeFlatten_square : (nativeFlatten w O).hom ≫ actualOpenSubspaceMap (n := w.dim) w.carrier O =
    canonicalMap w O :=
  (actualSubspaceMap_comp (flatten w O).contMDiff (contMDiff_subtype_val (U := O))
    (C := carrier w O) (D := (Subtype.val : O → w.ambient) ⁻¹' w.carrier) (E := w.carrier)
    (fun _ hx => hx) (fun _ hx => hx)).symm

private theorem restrictionMap_eq : w.restrictModelMapWith (coordinateOpen w O) (coordinateOpen_le w O)
    (carrier w O) (fun _ => Iff.rfl) = canonicalMap w O :=
  (actualSubspaceMap_comp (opensWithinDiffeo w.ambient (coordinateOpen w O) (coordinateOpen_le w O)).contMDiff
    (contMDiff_subtype_val (U := opensWithin w.ambient (coordinateOpen w O)))
    (C := carrier w O) (D := (Subtype.val : opensWithin w.ambient (coordinateOpen w O) → w.ambient) ⁻¹' w.carrier)
    (E := w.carrier) (fun _ hx => hx) (fun _ hx => hx)).symm

private abbrev chart : LocalEmbedding X := w.restrict (coordinateOpen w O) (coordinateOpen_le w O)

private theorem chart_map_eq : (chart w O).map = canonicalMap w O ≫ w.map :=
  congrArg (fun f : actualSubspaceLocallyRingedSpace (n := w.dim) (carrier w O) ⟶
    actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier => f ≫ w.map) (restrictionMap_eq w O)

private theorem current_square : (nativeFlatten w O).hom ≫ (actualOpenSubspaceMap (n := w.dim) w.carrier O ≫ w.map) =
    (chart w O).map :=
  (Category.assoc (nativeFlatten w O).hom (actualOpenSubspaceMap (n := w.dim) w.carrier O) w.map).symm.trans
    ((congrArg (fun f : actualSubspaceLocallyRingedSpace (n := w.dim) (carrier w O) ⟶
      actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier => f ≫ w.map) (nativeFlatten_square w O)).trans (chart_map_eq w O).symm)

private def center (c : w.carrier) (hc : c.val ∈ O) : (chart w O).carrier :=
  ⟨⟨c.val.val,⟨c.val,hc,rfl⟩⟩,c.property⟩

private theorem center_value (c : w.carrier) (hc : c.val ∈ O) : (center w O c hc).val.val = c.val.val := rfl

private theorem center_current (c : w.carrier) (hc : c.val ∈ O) :
    (chart w O).toPoint (center w O c hc) = w.toPoint c := rfl

private theorem nativeFlatten_point : (nativeFlatten w O).hom ≫
      subspacePointMap (n := w.dim) ((Subtype.val : O → w.ambient) ⁻¹' w.carrier) =
    subspacePointMap (n := w.dim) (carrier w O) :=
  actualSubspaceMap_point (flatten w O).contMDiff (fun _ hx => hx)

private def modelIso : ofClosedAnalytic (carrier w O)
      (w.restrictCarrier_analytic (coordinateOpen w O) (coordinateOpen_le w O)) ≅
    ofClosedAnalytic ((Subtype.val : O → w.ambient) ⁻¹' w.carrier)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val w.analytic O) :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (nativeFlatten w O) (nativeFlatten_point w O))

private theorem modelIso_current : (modelIso w O).hom ≫ (ambientOpenInclusion w.analytic O ≫ chartMorphism w) =
    chartMorphism (chart w O) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact current_square w O

end AmbientTrace

private theorem iso_pasting {𝒞 : Type*} [Category 𝒞] {A B C D T : 𝒞}
    (a : A ≅ C) (b : B ≅ D) (e : C ≅ D) (f : C ⟶ T) (g : D ⟶ T)
    (he : e.hom ≫ g = f) :
    (a.trans (e.trans b.symm)).hom ≫ (b.hom ≫ g) = a.hom ≫ f := by
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id_assoc]
  exact congrArg (fun k => a.hom ≫ k) he

namespace Prepared

variable {X : SourceReducedComplexSpace} {w v : LocalEmbedding X} {p : w.carrier} {q : v.carrier}
  {E : List (Set w.ambient)} {F : List (Set v.ambient)} {τ : Fin E.length ≃ Fin F.length}
  (z : Prepared w v p q E F τ)

private theorem left_flat_readout (O : Opens z.leftChart.ambient)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (i : Fin E.length) (x : (AmbientTrace.chart z.leftChart O).carrier) :
    nativePulledIdealStalkIdeal (AmbientTrace.chart z.leftChart O).map (B i) (b i) x =
      slotImageIdeal (r := z.R.r) (a := z.R.a) (AmbientTrace.coordinateOpen z.leftChart O)
        (AmbientTrace.carrier z.leftChart O) x (z.oldSlot i) :=
  (congrArg (fun f : actualSubspaceLocallyRingedSpace (n := z.leftChart.dim) (AmbientTrace.carrier z.leftChart O) ⟶ X.obj.left =>
      nativePulledIdealStalkIdeal f (B i) (b i) x) (AmbientTrace.chart_map_eq z.leftChart O)).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) (AmbientTrace.canonicalMap z.leftChart O) z.leftChart.map x).trans
      ((congrArg (Ideal.map ((AmbientTrace.canonicalMap z.leftChart O).stalkMap x).hom)
        (z.left_readout B b hw i ((AmbientTrace.canonicalMap z.leftChart O).base x))).trans
          (slotIdeal_inclusion _ _ (AmbientTrace.coordinateOpen_le z.leftChart O) _ x (z.oldSlot i))))

private theorem right_flat_readout (O : Opens z.rightChart.ambient)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y)
    (i : Fin E.length) (x : (AmbientTrace.chart z.rightChart O).carrier) :
    nativePulledIdealStalkIdeal (AmbientTrace.chart z.rightChart O).map (B i) (b i) x =
      slotImageIdeal (r := z.R.r) (a := z.R.b) (AmbientTrace.coordinateOpen z.rightChart O)
        (AmbientTrace.carrier z.rightChart O) x (z.oldSlot i) :=
  (congrArg (fun f : actualSubspaceLocallyRingedSpace (n := z.rightChart.dim) (AmbientTrace.carrier z.rightChart O) ⟶ X.obj.left =>
      nativePulledIdealStalkIdeal f (B i) (b i) x) (AmbientTrace.chart_map_eq z.rightChart O)).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) (AmbientTrace.canonicalMap z.rightChart O) z.rightChart.map x).trans
      ((congrArg (Ideal.map ((AmbientTrace.canonicalMap z.rightChart O).stalkMap x).hom)
        (z.right_readout B b hv i ((AmbientTrace.canonicalMap z.rightChart O).base x))).trans
          (slotIdeal_inclusion _ _ (AmbientTrace.coordinateOpen_le z.rightChart O) _ x (z.oldSlot i))))

private structure Localized where
  O : Opens z.leftChart.ambient
  T : Opens z.rightChart.ambient
  hc : z.leftCenter.val ∈ O
  hd : z.rightCenter.val ∈ T
  L : ofClosedAnalytic (n := z.leftChart.dim) (AmbientTrace.carrier z.leftChart O)
        (z.leftChart.restrictCarrier_analytic (AmbientTrace.coordinateOpen z.leftChart O) (AmbientTrace.coordinateOpen_le z.leftChart O)) ≅
      ofClosedAnalytic (n := z.rightChart.dim) (AmbientTrace.carrier z.rightChart T)
        (z.rightChart.restrictCarrier_analytic (AmbientTrace.coordinateOpen z.rightChart T) (AmbientTrace.coordinateOpen_le z.rightChart T))
  overX : L.hom ≫ chartMorphism (AmbientTrace.chart z.rightChart T) = chartMorphism (AmbientTrace.chart z.leftChart O)

private theorem localized_nonempty : Nonempty z.Localized := by
  obtain ⟨O,T,hO,hT,e,he,_⟩ := exists_base_overlap_iso z.leftChart z.rightChart
    (C := ∅) (D := ∅) (Z := ∅) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have hc : z.leftCenter.val ∈ O := (Set.ext_iff.mp hO z.leftCenter).mpr ⟨z.rightCenter,z.centers_same.symm⟩
  have hd : z.rightCenter.val ∈ T := (Set.ext_iff.mp hT z.rightCenter).mpr ⟨z.leftCenter,z.centers_same⟩
  let a := AmbientTrace.modelIso z.leftChart O
  let b := AmbientTrace.modelIso z.rightChart T
  let L := a.trans (e.trans b.symm)
  have hs := iso_pasting a b e
    (ambientOpenInclusion z.leftChart.analytic O ≫ chartMorphism z.leftChart)
    (ambientOpenInclusion z.rightChart.analytic T ≫ chartMorphism z.rightChart) he
  rw [AmbientTrace.modelIso_current,AmbientTrace.modelIso_current] at hs
  exact ⟨⟨O,T,hc,hd,L,hs⟩⟩

namespace Localized

variable (l : z.Localized)

private abbrev left := AmbientTrace.chart z.leftChart l.O
private abbrev right := AmbientTrace.chart z.rightChart l.T
private def e := nativeIso l.L
private def c : l.left.carrier := AmbientTrace.center z.leftChart l.O z.leftCenter l.hc
private def d : l.right.carrier := AmbientTrace.center z.rightChart l.T z.rightCenter l.hd

private theorem over_current : l.e.hom ≫ l.right.map = l.left.map :=
  congrArg (fun f => f.hom.left) l.overX

private theorem center_map : l.e.hom.base l.c = l.d := by
  apply l.right.toPoint_injective
  exact (congrArg (fun f : (modelOver l.left.ambient l.left.carrier).left ⟶ X.obj.left => f.base l.c) l.over_current).trans
    ((AmbientTrace.center_current z.leftChart l.O z.leftCenter l.hc).trans
      (z.centers_same.trans (AmbientTrace.center_current z.rightChart l.T z.rightCenter l.hd).symm))

private theorem all_slot_map
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y)
    (x : l.left.carrier) (i : Fin E.length) :
    Ideal.map (l.e.hom.stalkMap x).hom
      (slotImageIdeal (r := z.R.r) (a := z.R.b) l.right.ambient l.right.carrier (l.e.hom.base x) (z.oldSlot i)) =
      slotImageIdeal (r := z.R.r) (a := z.R.a) l.left.ambient l.left.carrier x (z.oldSlot i) :=
  (congrArg (Ideal.map (l.e.hom.stalkMap x).hom) (z.right_flat_readout l.T B b hv i (l.e.hom.base x)).symm).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) l.e.hom l.right.map x).symm.trans
      ((congrArg (fun f : (modelOver l.left.ambient l.left.carrier).left ⟶ X.obj.left => nativePulledIdealStalkIdeal f (B i) (b i) x)
        l.over_current).trans (z.left_flat_readout l.O B b hw i x)))

private theorem coordinate_map
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y)
    (x : l.left.carrier) (j : Fin z.R.r) :
    Ideal.map (l.e.hom.stalkMap x).hom
      (HironakaG1PrimaryNativeGraph.coordinateImageIdeal l.right.ambient l.right.carrier (l.e.hom.base x) (j.castAdd z.R.b)) =
      HironakaG1PrimaryNativeGraph.coordinateImageIdeal l.left.ambient l.left.carrier x (j.castAdd z.R.a) := by
  obtain ⟨i,hi⟩ := z.oldSlot_surjective j
  exact (congrArg (fun s : Option (Fin z.R.r) => Ideal.map (l.e.hom.stalkMap x).hom
      (slotImageIdeal (r := z.R.r) (a := z.R.b) l.right.ambient l.right.carrier (l.e.hom.base x) s)) hi).symm.trans
    ((all_slot_map z l B b hw hv x i).trans
      (congrArg (fun s : Option (Fin z.R.r) => slotImageIdeal (r := z.R.r) (a := z.R.a) l.left.ambient l.left.carrier x s) hi))

private def leftOriginal : (modelOver l.left.ambient l.left.carrier).left ⟶
    actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier :=
  z.leftChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.leftChart l.O) (AmbientTrace.coordinateOpen_le z.leftChart l.O)
    (AmbientTrace.carrier z.leftChart l.O) (fun _ => Iff.rfl) ≫
  (normalizedWindowMap (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁ ≫
    actualOpenSubspaceMap (n := w.dim) w.carrier z.U)

private def rightOriginal : (modelOver l.right.ambient l.right.carrier).left ⟶
    actualSubspaceLocallyRingedSpace (n := v.dim) v.carrier :=
  z.rightChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.rightChart l.T) (AmbientTrace.coordinateOpen_le z.rightChart l.T)
    (AmbientTrace.carrier z.rightChart l.T) (fun _ => Iff.rfl) ≫
  (normalizedWindowMap (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂ ≫
    actualOpenSubspaceMap (n := v.dim) v.carrier z.V)

private theorem leftOriginal_current : l.leftOriginal ≫ w.map = l.left.map := by
  let f := z.leftChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.leftChart l.O) (AmbientTrace.coordinateOpen_le z.leftChart l.O)
    (AmbientTrace.carrier z.leftChart l.O) (fun _ => Iff.rfl)
  let g := normalizedWindowMap (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁
  let h := actualOpenSubspaceMap (n := w.dim) w.carrier z.U
  exact (Category.assoc f (g ≫ h) w.map).trans (congrArg (fun k => f ≫ k) (Category.assoc g h w.map))

private theorem rightOriginal_current : l.rightOriginal ≫ v.map = l.right.map := by
  let f := z.rightChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.rightChart l.T) (AmbientTrace.coordinateOpen_le z.rightChart l.T)
    (AmbientTrace.carrier z.rightChart l.T) (fun _ => Iff.rfl)
  let g := normalizedWindowMap (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂
  let h := actualOpenSubspaceMap (n := v.dim) v.carrier z.V
  exact (Category.assoc f (g ≫ h) v.map).trans (congrArg (fun k => f ≫ k) (Category.assoc g h v.map))

private theorem leftOriginal_open : LocallyRingedSpace.IsOpenImmersion l.leftOriginal :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (z.leftChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.leftChart l.O) (AmbientTrace.coordinateOpen_le z.leftChart l.O)
      (AmbientTrace.carrier z.leftChart l.O) (fun _ => Iff.rfl))
    (LocalEmbedding.restrictModelMapWith_isOpenImmersion z.leftChart _ _ _ _)
    (normalizedWindowMap (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁ ≫
        actualOpenSubspaceMap (n := w.dim) w.carrier z.U)
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (normalizedWindowMap (M := CMfd.of (n := w.dim) z.U) z.leftCarrier z.R.Φ₁ z.R.hsrc₁ z.R.σ₁) (inferInstance)
      (actualOpenSubspaceMap (n := w.dim) w.carrier z.U) (inferInstance))

private theorem rightOriginal_open : LocallyRingedSpace.IsOpenImmersion l.rightOriginal :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (z.rightChart.restrictModelMapWith (AmbientTrace.coordinateOpen z.rightChart l.T) (AmbientTrace.coordinateOpen_le z.rightChart l.T)
      (AmbientTrace.carrier z.rightChart l.T) (fun _ => Iff.rfl))
    (LocalEmbedding.restrictModelMapWith_isOpenImmersion z.rightChart _ _ _ _)
    (normalizedWindowMap (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂ ≫
        actualOpenSubspaceMap (n := v.dim) v.carrier z.V)
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (normalizedWindowMap (M := CMfd.of (n := v.dim) z.V) z.rightCarrier z.R.Φ₂ z.R.hsrc₂ z.R.σ₂) (inferInstance)
      (actualOpenSubspaceMap (n := v.dim) v.carrier z.V) (inferInstance))

private theorem leftOriginal_point : l.leftOriginal ≫ subspacePointMap (n := w.dim) w.carrier =
    subspacePointMap (n := l.left.dim) l.left.carrier :=
  (congrArg (fun f : (modelOver w.ambient w.carrier).left ⟶ complexPoint => l.leftOriginal ≫ f) w.overPoint).symm.trans
    ((Category.assoc l.leftOriginal w.map X.obj.hom).symm.trans
      ((congrArg (fun f : (modelOver l.left.ambient l.left.carrier).left ⟶ X.obj.left => f ≫ X.obj.hom) l.leftOriginal_current).trans l.left.overPoint))

private theorem rightOriginal_point : l.rightOriginal ≫ subspacePointMap (n := v.dim) v.carrier =
    subspacePointMap (n := l.right.dim) l.right.carrier :=
  (congrArg (fun f : (modelOver v.ambient v.carrier).left ⟶ complexPoint => l.rightOriginal ≫ f) v.overPoint).symm.trans
    ((Category.assoc l.rightOriginal v.map X.obj.hom).symm.trans
      ((congrArg (fun f : (modelOver l.right.ambient l.right.carrier).left ⟶ X.obj.left => f ≫ X.obj.hom) l.rightOriginal_current).trans l.right.overPoint))

private theorem leftOriginal_center : l.leftOriginal.base l.c = p := by
  apply w.toPoint_injective
  exact (congrArg (fun f : (modelOver l.left.ambient l.left.carrier).left ⟶ X.obj.left => f.base l.c) l.leftOriginal_current).trans
    ((AmbientTrace.center_current z.leftChart l.O z.leftCenter l.hc).trans z.leftCenter_global)

private theorem rightOriginal_center : l.rightOriginal.base l.d = q := by
  apply v.toPoint_injective
  exact (congrArg (fun f : (modelOver l.right.ambient l.right.carrier).left ⟶ X.obj.left => f.base l.d) l.rightOriginal_current).trans
    ((AmbientTrace.center_current z.rightChart l.T z.rightCenter l.hd).trans z.rightCenter_global)

private theorem leftOriginal_old
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (x : l.left.carrier) (i : Fin E.length) :
    Ideal.map (l.leftOriginal.stalkMap x).hom
      (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i (l.leftOriginal.base x)) =
      slotImageIdeal (r := z.R.r) (a := z.R.a) l.left.ambient l.left.carrier x (z.oldSlot i) :=
  (congrArg (Ideal.map (l.leftOriginal.stalkMap x).hom) (hw i (l.leftOriginal.base x)).symm).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) l.leftOriginal w.map x).symm.trans
      ((congrArg (fun f : (modelOver l.left.ambient l.left.carrier).left ⟶ X.obj.left => nativePulledIdealStalkIdeal f (B i) (b i) x)
        l.leftOriginal_current).trans (z.left_flat_readout l.O B b hw i x)))

private theorem rightOriginal_old
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y)
    (x : l.right.carrier) (i : Fin E.length) :
    Ideal.map (l.rightOriginal.stalkMap x).hom
      (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) (l.rightOriginal.base x)) =
      slotImageIdeal (r := z.R.r) (a := z.R.b) l.right.ambient l.right.carrier x (z.oldSlot i) :=
  (congrArg (Ideal.map (l.rightOriginal.stalkMap x).hom) (hv i (l.rightOriginal.base x)).symm).trans
    ((nativePulledIdealStalkIdeal_comp (B i) (b i) l.rightOriginal v.map x).symm.trans
      ((congrArg (fun f : (modelOver l.right.ambient l.right.carrier).left ⟶ X.obj.left => nativePulledIdealStalkIdeal f (B i) (b i) x)
        l.rightOriginal_current).trans (z.right_flat_readout l.T B b hv i x)))

end Localized

end Prepared

/-- OUTPUT of the ordinary embedding construction, never an ordinary-input
hypothesis. The whole current scalar maps and original native windows remain. -/
structure CoordinateWindows {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (τ : Fin E.length ≃ Fin F.length) where
  r : ℕ
  a : ℕ
  b : ℕ
  P : Opens (ComplexModel (r+a))
  V : Opens (ComplexModel (r+b))
  C : Set P
  D : Set V
  analyticC : IsComplexAnalyticSubset (n := r+a) C
  analyticD : IsComplexAnalyticSubset (n := r+b) D
  leftOriginal : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier
  rightOriginal : actualSubspaceLocallyRingedSpace (n := r+b) D ⟶ actualSubspaceLocallyRingedSpace (n := v.dim) v.carrier
  leftOpen : LocallyRingedSpace.IsOpenImmersion leftOriginal
  rightOpen : LocallyRingedSpace.IsOpenImmersion rightOriginal
  leftPoint : leftOriginal ≫ subspacePointMap (n := w.dim) w.carrier = subspacePointMap (n := r+a) C
  rightPoint : rightOriginal ≫ subspacePointMap (n := v.dim) v.carrier = subspacePointMap (n := r+b) D
  e : actualSubspaceLocallyRingedSpace (n := r+a) C ≅ actualSubspaceLocallyRingedSpace (n := r+b) D
  overCurrent : e.hom ≫ (rightOriginal ≫ v.map) = leftOriginal ≫ w.map
  overPoint : e.hom ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C
  c : C
  d : D
  c_zero : c.val.val = 0
  d_zero : d.val.val = 0
  left_original : leftOriginal.base c = p
  right_original : rightOriginal.base d = q
  center_map : e.hom.base c = d
  slot : Fin E.length → Option (Fin r)
  slot_surjective : ∀ j, ∃ i, slot i = some j
  leftOld : ∀ (x : C) (i : Fin E.length),
    Ideal.map (leftOriginal.stalkMap x).hom
      (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i (leftOriginal.base x)) =
      slotImageIdeal P C x (slot i)
  rightOld : ∀ (x : D) (i : Fin E.length),
    Ideal.map (rightOriginal.stalkMap x).hom
      (actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) (rightOriginal.base x)) =
      slotImageIdeal V D x (slot i)
  wholeSlots : ∀ (x : C) (i : Fin E.length),
    Ideal.map (e.hom.stalkMap x).hom (slotImageIdeal V D (e.hom.base x) (slot i)) = slotImageIdeal P C x (slot i)
  coordinateIdeals : ∀ (x : C) (j : Fin r),
    Ideal.map (e.hom.stalkMap x).hom
      (HironakaG1PrimaryNativeGraph.coordinateImageIdeal V D (e.hom.base x) (j.castAdd b)) =
      HironakaG1PrimaryNativeGraph.coordinateImageIdeal P C x (j.castAdd a)

/-- Ordinary original embeddings and CURRENT whole old-ideal readouts produce
the actual normalized overlap; neither equal images nor a comparison packet is
assumed. -/
theorem exists_coordinate_windows {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (hpq : w.toPoint p = v.toPoint q)
    (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (hE : IsSNCDivisor w.dim E) (hF : IsSNCDivisor v.dim F)
    (τ : Fin E.length ≃ Fin F.length)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _) (hb : ∀ i, Mono (b i))
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y) :
    Nonempty (CoordinateWindows w v p q E F τ) := by
  obtain ⟨z⟩ := prepared_nonempty w v p q hpq E F hE hF τ B b hb hw hv
  obtain ⟨l⟩ := z.localized_nonempty
  refine ⟨{
    r := z.R.r, a := z.R.a, b := z.R.b
    P := l.left.ambient, V := l.right.ambient
    C := l.left.carrier, D := l.right.carrier
    analyticC := l.left.analytic, analyticD := l.right.analytic
    leftOriginal := l.leftOriginal, rightOriginal := l.rightOriginal
    leftOpen := l.leftOriginal_open, rightOpen := l.rightOriginal_open
    leftPoint := l.leftOriginal_point, rightPoint := l.rightOriginal_point
    e := l.e
    overCurrent := ?_
    overPoint := Over.w l.L.hom.hom
    c := l.c, d := l.d
    c_zero := z.leftCenter_zero, d_zero := z.rightCenter_zero
    left_original := l.leftOriginal_center, right_original := l.rightOriginal_center
    center_map := l.center_map
    slot := z.oldSlot
    slot_surjective := z.oldSlot_surjective
    leftOld := Prepared.Localized.leftOriginal_old z l B b hw
    rightOld := Prepared.Localized.rightOriginal_old z l B b hv
    wholeSlots := Prepared.Localized.all_slot_map z l B b hw hv
    coordinateIdeals := Prepared.Localized.coordinate_map z l B b hw hv }⟩
  exact (congrArg (fun f : (modelOver l.right.ambient l.right.carrier).left ⟶ X.obj.left => l.e.hom ≫ f)
    l.rightOriginal_current).trans (l.over_current.trans l.leftOriginal_current.symm)

namespace CoordinateWindows

variable {X : SourceReducedComplexSpace} {w v : LocalEmbedding X} {p : w.carrier} {q : v.carrier}
  {E : List (Set w.ambient)} {F : List (Set v.ambient)} {τ : Fin E.length ≃ Fin F.length}
  (W : CoordinateWindows w v p q E F τ)

open HironakaG1PrimaryNativeGraph HironakaG1PrimaryGraphSubmersions
  HironakaG1SymmetricNativeGraph HironakaG1SymmetricGraphWholeIdeal

local notation "hI₀" => W.coordinateIdeals W.c
local notation "A₀" => primaryOpen W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
local notation "Q₀" => commonOpen W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
local notation "G₀" => graphTrace W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
local notation "R₀" => inverseCommonOpen W.P W.V W.C W.D W.e W.overPoint W.c hI₀

/-- The ACTUAL unit-open ambient and graph are computed from the produced
ordinary windows, with no further presentation or graph assumption. -/
def commonAmbient := Q₀
def commonCarrier : Set W.commonAmbient := G₀
def entireGraphIdeal : GermIdeal ((W.r+W.a)+(W.r+W.b)) W.commonAmbient :=
  commonGraphIdeal W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀

def graphToLeftOriginal : actualSubspaceLocallyRingedSpace (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier ⟶
    actualSubspaceLocallyRingedSpace (n := w.dim) w.carrier :=
  (graphIso W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀).inv ≫
    (sourceWindowMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀ ≫ W.leftOriginal)

def graphToRightOriginal : actualSubspaceLocallyRingedSpace (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier ⟶
    actualSubspaceLocallyRingedSpace (n := v.dim) v.carrier :=
  secondNativeMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀ ≫ W.rightOriginal

/-- Both real graph projections give the SAME full current native map. -/
theorem original_square : W.graphToLeftOriginal ≫ w.map = W.graphToRightOriginal ≫ v.map := by
  let t := graphIso W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  let s := sourceWindowMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  let k := secondNativeMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  have hk : t.hom ≫ k = s ≫ W.e.hom := graph_overlap_square W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  have hh : k ≫ (W.rightOriginal ≫ v.map) = t.inv ≫ (s ≫ (W.leftOriginal ≫ w.map)) := by
    calc
      _ = t.inv ≫ (t.hom ≫ (k ≫ (W.rightOriginal ≫ v.map))) := by simp only [Iso.inv_hom_id_assoc]
      _ = t.inv ≫ ((t.hom ≫ k) ≫ (W.rightOriginal ≫ v.map)) := congrArg (fun f => t.inv ≫ f) (Category.assoc t.hom k _).symm
      _ = t.inv ≫ ((s ≫ W.e.hom) ≫ (W.rightOriginal ≫ v.map)) := congrArg (fun f => t.inv ≫ (f ≫ (W.rightOriginal ≫ v.map))) hk
      _ = _ := congrArg (fun f => t.inv ≫ f) ((Category.assoc s W.e.hom _).trans (congrArg (fun f => s ≫ f) W.overCurrent))
  exact (Category.assoc t.inv (s ≫ W.leftOriginal) w.map).trans
    ((congrArg (fun f => t.inv ≫ f) (Category.assoc s W.leftOriginal w.map)).trans
      (hh.symm.trans (Category.assoc k W.rightOriginal v.map).symm))

def sourceCenter : sourceTrace W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀ :=
  ⟨⟨W.c.val.val,mem_primaryOpen W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀⟩,W.c.property⟩

def graphCenter : W.commonCarrier :=
  (graphIso W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀).hom.base W.sourceCenter

theorem graphCenter_left : W.graphToLeftOriginal.base W.graphCenter = p := by
  let t := graphIso W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  have h : t.inv.base (t.hom.base W.sourceCenter) = W.sourceCenter :=
    congrArg (fun f => f.base W.sourceCenter) t.hom_inv_id
  exact (congrArg (fun x => W.leftOriginal.base ((sourceWindowMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀).base x)) h).trans W.left_original

theorem graphCenter_right : W.graphToRightOriginal.base W.graphCenter = q := by
  let t := graphIso W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  let k := secondNativeMap W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀
  have h : k.base (t.hom.base W.sourceCenter) = W.e.hom.base W.c :=
    congrArg (fun f => f.base W.sourceCenter) (graph_overlap_square W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀)
  exact (congrArg W.rightOriginal.base (h.trans W.center_map)).trans W.right_original

/-- The full ideal is literal source ideal plus ALL graph differences. -/
theorem whole_graph_ideal : vanishingIdeal (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier = W.entireGraphIdeal :=
  graph_whole_ideal W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀ W.analyticC

theorem actual_graph_kernel (z : W.commonCarrier) :
    RingHom.ker ((actualSubspaceInclusion (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier).stalkMap z).hom =
      actualWholeSheafStalkIdeal W.entireGraphIdeal z.val :=
  graph_stalk_kernel W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀ W.analyticC z

theorem first_submersion : Manifold.IsSubmersionOfComplement (ComplexModel (W.r+W.b))
    𝓘(ℂ,ComplexModel ((W.r+W.a)+(W.r+W.b))) 𝓘(ℂ,ComplexModel (W.r+W.a)) ∞
      (firstAmbient W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀) :=
  firstAmbient_isSubmersion W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀

theorem second_submersion : Manifold.IsSubmersionOfComplement
    (HironakaG1RelativeBoundaryProjections.Block W.r × HironakaG1RelativeBoundaryProjections.Block W.a)
    𝓘(ℂ,ComplexModel ((W.r+W.a)+(W.r+W.b))) 𝓘(ℂ,ComplexModel (W.r+W.b)) ∞
      (secondAmbient W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀) :=
  secondAmbient_isSubmersion W.P W.V W.C W.D W.e.hom W.overPoint W.c hI₀

/-- The SAME restricted graph has the ENTIRE target graph ideal in the real
normal coordinates; this is not an inverse-image carrier assertion. -/
theorem whole_target_ideal : restrictedGraphIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ =
    GermIdeal.pullback (m := (W.r+W.a)+(W.r+W.b)) (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀)
      (targetGraphIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀) :=
  entire_target_graph_ideal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.analyticC W.analyticD

theorem actual_target_kernel (z : restrictedGraph W.P W.V W.C W.D W.e W.overPoint W.c hI₀) :
    RingHom.ker ((actualSubspaceInclusion (n := (W.r+W.a)+(W.r+W.b)) (restrictedGraph W.P W.V W.C W.D W.e W.overPoint W.c hI₀)).stalkMap z).hom =
      actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m := (W.r+W.a)+(W.r+W.b)) (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀)
          (targetGraphIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀)) z.val :=
  entire_target_graph_kernel W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.analyticC W.analyticD z

theorem full_original_slots (z : R₀) (i : Fin E.length) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀)
      (normalMap_holomorphic W.P W.V W.C W.D W.e W.overPoint W.c hI₀)).stalkMap z).hom
      (targetSlotIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀ z) i) =
      sourceSlotIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot z i :=
  full_slot_ideal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot z i

theorem full_original_slot_images
    (z : restrictedGraph W.P W.V W.C W.D W.e W.overPoint W.c hI₀) (i : Fin E.length) :
    Ideal.map ((actualSubspaceInclusion (n := (W.r+W.a)+(W.r+W.b)) (restrictedGraph W.P W.V W.C W.D W.e W.overPoint W.c hI₀)).stalkMap z).hom
      (Ideal.map ((ChartedSpace.locallyRingedSpaceMap (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀)
        (normalMap_holomorphic W.P W.V W.C W.D W.e W.overPoint W.c hI₀)).stalkMap z.val).hom
          (targetSlotIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot (normalMap W.P W.V W.C W.D W.e W.overPoint W.c hI₀ z.val) i)) =
      Ideal.map ((actualSubspaceInclusion (n := (W.r+W.a)+(W.r+W.b)) (restrictedGraph W.P W.V W.C W.D W.e W.overPoint W.c hI₀)).stalkMap z).hom
        (sourceSlotIdeal W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot z.val i) :=
  full_slot_graph_image W.P W.V W.C W.D W.e W.overPoint W.c hI₀ W.slot z i

end CoordinateWindows

/-- Ordinary original inputs produce the real common graph, both full original
maps and the ENTIRE ideal/kernel, with no common-ambient premise. -/
theorem exists_common_ambient {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (hpq : w.toPoint p = v.toPoint q)
    (E : List (Set w.ambient)) (F : List (Set v.ambient))
    (hE : IsSNCDivisor w.dim E) (hF : IsSNCDivisor v.dim F)
    (τ : Fin E.length ≃ Fin F.length)
    (B : Fin E.length → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : ∀ i, B i ⟶ SheafOfModules.unit _) (hb : ∀ i, Mono (b i))
    (hw : ∀ i (y : w.carrier), nativePulledIdealStalkIdeal w.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := w.dim) w.ambient) w.carrier E i y)
    (hv : ∀ i (y : v.carrier), nativePulledIdealStalkIdeal v.map (B i) (b i) y =
      actualLabelledBoundaryTraceIdeal (X := CMfd.of (n := v.dim) v.ambient) v.carrier F (τ i) y) :
    ∃ W : CoordinateWindows w v p q E F τ,
      W.graphToLeftOriginal ≫ w.map = W.graphToRightOriginal ≫ v.map ∧
      W.graphToLeftOriginal.base W.graphCenter = p ∧
      W.graphToRightOriginal.base W.graphCenter = q ∧
      vanishingIdeal (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier = W.entireGraphIdeal ∧
      ∀ z : W.commonCarrier,
        RingHom.ker ((actualSubspaceInclusion (n := (W.r+W.a)+(W.r+W.b)) W.commonCarrier).stalkMap z).hom =
          actualWholeSheafStalkIdeal W.entireGraphIdeal z.val := by
  let W : CoordinateWindows w v p q E F τ :=
    Classical.choice (exists_coordinate_windows w v p q hpq E F hE hF τ B b hb hw hv)
  exact ⟨W,W.original_square,W.graphCenter_left,W.graphCenter_right,W.whole_graph_ideal,W.actual_graph_kernel⟩

/-- The actual empty initial boundary has no old-module/readout hypotheses. -/
theorem exists_empty_initial_common_ambient {X : SourceReducedComplexSpace} (w v : LocalEmbedding X)
    (p : w.carrier) (q : v.carrier) (hpq : w.toPoint p = v.toPoint q) :
    ∃ W : CoordinateWindows w v p q [] [] (Equiv.refl (Fin 0)), W.r = 0 := by
  let B : Fin 0 → SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf) := fun i => Fin.elim0 i
  let b : ∀ i, B i ⟶ SheafOfModules.unit _ := fun i => Fin.elim0 i
  obtain ⟨W⟩ := exists_coordinate_windows w v p q hpq [] []
    (isSNCDivisor_nil (n := w.dim) (M := CMfd.of (n := w.dim) w.ambient))
    (isSNCDivisor_nil (n := v.dim) (M := CMfd.of (n := v.dim) v.ambient))
    (Equiv.refl (Fin 0)) B b (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  refine ⟨W,?_⟩
  by_contra hr
  obtain ⟨i,_⟩ := W.slot_surjective ⟨0,Nat.pos_of_ne_zero hr⟩
  exact Fin.elim0 i

end
end SGPT.Unibranch.HironakaG1OrdinaryEmbeddingCommonAmbient
