import SGPT.Unibranch.HironakaG1SymmetricNativeGraph

/-!
# The actual normal chart and ENTIRE target graph ideal

The source is the SAME actual primary ambient restriction. The target is
an honest product open, with its real canonical model structure. Inverses
hold on ALL ambient points; whole ideal transport uses actual maps.
BP FIRST: `hironaka-g1-symmetric-graph-whole-ideal.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1SymmetricGraphWholeIdeal

open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspaceLocalFunctions
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaG1PrimaryNativeGraph HironakaG1PrimaryGraphSubmersions HironakaG1SymmetricNativeGraph
  HironakaFiniteSectionProductGraph OriginalProductGraphWholeIdeal
  HadamardBridge HironakaActualWholeStalkHolomorphicPullback
  HironakaHolomorphicJetRankLoci HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance

open scoped ProductComplexManifold
noncomputable section

variable {r a b : ℕ}
  (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
  (e : actualSubspaceLocallyRingedSpace (n := r+a) C ≅ actualSubspaceLocallyRingedSpace (n := r+b) D)
  (he : e.hom ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
  (hI : ∀ i : Fin r, Ideal.map (e.hom.stalkMap c).hom (coordinateImageIdeal V D (e.hom.base c) (i.castAdd b)) =
    coordinateImageIdeal P C c (i.castAdd a))

local notation "A0" => primaryOpen P V C D e.hom he c hI
local notation "B0" => inverseOpen P V C D e he c hI
local notation "R0" => inverseCommonOpen P V C D e he c hI
local notation "K0" => inverseFunctions P V C D e he c hI

private def unitSet : Set (B0 × ComplexModel (r+a)) := {p | ∀ i : Fin r, p.2 (i.castAdd a) ≠ 0}

private theorem unitSet_open : IsOpen (unitSet P V C D e he c hI) := by
  have h : unitSet P V C D e he c hI = ⋂ i : Fin r, {p : B0 × ComplexModel (r+a) | p.2 (i.castAdd a) ≠ 0} := by
    ext p
    simp only [unitSet,mem_ofPred_eq,mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun ((EuclideanSpace.proj (i.castAdd a)).continuous.comp continuous_snd) continuous_const

private theorem inverseSource_on_product :
    ContMDiffOn 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ComplexModel (r+a)) ∞
      (fun p : B0 × ComplexModel (r+a) => inverseSource r a b p.1.val p.2) (unitSet P V C D e he c hI) := by
  apply (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
  apply contMDiffOn_pi_space.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left]
    change ContMDiffOn 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞
      (fun p : B0 × ComplexModel (r+a) => p.1.val (i.castAdd b) / p.2 (i.castAdd a)) (unitSet P V C D e he c hI)
    have hn : ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞
        (fun p : B0 × ComplexModel (r+a) => p.1.val (i.castAdd b)) :=
      (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst)
    have hd : ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞
        (fun p : B0 × ComplexModel (r+a) => p.2 (i.castAdd a)) :=
      (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp ProductComplexManifold.contMDiff_snd
    exact hn.contMDiffOn.div₀ hd.contMDiffOn (fun p hp => hp i)
  · simp only [Fin.addCases_right]
    have hj : ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞
        (fun p : B0 × ComplexModel (r+a) => p.2 (j.natAdd r)) :=
      (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp ProductComplexManifold.contMDiff_snd
    exact hj.contMDiffOn

/-- The honest unit/division landing open of the ACTUAL target product. -/
def normalProductOpen : Opens (B0 × ComplexModel (r+a)) :=
  ⟨unitSet P V C D e he c hI ∩ (fun p => inverseSource r a b p.1.val p.2) ⁻¹' A0,
    (inverseSource_on_product P V C D e he c hI).continuousOn.isOpen_inter_preimage
      (unitSet_open P V C D e he c hI) (A0).isOpen⟩

local notation "Z0" => normalProductOpen P V C D e he c hI

/-- The actual target and ratio/source-other coordinates of the SAME ambient. -/
def normalMap (z : R0) : Z0 :=
  ⟨(targetAmbient P V C D e he c hI z,normalExtra r a b z.val.val.1.val z.val.val.2),
    (fun i => by rw [normalExtra_active];exact z.val.property.1 i),
    by
      change inverseSource r a b (assembled r a b z.val.val.1.val z.val.val.2)
        (normalExtra r a b z.val.val.1.val z.val.val.2) ∈ A0
      rw [(inverse_normal r a b _ _ z.val.property.1).1]
      exact z.val.val.1.property⟩

/-- The actual scaling inverse, defined on ALL points of the honest product open. -/
def normalInverse (p : Z0) : R0 :=
  ⟨⟨(⟨inverseSource r a b p.val.1.val p.val.2,p.property.2⟩,inverseExtra r a b p.val.1.val p.val.2),
    (fun i => by rw [inverseExtra_active];exact p.property.1 i),
    by
      change assembled r a b (inverseSource r a b p.val.1.val p.val.2) (inverseExtra r a b p.val.1.val p.val.2) ∈ V
      rw [assembled_inverse r a b _ _ p.property.1]
      exact inverseOpen_le P V C D e he c hI p.val.1.property⟩,
    by
      change assembled r a b (inverseSource r a b p.val.1.val p.val.2) (inverseExtra r a b p.val.1.val p.val.2) ∈ B0
      rw [assembled_inverse r a b _ _ p.property.1]
      exact p.val.1.property⟩

theorem normalInverse_normalMap (z : R0) : normalInverse P V C D e he c hI (normalMap P V C D e he c hI z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact (inverse_normal r a b _ _ z.val.property.1).1
  · exact (inverse_normal r a b _ _ z.val.property.1).2

theorem normalMap_normalInverse (p : Z0) : normalMap P V C D e he c hI (normalInverse P V C D e he c hI p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact assembled_inverse r a b _ _ p.property.1
  · ext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · change normalExtra r a b (inverseSource r a b p.val.1.val p.val.2)
        (inverseExtra r a b p.val.1.val p.val.2) (i.castAdd a) = p.val.2 (i.castAdd a)
      rw [normalExtra_active,inverseExtra_active]
    · change normalExtra r a b (inverseSource r a b p.val.1.val p.val.2)
        (inverseExtra r a b p.val.1.val p.val.2) (j.natAdd r) = p.val.2 (j.natAdd r)
      rw [normalExtra_other,inverseSource_other]

theorem normalMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) ∞ (normalMap P V C D e he c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff Z0 _).mp
  apply ProductComplexManifold.contMDiff_prodMk
  · exact targetAmbient_holomorphic P V C D e he c hI
  · apply (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
    apply contMDiff_pi_space.mpr
    intro j
    have hp : ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞
        (fun z : R0 => z.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]
      change ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (fun z : R0 => z.val.val.2 (i.castAdd b))
      exact (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp (ProductComplexManifold.contMDiff_snd.comp hp)
    · simp only [Fin.addCases_right]
      change ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (fun z : R0 => z.val.val.1.val (j.natAdd r))
      exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp
        (contMDiff_subtype_val.comp (ProductComplexManifold.contMDiff_fst.comp hp))

theorem normalInverse_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞ (normalInverse P V C D e he c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff R0 _).mp
  apply (ContMDiff.subtypeVal_comp_iff (commonOpen P V C D e.hom he c hI) _).mp
  apply ProductComplexManifold.contMDiff_prodMk
  · apply (ContMDiff.subtypeVal_comp_iff A0 _).mp
    intro p
    exact ((inverseSource_on_product P V C D e he c hI).contMDiffAt
      ((unitSet_open P V C D e he c hI).mem_nhds p.property.1)).comp p contMDiff_subtype_val.contMDiffAt
  · apply (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
    apply contMDiff_pi_space.mpr
    intro j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]
      change ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞ (fun p : Z0 => p.val.2 (i.castAdd a))
      exact (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp
        ((ProductComplexManifold.contMDiff_snd (n := r+b) (m := r+a) (X := B0) (Y := ComplexModel (r+a))).comp contMDiff_subtype_val)
    · simp only [Fin.addCases_right]
      change ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞ (fun p : Z0 => p.val.1.val (j.natAdd r))
      exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp
        (contMDiff_subtype_val.comp ((ProductComplexManifold.contMDiff_fst (n := r+b) (m := r+a) (X := B0) (Y := ComplexModel (r+a))).comp contMDiff_subtype_val))

/-- Genuine ambient biholomorphism with both original canonical model orders explicit. -/
def normalDiffeomorph : R0 ≃ₘ⟮𝓘(ℂ,ComplexModel ((r+a)+(r+b))),𝓘(ℂ,ComplexModel ((r+b)+(r+a)))⟯ Z0 where
  toFun := normalMap P V C D e he c hI
  invFun := normalInverse P V C D e he c hI
  left_inv := normalInverse_normalMap P V C D e he c hI
  right_inv := normalMap_normalInverse P V C D e he c hI
  contMDiff_toFun := normalMap_holomorphic P V C D e he c hI
  contMDiff_invFun := normalInverse_holomorphic P V C D e he c hI

private theorem mutual_vanishing {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (f : M → N) (g : N → M)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (S : Set N) :
    GermIdeal.pullback (m := n) f (vanishingIdeal (n := m) S) = vanishingIdeal (n := n) (f ⁻¹' S) := by
  refine GermIdeal.ext (funext fun x => funext fun u => propext ⟨fun hu => ?_, fun hu => ?_⟩)
  · obtain ⟨hhol,q,s,a,hs,_ha,hsum⟩ := hu
    refine ⟨hhol,?_⟩
    have hall : ∀ᶠ z in 𝓝 x, ∀ i : Fin q, z ∈ f ⁻¹' S → s i z = 0 := by
      apply eventually_all.mpr
      intro i
      obtain ⟨v,hv,hsv⟩ := hs i
      filter_upwards [(hf.continuous.tendsto x).eventually hv.2] with z hz hzs
      rw [hsv]
      exact hz hzs
    filter_upwards [hsum,hall] with z hz hallz hzs
    rw [hz]
    exact Finset.sum_eq_zero fun i _ => by rw [hallz i hzs,mul_zero]
  · let v : N → ℂ := u ∘ g
    have hhol : HolomorphicAt m v (f x) := by
      apply holomorphicAt_comp_map (Eventually.of_forall fun _ => hg.mdifferentiableAt (by simp))
      simpa only [hgf] using hu.1
    have hvan : ∀ᶠ y in 𝓝 (f x), y ∈ S → v y = 0 := by
      have ht : Tendsto g (𝓝 (f x)) (𝓝 x) := by simpa only [hgf] using hg.continuous.tendsto (f x)
      filter_upwards [ht.eventually hu.2] with y hy hys
      exact hy (by change f (g y) ∈ S;rw [hfg];exact hys)
    have heq : u = v ∘ f := funext fun z => by simp only [v,Function.comp_apply,hgf]
    apply RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    rw [heq]
    exact InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ w, (vanishingIdeal (n := m) S).mem (f x) w ∧ s = w ∘ f)
      ⟨v,⟨hhol,hvan⟩,rfl⟩
      (hhol.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt))

private theorem open_vanishing {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (U : Opens M) (S : Set M) :
    vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S) =
      GermIdeal.pullback (m := n) (Subtype.val : U → M) (vanishingIdeal (n := n) S) := by
  have hi : GermIdeal.pullback (m := n) (id : U → U)
      (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S)) =
      vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S) :=
    GermIdeal.ext (funext fun _ => funext fun _ => propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  exact hi.symm.trans (BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) S)

/-- Target entire source ideal PLUS literal k-K(y), restricted to the real product open. -/
def targetGraphIdeal : GermIdeal ((r+b)+(r+a)) Z0 :=
  GermIdeal.pullback (m := (r+b)+(r+a)) (Subtype.val : Z0 → B0 × ComplexModel (r+a))
    (productGraphIdeal B0 (targetTrace P V C D e he c hI) K0)

private def targetGraph : Set Z0 :=
  (Subtype.val : Z0 → B0 × ComplexModel (r+a)) ⁻¹' productGraph (targetTrace P V C D e he c hI) K0

private theorem targetTrace_analytic (hD : IsComplexAnalyticSubset (n := r+b) D) :
    IsComplexAnalyticSubset (n := r+b) (targetTrace P V C D e he c hI) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion (inverseOpen_le P V C D e he c hI)) hD

private theorem targetGraph_whole_ideal (hD : IsComplexAnalyticSubset (n := r+b) D) :
    vanishingIdeal (n := (r+b)+(r+a)) (targetGraph P V C D e he c hI) = targetGraphIdeal P V C D e he c hI :=
  (open_vanishing Z0 (productGraph (targetTrace P V C D e he c hI) K0)).trans
    (congrArg (fun I : GermIdeal ((r+b)+(r+a)) (B0 × ComplexModel (r+a)) =>
      GermIdeal.pullback (m := (r+b)+(r+a)) (Subtype.val : Z0 → B0 × ComplexModel (r+a)) I)
      (productGraph_whole_ideal B0 (targetTrace P V C D e he c hI) (targetTrace_analytic P V C D e he c hI hD)
        K0 (inverseFunctions_holomorphic P V C D e he c hI)))

private theorem normal_graph_preimage :
    (normalMap P V C D e he c hI) ⁻¹' targetGraph P V C D e he c hI = restrictedGraph P V C D e he c hI := by
  ext z
  exact (restrictedGraph_iff P V C D e he c hI z).symm

/-- WHOLE target graph ideal transport through the actual normal chart,
including offgraph ambient unit stalks. -/
theorem entire_target_graph_ideal (hC : IsComplexAnalyticSubset (n := r+a) C)
    (hD : IsComplexAnalyticSubset (n := r+b) D) :
    restrictedGraphIdeal P V C D e he c hI =
      GermIdeal.pullback (m := (r+a)+(r+b)) (normalMap P V C D e he c hI) (targetGraphIdeal P V C D e he c hI) := by
  have ht := mutual_vanishing (normalMap P V C D e he c hI) (normalInverse P V C D e he c hI)
    (normalMap_holomorphic P V C D e he c hI) (normalInverse_holomorphic P V C D e he c hI)
    (normalInverse_normalMap P V C D e he c hI) (normalMap_normalInverse P V C D e he c hI)
    (targetGraph P V C D e he c hI)
  calc
    _ = vanishingIdeal (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) :=
      (restrictedGraph_whole_ideal P V C D e he c hI hC).symm
    _ = vanishingIdeal (n := (r+a)+(r+b)) ((normalMap P V C D e he c hI) ⁻¹' targetGraph P V C D e he c hI) :=
      congrArg (vanishingIdeal (n := (r+a)+(r+b))) (normal_graph_preimage P V C D e he c hI).symm
    _ = GermIdeal.pullback (m := (r+a)+(r+b)) (normalMap P V C D e he c hI)
        (vanishingIdeal (n := (r+b)+(r+a)) (targetGraph P V C D e he c hI)) := ht.symm
    _ = _ := congrArg (fun I : GermIdeal ((r+b)+(r+a)) Z0 =>
      GermIdeal.pullback (m := (r+a)+(r+b)) (normalMap P V C D e he c hI) I)
      (targetGraph_whole_ideal P V C D e he c hI hD)

/-- ACTUAL native ambient kernel with the ENTIRE target graph ideal. -/
theorem entire_target_graph_kernel (hC : IsComplexAnalyticSubset (n := r+a) C)
    (hD : IsComplexAnalyticSubset (n := r+b) D) (z : restrictedGraph P V C D e he c hI) :
    RingHom.ker ((actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI)).stalkMap z).hom =
      actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m := (r+a)+(r+b)) (normalMap P V C D e he c hI) (targetGraphIdeal P V C D e he c hI)) z.val :=
  (restrictedGraph_stalk_kernel P V C D e he c hI hC z).trans
    (congrArg (fun I : GermIdeal ((r+a)+(r+b)) R0 => actualWholeSheafStalkIdeal I z.val)
      (entire_target_graph_ideal P V C D e he c hI hC hD))

private def sourceCoordinate (i : Fin r) (z : R0) : ℂ :=
  (firstAmbient P V C D e.hom he c hI z.val).val (i.castAdd a)

private def targetCoordinate (i : Fin r) (p : Z0) : ℂ := p.val.1.val (i.castAdd b)

private def ratioCoordinate (i : Fin r) (z : R0) : ℂ := z.val.val.2 (i.castAdd b)

private theorem sourceCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (sourceCoordinate P V C D e he c hI i) :=
  (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp
    (contMDiff_subtype_val.comp ((firstAmbient_holomorphic P V C D e.hom he c hI).comp contMDiff_subtype_val))

private theorem targetCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+b)+(r+a))) 𝓘(ℂ,ℂ) ∞ (targetCoordinate P V C D e he c hI i) :=
  (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
    (contMDiff_subtype_val.comp ((ProductComplexManifold.contMDiff_fst (n := r+b) (m := r+a)
      (X := B0) (Y := ComplexModel (r+a))).comp contMDiff_subtype_val))

private theorem ratioCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (ratioCoordinate P V C D e he c hI i) :=
  (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
    ((ProductComplexManifold.contMDiff_snd (n := r+a) (m := r+b) (X := A0) (Y := ComplexModel (r+b))).comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val))

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

private theorem original_mul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z * g z) (hf.mul hg) =
      actualOriginalFunctionGerm x f hf * actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  rw [← HolGerm.mk_mul]

private theorem original_unit {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f : M → ℂ) (hf : HolomorphicAt n f x) (hu : f x ≠ 0) :
    IsUnit (actualOriginalFunctionGerm x f hf) := by
  rw [← isUnit_map_iff (actualStalkChartEquiv (n := n) x),actualOriginalFunctionGerm_chart,
    HolGerm.isUnit_iff_eval_ne_zero]
  change f ((chartAt (ComplexModel n) x).symm (0 + chartAt (ComplexModel n) x x)) ≠ 0
  rw [zero_add,(chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x)]
  exact hu

/-- The original source-coordinate ideal, with the ENTIRE retained selector. -/
def sourceSlotIdeal {ι : Type*} (slot : ι → Option (Fin r)) (z : R0) (i : ι) :
    Ideal (actualComplexStructureStalk (n := (r+a)+(r+b)) z) :=
  match slot i with
  | none => Ideal.span {1}
  | some j => Ideal.span {actualOriginalFunctionGerm z (sourceCoordinate P V C D e he c hI j)
      (Eventually.of_forall fun _ => (sourceCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp))}

/-- Actual target ambient coordinate principal ideals; absent slots remain ONE. -/
def targetSlotIdeal {ι : Type*} (slot : ι → Option (Fin r)) (p : Z0) (i : ι) :
    Ideal (actualComplexStructureStalk (n := (r+b)+(r+a)) p) :=
  match slot i with
  | none => Ideal.span {1}
  | some j => Ideal.span {actualOriginalFunctionGerm p (targetCoordinate P V C D e he c hI j)
      (Eventually.of_forall fun _ => (targetCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp))}

private theorem original_eq {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) (heq : f = g) :
    actualOriginalFunctionGerm x f hf = actualOriginalFunctionGerm x g hg := by
  cases heq
  rfl

private theorem map_span_unit_mul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (b u : S) (hu : IsUnit u) (h : f a = u * b) :
    Ideal.map f (Ideal.span {a}) = Ideal.span {b} := by
  rw [Ideal.map_span,Set.image_singleton,h,← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr hu,Ideal.top_mul]

private theorem option_span_map {R S : Type*} [CommRing R] [CommRing S] {r : ℕ}
    (f : R →+* S) (a : Fin r → R) (b : Fin r → S)
    (h : ∀ j, Ideal.map f (Ideal.span {a j}) = Ideal.span {b j}) (k : Option (Fin r)) :
    Ideal.map f (match k with | none => Ideal.span {1} | some j => Ideal.span {a j}) =
      (match k with | none => Ideal.span {1} | some j => Ideal.span {b j}) := by
  cases k with
  | none => simp only [Ideal.map_span,Set.image_singleton,map_one]
  | some j => exact h j

private theorem active_slot_ideal (z : R0) (j : Fin r) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap (normalMap P V C D e he c hI)
      (normalMap_holomorphic P V C D e he c hI)).stalkMap z).hom
      (Ideal.span {actualOriginalFunctionGerm (normalMap P V C D e he c hI z) (targetCoordinate P V C D e he c hI j)
        (Eventually.of_forall fun _ => (targetCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp))}) =
      Ideal.span {actualOriginalFunctionGerm z (sourceCoordinate P V C D e he c hI j)
        (Eventually.of_forall fun _ => (sourceCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp))} := by
  have hf : HolomorphicAt ((r+a)+(r+b)) (sourceCoordinate P V C D e he c hI j) z :=
    Eventually.of_forall fun _ => (sourceCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp)
  have hg : HolomorphicAt ((r+a)+(r+b)) (ratioCoordinate P V C D e he c hI j) z :=
    Eventually.of_forall fun _ => (ratioCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp)
  have ht : HolomorphicAt ((r+b)+(r+a)) (targetCoordinate P V C D e he c hI j) (normalMap P V C D e he c hI z) :=
    Eventually.of_forall fun _ => (targetCoordinate_holomorphic P V C D e he c hI j).contMDiffAt.mdifferentiableAt (by simp)
  have heq : targetCoordinate P V C D e he c hI j ∘ normalMap P V C D e he c hI =
      fun w => ratioCoordinate P V C D e he c hI j w * sourceCoordinate P V C D e he c hI j w := by
    funext w
    exact assembled_active r a b w.val.val.1.val w.val.val.2 j
  have hn := native_function (normalMap P V C D e he c hI) (normalMap_holomorphic P V C D e he c hI) z
    (targetCoordinate P V C D e he c hI j) ht
  have helem := original_eq z _ _
    (ht.comp_contMDiff (Eventually.of_forall fun _ => (normalMap_holomorphic P V C D e he c hI).contMDiffAt)) (hg.mul hf) heq
  have hp := hn.trans (helem.trans (original_mul z _ _ hg hf))
  exact map_span_unit_mul _ _ _ _ (original_unit z _ hg (z.val.property.1 j)) hp

/-- ENTIRE original boundary ideals under the ACTUAL native normal-chart stalk map. -/
theorem full_slot_ideal {ι : Type*} (slot : ι → Option (Fin r)) (z : R0) (i : ι) :
    Ideal.map ((ChartedSpace.locallyRingedSpaceMap (normalMap P V C D e he c hI)
      (normalMap_holomorphic P V C D e he c hI)).stalkMap z).hom
        (targetSlotIdeal P V C D e he c hI slot (normalMap P V C D e he c hI z) i) =
      sourceSlotIdeal P V C D e he c hI slot z i :=
  option_span_map _ _ _ (active_slot_ideal P V C D e he c hI z) (slot i)

/-- Applying the ACTUAL graph quotient preserves full slots, including zero images. -/
theorem full_slot_graph_image {ι : Type*} (slot : ι → Option (Fin r))
    (z : restrictedGraph P V C D e he c hI) (i : ι) :
    Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI)).stalkMap z).hom
      (Ideal.map ((ChartedSpace.locallyRingedSpaceMap (normalMap P V C D e he c hI)
        (normalMap_holomorphic P V C D e he c hI)).stalkMap z.val).hom
          (targetSlotIdeal P V C D e he c hI slot (normalMap P V C D e he c hI z.val) i)) =
      Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI)).stalkMap z).hom
        (sourceSlotIdeal P V C D e he c hI slot z.val i) :=
  congrArg (Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI)).stalkMap z).hom)
    (full_slot_ideal P V C D e he c hI slot z.val i)

end
end SGPT.Unibranch.HironakaG1SymmetricGraphWholeIdeal
