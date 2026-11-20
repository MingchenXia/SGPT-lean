import SGPT.Unibranch.HironakaG1PrimaryGraphSubmersions

/-!
# The SAME primary graph over the genuine inverse native window

The GIVEN native isomorphism derives inverse sections, honest target
shrinking and the actual inverse scaling section. No ambient inverse or
reciprocal full-ambient window condition is supplied.
BP FIRST: `hironaka-g1-symmetric-native-graph.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1SymmetricNativeGraph

open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspacePresentationIndependence
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaG1PrimaryNativeGraph HironakaG1PrimaryGraphSubmersions

open scoped ProductComplexManifold
noncomputable section

/-- The actual inverse scaling source coordinate, retaining all other slots. -/
def inverseSource (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) : ComplexModel (r+a) :=
  (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm
    (Fin.addCases (fun i : Fin r => y (i.castAdd b) / k (i.castAdd a))
      (fun j : Fin a => k (j.natAdd r)))

/-- The actual old ratio and target-other coordinates in the original extra block. -/
def inverseExtra (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) : ComplexModel (r+b) :=
  (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm
    (Fin.addCases (fun i : Fin r => k (i.castAdd a)) (fun j : Fin b => y (j.natAdd r)))

/-- The SAME original ratio and source-other coordinates of the primary ambient. -/
def normalExtra (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) : ComplexModel (r+a) :=
  (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm
    (Fin.addCases (fun i : Fin r => z (i.castAdd b)) (fun j : Fin a => x (j.natAdd r)))

@[simp] theorem inverseSource_active (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) (i : Fin r) :
    inverseSource r a b y k (i.castAdd a) = y (i.castAdd b) / k (i.castAdd a) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => y (i.castAdd b) / k (i.castAdd a)) (fun j : Fin a => k (j.natAdd r)) (i.castAdd a) = _
  rw [Fin.addCases_left]

@[simp] theorem inverseSource_other (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) (j : Fin a) :
    inverseSource r a b y k (j.natAdd r) = k (j.natAdd r) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => y (i.castAdd b) / k (i.castAdd a)) (fun j : Fin a => k (j.natAdd r)) (j.natAdd r) = _
  rw [Fin.addCases_right]

@[simp] theorem inverseExtra_active (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) (i : Fin r) :
    inverseExtra r a b y k (i.castAdd b) = k (i.castAdd a) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => k (i.castAdd a)) (fun j : Fin b => y (j.natAdd r)) (i.castAdd b) = _
  rw [Fin.addCases_left]

@[simp] theorem inverseExtra_other (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a)) (j : Fin b) :
    inverseExtra r a b y k (j.natAdd r) = y (j.natAdd r) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => k (i.castAdd a)) (fun j : Fin b => y (j.natAdd r)) (j.natAdd r) = _
  rw [Fin.addCases_right]

@[simp] theorem normalExtra_active (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) (i : Fin r) :
    normalExtra r a b x z (i.castAdd a) = z (i.castAdd b) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => z (i.castAdd b)) (fun j : Fin a => x (j.natAdd r)) (i.castAdd a) = _
  rw [Fin.addCases_left]

@[simp] theorem normalExtra_other (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) (j : Fin a) :
    normalExtra r a b x z (j.natAdd r) = x (j.natAdd r) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => z (i.castAdd b)) (fun j : Fin a => x (j.natAdd r)) (j.natAdd r) = _
  rw [Fin.addCases_right]

private theorem inverseSource_holomorphic {n r a b : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (y : M → ComplexModel (r+b)) (k : M → ComplexModel (r+a))
    (hy : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+b)) ∞ y)
    (hk : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ k)
    (hu : ∀ (x : M) (i : Fin r), k x (i.castAdd a) ≠ 0) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ (fun x => inverseSource r a b (y x) (k x)) := by
  apply (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left]
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun x => y x (i.castAdd b) / k x (i.castAdd a))
    have hnum : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun x => y x (i.castAdd b)) :=
      (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp hy
    have hden : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun x => k x (i.castAdd a)) :=
      (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp hk
    exact hnum.div₀ hden (fun x => hu x i)
  · simp only [Fin.addCases_right]
    exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp hk

private theorem inverseExtra_holomorphic {n r a b : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (y : M → ComplexModel (r+b)) (k : M → ComplexModel (r+a))
    (hy : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+b)) ∞ y)
    (hk : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ k) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+b)) ∞ (fun x => inverseExtra r a b (y x) (k x)) := by
  apply (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left]
    exact (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp hk
  · simp only [Fin.addCases_right]
    exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp hy

private theorem normalExtra_holomorphic {n r a b : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M → ComplexModel (r+a)) (z : M → ComplexModel (r+b))
    (hx : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ x)
    (hz : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+b)) ∞ z) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (r+a)) ∞ (fun p => normalExtra r a b (x p) (z p)) := by
  apply (EuclideanSpace.equiv (Fin (r+a)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left]
    exact (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp hz
  · simp only [Fin.addCases_right]
    exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp hx

theorem assembled_inverse (r a b : ℕ) (y : ComplexModel (r+b)) (k : ComplexModel (r+a))
    (hu : ∀ i : Fin r, k (i.castAdd a) ≠ 0) :
    assembled r a b (inverseSource r a b y k) (inverseExtra r a b y k) = y := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · rw [assembled_active,inverseExtra_active,inverseSource_active]
    exact mul_div_cancel₀ _ (hu i)
  · rw [assembled_other,inverseExtra_other]

theorem inverse_normal (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b))
    (hu : ∀ i : Fin r, z (i.castAdd b) ≠ 0) :
    inverseSource r a b (assembled r a b x z) (normalExtra r a b x z) = x ∧
      inverseExtra r a b (assembled r a b x z) (normalExtra r a b x z) = z := by
  constructor
  · ext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · rw [inverseSource_active,assembled_active,normalExtra_active]
      exact mul_div_cancel_left₀ _ (hu i)
    · rw [inverseSource_other,normalExtra_other]
  · ext j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · rw [inverseExtra_active,normalExtra_active]
    · rw [inverseExtra_other,assembled_other]

private theorem open_whole_ideal {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (U : Opens M) (S : Set M) :
    vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S) =
      GermIdeal.pullback (m := n) (Subtype.val : U → M) (vanishingIdeal (n := n) S) := by
  have hi : GermIdeal.pullback (m := n) (id : U → U)
      (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S)) =
      vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' S) :=
    GermIdeal.ext (funext fun _ => funext fun _ => propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  exact hi.symm.trans (BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) S)

variable {r a b : ℕ}
  (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
  (e : actualSubspaceLocallyRingedSpace (n := r+a) C ≅ actualSubspaceLocallyRingedSpace (n := r+b) D)
  (he : e.hom ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
  (hI : ∀ i : Fin r, Ideal.map (e.hom.stalkMap c).hom (coordinateImageIdeal V D (e.hom.base c) (i.castAdd b)) =
    coordinateImageIdeal P C c (i.castAdd a))

local notation "A0" => primaryOpen P V C D e.hom he c hI
local notation "G0" => primaryFunctions P V C D e.hom he c hI
local notation "Q0" => commonOpen P V C D e.hom he c hI

private theorem primary_point (x : C) (hx : x.val.val ∈ A0) :
    (e.hom.base x).val.val = assembled r a b x.val.val (G0 ⟨x.val.val,hx⟩) := by
  let z : sourceTrace P V C D e.hom he c hI := ⟨⟨x.val.val,hx⟩,x.property⟩
  exact (congrArg (fun f => (f.base z).val.val) (graph_overlap_square P V C D e.hom he c hI)).symm

/-- The SAME primary ratios pull through the actual inverse native map;
all ambient landing conditions are DERIVED by honest open shrinking. -/
theorem exists_inverse_coordinates :
    ∃ (B : Opens (ComplexModel (r+b))) (_hBV : B ≤ V) (_hdB : (e.hom.base c).val.val ∈ B)
      (H : B → A0) (_hH : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ H),
      (∀ (y : D) (hy : y.val.val ∈ B), (H ⟨y.val.val,hy⟩).val = (e.inv.base y).val.val) ∧
      ∀ y : B, inverseSource r a b y.val (normalExtra r a b (H y).val (G0 (H y))) ∈ A0 := by
  have hi : e.inv ≫ subspacePointMap (n := r+a) C = subspacePointMap (n := r+b) D := by
    rw [← he,← Category.assoc,e.inv_hom_id,Category.id_comp]
  let d := e.hom.base c
  obtain ⟨O,hdO,f,hf,hDC,hsquare⟩ := exists_actualSubspaceMap_local_holomorphic_lift e.inv hi d
  have hpoint (y : D) (hy : y.val ∈ O) : f ⟨y.val,hy⟩ = (e.inv.base y).val :=
    congrArg (fun g => (g.base ⟨⟨y.val,hy⟩,y.property⟩).val) hsquare
  have hdc : (e.inv.base d).val.val = c.val.val :=
    congrArg (fun g => (g.base c).val.val) e.hom_inv_id
  let T : Opens O := ⟨{z | (f z).val ∈ A0},(A0).isOpen.preimage (contMDiff_subtype_val.comp hf).continuous⟩
  let B0 : Opens (ComplexModel (r+b)) :=
    ⟨(fun z : O => z.val.val) '' (T : Set O),
      (V.isOpen.isOpenMap_subtype_val.comp O.isOpen.isOpenMap_subtype_val) _ T.isOpen⟩
  have hB0V : B0 ≤ V := by rintro _ ⟨z,_,rfl⟩; exact z.val.property
  have hB0O (y : B0) : (⟨y.val,hB0V y.property⟩ : V) ∈ O := by
    obtain ⟨z,_hz,hzy⟩ := y.property
    exact (Subtype.ext hzy : z.val = ⟨y.val,hB0V y.property⟩) ▸ z.property
  let lift0 : B0 → O := fun y => ⟨⟨y.val,hB0V y.property⟩,hB0O y⟩
  have hlift0 : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+b)) ∞ lift0 :=
    (ContMDiff.subtypeVal_comp_iff O _).mp (contMDiff_inclusion hB0V)
  have hA (y : B0) : (f (lift0 y)).val ∈ A0 := by
    obtain ⟨z,hz,hzy⟩ := y.property
    have hz' : z = lift0 y := Subtype.ext (Subtype.ext hzy)
    exact hz' ▸ hz
  let H0 : B0 → A0 := fun y => ⟨(f (lift0 y)).val,hA y⟩
  have hH0 : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ H0 := by
    apply (ContMDiff.subtypeVal_comp_iff A0 H0).mp
    change ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ (fun y : B0 => (f (lift0 y)).val)
    exact contMDiff_subtype_val.comp (hf.comp hlift0)
  have hdT : (⟨d.val,hdO⟩ : O) ∈ T := by
    change (f ⟨d.val,hdO⟩).val ∈ A0
    rw [hpoint d hdO,hdc]
    exact mem_primaryOpen P V C D e.hom he c hI
  have hdB0 : d.val.val ∈ B0 := ⟨⟨d.val,hdO⟩,hdT,rfl⟩
  have hHpoint (y : D) (hy : y.val.val ∈ B0) : (H0 ⟨y.val.val,hy⟩).val = (e.inv.base y).val.val :=
    congrArg Subtype.val (hpoint y (hB0O ⟨y.val.val,hy⟩))
  let K0 : B0 → ComplexModel (r+a) := fun y => normalExtra r a b (H0 y).val (G0 (H0 y))
  have hK0 : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ K0 :=
    normalExtra_holomorphic _ _ (contMDiff_subtype_val.comp hH0)
      ((primaryFunctions_holomorphic P V C D e.hom he c hI).comp hH0)
  have hKunit (y : B0) (i : Fin r) : K0 y (i.castAdd a) ≠ 0 := by
    rw [show K0 y (i.castAdd a) = G0 (H0 y) (i.castAdd b) from normalExtra_active r a b _ _ i]
    exact primaryFunctions_nonzero P V C D e.hom he c hI (H0 y) i
  let X0 : B0 → ComplexModel (r+a) := fun y => inverseSource r a b y.val (K0 y)
  have hX0 : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ X0 :=
    inverseSource_holomorphic _ _ contMDiff_subtype_val hK0 hKunit
  have hdX : X0 ⟨d.val.val,hdB0⟩ = c.val.val := by
    have hHc : H0 ⟨d.val.val,hdB0⟩ = ⟨c.val.val,mem_primaryOpen P V C D e.hom he c hI⟩ :=
      Subtype.ext ((hHpoint d hdB0).trans hdc)
    change inverseSource r a b d.val.val (normalExtra r a b (H0 ⟨d.val.val,hdB0⟩).val (G0 (H0 ⟨d.val.val,hdB0⟩))) = _
    rw [hHc,primary_point P V C D e he c hI c (mem_primaryOpen P V C D e.hom he c hI)]
    exact (inverse_normal r a b c.val.val _ (primaryFunctions_nonzero P V C D e.hom he c hI _)).1
  let L : Opens B0 := ⟨X0 ⁻¹' A0,(A0).isOpen.preimage hX0.continuous⟩
  let B : Opens (ComplexModel (r+b)) :=
    ⟨(Subtype.val : B0 → ComplexModel (r+b)) '' (L : Set B0),B0.isOpen.isOpenMap_subtype_val _ L.isOpen⟩
  have hBB0 : B ≤ B0 := by rintro _ ⟨y,_,rfl⟩; exact y.property
  have hdB : d.val.val ∈ B := ⟨⟨d.val.val,hdB0⟩,by change X0 _ ∈ A0;rw [hdX];exact mem_primaryOpen P V C D e.hom he c hI,rfl⟩
  refine ⟨B,hBB0.trans hB0V,hdB,H0 ∘ Set.inclusion hBB0,hH0.comp (contMDiff_inclusion hBB0),?_,?_⟩
  · intro y hy
    exact hHpoint y (hBB0 hy)
  · intro y
    obtain ⟨z,hz,hzy⟩ := y.property
    have hz' : z = Set.inclusion hBB0 y := Subtype.ext hzy
    change X0 (Set.inclusion hBB0 y) ∈ A0
    rw [← hz']
    exact hz

private structure InverseCoordinates where
  B : Opens (ComplexModel (r+b))
  hBV : B ≤ V
  hdB : (e.hom.base c).val.val ∈ B
  H : B → A0
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ H
  point : ∀ (y : D) (hy : y.val.val ∈ B), (H ⟨y.val.val,hy⟩).val = (e.inv.base y).val.val
  landing : ∀ y : B, inverseSource r a b y.val (normalExtra r a b (H y).val (G0 (H y))) ∈ A0

include he hI in
private theorem inverse_coordinates_nonempty : Nonempty (InverseCoordinates P V C D e he c hI) := by
  obtain ⟨B,hBV,hdB,H,hH,hp,hl⟩ := exists_inverse_coordinates P V C D e he c hI
  exact ⟨⟨B,hBV,hdB,H,hH,hp,hl⟩⟩

private def chosen : InverseCoordinates P V C D e he c hI :=
  Classical.choice (inverse_coordinates_nonempty P V C D e he c hI)

/-- Honest target shrinking, DERIVED from the given actual inverse. -/
def inverseOpen : Opens (ComplexModel (r+b)) := (chosen P V C D e he c hI).B

theorem inverseOpen_le : inverseOpen P V C D e he c hI ≤ V := (chosen P V C D e he c hI).hBV

theorem mem_inverseOpen : (e.hom.base c).val.val ∈ inverseOpen P V C D e he c hI :=
  (chosen P V C D e he c hI).hdB

/-- Actual ambient representative of the GIVEN inverse, into the SAME primary open. -/
def inverseBaseMap : inverseOpen P V C D e he c hI → A0 := (chosen P V C D e he c hI).H

theorem inverseBaseMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ (inverseBaseMap P V C D e he c hI) :=
  (chosen P V C D e he c hI).holomorphic

theorem inverseBaseMap_point (y : D) (hy : y.val.val ∈ inverseOpen P V C D e he c hI) :
    (inverseBaseMap P V C D e he c hI ⟨y.val.val,hy⟩).val = (e.inv.base y).val.val :=
  (chosen P V C D e he c hI).point y hy

local notation "B0" => inverseOpen P V C D e he c hI
local notation "H0" => inverseBaseMap P V C D e he c hI

/-- Target-side functions are built from SAME chosen primary ratios, not rechosen units. -/
def inverseFunctions (y : B0) : ComplexModel (r+a) := normalExtra r a b (H0 y).val (G0 (H0 y))

theorem inverseFunctions_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel (r+a)) ∞ (inverseFunctions P V C D e he c hI) :=
  normalExtra_holomorphic _ _ (contMDiff_subtype_val.comp (inverseBaseMap_holomorphic P V C D e he c hI))
    ((primaryFunctions_holomorphic P V C D e.hom he c hI).comp (inverseBaseMap_holomorphic P V C D e he c hI))

theorem inverseFunctions_nonzero (y : B0) (i : Fin r) :
    inverseFunctions P V C D e he c hI y (i.castAdd a) ≠ 0 := by
  rw [inverseFunctions,normalExtra_active]
  exact primaryFunctions_nonzero P V C D e.hom he c hI (H0 y) i

theorem inverseFunctions_landing (y : B0) :
    inverseSource r a b y.val (inverseFunctions P V C D e he c hI y) ∈ A0 :=
  (chosen P V C D e he c hI).landing y

private theorem inverse_primary_point (y : D) (hy : y.val.val ∈ B0) :
    assembled r a b (H0 ⟨y.val.val,hy⟩).val (G0 (H0 ⟨y.val.val,hy⟩)) = y.val.val := by
  let x := e.inv.base y
  have hHx : (H0 ⟨y.val.val,hy⟩).val = x.val.val := inverseBaseMap_point P V C D e he c hI y hy
  have hxA : x.val.val ∈ A0 := hHx ▸ (H0 ⟨y.val.val,hy⟩).property
  have hH : H0 ⟨y.val.val,hy⟩ = ⟨x.val.val,hxA⟩ := Subtype.ext hHx
  have hxy : e.hom.base x = y := congrArg (fun f => f.base y) e.inv_hom_id
  have hp := primary_point P V C D e he c hI x hxA
  rw [hxy,← hH] at hp
  exact (congrArg (fun w => assembled r a b w (G0 (H0 ⟨y.val.val,hy⟩))) hHx).trans hp.symm

private theorem inverseSource_native (y : D) (hy : y.val.val ∈ B0) :
    inverseSource r a b y.val.val (inverseFunctions P V C D e he c hI ⟨y.val.val,hy⟩) =
      (H0 ⟨y.val.val,hy⟩).val := by
  exact (congrArg (fun w => inverseSource r a b w (inverseFunctions P V C D e he c hI ⟨y.val.val,hy⟩))
    (inverse_primary_point P V C D e he c hI y hy).symm).trans
      (inverse_normal r a b _ _ (primaryFunctions_nonzero P V C D e.hom he c hI _)).1

private theorem inverseExtra_native (y : D) (hy : y.val.val ∈ B0) :
    inverseExtra r a b y.val.val (inverseFunctions P V C D e he c hI ⟨y.val.val,hy⟩) =
      G0 (H0 ⟨y.val.val,hy⟩) := by
  exact (congrArg (fun w => inverseExtra r a b w (inverseFunctions P V C D e he c hI ⟨y.val.val,hy⟩))
    (inverse_primary_point P V C D e he c hI y hy).symm).trans
      (inverse_normal r a b _ _ (primaryFunctions_nonzero P V C D e.hom he c hI _)).2

/-- Actual scaling-inverse section into the SAME primary ambient, on ALL of B. -/
def inverseAmbient (y : B0) : Q0 :=
  ⟨(⟨inverseSource r a b y.val (inverseFunctions P V C D e he c hI y),inverseFunctions_landing P V C D e he c hI y⟩,
      inverseExtra r a b y.val (inverseFunctions P V C D e he c hI y)),
    (fun i => by rw [inverseExtra_active];exact inverseFunctions_nonzero P V C D e he c hI y i),
    by
      change assembled r a b (inverseSource r a b y.val (inverseFunctions P V C D e he c hI y))
        (inverseExtra r a b y.val (inverseFunctions P V C D e he c hI y)) ∈ V
      rw [assembled_inverse r a b _ _ (inverseFunctions_nonzero P V C D e he c hI y)]
      exact inverseOpen_le P V C D e he c hI y.property⟩

theorem inverseAmbient_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞ (inverseAmbient P V C D e he c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff Q0 _).mp
  apply ProductComplexManifold.contMDiff_prodMk
  · apply (ContMDiff.subtypeVal_comp_iff A0 _).mp
    exact inverseSource_holomorphic _ _ contMDiff_subtype_val
      (inverseFunctions_holomorphic P V C D e he c hI) (inverseFunctions_nonzero P V C D e he c hI)
  · exact inverseExtra_holomorphic _ _ contMDiff_subtype_val (inverseFunctions_holomorphic P V C D e he c hI)

/-- EXACT ambient identity, including points outside the native carrier. -/
theorem secondAmbient_inverseAmbient (y : B0) :
    secondAmbient P V C D e.hom he c hI (inverseAmbient P V C D e he c hI y) =
      Set.inclusion (inverseOpen_le P V C D e he c hI) y :=
  Subtype.ext (assembled_inverse r a b _ _ (inverseFunctions_nonzero P V C D e he c hI y))

/-- The genuine restriction of the SAME primary ambient along its actual second map. -/
def inverseCommonOpen : Opens Q0 :=
  ⟨{z | (secondAmbient P V C D e.hom he c hI z).val ∈ B0},
    (B0).isOpen.preimage (contMDiff_subtype_val.comp (secondAmbient_holomorphic P V C D e.hom he c hI)).continuous⟩

local notation "R0" => inverseCommonOpen P V C D e he c hI

/-- The actual projection to the honest target reader window. -/
def targetAmbient (z : R0) : B0 := ⟨(secondAmbient P V C D e.hom he c hI z.val).val,z.property⟩

theorem targetAmbient_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞ (targetAmbient P V C D e he c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff B0 _).mp
  change ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞
    (fun z : R0 => (secondAmbient P V C D e.hom he c hI z.val).val)
  exact contMDiff_subtype_val.comp ((secondAmbient_holomorphic P V C D e.hom he c hI).comp contMDiff_subtype_val)

/-- The literal same inverse section, now with its DERIVED actual open membership. -/
def inverseSection (y : B0) : R0 :=
  ⟨inverseAmbient P V C D e he c hI y,by
    change (secondAmbient P V C D e.hom he c hI (inverseAmbient P V C D e he c hI y)).val ∈ B0
    rw [secondAmbient_inverseAmbient]
    exact y.property⟩

theorem inverseSection_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+b)) 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞ (inverseSection P V C D e he c hI) :=
  (ContMDiff.subtypeVal_comp_iff R0 _).mp (inverseAmbient_holomorphic P V C D e he c hI)

theorem targetAmbient_inverseSection (y : B0) :
    targetAmbient P V C D e he c hI (inverseSection P V C D e he c hI y) = y := by
  apply Subtype.ext
  change (secondAmbient P V C D e.hom he c hI (inverseAmbient P V C D e he c hI y)).val = y.val
  exact congrArg Subtype.val (secondAmbient_inverseAmbient P V C D e he c hI y)

/-- Honest original target trace on the actual target model open. -/
def targetTrace : Set B0 := (Set.inclusion (inverseOpen_le P V C D e he c hI)) ⁻¹' D

/-- SAME primary graph, genuinely restricted by the actual second ambient map. -/
def restrictedGraph : Set R0 := (Subtype.val : R0 → Q0) ⁻¹' graphTrace P V C D e.hom he c hI

private theorem inverseSection_mapsTo (y : B0) (hy : y ∈ targetTrace P V C D e he c hI) :
    inverseSection P V C D e he c hI y ∈ restrictedGraph P V C D e he c hI := by
  let d : D := ⟨Set.inclusion (inverseOpen_le P V C D e he c hI) y,hy⟩
  have hs : (inverseAmbient P V C D e he c hI y).val.1 = H0 y :=
    Subtype.ext (inverseSource_native P V C D e he c hI d y.property)
  change Set.inclusion (primaryOpen_le P V C D e.hom he c hI) (inverseAmbient P V C D e he c hI y).val.1 ∈ C ∧
    (inverseAmbient P V C D e he c hI y).val.2 = G0 (inverseAmbient P V C D e he c hI y).val.1
  rw [hs]
  constructor
  · have hp := inverseBaseMap_point P V C D e he c hI d y.property
    have heq : Set.inclusion (primaryOpen_le P V C D e.hom he c hI) (H0 y) = (e.inv.base d).val := Subtype.ext hp
    rw [heq]
    exact (e.inv.base d).property
  · exact inverseExtra_native P V C D e he c hI d y.property

private theorem targetAmbient_mapsTo (z : R0) (hz : z ∈ restrictedGraph P V C D e he c hI) :
    targetAmbient P V C D e he c hI z ∈ targetTrace P V C D e he c hI :=
  ((secondNativeMap P V C D e.hom he c hI).base ⟨z.val,hz⟩).property

private theorem inverseFunctions_of_graph (z : R0) (hz : z ∈ restrictedGraph P V C D e he c hI) :
    inverseFunctions P V C D e he c hI (targetAmbient P V C D e he c hI z) =
      normalExtra r a b z.val.val.1.val z.val.val.2 := by
  let x : C := ⟨Set.inclusion (primaryOpen_le P V C D e.hom he c hI) z.val.val.1,hz.1⟩
  let y : D := ⟨Set.inclusion (inverseOpen_le P V C D e he c hI) (targetAmbient P V C D e he c hI z),
    targetAmbient_mapsTo P V C D e he c hI z hz⟩
  have hxy : e.hom.base x = y := by
    apply Subtype.ext
    apply Subtype.ext
    change (e.hom.base x).val.val = assembled r a b z.val.val.1.val z.val.val.2
    rw [hz.2]
    exact primary_point P V C D e he c hI x z.val.val.1.property
  have hi : e.inv.base (e.hom.base x) = x := congrArg (fun f => f.base x) e.hom_inv_id
  have hyinv : e.inv.base y = x := (congrArg (fun v : D => e.inv.base v) hxy.symm).trans hi
  have hH : H0 (targetAmbient P V C D e he c hI z) = z.val.val.1 := by
    apply Subtype.ext
    exact (inverseBaseMap_point P V C D e he c hI y z.property).trans
      (congrArg (fun v : C => v.val.val) hyinv)
  change normalExtra r a b (H0 (targetAmbient P V C D e he c hI z)).val
    (G0 (H0 (targetAmbient P V C D e he c hI z))) = _
  rw [hH,hz.2]

private theorem inverseSection_eq_of_normal (z : R0)
    (hk : inverseFunctions P V C D e he c hI (targetAmbient P V C D e he c hI z) =
      normalExtra r a b z.val.val.1.val z.val.val.2) :
    inverseSection P V C D e he c hI (targetAmbient P V C D e he c hI z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change inverseSource r a b (targetAmbient P V C D e he c hI z).val
      (inverseFunctions P V C D e he c hI (targetAmbient P V C D e he c hI z)) = z.val.val.1.val
    rw [hk]
    exact (inverse_normal r a b _ _ z.val.property.1).1
  · change inverseExtra r a b (targetAmbient P V C D e he c hI z).val
      (inverseFunctions P V C D e he c hI (targetAmbient P V C D e he c hI z)) = z.val.val.2
    rw [hk]
    exact (inverse_normal r a b _ _ z.val.property.1).2

theorem inverseSection_targetAmbient (z : R0) (hz : z ∈ restrictedGraph P V C D e he c hI) :
    inverseSection P V C D e he c hI (targetAmbient P V C D e he c hI z) = z :=
  inverseSection_eq_of_normal P V C D e he c hI z (inverseFunctions_of_graph P V C D e he c hI z hz)

/-- EXACT target normal-coordinate carrier equations for the SAME graph.
This is not equality with the whole inverse image of the target carrier. -/
theorem restrictedGraph_iff (z : R0) : z ∈ restrictedGraph P V C D e he c hI ↔
    targetAmbient P V C D e he c hI z ∈ targetTrace P V C D e he c hI ∧
      normalExtra r a b z.val.val.1.val z.val.val.2 =
        inverseFunctions P V C D e he c hI (targetAmbient P V C D e he c hI z) := by
  constructor
  · intro hz
    exact ⟨targetAmbient_mapsTo P V C D e he c hI z hz,
      (inverseFunctions_of_graph P V C D e he c hI z hz).symm⟩
  · rintro ⟨hy,hk⟩
    have heq := inverseSection_eq_of_normal P V C D e he c hI z hk.symm
    exact heq ▸ inverseSection_mapsTo P V C D e he c hI (targetAmbient P V C D e he c hI z) hy

/-- Full native target-to-SAME-primary-graph isomorphism, internally constructed. -/
def symmetricGraphIso : actualSubspaceLocallyRingedSpace (n := r+b) (targetTrace P V C D e he c hI) ≅
    actualSubspaceLocallyRingedSpace (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) :=
  actualSubspaceMutualRestrictionIso (inverseSection_holomorphic P V C D e he c hI)
    (targetAmbient_holomorphic P V C D e he c hI)
    (inverseSection_mapsTo P V C D e he c hI) (targetAmbient_mapsTo P V C D e he c hI)
    (fun y _ => targetAmbient_inverseSection P V C D e he c hI y)
    (inverseSection_targetAmbient P V C D e he c hI)

/-- The actual target original-window inclusion, with its whole scalar map. -/
def targetWindowMap : actualSubspaceLocallyRingedSpace (n := r+b) (targetTrace P V C D e he c hI) ⟶
    actualSubspaceLocallyRingedSpace (n := r+b) D :=
  actualSubspaceMap (contMDiff_inclusion (inverseOpen_le P V C D e he c hI)) (fun _ hy => hy)

private theorem targetWindowMap_point : targetWindowMap P V C D e he c hI ≫ subspacePointMap (n := r+b) D =
    subspacePointMap (n := r+b) (targetTrace P V C D e he c hI) :=
  actualSubspaceMap_point (contMDiff_inclusion (inverseOpen_le P V C D e he c hI)) (fun _ hy => hy)

/-- The SAME graph's true native open-restriction inclusion. -/
def graphRestrictionMap : actualSubspaceLocallyRingedSpace (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) ⟶
    actualSubspaceLocallyRingedSpace (n := (r+a)+(r+b)) (graphTrace P V C D e.hom he c hI) :=
  actualOpenSubspaceMap (n := (r+a)+(r+b)) (graphTrace P V C D e.hom he c hI) R0

/-- FULL native inclusion square of the actual second ambient projection. -/
theorem symmetricGraphIso_inv_inclusion : (symmetricGraphIso P V C D e he c hI).inv ≫
      actualSubspaceInclusion (n := r+b) (targetTrace P V C D e he c hI) =
    actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) ≫
      ChartedSpace.locallyRingedSpaceMap (targetAmbient P V C D e he c hI) (targetAmbient_holomorphic P V C D e he c hI) :=
  (actualSubspaceMap_inclusion (targetAmbient_holomorphic P V C D e he c hI) (targetAmbient_mapsTo P V C D e he c hI)).symm

/-- The actual target original-window square, as ENTIRE native maps. -/
theorem symmetricGraphIso_inv_window : (symmetricGraphIso P V C D e he c hI).inv ≫ targetWindowMap P V C D e he c hI =
    graphRestrictionMap P V C D e he c hI ≫ secondNativeMap P V C D e.hom he c hI := by
  apply actualSubspaceMap_eq_of_base_eq
  · rw [Category.assoc,targetWindowMap_point]
    exact actualSubspaceMap_point (targetAmbient_holomorphic P V C D e he c hI) (targetAmbient_mapsTo P V C D e he c hI)
  · rw [Category.assoc,secondNativeMap_point]
    exact actualSubspaceMap_point (contMDiff_subtype_val (U := R0)) (fun _ hz => hz)
  · rfl

/-- The reverse graph square is the GIVEN original native inverse, not a pointwise substitute. -/
theorem symmetricGraphIso_inverse_overlap : (symmetricGraphIso P V C D e he c hI).hom ≫
      graphRestrictionMap P V C D e he c hI ≫ (graphIso P V C D e.hom he c hI).inv ≫ sourceWindowMap P V C D e.hom he c hI =
    targetWindowMap P V C D e he c hI ≫ e.inv := by
  have hPrimary : (graphIso P V C D e.hom he c hI).inv ≫ (sourceWindowMap P V C D e.hom he c hI ≫ e.hom) =
      secondNativeMap P V C D e.hom he c hI := by
    rw [← graph_overlap_square,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  have hInv : (graphIso P V C D e.hom he c hI).inv ≫ sourceWindowMap P V C D e.hom he c hI =
      secondNativeMap P V C D e.hom he c hI ≫ e.inv := by
    rw [← hPrimary]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [hInv,← Category.assoc (graphRestrictionMap P V C D e he c hI),← symmetricGraphIso_inv_window]
  simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]

/-- The ORIGINAL entire primary graph ideal, on its genuine new open restriction. -/
def restrictedGraphIdeal : GermIdeal ((r+a)+(r+b)) R0 :=
  GermIdeal.pullback (m := (r+a)+(r+b)) (Subtype.val : R0 → Q0) (commonGraphIdeal P V C D e.hom he c hI)

/-- WHOLE ideal restriction, not a support-to-scheme inference. -/
theorem restrictedGraph_whole_ideal (hC : IsComplexAnalyticSubset (n := r+a) C) :
    vanishingIdeal (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) = restrictedGraphIdeal P V C D e he c hI := by
  exact (open_whole_ideal R0 (graphTrace P V C D e.hom he c hI)).trans
    (congrArg (fun I : GermIdeal ((r+a)+(r+b)) Q0 =>
      GermIdeal.pullback (m := (r+a)+(r+b)) (Subtype.val : R0 → Q0) I)
      (graph_whole_ideal P V C D e.hom he c hI hC))

/-- The actual ambient-to-SAME-graph kernel retains the ENTIRE original ideal. -/
theorem restrictedGraph_stalk_kernel (hC : IsComplexAnalyticSubset (n := r+a) C)
    (z : restrictedGraph P V C D e he c hI) :
    RingHom.ker ((actualSubspaceInclusion (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI)).stalkMap z).hom =
      actualWholeSheafStalkIdeal (restrictedGraphIdeal P V C D e he c hI) z.val := by
  exact (actualSubspaceInclusion_stalk_kernel (n := (r+a)+(r+b)) (restrictedGraph P V C D e he c hI) z).trans
    (congrArg (fun I : GermIdeal ((r+a)+(r+b)) R0 => actualWholeSheafStalkIdeal I z.val)
      (restrictedGraph_whole_ideal P V C D e he c hI hC))

end
end SGPT.Unibranch.HironakaG1SymmetricNativeGraph
