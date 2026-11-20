import SGPT.Unibranch.OriginalProductGraphWholeIdeal
import SGPT.Foundations.Analysis.Pending.HironakaG1RelativeBoundaryUnitLifts
import SGPT.Foundations.Analysis.Pending.HironakaG1RelativeBoundaryProjections
import SGPT.Foundations.Analysis.Pending.HironakaG10PNPointIdeal

/-!
# Actual primary native unit-ratio graph from whole coordinate-image ideals

Ordinary independent reader coordinate opens, the GIVEN native complex map,
and ENTIRE paired coordinate-image ideals produce actual ambient functions.
No ambient lift, graph, nearby equation, quotient regularity or future-history
comparison is a caller input. Blueprint FIRST: `hironaka-g1-primary-native-graph.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1PrimaryNativeGraph

open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaActualAnalyticSubspaceOpenRestriction
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaG1RelativeBoundaryUnitLifts HironakaFiniteSectionGraph HironakaFiniteSectionProductGraph
  OriginalProductGraphWholeIdeal

noncomputable section

private abbrev NS {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (C : Set M) (p : C) :=
  ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier

private def pullGlobalScalar {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (a : actualComplexSection (n := m) (⊤ : Opens N)) :
    ((actualSubspaceSheaf (n := n) C).presheaf.obj (op (⊤ : Opens C))).carrier := by
  let K := F ≫ actualSubspaceInclusion (n := m) D
  let W := (Opens.map K.base).obj (⊤ : Opens N)
  let hW : (⊤ : Opens C) ≤ W := fun _ _ => trivial
  exact (actualSubspaceSheaf (n := n) C).presheaf.map (homOfLE hW).op (K.c.app (op ⊤) a)

private theorem pullGlobalScalar_germ {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (a : actualComplexSection (n := m) (⊤ : Opens N)) (x : C) :
    (actualSubspaceSheaf (n := n) C).presheaf.germ ⊤ x (by trivial) (pullGlobalScalar F a) =
      F.stalkMap x ((actualSubspaceInclusion (n := m) D).stalkMap (F.base x)
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ ⊤ (F.base x).val (by trivial) a)) := by
  let K := F ≫ actualSubspaceInclusion (n := m) D
  let W := (Opens.map K.base).obj (⊤ : Opens N)
  let hW : (⊤ : Opens C) ≤ W := fun _ _ => trivial
  exact (TopCat.Presheaf.germ_res_apply (actualSubspaceSheaf (n := n) C).presheaf
    (homOfLE hW) x (by trivial) (K.c.app (op ⊤) a)).trans
      ((LocallyRingedSpace.stalkMap_germ_apply K ⊤ x (by trivial) a).symm.trans
        (ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F (actualSubspaceInclusion (n := m) D) x) _))

private theorem pullGlobalScalar_value {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (a : actualComplexSection (n := m) (⊤ : Opens N)) (x : C) :
    actualSubspaceStalkEval (n := n) C x
      ((actualSubspaceSheaf (n := n) C).presheaf.germ ⊤ x (by trivial) (pullGlobalScalar F a)) =
      a ⟨(F.base x).val, by trivial⟩ := by
  rw [pullGlobalScalar_germ, actualSubspaceMap_eval_of_point_compatible F hF x]
  exact actualSubspaceStalkEval_inclusion_germ D ⊤ a (F.base x) (by trivial)

/-- The ENTIRE actual normalized reader-coordinate image ideal at its native point. -/
def coordinateImageIdeal {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P) (x : C) (i : Fin n) :
    Ideal (NS (n := n) C x) :=
  Ideal.span {(actualSubspaceInclusion (n := n) C).stalkMap x
    ((actualComplexStructureSheaf (n := n) P).presheaf.germ ⊤ x.val (by trivial) (actualCoordinateSection P i))}

private theorem finite_sections_eq_on_open {Z : TopCat} (S : Z.Presheaf CommRingCat)
    {r : ℕ} (V : Opens Z) (x : Z) (hx : x ∈ V)
    (s t : Fin r → (S.obj (op V)).carrier)
    (h : ∀ i, S.germ V x hx (s i) = S.germ V x hx (t i)) :
    ∃ (W : Opens Z) (hWV : W ≤ V) (_hxW : x ∈ W),
      ∀ i, S.map (homOfLE hWV).op (s i) = S.map (homOfLE hWV).op (t i) := by
  classical
  choose W hxW iV jV he using fun i => S.germ_eq x hx hx (s i) (t i) (h i)
  let A : Opens Z := V ⊓ ⨅ i : Fin r, W i
  have hAV : A ≤ V := inf_le_left
  have hAW (i : Fin r) : A ≤ W i := inf_le_right.trans (iInf_le W i)
  have hxA : x ∈ A := by
    change x ∈ (V : Set Z) ∩ ((⨅ i : Fin r, W i : Opens Z) : Set Z)
    rw [Opens.coe_iInf]
    exact ⟨hx, Set.mem_iInter.mpr hxW⟩
  refine ⟨A, hAV, hxA, ?_⟩
  intro i
  have hi := congrArg (fun a => S.map (homOfLE (hAW i)).op a) (he i)
  change S.map (homOfLE (hAW i)).op (S.map (iV i).op (s i)) =
    S.map (homOfLE (hAW i)).op (S.map (jV i).op (t i)) at hi
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp] at hi
  have hI : (iV i).op ≫ (homOfLE (hAW i)).op = (homOfLE hAV).op := Subsingleton.elim _ _
  have hJ : (jV i).op ≫ (homOfLE (hAW i)).op = (homOfLE hAV).op := Subsingleton.elim _ _
  simpa only [hI, hJ] using hi

private theorem sourceCoordinateSection_germ {n : ℕ} (P : Opens (ComplexModel n))
    (C : Set P) (x : C) (i : Fin n) :
    (actualSubspaceSheaf (n := n) C).presheaf.germ ⊤ x (by trivial)
        (pullGlobalScalar (𝟙 (actualSubspaceLocallyRingedSpace (n := n) C)) (actualCoordinateSection P i)) =
      (actualSubspaceInclusion (n := n) C).stalkMap x
        ((actualComplexStructureSheaf (n := n) P).presheaf.germ ⊤ x.val (by trivial) (actualCoordinateSection P i)) := by
  exact (pullGlobalScalar_germ (𝟙 (actualSubspaceLocallyRingedSpace (n := n) C))
    (actualCoordinateSection P i) x).trans (by rw [LocallyRingedSpace.stalkMap_id]; rfl)

/-- Whole paired coordinate-image ideals DERIVE native unit sections and
nearby coordinate identities on ONE genuine original native open. -/
theorem exists_native_ratio_sections {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
    (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
    (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
      coordinateImageIdeal P C c (i.castAdd a)) :
    ∃ (W : Opens (TopCat.of C)) (hcW : c ∈ W)
      (u : Fin r → ((actualSubspaceSheaf (n := r+a) C).presheaf.obj (op W)).carrier),
      (∀ i, IsUnit ((actualSubspaceSheaf (n := r+a) C).presheaf.germ W c hcW (u i))) ∧
      ∀ (y : C) (hy : y ∈ W) (i : Fin r),
        (F.base y).val.val (i.castAdd b) =
          actualSubspaceStalkEval (n := r+a) C y
            ((actualSubspaceSheaf (n := r+a) C).presheaf.germ W y hy (u i)) * y.val.val (i.castAdd a) := by
  let S := (actualSubspaceSheaf (n := r+a) C).presheaf
  let α := fun i : Fin r => pullGlobalScalar (𝟙 (actualSubspaceLocallyRingedSpace (n := r+a) C))
    (actualCoordinateSection P (i.castAdd a))
  let β := fun i : Fin r => pullGlobalScalar F (actualCoordinateSection V (i.castAdd b))
  have hspan : ∀ i : Fin r, Ideal.span {S.germ ⊤ c (by trivial) (α i)} =
      Ideal.span {S.germ ⊤ c (by trivial) (β i)} := by
    intro i
    calc
      _ = coordinateImageIdeal P C c (i.castAdd a) :=
        congrArg (fun z => Ideal.span {z}) (sourceCoordinateSection_germ P C c (i.castAdd a))
      _ = Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) := (hI i).symm
      _ = _ := by
        rw [coordinateImageIdeal, Ideal.map_span, Set.image_singleton]
        exact congrArg (fun z => Ideal.span {z}) (pullGlobalScalar_germ F (actualCoordinateSection V (i.castAdd b)) c).symm
  let : IsLocalRing (NS (n := r+a) C c) := actualSubspaceStalk_isLocalRing (n := r+a) C c
  choose u hu using fun i => exists_unit_mul_of_span_eq
    (S.germ ⊤ c (by trivial) (α i)) (S.germ ⊤ c (by trivial) (β i)) (hspan i)
  obtain ⟨W, hcW, s₀, hs₀⟩ := HironakaG10PNPointIdeal.exists_common_sections
    (X := actualSubspaceLocallyRingedSpace (n := r+a) C) c (fun i : Fin r => (u i : NS (n := r+a) C c))
  let s : Fin r → (S.obj (op W)).carrier := s₀
  have hs : ∀ i, S.germ W c hcW (s i) = (u i : NS (n := r+a) C c) := hs₀
  let hW : W ≤ (⊤ : Opens (TopCat.of C)) := le_top
  let A := fun i => S.map (homOfLE hW).op (α i)
  let B := fun i => S.map (homOfLE hW).op (β i)
  have he : ∀ i, S.germ W c hcW (s i * A i) = S.germ W c hcW (B i) := by
    intro i
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hs i]
    exact (hu i).symm
  obtain ⟨T, hTW, hcT, hT⟩ := finite_sections_eq_on_open S W c hcW (fun i => s i * A i) B he
  refine ⟨T, hcT, fun i => S.map (homOfLE hTW).op (s i), ?_, ?_⟩
  · intro i
    change IsUnit (S.germ T c hcT (S.map (homOfLE hTW).op (s i)))
    rw [TopCat.Presheaf.germ_res_apply, hs i]
    exact (u i).isUnit
  · intro y hy i
    have heval := congrArg (fun z => actualSubspaceStalkEval (n := r+a) C y (S.germ T y hy z)) (hT i)
    simp only [map_mul] at heval
    have hα : actualSubspaceStalkEval (n := r+a) C y (S.germ ⊤ y (by trivial) (α i)) =
        y.val.val (i.castAdd a) :=
      pullGlobalScalar_value (𝟙 (actualSubspaceLocallyRingedSpace (n := r+a) C))
        (Category.id_comp _) (actualCoordinateSection P (i.castAdd a)) y
    have hβ : actualSubspaceStalkEval (n := r+a) C y (S.germ ⊤ y (by trivial) (β i)) =
        (F.base y).val.val (i.castAdd b) :=
      pullGlobalScalar_value F hF (actualCoordinateSection V (i.castAdd b)) y
    have hApoint : actualSubspaceStalkEval (n := r+a) C y
        (S.germ T y hy (S.map (homOfLE hTW).op (A i))) = y.val.val (i.castAdd a) :=
      (congrArg (actualSubspaceStalkEval (n := r+a) C y)
        (TopCat.Presheaf.germ_res_apply S (homOfLE hTW) y hy (A i))).trans
          ((congrArg (actualSubspaceStalkEval (n := r+a) C y)
            (TopCat.Presheaf.germ_res_apply S (homOfLE hW) y (hTW hy) (α i))).trans hα)
    have hBpoint : actualSubspaceStalkEval (n := r+a) C y
        (S.germ T y hy (S.map (homOfLE hTW).op (B i))) = (F.base y).val.val (i.castAdd b) :=
      (congrArg (actualSubspaceStalkEval (n := r+a) C y)
        (TopCat.Presheaf.germ_res_apply S (homOfLE hTW) y hy (B i))).trans
          ((congrArg (actualSubspaceStalkEval (n := r+a) C y)
            (TopCat.Presheaf.germ_res_apply S (homOfLE hW) y (hTW hy) (β i))).trans hβ)
    rw [hApoint, hBpoint] at heval
    exact heval.symm

private theorem exists_ambient_ratio_coordinates_at_point {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
    (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
    (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
      coordinateImageIdeal P C c (i.castAdd a)) :
    ∃ (O : Opens P) (hcO : c.val ∈ O) (G : O → ComplexModel (r+b))
      (_hG : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G),
      (∀ i : Fin r, G ⟨c.val,hcO⟩ (i.castAdd b) ≠ 0) ∧
      (∀ (y : C) (hy : y.val ∈ O) (i : Fin r),
        (F.base y).val.val (i.castAdd b) = G ⟨y.val,hy⟩ (i.castAdd b) * y.val.val (i.castAdd a)) ∧
      (∀ (y : C) (hy : y.val ∈ O) (j : Fin b),
        (F.base y).val.val (j.natAdd r) = G ⟨y.val,hy⟩ (j.natAdd r)) := by
  obtain ⟨W, hcW, u, hu, he⟩ := exists_native_ratio_sections P V C D F hF c hI
  let S := (actualSubspaceSheaf (n := r+a) C).presheaf
  let hW : W ≤ (⊤ : Opens (TopCat.of C)) := le_top
  let β := fun j : Fin b => pullGlobalScalar F (actualCoordinateSection V (j.natAdd r))
  let s : Fin (r+b) → (S.obj (op W)).carrier := Fin.addCases u
    (fun j => S.map (homOfLE hW).op (β j))
  obtain ⟨O, hcO, t, hOW, ht⟩ := exists_finite_ambient_sections (n := r+a) C W s c hcW
  let G : O → ComplexModel (r+b) := fun z =>
    (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm (fun j => t j z)
  have hG : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G :=
    (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
      (contMDiff_pi_space.mpr fun j => smoothSheaf.contMDiff_section (t j))
  have hvalue (j : Fin (r+b)) (y : C) (hy : y.val ∈ O) :
      G ⟨y.val,hy⟩ j = actualSubspaceStalkEval (n := r+a) C y (S.germ W y (hOW y hy) (s j)) := by
    change t j ⟨y.val,hy⟩ = _
    exact (actualSubspaceStalkEval_inclusion_germ C O (t j) y hy).symm.trans
      (congrArg (actualSubspaceStalkEval (n := r+a) C y) (ht j y hy)).symm
  have hleft (i : Fin r) (y : C) (hy : y.val ∈ O) :
      G ⟨y.val,hy⟩ (i.castAdd b) =
        actualSubspaceStalkEval (n := r+a) C y (S.germ W y (hOW y hy) (u i)) := by
    simpa only [s, Fin.addCases_left] using hvalue (i.castAdd b) y hy
  refine ⟨O, hcO, G, hG, ?_, ?_, ?_⟩
  · intro i
    rw [hleft]
    exact ((hu i).map (actualSubspaceStalkEval (n := r+a) C c)).ne_zero
  · intro y hy i
    rw [hleft]
    exact he y (hOW y hy) i
  · intro y hy j
    have hv := hvalue (j.natAdd r) y hy
    simp only [s, Fin.addCases_right] at hv
    have hres := congrArg (actualSubspaceStalkEval (n := r+a) C y)
      (TopCat.Presheaf.germ_res_apply S (homOfLE hW) y (hOW y hy) (β j))
    exact (hv.trans (hres.trans (pullGlobalScalar_value F hF (actualCoordinateSection V (j.natAdd r)) y))).symm

/-- ONE real ambient open carries all DERIVED ratio/remaining coordinates;
all ratio coordinates are nonzero on the ambient open, not only the source. -/
theorem exists_ambient_ratio_coordinates {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
    (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
    (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
      coordinateImageIdeal P C c (i.castAdd a)) :
    ∃ (O : Opens P) (_hcO : c.val ∈ O) (G : O → ComplexModel (r+b))
      (_hG : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G),
      (∀ (z : O) (i : Fin r), G z (i.castAdd b) ≠ 0) ∧
      (∀ (y : C) (hy : y.val ∈ O) (i : Fin r),
        (F.base y).val.val (i.castAdd b) = G ⟨y.val,hy⟩ (i.castAdd b) * y.val.val (i.castAdd a)) ∧
      (∀ (y : C) (hy : y.val ∈ O) (j : Fin b),
        (F.base y).val.val (j.natAdd r) = G ⟨y.val,hy⟩ (j.natAdd r)) := by
  obtain ⟨O, hcO, G, hG, hnz, hactive, hother⟩ := exists_ambient_ratio_coordinates_at_point P V C D F hF c hI
  let T : Set O := {z | ∀ i : Fin r, G z (i.castAdd b) ≠ 0}
  have hT : IsOpen T := by
    have hEq : T = ⋂ i : Fin r, {z : O | G z (i.castAdd b) ≠ 0} := by
      ext z
      simp only [T, mem_ofPred_eq, mem_iInter]
    rw [hEq]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun ((EuclideanSpace.proj (i.castAdd b)).continuous.comp hG.continuous) continuous_const
  let A : Opens P := ⟨(Subtype.val : O → P) '' T, O.isOpen.isOpenMap_subtype_val T hT⟩
  have hAO : A ≤ O := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hcA : c.val ∈ A := ⟨⟨c.val,hcO⟩,hnz,rfl⟩
  let G' : A → ComplexModel (r+b) := G ∘ Set.inclusion hAO
  have hG' : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G' :=
    hG.comp (contMDiff_inclusion hAO)
  refine ⟨A,hcA,G',hG',?_,?_,?_⟩
  · intro z i
    obtain ⟨w, hw, he⟩ := z.property
    have hew : Set.inclusion hAO z = w := Subtype.ext he.symm
    change G (Set.inclusion hAO z) (i.castAdd b) ≠ 0
    rw [hew]
    exact hw i
  · intro y hy i
    exact hactive y (hAO hy) i
  · intro y hy j
    exact hother y (hAO hy) j

open scoped ProductComplexManifold

/-- The ACTUAL target coordinate formula in independent reader block order. -/
def assembled (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) : ComplexModel (r+b) :=
  (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm
    (Fin.addCases (fun i : Fin r => z (i.castAdd b) * x (i.castAdd a))
      (fun j : Fin b => z (j.natAdd r)))

@[simp] theorem assembled_active (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) (i : Fin r) :
    assembled r a b x z (i.castAdd b) = z (i.castAdd b) * x (i.castAdd a) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => z (i.castAdd b) * x (i.castAdd a))
    (fun j : Fin b => z (j.natAdd r)) (i.castAdd b) = _
  rw [Fin.addCases_left]

@[simp] theorem assembled_other (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) (j : Fin b) :
    assembled r a b x z (j.natAdd r) = z (j.natAdd r) := by
  change Fin.addCases (motive := fun _ => ℂ) (fun i : Fin r => z (i.castAdd b) * x (i.castAdd a))
    (fun j : Fin b => z (j.natAdd r)) (j.natAdd r) = _
  rw [Fin.addCases_right]

private theorem assembled_holomorphic (r a b : ℕ) (P : Opens (ComplexModel (r+a))) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞
      (fun w : P × ComplexModel (r+b) => assembled r a b w.1.val w.2) := by
  apply (EuclideanSpace.equiv (Fin (r+b)) ℂ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp only [Fin.addCases_left]
    change ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞
      (fun w : P × ComplexModel (r+b) => w.2 (i.castAdd b) * w.1.val (i.castAdd a))
    exact ((EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
        (ProductComplexManifold.contMDiff_snd (n := r+a) (m := r+b) (X := P) (Y := ComplexModel (r+b)))).mul
          ((EuclideanSpace.proj (i.castAdd a)).contMDiff.comp
            (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst))
  · simp only [Fin.addCases_right]
    change ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞
      (fun w : P × ComplexModel (r+b) => w.2 (j.natAdd r))
    exact (EuclideanSpace.proj (j.natAdd r)).contMDiff.comp
        (ProductComplexManifold.contMDiff_snd (n := r+a) (m := r+b) (X := P) (Y := ComplexModel (r+b)))

/-- Actual representatives are also made to land in the GIVEN target reader
open on the WHOLE ambient graph section by one further honest shrinking. -/
theorem exists_landing_ambient_ratio_coordinates {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
    (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
    (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
      coordinateImageIdeal P C c (i.castAdd a)) :
    ∃ (O : Opens P) (_hcO : c.val ∈ O) (G : O → ComplexModel (r+b))
      (_hG : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G),
      (∀ (z : O) (i : Fin r), G z (i.castAdd b) ≠ 0) ∧
      (∀ z : O, assembled r a b z.val.val (G z) ∈ V) ∧
      (∀ (y : C) (hy : y.val ∈ O) (i : Fin r),
        (F.base y).val.val (i.castAdd b) = G ⟨y.val,hy⟩ (i.castAdd b) * y.val.val (i.castAdd a)) ∧
      (∀ (y : C) (hy : y.val ∈ O) (j : Fin b),
        (F.base y).val.val (j.natAdd r) = G ⟨y.val,hy⟩ (j.natAdd r)) := by
  obtain ⟨O,hcO,G,hG,hnz,hactive,hother⟩ := exists_ambient_ratio_coordinates P V C D F hF c hI
  let H : O → ComplexModel (r+b) := fun z => assembled r a b z.val.val (G z)
  have hH : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ H :=
    (assembled_holomorphic r a b P).comp
      (ProductComplexManifold.contMDiff_prodMk contMDiff_subtype_val hG)
  have hcHV : H ⟨c.val,hcO⟩ ∈ V := by
    have he : H ⟨c.val,hcO⟩ = (F.base c).val.val := by
      ext j
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · change assembled r a b c.val.val (G ⟨c.val,hcO⟩) (i.castAdd b) = _
        rw [assembled_active]
        exact (hactive c hcO i).symm
      · change assembled r a b c.val.val (G ⟨c.val,hcO⟩) (j.natAdd r) = _
        rw [assembled_other]
        exact (hother c hcO j).symm
    rw [he]
    exact (F.base c).val.property
  let T : Set O := H ⁻¹' V
  have hT : IsOpen T := V.isOpen.preimage hH.continuous
  let A : Opens P := ⟨(Subtype.val : O → P) '' T, O.isOpen.isOpenMap_subtype_val T hT⟩
  have hAO : A ≤ O := by
    rintro _ ⟨z,_,rfl⟩
    exact z.property
  have hcA : c.val ∈ A := ⟨⟨c.val,hcO⟩,hcHV,rfl⟩
  let G' : A → ComplexModel (r+b) := G ∘ Set.inclusion hAO
  have hG' : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G' :=
    hG.comp (contMDiff_inclusion hAO)
  refine ⟨A,hcA,G',hG',?_,?_,?_,?_⟩
  · intro z i
    exact hnz (Set.inclusion hAO z) i
  · intro z
    obtain ⟨w,hw,he⟩ := z.property
    have hew : Set.inclusion hAO z = w := Subtype.ext he.symm
    change assembled r a b (Set.inclusion hAO z).val.val (G (Set.inclusion hAO z)) ∈ V
    rw [hew]
    exact hw
  · intro y hy i
    exact hactive y (hAO hy) i
  · intro y hy j
    exact hother y (hAO hy) j

/-- The primary open is an ACTUAL original complex-model open, with explicit
inclusion into the given reader window and all derived coordinate maps. -/
theorem exists_primary_coordinates {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
    (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
    (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
      coordinateImageIdeal P C c (i.castAdd a)) :
    ∃ (A : Opens (ComplexModel (r+a))) (_hAP : A ≤ P) (_hcA : c.val.val ∈ A)
      (G : A → ComplexModel (r+b))
      (_hG : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G),
      (∀ (z : A) (i : Fin r), G z (i.castAdd b) ≠ 0) ∧
      (∀ z : A, assembled r a b z.val (G z) ∈ V) ∧
      (∀ (y : C) (hy : y.val.val ∈ A),
        (F.base y).val.val = assembled r a b y.val.val (G ⟨y.val.val,hy⟩)) := by
  obtain ⟨O,hcO,G,hG,hnz,hland,hactive,hother⟩ := exists_landing_ambient_ratio_coordinates P V C D F hF c hI
  let A : Opens (ComplexModel (r+a)) :=
    ⟨(Subtype.val : P → ComplexModel (r+a)) '' (O : Set P), P.isOpen.isOpenMap_subtype_val _ O.isOpen⟩
  have hAP : A ≤ P := by
    rintro _ ⟨p,_,rfl⟩
    exact p.property
  let j : A → P := Set.inclusion hAP
  have hjO : ∀ z : A, j z ∈ O := by
    intro z
    obtain ⟨p,hp,he⟩ := z.property
    have hpz : p = j z := Subtype.ext he
    exact hpz ▸ hp
  let i : A → O := fun z => ⟨j z,hjO z⟩
  have hi : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+a)) ∞ i :=
    (ContMDiff.subtypeVal_comp_iff O _).mp (contMDiff_inclusion hAP)
  let G' : A → ComplexModel (r+b) := G ∘ i
  have hG' : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G' := hG.comp hi
  have hcA : c.val.val ∈ A := ⟨c.val,hcO,rfl⟩
  refine ⟨A,hAP,hcA,G',hG',?_,?_,?_⟩
  · intro z k
    exact hnz (i z) k
  · intro z
    exact hland (i z)
  · intro y hy
    have hyO : y.val ∈ O := hjO ⟨y.val.val,hy⟩
    ext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [assembled_active]
      exact hactive y hyO k
    · rw [assembled_other]
      exact hother y hyO k

private structure Coordinates {r a b : ℕ}
    (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
    (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D) (c : C) where
  A : Opens (ComplexModel (r+a))
  hAP : A ≤ P
  hcA : c.val.val ∈ A
  G : A → ComplexModel (r+b)
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ G
  unit : ∀ (z : A) (i : Fin r), G z (i.castAdd b) ≠ 0
  landing : ∀ z : A, assembled r a b z.val (G z) ∈ V
  point : ∀ (y : C) (hy : y.val.val ∈ A), (F.base y).val.val = assembled r a b y.val.val (G ⟨y.val.val,hy⟩)

variable {r a b : ℕ}
  (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
  (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
  (hF : F ≫ subspacePointMap (n := r+b) D = subspacePointMap (n := r+a) C) (c : C)
  (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
    coordinateImageIdeal P C c (i.castAdd a))

include hF hI in
private theorem coordinates_nonempty : Nonempty (Coordinates P V C D F c) := by
  obtain ⟨A,hAP,hcA,G,hG,hu,hl,hp⟩ := exists_primary_coordinates P V C D F hF c hI
  exact ⟨⟨A,hAP,hcA,G,hG,hu,hl,hp⟩⟩

private def chosen : Coordinates P V C D F c := Classical.choice (coordinates_nonempty P V C D F hF c hI)

/-- The genuine primary original model open, produced from ordinary native inputs. -/
def primaryOpen : Opens (ComplexModel (r+a)) := (chosen P V C D F hF c hI).A

theorem primaryOpen_le : primaryOpen P V C D F hF c hI ≤ P := (chosen P V C D F hF c hI).hAP

theorem mem_primaryOpen : c.val.val ∈ primaryOpen P V C D F hF c hI := (chosen P V C D F hF c hI).hcA

/-- Derived actual unit-ratio and remaining target functions on that SAME open. -/
def primaryFunctions : primaryOpen P V C D F hF c hI → ComplexModel (r+b) := (chosen P V C D F hF c hI).G

theorem primaryFunctions_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel (r+b)) ∞ (primaryFunctions P V C D F hF c hI) :=
  (chosen P V C D F hF c hI).holomorphic

theorem primaryFunctions_nonzero (z : primaryOpen P V C D F hF c hI) (i : Fin r) :
    primaryFunctions P V C D F hF c hI z (i.castAdd b) ≠ 0 := (chosen P V C D F hF c hI).unit z i

theorem primaryFunctions_landing (z : primaryOpen P V C D F hF c hI) :
    assembled r a b z.val (primaryFunctions P V C D F hF c hI z) ∈ V := (chosen P V C D F hF c hI).landing z

/-- The actual original source trace, with its true reader inclusion. -/
def sourceTrace : Set (primaryOpen P V C D F hF c hI) :=
  (Set.inclusion (primaryOpen_le P V C D F hF c hI)) ⁻¹' C

include hI in
theorem sourceTrace_analytic (hC : IsComplexAnalyticSubset (n := r+a) C) :
    IsComplexAnalyticSubset (n := r+a) (sourceTrace P V C D F hF c hI) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion (primaryOpen_le P V C D F hF c hI)) hC

/-- FULL native source-window map, never just a source support function. -/
def sourceWindowMap : actualSubspaceLocallyRingedSpace (n := r+a) (sourceTrace P V C D F hF c hI) ⟶
    actualSubspaceLocallyRingedSpace (n := r+a) C :=
  actualSubspaceMap (contMDiff_inclusion (primaryOpen_le P V C D F hF c hI)) (fun _ hz => hz)

theorem sourceWindowMap_point : sourceWindowMap P V C D F hF c hI ≫ subspacePointMap (n := r+a) C =
    subspacePointMap (n := r+a) (sourceTrace P V C D F hF c hI) :=
  actualSubspaceMap_point (contMDiff_inclusion (primaryOpen_le P V C D F hF c hI)) (fun _ hz => hz)

private theorem sourcePoint (x : sourceTrace P V C D F hF c hI) :
    (F.base ((sourceWindowMap P V C D F hF c hI).base x)).val.val =
      assembled r a b x.val.val (primaryFunctions P V C D F hF c hI x.val) :=
  (chosen P V C D F hF c hI).point ((sourceWindowMap P V C D F hF c hI).base x) x.val.property

local notation "A0" => primaryOpen P V C D F hF c hI
local notation "G0" => primaryFunctions P V C D F hF c hI
local notation "S0" => sourceTrace P V C D F hF c hI

/-- The TRUE common ambient open has unit ratios AND the given target domain. -/
def commonOpen : Opens (A0 × ComplexModel (r+b)) := by
  let U : Set (A0 × ComplexModel (r+b)) := {w | ∀ i : Fin r, w.2 (i.castAdd b) ≠ 0}
  have hU : IsOpen U := by
    have hEq : U = ⋂ i : Fin r, {w : A0 × ComplexModel (r+b) | w.2 (i.castAdd b) ≠ 0} := by
      ext w
      simp only [U, mem_ofPred_eq, mem_iInter]
    rw [hEq]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun ((EuclideanSpace.proj (i.castAdd b)).continuous.comp continuous_snd) continuous_const
  exact ⟨U ∩ {w | assembled r a b w.1.val w.2 ∈ V},
    hU.inter (V.isOpen.preimage (assembled_holomorphic r a b A0).continuous)⟩

/-- Actual graph equations retain source membership and ALL graph differences. -/
def graphTrace : Set (commonOpen P V C D F hF c hI) :=
  (Subtype.val : commonOpen P V C D F hF c hI → A0 × ComplexModel (r+b)) ⁻¹' productGraph S0 G0

/-- The literal original source ideal plus z-U,q-V, restricted to the REAL open. -/
def commonGraphIdeal : GermIdeal ((r+a)+(r+b)) (commonOpen P V C D F hF c hI) :=
  GermIdeal.pullback (m := (r+a)+(r+b)) (Subtype.val : commonOpen P V C D F hF c hI → A0 × ComplexModel (r+b))
    (productGraphIdeal A0 S0 G0)

/-- Actual first ambient projection on the genuine common open. -/
def firstAmbient (z : commonOpen P V C D F hF c hI) : A0 := z.val.1

theorem firstAmbient_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+a)) ∞ (firstAmbient P V C D F hF c hI) :=
  ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val

/-- Actual second ambient projection into the GIVEN target reader open. -/
def secondAmbient (z : commonOpen P V C D F hF c hI) : V :=
  ⟨assembled r a b z.val.1.val z.val.2,z.property.2⟩

theorem secondAmbient_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞ (secondAmbient P V C D F hF c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact (assembled_holomorphic r a b A0).comp contMDiff_subtype_val

/-- DERIVED graph parametrization lands in the genuine common open even on
all ambient source points; this was enforced by honest target shrinking. -/
def graphSection (z : A0) : commonOpen P V C D F hF c hI :=
  ⟨(z,G0 z),primaryFunctions_nonzero P V C D F hF c hI z,primaryFunctions_landing P V C D F hF c hI z⟩

theorem graphSection_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞ (graphSection P V C D F hF c hI) := by
  apply (ContMDiff.subtypeVal_comp_iff (commonOpen P V C D F hF c hI) _).mp
  exact ProductComplexManifold.contMDiff_prodMk contMDiff_id (primaryFunctions_holomorphic P V C D F hF c hI)

/-- Genuine FULL native graph/first-projection isomorphism, from real ambient maps. -/
def graphIso : actualSubspaceLocallyRingedSpace (n := r+a) S0 ≅
    actualSubspaceLocallyRingedSpace (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) :=
  HironakaActualAnalyticSubspacePresentationIndependence.actualSubspaceMutualRestrictionIso
    (graphSection_holomorphic P V C D F hF c hI) (firstAmbient_holomorphic P V C D F hF c hI)
    (fun _ hx => ⟨hx,rfl⟩) (fun _ hz => hz.1) (fun _ _ => rfl)
    (fun _z hz => Subtype.ext (Prod.ext rfl hz.2.symm))

theorem graphIso_hom_point : (graphIso P V C D F hF c hI).hom ≫
      subspacePointMap (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) =
    subspacePointMap (n := r+a) S0 :=
  actualSubspaceMap_point (C := S0) (D := graphTrace P V C D F hF c hI)
    (graphSection_holomorphic P V C D F hF c hI) (fun _ hx => ⟨hx,rfl⟩)

/-- The full first native projection retains its ORIGINAL scalar/inclusion square. -/
theorem graphIso_inv_inclusion : (graphIso P V C D F hF c hI).inv ≫ actualSubspaceInclusion (n := r+a) S0 =
    actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) ≫
      ChartedSpace.locallyRingedSpaceMap (firstAmbient P V C D F hF c hI) (firstAmbient_holomorphic P V C D F hF c hI) :=
  (actualSubspaceMap_inclusion (C := graphTrace P V C D F hF c hI) (D := S0)
    (firstAmbient_holomorphic P V C D F hF c hI) (fun _ hz => hz.1)).symm

/-- Closed analytic graph on the ACTUAL common ambient open. -/
theorem graphTrace_analytic (hC : IsComplexAnalyticSubset (n := r+a) C) :
    IsComplexAnalyticSubset (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) :=
  AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    (productGraph_analytic S0 (sourceTrace_analytic P V C D F hF c hI hC) G0
      (primaryFunctions_holomorphic P V C D F hF c hI)) (commonOpen P V C D F hF c hI)

/-- ENTIRE original graph ideal including offgraph/unit stalks, using the
held graph elimination theorem and the genuine whole open restriction. -/
theorem graph_whole_ideal (hC : IsComplexAnalyticSubset (n := r+a) C) :
    vanishingIdeal (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) = commonGraphIdeal P V C D F hF c hI := by
  have hid : GermIdeal.pullback (m := (r+a)+(r+b)) (id : commonOpen P V C D F hF c hI → commonOpen P V C D F hF c hI)
      (vanishingIdeal (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)) =
        vanishingIdeal (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) :=
    GermIdeal.ext (funext fun _ => funext fun _ =>
      propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := (r+a)+(r+b))
    (m := (r+a)+(r+b)) (commonOpen P V C D F hF c hI)
    (id : commonOpen P V C D F hF c hI → commonOpen P V C D F hF c hI) (productGraph S0 G0)
  calc
    _ = GermIdeal.pullback (m := (r+a)+(r+b))
        (id : commonOpen P V C D F hF c hI → commonOpen P V C D F hF c hI)
        (vanishingIdeal (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)) := hid.symm
    _ = GermIdeal.pullback (m := (r+a)+(r+b))
        (Subtype.val : commonOpen P V C D F hF c hI → A0 × ComplexModel (r+b))
        (vanishingIdeal (n := (r+a)+(r+b)) (productGraph S0 G0)) := h
    _ = _ := congrArg
      (fun I => GermIdeal.pullback (m := (r+a)+(r+b))
        (Subtype.val : commonOpen P V C D F hF c hI → A0 × ComplexModel (r+b)) I)
      (productGraph_whole_ideal A0 S0 (sourceTrace_analytic P V C D F hF c hI hC) G0
        (primaryFunctions_holomorphic P V C D F hF c hI))

/-- The REAL native ambient-to-graph kernel is the SAME entire original ideal. -/
theorem graph_stalk_kernel (hC : IsComplexAnalyticSubset (n := r+a) C) (z : graphTrace P V C D F hF c hI) :
    RingHom.ker ((actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)).stalkMap z).hom =
      actualWholeSheafStalkIdeal (commonGraphIdeal P V C D F hF c hI) z.val := by
  rw [actualSubspaceInclusion_stalk_kernel, graph_whole_ideal P V C D F hF c hI hC]

private theorem secondAmbient_mapsTo (z : commonOpen P V C D F hF c hI)
    (hz : z ∈ graphTrace P V C D F hF c hI) : secondAmbient P V C D F hF c hI z ∈ D := by
  let x : S0 := ⟨z.val.1,hz.1⟩
  let y : C := (sourceWindowMap P V C D F hF c hI).base x
  have he : secondAmbient P V C D F hF c hI z = (F.base y).val := by
    apply Subtype.ext
    change assembled r a b z.val.1.val z.val.2 = (F.base y).val.val
    rw [hz.2]
    exact (sourcePoint P V C D F hF c hI x).symm
  rw [he]
  exact (F.base y).property

/-- The second native map is CONSTRUCTED from the real ambient second projection. -/
def secondNativeMap : actualSubspaceLocallyRingedSpace (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) ⟶
    actualSubspaceLocallyRingedSpace (n := r+b) D :=
  actualSubspaceMap (secondAmbient_holomorphic P V C D F hF c hI) (secondAmbient_mapsTo P V C D F hF c hI)

theorem secondNativeMap_point : secondNativeMap P V C D F hF c hI ≫ subspacePointMap (n := r+b) D =
    subspacePointMap (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) :=
  actualSubspaceMap_point (secondAmbient_holomorphic P V C D F hF c hI) (secondAmbient_mapsTo P V C D F hF c hI)

/-- The WHOLE second native scalar/inclusion square uses its ACTUAL ambient map. -/
theorem secondNativeMap_inclusion : secondNativeMap P V C D F hF c hI ≫ actualSubspaceInclusion (n := r+b) D =
    actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI) ≫
      ChartedSpace.locallyRingedSpaceMap (secondAmbient P V C D F hF c hI) (secondAmbient_holomorphic P V C D F hF c hI) :=
  (actualSubspaceMap_inclusion (secondAmbient_holomorphic P V C D F hF c hI) (secondAmbient_mapsTo P V C D F hF c hI)).symm

/-- Full native equality with the GIVEN overlap follows from DERIVED coordinate
identities and whole quotient-map faithfulness, not from a supplied graph square. -/
theorem graph_overlap_square : (graphIso P V C D F hF c hI).hom ≫ secondNativeMap P V C D F hF c hI =
    sourceWindowMap P V C D F hF c hI ≫ F := by
  apply actualSubspaceMap_eq_of_base_eq
  · rw [Category.assoc, secondNativeMap_point]
    exact graphIso_hom_point P V C D F hF c hI
  · rw [Category.assoc, hF]
    exact sourceWindowMap_point P V C D F hF c hI
  · apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change assembled r a b x.val.val (G0 x.val) = (F.base ((sourceWindowMap P V C D F hF c hI).base x)).val.val
    exact (sourcePoint P V C D F hF c hI x).symm

end
end SGPT.Unibranch.HironakaG1PrimaryNativeGraph
