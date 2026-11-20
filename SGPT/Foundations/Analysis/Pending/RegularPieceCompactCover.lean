import SGPT.Foundations.Analysis.Pending.PatchFormMass
import SGPT.Foundations.Analysis.Pending.SubvarietyBackgroundMass

set_option autoImplicit false

/-!
# Every compact part of `V_reg` is covered by one finite regular-piece family

`Pending.PatchFormMass` compares two regular-piece families but produces none.
This module produces them, and in the only shape an exhaustion of `V_reg` can
consume:

* `singletonFamily` and `emptyFamily` — the two trivial families;
* `exists_family_iUnion_image_superset` — finitely many measurable pieces of
  finitely many patches, with no disjointness assumed, are all covered by the
  images of ONE regular-piece family.  Disjointness is not a hypothesis because
  `PatchFormMass.unionFamily` removes the overlaps: the parameters of a piece
  whose image an earlier piece already sees form an overlap set, which is
  measurable in the parameter space;
* `exists_family_covering_of_isCompact` — every compact subset of `V_reg` that
  misses a closed avoided set is covered by the images of a regular-piece family
  avoiding that set.

The second statement is what makes the first useful: a compact subset of `V_reg`
is covered by finitely many patch images, by `Pending.PatchParameterNull`, but
those images overlap, and the overlaps are exactly what a family may not have.

**What this is and is not.**  `SubvarietyStokesMassInterfaces` records that a
proof of Stokes against `[V]` needs finite regular pieces approximating `V_reg`
in measure, and that no such sequence is available.  This module supplies the
covering half — every compact part of `V_reg` is reached — for families avoiding
any closed set, so in particular for the families of `acTopMass` (the pole set of
a potential with analytic singularities is closed) as well as those of
`backgroundMass`.  The complementary half — compact subsets of `V_reg` carrying
all of the mass — is `Pending.RegularPieceInnerRegular`, which shrinks the pieces
of a family to compact subpieces without losing mass; the two together exhaust
`V_reg` in measure by finite regular pieces
(`RegularPieceInnerRegular.exists_isCompact_carrying_mass`).
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RegularPieceCompactCover

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood
open PatchFormMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The empty regular-piece family. -/
def emptyFamily (V : ClosedIrreducibleAnalyticSubvariety n M) (avoid : Set M) :
    RegularPieceFamily V avoid where
  size := 0
  patch := Fin.elim0
  piece := Fin.elim0
  measurableSet_piece := fun i => Fin.elim0 i
  piece_subset := fun i => Fin.elim0 i
  image_subset_regularLocus := fun i => Fin.elim0 i
  image_disjoint_avoid := fun i => Fin.elim0 i
  pairwise_disjoint_image := fun i => Fin.elim0 i

/-- One measurable piece of one patch, as a regular-piece family.  Its image lies
in `V_reg` automatically: every point parametrized by a regular patch is a
regular point of the certified dimension. -/
def singletonFamily {avoid : Set M} (P : RegularPatch V) (S : Set (ComplexModel V.dim))
    (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain)
    (havoid : Disjoint (P.toManifold '' S) avoid) : RegularPieceFamily V avoid where
  size := 1
  patch := fun _ => P
  piece := fun _ => S
  measurableSet_piece := fun _ => hS
  piece_subset := fun _ => hsub
  image_subset_regularLocus := by
    rintro _ _ ⟨w, hw, rfl⟩
    exact RegularPatch.toManifold_mem_regularLocus P (hsub hw)
  image_disjoint_avoid := fun _ => havoid
  pairwise_disjoint_image := fun i j hij => absurd (Subsingleton.elim i j) hij

@[simp] theorem singletonFamily_patch {avoid : Set M} (P : RegularPatch V)
    (S : Set (ComplexModel V.dim)) (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain)
    (havoid : Disjoint (P.toManifold '' S) avoid) (i : Fin 1) :
    (singletonFamily P S hS hsub havoid).patch i = P := rfl

@[simp] theorem singletonFamily_piece {avoid : Set M} (P : RegularPatch V)
    (S : Set (ComplexModel V.dim)) (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain)
    (havoid : Disjoint (P.toManifold '' S) avoid) (i : Fin 1) :
    (singletonFamily P S hS hsub havoid).piece i = S := rfl

/-- The union of the images of a family is contained in that of its union with
another family. -/
theorem iUnion_image_subset_unionFamily_left {avoid : Set M}
    (F G : RegularPieceFamily V avoid) :
    (⋃ i, (F.patch i).toManifold '' F.piece i) ⊆
      ⋃ k, ((unionFamily F G).patch k).toManifold '' (unionFamily F G).piece k :=
  Set.iUnion_subset fun i => image_subset_iUnion_image_unionFamily F G i

/-- **Finitely many measurable pieces of finitely many patches are covered by one
regular-piece family.**  No disjointness is assumed: the overlaps are removed by
`PatchFormMass.unionFamily`, which is legitimate because the parameters of a
piece whose image an earlier piece already sees form a measurable overlap set. -/
theorem exists_family_iUnion_image_superset {avoid : Set M} :
    ∀ (N : ℕ) (P : Fin N → RegularPatch V) (S : Fin N → Set (ComplexModel V.dim)),
      (∀ i, MeasurableSet (S i)) → (∀ i, S i ⊆ (P i).parameterDomain) →
      (∀ i, Disjoint ((P i).toManifold '' S i) avoid) →
      ∃ F : RegularPieceFamily V avoid,
        ∀ i, (P i).toManifold '' S i ⊆ ⋃ k, (F.patch k).toManifold '' F.piece k := by
  intro N
  induction N with
  | zero => exact fun P S _ _ _ => ⟨emptyFamily V avoid, fun i => Fin.elim0 i⟩
  | succ N ih =>
    intro P S hmeas hsub havoid
    obtain ⟨F, hF⟩ := ih (fun j => P j.castSucc) (fun j => S j.castSucc)
      (fun j => hmeas _) (fun j => hsub _) (fun j => havoid _)
    refine ⟨unionFamily F
      (singletonFamily (P (Fin.last N)) (S (Fin.last N)) (hmeas _) (hsub _) (havoid _)), ?_⟩
    refine Fin.lastCases ?_ ?_
    · exact image_subset_iUnion_image_unionFamily' F
        (singletonFamily (P (Fin.last N)) (S (Fin.last N)) (hmeas _) (hsub _) (havoid _))
        ⟨0, Nat.one_pos⟩
    · intro j
      exact (hF j).trans (iUnion_image_subset_unionFamily_left F _)

/-- The same statement for an arbitrary finite index type. -/
theorem exists_family_iUnion_image_superset' {avoid : Set M} {iota : Type*} [Fintype iota]
    (P : iota → RegularPatch V) (S : iota → Set (ComplexModel V.dim))
    (hmeas : ∀ i, MeasurableSet (S i)) (hsub : ∀ i, S i ⊆ (P i).parameterDomain)
    (havoid : ∀ i, Disjoint ((P i).toManifold '' S i) avoid) :
    ∃ F : RegularPieceFamily V avoid,
      ∀ i, (P i).toManifold '' S i ⊆ ⋃ k, (F.patch k).toManifold '' F.piece k := by
  obtain ⟨F, hF⟩ := exists_family_iUnion_image_superset (avoid := avoid) (Fintype.card iota)
    (fun j => P ((Fintype.equivFin iota).symm j)) (fun j => S ((Fintype.equivFin iota).symm j))
    (fun j => hmeas _) (fun j => hsub _) (fun j => havoid _)
  refine ⟨F, fun i => ?_⟩
  simpa using hF (Fintype.equivFin iota i)

/-- **Every compact part of `V_reg` is covered by one regular-piece family.**
Around each of its points a single patch parametrizes `V`, and
`Pending.PatchParameterNull` turns that into an ambient open set meeting `V`
inside the patch image; compactness leaves finitely many of them, and
`exists_family_iUnion_image_superset` removes their overlaps. -/
theorem exists_family_covering_of_isCompact {avoid : Set M} (havoid : IsClosed avoid)
    {K : Set M} (hK : IsCompact K)
    (hKreg : K ⊆ regularLocus (n := n) V.carrier V.dim) (hKavoid : Disjoint K avoid) :
    ∃ F : RegularPieceFamily V avoid,
      K ⊆ ⋃ k, (F.patch k).toManifold '' F.piece k := by
  classical
  -- around every point of `K`: a patch, a parameter ball, and an ambient open set
  have hloc : ∀ x : ↥K, ∃ (P : RegularPatch V) (r : ℝ) (W : Set M),
      0 < r ∧ Metric.ball (0 : ComplexModel V.dim) r ⊆ P.parameterDomain ∧
        IsOpen W ∧ (x : M) ∈ W ∧ Disjoint W avoid ∧
        V.carrier ∩ W ⊆ P.toManifold '' Metric.ball (0 : ComplexModel V.dim) r := by
    rintro ⟨x, hx⟩
    set P : RegularPatch V :=
      SubvarietyStokesMassInterfaces.patchOfMemRegularLocus (hKreg hx) with hP
    obtain ⟨r, hr0, hball⟩ := RegularPatch.regularAtDim_toManifold P
    have hsub : Metric.ball (0 : ComplexModel V.dim) r ⊆ P.parameterDomain :=
      fun w hw => (hball w hw).1
    obtain ⟨U, hUo, himg, hVU⟩ :=
      PatchParameterNull.exists_isOpen_carrier_inter_subset_image P Metric.isOpen_ball hsub
    have hxU : x ∈ U := by
      have h0 : P.toManifold 0 ∈ P.toManifold '' Metric.ball (0 : ComplexModel V.dim) r :=
        ⟨0, Metric.mem_ball_self hr0, rfl⟩
      have hU := himg h0
      rwa [RegularPatch.toManifold_zero] at hU
    exact ⟨P, r, U ∩ avoidᶜ, hr0, hsub, hUo.inter havoid.isOpen_compl,
      ⟨hxU, fun hxa => (Set.disjoint_left.mp hKavoid hx) hxa⟩,
      Set.disjoint_left.mpr fun y hy => hy.2, fun y hy => hVU ⟨hy.1, hy.2.1⟩⟩
  choose P r W hr0 hrsub hWo hxW hWavoid hWimg using hloc
  obtain ⟨t, htcover⟩ :=
    hK.elim_finite_subcover W hWo fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  set Q : ↥t → RegularPatch V := fun i => P (i : ↥K) with hQ
  set S : ↥t → Set (ComplexModel V.dim) := fun i =>
    Metric.ball (0 : ComplexModel V.dim) (r (i : ↥K)) ∩
      (Q i).toManifold ⁻¹' W (i : ↥K) with hS
  have hSmeas : ∀ i, MeasurableSet (S i) := fun i =>
    SubvarietyStokesMassInterfaces.measurableSet_inter_toManifold_preimage (Q i)
      measurableSet_ball (hrsub _) (hWo _)
  have hSsub : ∀ i, S i ⊆ (Q i).parameterDomain :=
    fun i => Set.inter_subset_left.trans (hrsub _)
  have hSavoid : ∀ i, Disjoint ((Q i).toManifold '' S i) avoid := by
    intro i
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    exact Set.disjoint_left.mp (hWavoid _) hw.2
  obtain ⟨F, hF⟩ :=
    exists_family_iUnion_image_superset' (avoid := avoid) Q S hSmeas hSsub hSavoid
  refine ⟨F, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyW⟩ := Set.mem_iUnion₂.mp (htcover hy)
  have hycar : y ∈ V.carrier := FirstPass.regularLocus_subset _ _ (hKreg hy)
  obtain ⟨w, hw, hwy⟩ := hWimg x ⟨hycar, hyW⟩
  refine hF ⟨x, hxt⟩ ⟨w, ⟨hw, ?_⟩, hwy⟩
  rw [Set.mem_preimage, hwy]
  exact hyW

end

end SGPT.Foundations.Analysis.Pending.RegularPieceCompactCover
