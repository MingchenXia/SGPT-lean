import SGPT.Foundations.Analysis.Pending.RegularPatchTransition

set_option autoImplicit false

/-!
# The regular-piece mass of an arbitrary smooth two-form

`Pending.RegularPieceMassComparison` proves that the regular-piece mass of the
BACKGROUND Kähler form depends only on the region of `V_reg` a family covers,
and deduces that the supremum defining `backgroundMass` is directed.  Its
docstring, and that of the Stokes interface
`SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass`, both record the
same limitation: the argument was written for `beta.form` and for families
avoiding `∅`, so it says nothing about `acTopMass`, whose families avoid the
pole set and whose density is built from `coordinateCurrentForm`.

Nothing in the argument uses either restriction.  This module carries it out
once, for an arbitrary `a : SmoothRealForm n M 2` and arbitrary avoided sets,
against the density `MongeAmpere.actualTopPowerDensity (patchCoordinateForm a P w)`
of `Pending.RegularPatchTransition`:

* `overlapParameters` — the `Q`-parameters of the part of `S` that the patch `P`
  sees inside `T`, and `inter_preimage_image_toManifold`, which identifies it
  with a preimage under the transition and so avoids any measurability
  statement about images in `M`;
* `formPieceMass_mono_of_image_subset` — a family covered by another computes no
  more mass, for ANY smooth two-form and any two avoided sets;
* `unionFamily` and `directed_formPieceMass` — two families with the SAME
  avoided set are dominated by a common one.

`Pending.ACTopMassComparison` then applies this to `acTopMass`, and
`Pending.RegularPieceMassComparison` recovers its background statements as the
special case `a = beta.form.val`, `avoid = ∅`.

The two limitations of the background version survive unchanged, because they
are not about the form: this does NOT produce a sequence of families exhausting
`V_reg`, and it says nothing about `V_sing`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.PatchFormMass

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parameter density of a smooth real two-form on a regular patch. -/
def patchFormDensity (a : SmoothRealForm n M 2) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ℝ :=
  MongeAmpere.actualTopPowerDensity (RegularPatchTransition.patchCoordinateForm a P w)

/-- The `Q`-parameters of the part of `S` that the patch `P` sees inside `T`:
the points of `S` at which the transition to `P` is defined and lands in `T`. -/
def overlapParameters (P Q : RegularPatch V) (S T : Set (ComplexModel V.dim)) :
    Set (ComplexModel V.dim) :=
  S ∩ RegularPatchTransition.transitionDomain P Q ∩
    RegularPatchTransition.transition P Q ⁻¹' T

theorem overlapParameters_subset (P Q : RegularPatch V) (S T : Set (ComplexModel V.dim)) :
    overlapParameters P Q S T ⊆ S :=
  fun _ hw => hw.1.1

theorem overlapParameters_subset_transitionDomain (P Q : RegularPatch V)
    (S T : Set (ComplexModel V.dim)) :
    overlapParameters P Q S T ⊆ RegularPatchTransition.transitionDomain P Q :=
  fun _ hw => hw.1.2

theorem image_overlapParameters_subset (P Q : RegularPatch V)
    (S T : Set (ComplexModel V.dim)) :
    RegularPatchTransition.transition P Q '' overlapParameters P Q S T ⊆ T := by
  rintro _ ⟨w, hw, rfl⟩
  exact hw.2

/-- **The overlap of two patches is a parameter set.**  On a piece of `Q` inside
its parameter domain, the points whose image is seen by `P` inside a piece `T` of
`P`'s parameter domain are exactly the points at which the transition `τ` to `P`
is defined and lands in `T`.  No measurability of images in `M` is involved. -/
theorem inter_preimage_image_toManifold (P Q : RegularPatch V)
    {S T : Set (ComplexModel V.dim)} (hS : S ⊆ Q.parameterDomain)
    (hT : T ⊆ P.parameterDomain) :
    S ∩ Q.toManifold ⁻¹' (P.toManifold '' T) = overlapParameters P Q S T := by
  ext w
  constructor
  · rintro ⟨hwS, v, hvT, hv⟩
    obtain ⟨hmem, hτ⟩ :=
      RegularPatchTransition.mem_transitionDomain_and_transition_eq (hS hwS) (hT hvT) hv.symm
    exact ⟨⟨hwS, hmem⟩, by rw [Set.mem_preimage, hτ]; exact hvT⟩
  · rintro ⟨⟨hwS, hmem⟩, hτ⟩
    refine ⟨hwS, ⟨RegularPatchTransition.transition P Q w, hτ, ?_⟩⟩
    exact RegularPatchTransition.toManifold_transition hmem

/-- The transition is measurable on its (open) domain, so the overlap of two
measurable pieces is measurable. -/
theorem measurableSet_overlapParameters (P Q : RegularPatch V)
    {S T : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    MeasurableSet (overlapParameters P Q S T) := by
  classical
  set D := RegularPatchTransition.transitionDomain P Q with hD
  have hDopen : IsOpen D := RegularPatchTransition.isOpen_transitionDomain P Q
  have hcont : ContinuousOn (RegularPatchTransition.transition P Q) D :=
    (RegularPatchTransition.differentiableOn_transition P Q).continuousOn
  have hrestr : Continuous (D.domRestrict (RegularPatchTransition.transition P Q)) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  have hsub : MeasurableSet
      (D.domRestrict (RegularPatchTransition.transition P Q) ⁻¹' T) :=
    hrestr.measurable hT
  have himg : ((↑) : D → ComplexModel V.dim) ''
      (D.domRestrict (RegularPatchTransition.transition P Q) ⁻¹' T) =
      D ∩ RegularPatchTransition.transition P Q ⁻¹' T := by
    ext w
    constructor
    · rintro ⟨⟨v, hv⟩, hmem, rfl⟩
      exact ⟨hv, hmem⟩
    · rintro ⟨hwD, hwT⟩
      exact ⟨⟨w, hwD⟩, hwT, rfl⟩
  have hDT : MeasurableSet (D ∩ RegularPatchTransition.transition P Q ⁻¹' T) := by
    rw [← himg]
    exact hDopen.measurableSet.subtype_image hsub
  have hrw : overlapParameters P Q S T =
      S ∩ (D ∩ RegularPatchTransition.transition P Q ⁻¹' T) := by
    ext w
    exact ⟨fun hw => ⟨hw.1.1, hw.1.2, hw.2⟩, fun hw => ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩⟩
  rw [hrw]
  exact hS.inter hDT

/-- The image of an overlap under the transition is measurable: the transition is
holomorphic, hence continuous, and injective on its domain. -/
theorem measurableSet_image_overlapParameters (P Q : RegularPatch V)
    {S T : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    MeasurableSet (RegularPatchTransition.transition P Q '' overlapParameters P Q S T) := by
  refine (measurableSet_overlapParameters P Q hS hT).image_of_continuousOn_injOn ?_ ?_
  · exact fun w hw =>
      (RegularPatchTransition.differentiableAt_transition
        (overlapParameters_subset_transitionDomain P Q S T hw)).continuousAt.continuousWithinAt
  · exact (RegularPatchTransition.injOn_transition P Q).mono
      (overlapParameters_subset_transitionDomain P Q S T)

/-- **Change of variables on an overlap**, for an arbitrary smooth two-form. -/
theorem lintegral_image_overlapParameters (a : SmoothRealForm n M 2)
    (P Q : RegularPatch V) {S T : Set (ComplexModel V.dim)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫⁻ v in RegularPatchTransition.transition P Q '' overlapParameters P Q S T,
        ENNReal.ofReal (patchFormDensity a P v)) =
      ∫⁻ w in overlapParameters P Q S T,
        ENNReal.ofReal (patchFormDensity a Q w) :=
  RegularPatchTransition.lintegral_actualTopPowerDensity_transition a
    (measurableSet_overlapParameters P Q hS hT)
    (overlapParameters_subset_transitionDomain P Q S T)

section Families

variable (a : SmoothRealForm n M 2)

/-- The regular-piece mass of a smooth two-form attached to one family. -/
def formPieceMass {avoid : Set M} (F : RegularPieceFamily V avoid) : ℝ≥0∞ :=
  ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchFormDensity a (F.patch i) w)

/-- The decomposition of a piece of `F` along the pieces of `G`. -/
private def slice {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (i : Fin F.size) (j : Fin G.size) :
    Set (ComplexModel V.dim) :=
  overlapParameters (G.patch j) (F.patch i) (F.piece i) (G.piece j)

private theorem slice_eq {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (i : Fin F.size) (j : Fin G.size) :
    slice F G i j =
      F.piece i ∩ (F.patch i).toManifold ⁻¹' ((G.patch j).toManifold '' G.piece j) :=
  (inter_preimage_image_toManifold (G.patch j) (F.patch i)
    (F.piece_subset i) (G.piece_subset j)).symm

private theorem measurableSet_slice {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (i : Fin F.size) (j : Fin G.size) :
    MeasurableSet (slice F G i j) :=
  measurableSet_overlapParameters (G.patch j) (F.patch i)
    (F.measurableSet_piece i) (G.measurableSet_piece j)

private theorem measurableSet_image_slice {avoidF avoidG : Set M}
    (F : RegularPieceFamily V avoidF) (G : RegularPieceFamily V avoidG)
    (i : Fin F.size) (j : Fin G.size) :
    MeasurableSet
      (RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j) :=
  measurableSet_image_overlapParameters (G.patch j) (F.patch i)
    (F.measurableSet_piece i) (G.measurableSet_piece j)

private theorem image_slice_subset {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (i : Fin F.size) (j : Fin G.size) :
    RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j ⊆
      G.piece j :=
  image_overlapParameters_subset (G.patch j) (F.patch i) (F.piece i) (G.piece j)

/-- The slices of one piece of `F` are pairwise disjoint: they are the preimages
of the pairwise disjoint images of `G`. -/
private theorem pairwise_disjoint_slice {avoidF avoidG : Set M}
    (F : RegularPieceFamily V avoidF) (G : RegularPieceFamily V avoidG) (i : Fin F.size) :
    Pairwise (Function.onFun Disjoint fun j : Fin G.size => slice F G i j) := by
  intro j j' hjj'
  rw [Function.onFun, slice_eq, slice_eq, Set.disjoint_left]
  rintro w ⟨_, hw⟩ ⟨_, hw'⟩
  exact Set.disjoint_left.mp (G.pairwise_disjoint_image hjj') hw hw'

/-- The slices of a piece of `F` exhaust it, provided `G` covers the images of `F`. -/
private theorem iUnion_slice {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG)
    (hcov : ∀ i, (F.patch i).toManifold '' F.piece i ⊆
      ⋃ j, (G.patch j).toManifold '' G.piece j)
    (i : Fin F.size) :
    ⋃ j, slice F G i j = F.piece i := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) fun w hw => ?_
  · rw [slice_eq]; exact Set.inter_subset_left
  · obtain ⟨_, ⟨j, rfl⟩, hmem⟩ := hcov i ⟨w, hw, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, by rw [slice_eq]; exact ⟨hw, hmem⟩⟩

/-- For a fixed piece of `G`, the transported slices coming from different pieces
of `F` are pairwise disjoint: their images in `M` are the pairwise disjoint
images of `F`. -/
private theorem pairwise_disjoint_image_slice {avoidF avoidG : Set M}
    (F : RegularPieceFamily V avoidF) (G : RegularPieceFamily V avoidG) (j : Fin G.size) :
    Pairwise (Function.onFun Disjoint fun i : Fin F.size =>
      RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j) := by
  intro i i' hii'
  rw [Function.onFun, Set.disjoint_left]
  rintro v ⟨w, hw, rfl⟩ ⟨w', hw', hvw'⟩
  have h1 : (G.patch j).toManifold
      (RegularPatchTransition.transition (G.patch j) (F.patch i) w) =
      (F.patch i).toManifold w :=
    RegularPatchTransition.toManifold_transition
      (overlapParameters_subset_transitionDomain _ _ _ _ hw)
  have h2 : (G.patch j).toManifold
      (RegularPatchTransition.transition (G.patch j) (F.patch i') w') =
      (F.patch i').toManifold w' :=
    RegularPatchTransition.toManifold_transition
      (overlapParameters_subset_transitionDomain _ _ _ _ hw')
  rw [← hvw'] at h1
  refine Set.disjoint_left.mp (F.pairwise_disjoint_image hii')
    ⟨w, overlapParameters_subset _ _ _ _ hw, h1.symm.trans h2⟩ ?_
  exact ⟨w', overlapParameters_subset _ _ _ _ hw', rfl⟩

/-- **The regular-piece mass is monotone in the region covered**, for an arbitrary
smooth two-form and arbitrary avoided sets.  If every image of `F` lies in the
union of the images of `G`, then `F` computes no more mass than `G`.

This is the patch-independence of the subvariety mass in its usable form: the
number `formPieceMass a F` is controlled by the *region* of `V_reg` that `F`
covers and not by the patches it is read in, nor by the set its family was
declared to avoid. -/
theorem formPieceMass_mono_of_image_subset {avoidF avoidG : Set M}
    {F : RegularPieceFamily V avoidF} {G : RegularPieceFamily V avoidG}
    (hcov : ∀ i, (F.patch i).toManifold '' F.piece i ⊆
      ⋃ j, (G.patch j).toManifold '' G.piece j) :
    formPieceMass a F ≤ formPieceMass a G := by
  classical
  have hsplit : ∀ i : Fin F.size,
      (∫⁻ w in F.piece i, ENNReal.ofReal (patchFormDensity a (F.patch i) w)) =
        ∑ j : Fin G.size, ∫⁻ w in slice F G i j,
          ENNReal.ofReal (patchFormDensity a (F.patch i) w) := by
    intro i
    rw [← iUnion_slice F G hcov i,
      lintegral_iUnion (measurableSet_slice F G i) (pairwise_disjoint_slice F G i),
      tsum_fintype]
  have htrans : ∀ (i : Fin F.size) (j : Fin G.size),
      (∫⁻ w in slice F G i j,
          ENNReal.ofReal (patchFormDensity a (F.patch i) w)) =
        ∫⁻ v in RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
          ENNReal.ofReal (patchFormDensity a (G.patch j) v) :=
    fun i j => (lintegral_image_overlapParameters a (G.patch j) (F.patch i)
      (F.measurableSet_piece i) (G.measurableSet_piece j)).symm
  have hgather : ∀ j : Fin G.size,
      (∑ i : Fin F.size, ∫⁻ v in
          RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
            ENNReal.ofReal (patchFormDensity a (G.patch j) v)) ≤
        ∫⁻ v in G.piece j, ENNReal.ofReal (patchFormDensity a (G.patch j) v) := by
    intro j
    have hunion : (∫⁻ v in ⋃ i : Fin F.size,
        RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
          ENNReal.ofReal (patchFormDensity a (G.patch j) v)) =
        ∑ i : Fin F.size, ∫⁻ v in
          RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
            ENNReal.ofReal (patchFormDensity a (G.patch j) v) := by
      rw [lintegral_iUnion (fun i => measurableSet_image_slice F G i j)
        (pairwise_disjoint_image_slice F G j), tsum_fintype]
    rw [← hunion]
    exact lintegral_mono_set (Set.iUnion_subset fun i => image_slice_subset F G i j)
  calc formPieceMass a F
      = ∑ i : Fin F.size, ∑ j : Fin G.size, ∫⁻ v in
          RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
            ENNReal.ofReal (patchFormDensity a (G.patch j) v) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsplit i]
        exact Finset.sum_congr rfl fun j _ => htrans i j
    _ = ∑ j : Fin G.size, ∑ i : Fin F.size, ∫⁻ v in
          RegularPatchTransition.transition (G.patch j) (F.patch i) '' slice F G i j,
            ENNReal.ofReal (patchFormDensity a (G.patch j) v) := Finset.sum_comm
    _ ≤ ∑ j : Fin G.size, ∫⁻ v in G.piece j,
          ENNReal.ofReal (patchFormDensity a (G.patch j) v) :=
        Finset.sum_le_sum fun j _ => hgather j
    _ = formPieceMass a G := rfl

/-- **Two families covering the same part of `V_reg` compute the same mass.** -/
theorem formPieceMass_congr_of_iUnion_image_eq {avoidF avoidG : Set M}
    {F : RegularPieceFamily V avoidF} {G : RegularPieceFamily V avoidG}
    (h : (⋃ i, (F.patch i).toManifold '' F.piece i) =
      ⋃ j, (G.patch j).toManifold '' G.piece j) :
    formPieceMass a F = formPieceMass a G := by
  refine le_antisymm (formPieceMass_mono_of_image_subset a fun i => ?_)
    (formPieceMass_mono_of_image_subset a fun j => ?_)
  · exact h ▸ Set.subset_iUnion_of_subset i le_rfl
  · exact h ▸ Set.subset_iUnion_of_subset j le_rfl

/-- The `G`-parameters of the piece `G.piece j` that no piece of `F` already sees. -/
def freshParameters {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (j : Fin G.size) : Set (ComplexModel V.dim) :=
  G.piece j \ ⋃ i : Fin F.size,
    overlapParameters (F.patch i) (G.patch j) (G.piece j) (F.piece i)

theorem freshParameters_subset {avoidF avoidG : Set M} (F : RegularPieceFamily V avoidF)
    (G : RegularPieceFamily V avoidG) (j : Fin G.size) :
    freshParameters F G j ⊆ G.piece j := Set.sdiff_subset

theorem measurableSet_freshParameters {avoidF avoidG : Set M}
    (F : RegularPieceFamily V avoidF) (G : RegularPieceFamily V avoidG) (j : Fin G.size) :
    MeasurableSet (freshParameters F G j) :=
  (G.measurableSet_piece j).diff
    (MeasurableSet.iUnion fun i => measurableSet_overlapParameters (F.patch i) (G.patch j)
      (G.measurableSet_piece j) (F.measurableSet_piece i))

/-- The image of a fresh piece of `G` misses every image of `F`: a `G`-parameter
whose image `F` sees lies, by `inter_preimage_image_toManifold`, in the
corresponding overlap, which is exactly what `freshParameters` removes. -/
theorem disjoint_image_freshParameters {avoidF avoidG : Set M}
    (F : RegularPieceFamily V avoidF) (G : RegularPieceFamily V avoidG)
    (i : Fin F.size) (j : Fin G.size) :
    Disjoint ((F.patch i).toManifold '' F.piece i)
      ((G.patch j).toManifold '' freshParameters F G j) := by
  rw [Set.disjoint_right]
  rintro _ ⟨w, hw, rfl⟩ hmem
  refine hw.2 (Set.mem_iUnion.2 ⟨i, ?_⟩)
  rw [← inter_preimage_image_toManifold (F.patch i) (G.patch j)
    (G.piece_subset j) (F.piece_subset i)]
  exact ⟨hw.1, hmem⟩

/-- **The union of two regular-piece families avoiding the same set.**  `F`'s
pieces, together with the parts of `G`'s pieces that `F` does not already see. -/
def unionFamily {avoid : Set M} (F G : RegularPieceFamily V avoid) :
    RegularPieceFamily V avoid where
  size := F.size + G.size
  patch := Fin.addCases F.patch G.patch
  piece := Fin.addCases F.piece (freshParameters F G)
  measurableSet_piece := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa using F.measurableSet_piece i
    · simpa using measurableSet_freshParameters F G j
  piece_subset := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa using F.piece_subset i
    · simpa using (freshParameters_subset F G j).trans (G.piece_subset j)
  image_subset_regularLocus := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa using F.image_subset_regularLocus i
    · simpa using
        (Set.image_mono (freshParameters_subset F G j)).trans (G.image_subset_regularLocus j)
  image_disjoint_avoid := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · simpa using F.image_disjoint_avoid i
    · simpa using (G.image_disjoint_avoid j).mono_left
        (Set.image_mono (freshParameters_subset F G j))
  pairwise_disjoint_image := by
    have key : ∀ (k k' : Fin (F.size + G.size)), k ≠ k' →
        Disjoint
          ((Fin.addCases F.patch G.patch k : RegularPatch V).toManifold ''
            Fin.addCases F.piece (freshParameters F G) k)
          ((Fin.addCases F.patch G.patch k' : RegularPatch V).toManifold ''
            Fin.addCases F.piece (freshParameters F G) k') := by
      refine Fin.addCases (fun i => Fin.addCases (fun i' => ?_) (fun j' => ?_))
        (fun j => Fin.addCases (fun i' => ?_) (fun j' => ?_))
      · intro hne
        simp only [Fin.addCases_left]
        exact F.pairwise_disjoint_image (fun h => hne (by rw [h]))
      · intro _
        simpa using disjoint_image_freshParameters F G i j'
      · intro _
        simpa using (disjoint_image_freshParameters F G i' j).symm
      · intro hne
        simp only [Fin.addCases_right]
        exact ((G.pairwise_disjoint_image (fun h => hne (by rw [h]))).mono
          (Set.image_mono (freshParameters_subset F G j))
          (Set.image_mono (freshParameters_subset F G j')))
    exact fun k k' hne => key k k' hne

@[simp] theorem unionFamily_patch_castAdd {avoid : Set M} (F G : RegularPieceFamily V avoid)
    (i : Fin F.size) :
    (unionFamily F G).patch (Fin.castAdd G.size i) = F.patch i := by
  simp [unionFamily]

@[simp] theorem unionFamily_piece_castAdd {avoid : Set M} (F G : RegularPieceFamily V avoid)
    (i : Fin F.size) :
    (unionFamily F G).piece (Fin.castAdd G.size i) = F.piece i := by
  simp [unionFamily]

@[simp] theorem unionFamily_patch_natAdd {avoid : Set M} (F G : RegularPieceFamily V avoid)
    (j : Fin G.size) :
    (unionFamily F G).patch (Fin.natAdd F.size j) = G.patch j := by
  simp [unionFamily]

@[simp] theorem unionFamily_piece_natAdd {avoid : Set M} (F G : RegularPieceFamily V avoid)
    (j : Fin G.size) :
    (unionFamily F G).piece (Fin.natAdd F.size j) = freshParameters F G j := by
  simp [unionFamily]

/-- Every image of `F` is an image of `unionFamily F G`. -/
theorem image_subset_iUnion_image_unionFamily {avoid : Set M}
    (F G : RegularPieceFamily V avoid) (i : Fin F.size) :
    (F.patch i).toManifold '' F.piece i ⊆
      ⋃ k, ((unionFamily F G).patch k).toManifold '' (unionFamily F G).piece k := by
  refine Set.subset_iUnion_of_subset (Fin.castAdd G.size i) ?_
  rw [unionFamily_patch_castAdd, unionFamily_piece_castAdd]

/-- Every image of `G` is covered by the images of `unionFamily F G`: a
`G`-parameter is either fresh, or its image is already seen by a piece of `F`. -/
theorem image_subset_iUnion_image_unionFamily' {avoid : Set M}
    (F G : RegularPieceFamily V avoid) (j : Fin G.size) :
    (G.patch j).toManifold '' G.piece j ⊆
      ⋃ k, ((unionFamily F G).patch k).toManifold '' (unionFamily F G).piece k := by
  rintro _ ⟨w, hw, rfl⟩
  by_cases hfresh : w ∈ ⋃ i : Fin F.size,
      overlapParameters (F.patch i) (G.patch j) (G.piece j) (F.piece i)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hfresh
    rw [← inter_preimage_image_toManifold (F.patch i) (G.patch j)
      (G.piece_subset j) (F.piece_subset i)] at hi
    exact image_subset_iUnion_image_unionFamily F G i hi.2
  · refine Set.mem_iUnion.2 ⟨Fin.natAdd F.size j, ?_⟩
    rw [unionFamily_patch_natAdd, unionFamily_piece_natAdd]
    exact ⟨w, ⟨hw, hfresh⟩, rfl⟩

theorem le_formPieceMass_unionFamily_left {avoid : Set M} (F G : RegularPieceFamily V avoid) :
    formPieceMass a F ≤ formPieceMass a (unionFamily F G) :=
  formPieceMass_mono_of_image_subset a (image_subset_iUnion_image_unionFamily F G)

theorem le_formPieceMass_unionFamily_right {avoid : Set M} (F G : RegularPieceFamily V avoid) :
    formPieceMass a G ≤ formPieceMass a (unionFamily F G) :=
  formPieceMass_mono_of_image_subset a (image_subset_iUnion_image_unionFamily' F G)

/-- **The supremum of the regular-piece masses of a smooth two-form is DIRECTED**,
over the families avoiding any fixed set. -/
theorem directed_formPieceMass (avoid : Set M) :
    Directed (· ≤ ·) (fun F : RegularPieceFamily V avoid => formPieceMass a F) :=
  fun F G => ⟨unionFamily F G, le_formPieceMass_unionFamily_left a F G,
    le_formPieceMass_unionFamily_right a F G⟩

end Families

end

end SGPT.Foundations.Analysis.Pending.PatchFormMass
