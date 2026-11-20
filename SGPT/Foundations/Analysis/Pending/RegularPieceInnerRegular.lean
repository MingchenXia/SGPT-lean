import SGPT.Foundations.Analysis.Pending.RegularPieceCompactCover
import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity

set_option autoImplicit false

/-!
# Inner regularity of the parameter integrals: compact pieces carry all the mass

`Pending.RegularPieceCompactCover` supplies the COVERING half of the exhaustion
of `V_reg` that `Pending.SubvarietyStokesMassInterfaces` needs: every compact
part of `V_reg` is reached by one finite regular-piece family.  Its docstring
records what was missing: compact subsets of `V_reg` carrying all of the mass.

This module supplies exactly that, for an arbitrary smooth real two-form and an
arbitrary avoided set:

* `exists_isCompact_subset_lt_setLIntegral` — the abstract measure-theoretic
  statement.  On a proper metric space with an inner-regular locally finite
  measure, `∫⁻_S f` is the supremum of `∫⁻_K f` over compact `K ⊆ S`, for ANY
  `S`-a.e.-measurable `f ≥ 0`.  No continuity and no finiteness is assumed:
  truncate `f` at height `m` and cut with the ball of radius `m`, then use inner
  regularity of the measure on the resulting finite piece.
* `exists_compactPieces_lt_formPieceMass` — the same statement for a whole
  regular-piece family: every value below `formPieceMass a F` is already
  attained by a family with the SAME patches whose pieces are compact subsets of
  those of `F`.  The finitely many pieces are shrunk simultaneously, which is
  what `ENNReal.finsetSum_iSup` provides: the candidate choices are directed
  because a union of compact subsets of a piece is again one.
* `isCompact_iUnion_image` and `exists_isCompact_carrying_mass` — the images of
  such a family form a COMPACT subset of `V_reg` disjoint from the avoided set,
  and every family covering that compact set already computes more than the
  prescribed value.

Together with `RegularPieceCompactCover.exists_family_covering_of_isCompact`
this is the exhaustion: below `⨆ F, formPieceMass a F` there is a compact
`K ⊆ V_reg` away from the avoided set such that a family covering `K` exists and
EVERY family covering `K` is already above the prescribed value.

What is still not proved, and what the Stokes obligation
`SubvarietyStokesMassInterfaces.iSup_formPieceMass_currentForm_eq` still needs,
is Stokes itself: that the two forms `β + ddᶜv` and `β` have the same mass in
the limit along such an exhaustion.  Nothing here compares two forms.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RegularPieceInnerRegular

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood
open PatchFormMass

noncomputable section

/-! ## The abstract statement -/

section Abstract

variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [ProperSpace E]
  [OpensMeasurableSpace E] [T2Space E] [Nonempty E]
  {mu : Measure E} [IsFiniteMeasureOnCompacts mu] [mu.InnerRegularCompactLTTop]

/-- Truncation at the natural numbers recovers any extended nonnegative real. -/
private theorem iSup_min_natCast (x : ℝ≥0∞) : (⨆ m : ℕ, min x (m : ℝ≥0∞)) = x := by
  refine le_antisymm (iSup_le fun m => min_le_left _ _) ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp only [min_top_left]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le m (by simp [min_eq_left hm.le])

/-- **Inner regularity of a parameter integral.**  Every value strictly below
`∫⁻_S f` is already attained on a COMPACT subset of `S`.

Neither continuity nor integrability of `f` is used: truncating `f` at height
`m` and intersecting `S` with the closed ball of radius `m` produces an
increasing sequence of integrals converging to `∫⁻_S f`, each of them over a set
of finite measure with a bounded integrand, and there inner regularity of the
measure itself removes a set of small measure. -/
theorem exists_isCompact_subset_lt_setLIntegral
    {f : E → ℝ≥0∞} {S : Set E} (hS : MeasurableSet S)
    (hf : AEMeasurable f (mu.restrict S)) {c : ℝ≥0∞}
    (hc : c < ∫⁻ w in S, f w ∂mu) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ S ∧ c < ∫⁻ w in K, f w ∂mu := by
  classical
  set x0 : E := Classical.arbitrary E with hx0
  set B : ℕ → Set E := fun m => Metric.closedBall x0 m with hB
  have hBmeas : ∀ m, MeasurableSet (B m) := fun m => measurableSet_closedBall
  set g : ℕ → E → ℝ≥0∞ := fun m w => (B m).indicator (fun w => min (f w) (m : ℝ≥0∞)) w with hg
  have hgmeas : ∀ m, AEMeasurable (g m) (mu.restrict S) := fun m =>
    (hf.min aemeasurable_const).indicator (hBmeas m)
  have hmono : ∀ w, Monotone fun m => g m w := by
    intro w m m' hmm'
    by_cases hw : w ∈ B m
    · have hw' : w ∈ B m' := by
        refine Metric.closedBall_subset_closedBall ?_ hw
        exact_mod_cast Nat.cast_le.2 hmm'
      simp only [hg, Set.indicator_of_mem hw, Set.indicator_of_mem hw']
      exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.2 hmm')
    · simp only [hg, Set.indicator_of_notMem hw]
      exact bot_le
  have hsup : ∀ w, (⨆ m : ℕ, g m w) = f w := by
    intro w
    refine le_antisymm (iSup_le fun m => ?_) ?_
    · by_cases hw : w ∈ B m
      · simpa only [hg, Set.indicator_of_mem hw] using min_le_left (f w) ((m : ℝ≥0∞))
      · simp only [hg, Set.indicator_of_notMem hw]
        exact bot_le
    · obtain ⟨N, hN⟩ := exists_nat_ge (dist w x0)
      rw [← iSup_min_natCast (f w)]
      refine iSup_le fun k => ?_
      refine le_iSup_of_le (max k N) ?_
      have hwmem : w ∈ B (max k N) := by
        refine Metric.mem_closedBall.2 (hN.trans ?_)
        exact_mod_cast Nat.cast_le.2 (le_max_right k N)
      simp only [hg, Set.indicator_of_mem hwmem]
      exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.2 (le_max_left k N))
  have hlim : (⨆ m : ℕ, ∫⁻ w in S, g m w ∂mu) = ∫⁻ w in S, f w ∂mu := by
    rw [← lintegral_iSup' hgmeas (Filter.Eventually.of_forall hmono)]
    exact lintegral_congr fun w => hsup w
  rw [← hlim] at hc
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 hc
  -- rewrite the truncated integral as an integral over a set of finite measure
  set A : Set E := B m ∩ S with hA
  have hAmeas : MeasurableSet A := (hBmeas m).inter hS
  have hAeq : (∫⁻ w in S, g m w ∂mu) = ∫⁻ w in A, min (f w) (m : ℝ≥0∞) ∂mu := by
    rw [hg]
    rw [lintegral_indicator (hBmeas m), Measure.restrict_restrict (hBmeas m)]
  rw [hAeq] at hm
  have hAtop : mu A ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt
      (isCompact_closedBall x0 (m : ℝ)).measure_lt_top).ne
  have httop : (∫⁻ w in A, min (f w) (m : ℝ≥0∞) ∂mu) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun w => min_le_right _ _)
    rw [setLIntegral_const]
    exact (ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.2 hAtop)).ne
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hm
  set delta : ℝ≥0∞ := (r : ℝ≥0∞) / ((m : ℝ≥0∞) + 1) with hdelta
  have hdelta0 : delta ≠ 0 := by
    simp only [hdelta, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨by exact_mod_cast hr0.ne', by simp⟩
  obtain ⟨K, hKA, hKc, hKmeas⟩ := hAmeas.exists_isCompact_sdiff_lt hAtop hdelta0
  refine ⟨K, hKc, hKA.trans Set.inter_subset_right, ?_⟩
  have hdiff : (∫⁻ w in A \ K, min (f w) (m : ℝ≥0∞) ∂mu) ≤ (r : ℝ≥0∞) := by
    refine (lintegral_mono fun w => min_le_right _ _).trans ?_
    rw [setLIntegral_const]
    calc (m : ℝ≥0∞) * mu (A \ K) ≤ ((m : ℝ≥0∞) + 1) * delta :=
          mul_le_mul' (le_self_add) hKmeas.le
      _ = (r : ℝ≥0∞) := by
          rw [hdelta, ENNReal.mul_div_cancel (by simp) (by simp)]
  have hsplit : (∫⁻ w in A, min (f w) (m : ℝ≥0∞) ∂mu) ≤
      (∫⁻ w in K, f w ∂mu) + (r : ℝ≥0∞) := by
    have hcover : A ⊆ K ∪ (A \ K) := by
      intro w hw
      by_cases hwK : w ∈ K
      · exact Or.inl hwK
      · exact Or.inr ⟨hw, hwK⟩
    refine (lintegral_mono_set hcover).trans ?_
    refine (lintegral_union_le _ _ _).trans ?_
    exact add_le_add (lintegral_mono fun w => min_le_left _ _) hdiff
  have hfinal : c + (r : ℝ≥0∞) < (∫⁻ w in K, f w ∂mu) + (r : ℝ≥0∞) := hr.trans_le hsplit
  exact (ENNReal.add_lt_add_iff_right (by simp)).1 hfinal

end Abstract

/-! ## Compact pieces carry all the mass of a regular-piece family -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The density of a smooth two-form is a.e.-measurable on any measurable piece
of a parameter domain: it is continuous there. -/
theorem aemeasurable_patchFormDensity (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain) :
    AEMeasurable (fun w => ENNReal.ofReal (patchFormDensity a P w))
      (volume.restrict S) :=
  (ENNReal.measurable_ofReal.comp_aemeasurable
    (((RegularPatchTransition.continuousOn_actualTopPowerDensity_patchCoordinateForm
      a P).mono hsub).aemeasurable hS))

/-- **Inner regularity for one piece.**  Every value below the parameter
integral of the density over a piece is attained on a compact subpiece. -/
theorem exists_isCompact_subset_lt_pieceIntegral (a : SmoothRealForm n M 2)
    (P : RegularPatch V) {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S)
    (hsub : S ⊆ P.parameterDomain) {c : ℝ≥0∞}
    (hc : c < ∫⁻ w in S, ENNReal.ofReal (patchFormDensity a P w)) :
    ∃ K : Set (ComplexModel V.dim), IsCompact K ∧ K ⊆ S ∧
      c < ∫⁻ w in K, ENNReal.ofReal (patchFormDensity a P w) :=
  exists_isCompact_subset_lt_setLIntegral hS (aemeasurable_patchFormDensity a P hS hsub) hc

/-! ## Shrinking a whole family to compact pieces -/

/-- The candidate compact subpiece attached to a set `T`: `T` itself when it is a
compact subset of the `i`-th piece, and `∅` otherwise.  Sanitizing this way lets
all the pieces of a family be shrunk SIMULTANEOUSLY, indexed by one choice
function, which is what `ENNReal.finsetSum_iSup` consumes. -/
def trim {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    (T : Set (ComplexModel V.dim)) : Set (ComplexModel V.dim) :=
  ⋃ _ : IsCompact T ∧ T ⊆ F.piece i, T

theorem trim_subset_self {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    (T : Set (ComplexModel V.dim)) : trim F i T ⊆ T :=
  Set.iUnion_subset fun _ => subset_rfl

theorem trim_eq_self {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    {T : Set (ComplexModel V.dim)} (hT : IsCompact T) (hsub : T ⊆ F.piece i) :
    trim F i T = T :=
  Set.Subset.antisymm (trim_subset_self F i T)
    (fun _w hw => Set.mem_iUnion.2 ⟨⟨hT, hsub⟩, hw⟩)

theorem trim_eq_empty {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    {T : Set (ComplexModel V.dim)} (h : ¬ (IsCompact T ∧ T ⊆ F.piece i)) :
    trim F i T = ∅ :=
  Set.eq_empty_of_subset_empty (Set.iUnion_subset fun hh => absurd hh h)

theorem isCompact_trim {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    (T : Set (ComplexModel V.dim)) : IsCompact (trim F i T) := by
  by_cases h : IsCompact T ∧ T ⊆ F.piece i
  · rw [trim_eq_self F i h.1 h.2]; exact h.1
  · rw [trim_eq_empty F i h]; exact isCompact_empty

theorem trim_subset {avoid : Set M} (F : RegularPieceFamily V avoid) (i : Fin F.size)
    (T : Set (ComplexModel V.dim)) : trim F i T ⊆ F.piece i := by
  by_cases h : IsCompact T ∧ T ⊆ F.piece i
  · rw [trim_eq_self F i h.1 h.2]; exact h.2
  · rw [trim_eq_empty F i h]; exact Set.empty_subset _

/-- The family with the same patches as `F` whose `i`-th piece is the compact
subpiece selected by `kappa i`. -/
def trimFamily {avoid : Set M} (F : RegularPieceFamily V avoid)
    (kappa : Fin F.size → Set (ComplexModel V.dim)) : RegularPieceFamily V avoid where
  size := F.size
  patch := F.patch
  piece := fun i => trim F i (kappa i)
  measurableSet_piece := fun i => (isCompact_trim F i _).isClosed.measurableSet
  piece_subset := fun i => (trim_subset F i _).trans (F.piece_subset i)
  image_subset_regularLocus := fun i =>
    (Set.image_mono (trim_subset F i _)).trans (F.image_subset_regularLocus i)
  image_disjoint_avoid := fun i =>
    (F.image_disjoint_avoid i).mono_left (Set.image_mono (trim_subset F i _))
  pairwise_disjoint_image := fun i j hij =>
    (F.pairwise_disjoint_image hij).mono (Set.image_mono (trim_subset F i _))
      (Set.image_mono (trim_subset F j _))

@[simp] theorem trimFamily_piece {avoid : Set M} (F : RegularPieceFamily V avoid)
    (kappa : Fin F.size → Set (ComplexModel V.dim)) (i : Fin (trimFamily F kappa).size) :
    (trimFamily F kappa).piece i = trim F i (kappa i) := rfl

theorem isCompact_piece_trimFamily {avoid : Set M} (F : RegularPieceFamily V avoid)
    (kappa : Fin F.size → Set (ComplexModel V.dim)) (i : Fin (trimFamily F kappa).size) :
    IsCompact ((trimFamily F kappa).piece i) := isCompact_trim F i (kappa i)

/-- The parameter integral over a piece is the supremum of the integrals over the
compact subpieces selected by a choice function. -/
theorem iSup_lintegral_trim (a : SmoothRealForm n M 2) {avoid : Set M}
    (F : RegularPieceFamily V avoid) (i : Fin F.size) :
    (⨆ kappa : Fin F.size → Set (ComplexModel V.dim),
        ∫⁻ w in trim F i (kappa i), ENNReal.ofReal (patchFormDensity a (F.patch i) w)) =
      ∫⁻ w in F.piece i, ENNReal.ofReal (patchFormDensity a (F.patch i) w) := by
  refine le_antisymm (iSup_le fun kappa => lintegral_mono_set (trim_subset F i _)) ?_
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨K, hKc, hKsub, hK⟩ := exists_isCompact_subset_lt_pieceIntegral a (F.patch i)
    (F.measurableSet_piece i) (F.piece_subset i) hc
  refine lt_of_lt_of_le hK (le_iSup_of_le (fun _ => K) ?_)
  rw [trim_eq_self F i hKc hKsub]

/-- **Compact pieces carry all the mass.**  The regular-piece mass of a family is
the supremum of the masses of the families obtained by shrinking every piece to a
compact subpiece.  The choices are directed because a union of two compact
subsets of a piece is again one, so the finitely many suprema can be pulled out
of the sum at once. -/
theorem formPieceMass_eq_iSup_trimFamily (a : SmoothRealForm n M 2) {avoid : Set M}
    (F : RegularPieceFamily V avoid) :
    formPieceMass a F =
      ⨆ kappa : Fin F.size → Set (ComplexModel V.dim),
        formPieceMass a (trimFamily F kappa) := by
  classical
  have hdir : ∀ kappa kappa' : Fin F.size → Set (ComplexModel V.dim),
      ∃ kappa'' : Fin F.size → Set (ComplexModel V.dim), ∀ i : Fin F.size,
        (∫⁻ w in trim F i (kappa i), ENNReal.ofReal (patchFormDensity a (F.patch i) w)) ≤
            ∫⁻ w in trim F i (kappa'' i),
              ENNReal.ofReal (patchFormDensity a (F.patch i) w) ∧
          (∫⁻ w in trim F i (kappa' i),
              ENNReal.ofReal (patchFormDensity a (F.patch i) w)) ≤
            ∫⁻ w in trim F i (kappa'' i),
              ENNReal.ofReal (patchFormDensity a (F.patch i) w) := by
    intro kappa kappa'
    refine ⟨fun i => trim F i (kappa i) ∪ trim F i (kappa' i), fun i => ?_⟩
    have hcomp : IsCompact (trim F i (kappa i) ∪ trim F i (kappa' i)) :=
      (isCompact_trim F i _).union (isCompact_trim F i _)
    have hsub : trim F i (kappa i) ∪ trim F i (kappa' i) ⊆ F.piece i :=
      Set.union_subset (trim_subset F i _) (trim_subset F i _)
    rw [trim_eq_self F i hcomp hsub]
    exact ⟨lintegral_mono_set Set.subset_union_left,
      lintegral_mono_set Set.subset_union_right⟩
  calc formPieceMass a F
      = ∑ i : Fin F.size, ⨆ kappa : Fin F.size → Set (ComplexModel V.dim),
          ∫⁻ w in trim F i (kappa i),
            ENNReal.ofReal (patchFormDensity a (F.patch i) w) :=
        Finset.sum_congr rfl fun i _ => (iSup_lintegral_trim a F i).symm
    _ = ⨆ kappa : Fin F.size → Set (ComplexModel V.dim),
          ∑ i : Fin F.size, ∫⁻ w in trim F i (kappa i),
            ENNReal.ofReal (patchFormDensity a (F.patch i) w) :=
        ENNReal.finsetSum_iSup hdir
    _ = ⨆ kappa : Fin F.size → Set (ComplexModel V.dim),
          formPieceMass a (trimFamily F kappa) := rfl

/-- Every value below the mass of a family is already attained by a family with
the same patches and COMPACT pieces inside those of `F`. -/
theorem exists_compactPieces_lt_formPieceMass (a : SmoothRealForm n M 2) {avoid : Set M}
    (F : RegularPieceFamily V avoid) {c : ℝ≥0∞} (hc : c < formPieceMass a F) :
    ∃ G : RegularPieceFamily V avoid, (∀ i, IsCompact (G.piece i)) ∧
      (⋃ i, (G.patch i).toManifold '' G.piece i) ⊆
        ⋃ i, (F.patch i).toManifold '' F.piece i ∧
      c < formPieceMass a G := by
  rw [formPieceMass_eq_iSup_trimFamily a F] at hc
  obtain ⟨kappa, hkappa⟩ := lt_iSup_iff.1 hc
  refine ⟨trimFamily F kappa, isCompact_piece_trimFamily F kappa, ?_, hkappa⟩
  exact Set.iUnion_mono fun i => Set.image_mono (trim_subset F i (kappa i))

/-- The images of a family with compact pieces form a compact subset of `M`. -/
theorem isCompact_iUnion_image {avoid : Set M} (G : RegularPieceFamily V avoid)
    (hG : ∀ i, IsCompact (G.piece i)) :
    IsCompact (⋃ i, (G.patch i).toManifold '' G.piece i) :=
  isCompact_iUnion fun i => (hG i).image_of_continuousOn
    ((RegularPatch.continuousOn_toManifold (G.patch i)).mono (G.piece_subset i))

/-- **The exhaustion.**  Below the mass of any regular-piece family there is a
COMPACT subset `K` of `V_reg`, away from the avoided set, which already carries
that much mass: a family covering `K` exists, and every family covering `K`
computes more than the prescribed value.

This is the statement `Pending.RegularPieceCompactCover` names as missing:
together with `exists_family_covering_of_isCompact` (the covering half, proved
there) it exhausts `V_reg` in measure by finite regular pieces. -/
theorem exists_isCompact_carrying_mass {avoid : Set M} (havoid : IsClosed avoid)
    (a : SmoothRealForm n M 2) (F : RegularPieceFamily V avoid) {c : ℝ≥0∞}
    (hc : c < formPieceMass a F) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ regularLocus (n := n) V.carrier V.dim ∧
      Disjoint K avoid ∧
      (∃ G : RegularPieceFamily V avoid,
        K ⊆ ⋃ j, (G.patch j).toManifold '' G.piece j) ∧
      ∀ G : RegularPieceFamily V avoid,
        K ⊆ (⋃ j, (G.patch j).toManifold '' G.piece j) → c < formPieceMass a G := by
  obtain ⟨G, hGcpt, _, hGmass⟩ := exists_compactPieces_lt_formPieceMass a F hc
  refine ⟨⋃ i, (G.patch i).toManifold '' G.piece i, isCompact_iUnion_image G hGcpt,
    Set.iUnion_subset G.image_subset_regularLocus,
    Set.disjoint_iUnion_left.2 G.image_disjoint_avoid, ?_, ?_⟩
  · exact RegularPieceCompactCover.exists_family_covering_of_isCompact havoid
      (isCompact_iUnion_image G hGcpt) (Set.iUnion_subset G.image_subset_regularLocus)
      (Set.disjoint_iUnion_left.2 G.image_disjoint_avoid)
  · intro G' hG'
    refine hGmass.trans_le (formPieceMass_mono_of_image_subset a ?_)
    exact fun i => (Set.subset_iUnion _ i).trans hG'

/-- The supremum defining the mass is unchanged if only families with compact
pieces are allowed. -/
theorem iSup_formPieceMass_eq_iSup_compactPieces (a : SmoothRealForm n M 2)
    (avoid : Set M) :
    (⨆ F : RegularPieceFamily V avoid, formPieceMass a F) =
      ⨆ G : {G : RegularPieceFamily V avoid // ∀ i, IsCompact (G.piece i)},
        formPieceMass a (G : RegularPieceFamily V avoid) := by
  refine le_antisymm (iSup_le fun F => ?_)
    (iSup_le fun G => le_iSup (fun F : RegularPieceFamily V avoid => formPieceMass a F)
      (G : RegularPieceFamily V avoid))
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨G, hGcpt, _, hGmass⟩ := exists_compactPieces_lt_formPieceMass a F hc
  exact hGmass.trans_le (le_iSup (fun G : {G : RegularPieceFamily V avoid //
    ∀ i, IsCompact (G.piece i)} => formPieceMass a (G : RegularPieceFamily V avoid))
    ⟨G, hGcpt⟩)

end

end SGPT.Foundations.Analysis.Pending.RegularPieceInnerRegular
