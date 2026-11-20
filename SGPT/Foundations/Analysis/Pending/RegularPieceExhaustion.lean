import SGPT.Foundations.Analysis.Pending.RegularPieceInnerRegular
import SGPT.Foundations.Analysis.Pending.RegularPieceCompactCover
import SGPT.Foundations.Analysis.Pending.PatchParameterNull
import SGPT.Foundations.Analysis.Pending.SubvarietyBackgroundMass

set_option autoImplicit false

/-!
# A countable exhaustion of `V_reg` by regular-piece families

`Pending.PatchFormMass` computes the regular-piece mass of a smooth two-form as a
supremum over FINITE families of disjoint measurable parameter pieces.  Several
statements about that supremum — Stokes against the integration current of `V`
above all — cannot be proved family by family: they only hold in the limit over
an exhaustion of the regular locus.  What was missing was the exhaustion itself.

This module supplies it, with no new hypothesis and no new interface:

`exists_exhaustion` produces, for every closed `avoid`, a MONOTONE sequence
`H : ℕ → RegularPieceFamily V avoid` whose covered regions increase and which
absorbs every compact part of `V_reg ∖ avoid`: every such compact set lies in the
region covered by some `H m`.

Combined with the inner regularity of `Pending.RegularPieceInnerRegular`, this
gives `iSup_formPieceMass_eq_iSup_exhaustion`: for EVERY smooth real two-form `a`
simultaneously, the regular-piece supremum of `a` is already reached along that
one sequence.  The sequence does not depend on `a`, which is what makes it usable
for statements comparing two different forms on the same variety.

The construction is the Lindelöf argument.  Around each point `x` of
`V_reg ∖ avoid` the flattening chart of a regular patch centred at `x`
parametrizes a whole parameter ball by regular points off `avoid`, and
`Pending.PatchParameterNull.exists_isOpen_carrier_inter_subset_image` turns that
ball into an AMBIENT open set `U x` whose trace on `V` is contained in the ball's
image.  The `U x` cover `V_reg ∖ avoid`; `M` is second countable, so countably
many of them suffice, and the finite unions of the corresponding parameter balls
are the families.  A compact subset of `V_reg ∖ avoid` meets only finitely many
of the `U x`, hence sits inside one member of the sequence.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The part of the ambient manifold that a regular-piece family actually
covers. -/
def coveredRegion {avoid : Set M} (F : RegularPieceFamily V avoid) : Set M :=
  ⋃ i, (F.patch i).toManifold '' F.piece i

theorem coveredRegion_subset_regularLocus {avoid : Set M} (F : RegularPieceFamily V avoid) :
    coveredRegion F ⊆ regularLocus (n := n) V.carrier V.dim :=
  iUnion_subset F.image_subset_regularLocus

theorem disjoint_coveredRegion_avoid {avoid : Set M} (F : RegularPieceFamily V avoid) :
    Disjoint (coveredRegion F) avoid :=
  disjoint_iUnion_left.2 F.image_disjoint_avoid

/-- **A parameter ball of regular points off `avoid`, together with an ambient
open set that traps it.**  This is the local step of the Lindelöf argument: at a
regular point `x` off the closed set `avoid` there is a regular patch centred at
`x`, a parameter ball `Ω` whose image consists of regular points off `avoid`, and
an ambient open `U ∋ x` with `V ∩ U ⊆ P(Ω)`. -/
theorem exists_localPatchData {avoid : Set M} (havoid : IsClosed avoid) {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) (hxa : x ∉ avoid) :
    ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (U : Set M),
      IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧
        P.toManifold '' Ω ⊆ regularLocus (n := n) V.carrier V.dim ∧
        Disjoint (P.toManifold '' Ω) avoid ∧
        IsOpen U ∧ x ∈ U ∧ V.carrier ∩ U ⊆ P.toManifold '' Ω := by
  classical
  set P : RegularPatch V := SubvarietyStokesMassInterfaces.patchOfMemRegularLocus hx with hP
  have hcentre : P.center = x := rfl
  have hzero : P.toManifold 0 = x := by
    rw [RegularPatch.toManifold_zero, hcentre]
  obtain ⟨r₀, hr₀, hball₀⟩ := RegularPatch.regularAtDim_toManifold P
  -- continuity at the centre keeps a smaller ball off the closed set `avoid`
  have hpre : P.toManifold ⁻¹' avoidᶜ ∈ 𝓝 (0 : ComplexModel V.dim) :=
    RegularPatch.continuousAt_toManifold_zero P (by rw [hzero]; exact havoid.isOpen_compl.mem_nhds hxa)
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨P, Metric.ball (0 : ComplexModel V.dim) (min r₀ r₁), ?_⟩
  set Ω : Set (ComplexModel V.dim) := Metric.ball (0 : ComplexModel V.dim) (min r₀ r₁) with hΩ
  have hrpos : 0 < min r₀ r₁ := lt_min hr₀ hr₁
  have hΩopen : IsOpen Ω := Metric.isOpen_ball
  have hΩsub : Ω ⊆ P.parameterDomain := fun w hw =>
    (hball₀ w (Metric.ball_subset_ball (min_le_left _ _) hw)).1
  have hΩreg : P.toManifold '' Ω ⊆ regularLocus (n := n) V.carrier V.dim := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hball₀ w (Metric.ball_subset_ball (min_le_left _ _) hw)).2
  have hΩavoid : Disjoint (P.toManifold '' Ω) avoid := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩
    exact hball₁ (Metric.ball_subset_ball (min_le_right _ _) hw)
  obtain ⟨U, hUopen, hsubU, hUtrace⟩ :=
    PatchParameterNull.exists_isOpen_carrier_inter_subset_image P hΩopen hΩsub
  exact ⟨U, hΩopen, hΩsub, hΩreg, hΩavoid, hUopen,
    hsubU ⟨0, Metric.mem_ball_self hrpos, hzero⟩, hUtrace⟩


/-- Regular patches always exist: `V` has a nonempty regular locus by definition. -/
instance nonempty_regularPatch : Nonempty (RegularPatch V) :=
  ⟨SubvarietyStokesMassInterfaces.patchOfMemRegularLocus V.regularLocus_nonempty.choose_spec⟩

/-- The running union of a sequence of regular-piece families. -/
def runningUnion {avoid : Set M} (G : ℕ → RegularPieceFamily V avoid) :
    ℕ → RegularPieceFamily V avoid
  | 0 => G 0
  | (N + 1) => PatchFormMass.unionFamily (runningUnion G N) (G (N + 1))

theorem coveredRegion_runningUnion_subset_succ {avoid : Set M}
    (G : ℕ → RegularPieceFamily V avoid) (N : ℕ) :
    coveredRegion (runningUnion G N) ⊆ coveredRegion (runningUnion G (N + 1)) :=
  Set.iUnion_subset fun i =>
    PatchFormMass.image_subset_iUnion_image_unionFamily (runningUnion G N) (G (N + 1)) i

theorem coveredRegion_subset_runningUnion {avoid : Set M}
    (G : ℕ → RegularPieceFamily V avoid) : ∀ N : ℕ,
    coveredRegion (G N) ⊆ coveredRegion (runningUnion G N)
  | 0 => subset_rfl
  | (N + 1) => Set.iUnion_subset fun j =>
      PatchFormMass.image_subset_iUnion_image_unionFamily' (runningUnion G N) (G (N + 1)) j

/-- **The exhaustion of `V_reg ∖ avoid` by regular-piece families.**  There is one
MONOTONE sequence of finite families, chosen once and for all — it depends on `V`
and on `avoid`, on no form and on no current — whose covered regions absorb every
compact subset of the regular locus lying off `avoid`.

This is the step that statements about the regular-piece supremum which are false
family by family have to go through; see
`iSup_formPieceMass_eq_iSup_exhaustion` below. -/
theorem exists_exhaustion {avoid : Set M} (havoid : IsClosed avoid) :
    ∃ H : ℕ → RegularPieceFamily V avoid,
      (∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1))) ∧
      ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        Disjoint K avoid → ∃ m, K ⊆ coveredRegion (H m) := by
  classical
  set S : Set M := regularLocus (n := n) V.carrier V.dim \ avoid with hSdef
  have hKS : ∀ K : Set M, K ⊆ regularLocus (n := n) V.carrier V.dim → Disjoint K avoid →
      K ⊆ S := fun K hKreg hKavoid x hx =>
    ⟨hKreg hx, fun hxa => (Set.disjoint_left.mp hKavoid hx) hxa⟩
  rcases eq_empty_or_nonempty S with hSe | hSne
  · refine ⟨fun _ => RegularPieceCompactCover.emptyFamily V avoid, fun _ => subset_rfl, ?_⟩
    intro K _ hKreg hKavoid
    exact ⟨0, ((hKS K hKreg hKavoid).trans hSe.subset).trans (empty_subset _)⟩
  · have hdata : ∀ x : S, ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (U : Set M),
        IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧
          P.toManifold '' Ω ⊆ regularLocus (n := n) V.carrier V.dim ∧
          Disjoint (P.toManifold '' Ω) avoid ∧
          IsOpen U ∧ (x : M) ∈ U ∧ V.carrier ∩ U ⊆ P.toManifold '' Ω :=
      fun x => exists_localPatchData havoid x.2.1 x.2.2
    choose P Ω U hΩopen hΩsub hΩreg hΩavoid hUopen hxU hUtrace using hdata
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUopen
    have hScov : S ⊆ ⋃ i ∈ T, U i := by
      intro x hx
      rw [hTU]
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hSne
      obtain ⟨i, hiT, -⟩ := mem_iUnion₂.1 (hScov hx)
      exact ⟨i, hiT⟩
    obtain ⟨p, hp⟩ := hTc.exists_eq_range hTne
    -- finitely many balls at a time form a family
    have hfam : ∀ N : ℕ, ∃ F : RegularPieceFamily V avoid,
        ∀ i : Fin (N + 1), (P (p i)).toManifold '' Ω (p i) ⊆ coveredRegion F :=
      fun N => RegularPieceCompactCover.exists_family_iUnion_image_superset'
        (fun i : Fin (N + 1) => P (p i)) (fun i : Fin (N + 1) => Ω (p i))
        (fun i => (hΩopen (p i)).measurableSet) (fun i => hΩsub (p i))
        (fun i => hΩavoid (p i))
    choose G hG using hfam
    refine ⟨runningUnion G, coveredRegion_runningUnion_subset_succ G, ?_⟩
    intro K hK hKreg hKavoid
    -- `K` is compact and covered by the open sets `U (p m)`, so finitely many suffice
    have hKcov : K ⊆ ⋃ m : ℕ, U (p m) := by
      intro x hx
      obtain ⟨i, hiT, hiU⟩ := mem_iUnion₂.1 (hScov (hKS K hKreg hKavoid hx))
      rw [hp] at hiT
      obtain ⟨m, rfl⟩ := hiT
      exact mem_iUnion.2 ⟨m, hiU⟩
    obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun m : ℕ => U (p m))
      (fun m => hUopen (p m)) hKcov
    obtain ⟨N, hN⟩ := I.exists_le
    refine ⟨N, ?_⟩
    refine subset_trans ?_ (coveredRegion_subset_runningUnion G N)
    intro x hx
    obtain ⟨m, hmI, hmU⟩ := mem_iUnion₂.1 (hI hx)
    have hmN : m < N + 1 := Nat.lt_succ_of_le (hN m hmI)
    refine hG N ⟨m, hmN⟩ ?_
    exact hUtrace _ ⟨(FirstPass.regularLocus_subset _ _) (hKS K hKreg hKavoid hx).1, hmU⟩

/-- **The regular-piece supremum of ANY smooth two-form is reached along the
exhaustion.**  The sequence is fixed before the form is chosen, so the same
sequence computes the suprema of two different forms — which is exactly what a
comparison of `(beta + dd^c v)^k` with `beta^k` over `V_reg` needs, since no
single finite family computes either.

The proof is inner regularity: below the mass of any family there is a COMPACT
subset of `V_reg ∖ avoid` (`RegularPieceInnerRegular.exists_isCompact_carrying_mass`)
every cover of which already has that much mass, and the exhaustion absorbs that
compact set. -/
theorem iSup_formPieceMass_eq_iSup_of_exhaustion {avoid : Set M} (havoid : IsClosed avoid)
    {H : ℕ → RegularPieceFamily V avoid}
    (hexh : ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
      Disjoint K avoid → ∃ m, K ⊆ coveredRegion (H m))
    (a : SmoothRealForm n M 2) :
    (⨆ m : ℕ, PatchFormMass.formPieceMass a (H m)) =
      ⨆ F : RegularPieceFamily V avoid, PatchFormMass.formPieceMass a F := by
  refine le_antisymm (iSup_le fun m => le_iSup _ (H m)) (iSup_le fun F => ?_)
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨K, hKcpt, hKreg, hKavoid, -, hKmass⟩ :=
    RegularPieceInnerRegular.exists_isCompact_carrying_mass havoid a F hc
  obtain ⟨m, hm⟩ := hexh K hKcpt hKreg hKavoid
  exact lt_of_lt_of_le (hKmass (H m) hm)
    (le_iSup (fun j : ℕ => PatchFormMass.formPieceMass a (H j)) m)

/-- **The exhaustion, packaged with the two facts its consumers use.**  One
sequence of finite families, monotone, computing the regular-piece supremum of
every smooth real two-form at once. -/
theorem exists_exhaustion_iSup_formPieceMass {avoid : Set M} (havoid : IsClosed avoid) :
    ∃ H : ℕ → RegularPieceFamily V avoid,
      (∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1))) ∧
      ∀ a : SmoothRealForm n M 2,
        (⨆ m : ℕ, PatchFormMass.formPieceMass a (H m)) =
          ⨆ F : RegularPieceFamily V avoid, PatchFormMass.formPieceMass a F := by
  obtain ⟨H, hmono, hexh⟩ := exists_exhaustion (V := V) havoid
  exact ⟨H, hmono, fun a => iSup_formPieceMass_eq_iSup_of_exhaustion havoid hexh a⟩

/-- Along a sequence of families whose covered regions increase, the regular-piece
mass of any smooth two-form is monotone. -/
theorem monotone_formPieceMass {avoid : Set M} {H : ℕ → RegularPieceFamily V avoid}
    (hmono : ∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1)))
    (a : SmoothRealForm n M 2) :
    Monotone (fun m : ℕ => PatchFormMass.formPieceMass a (H m)) :=
  monotone_nat_of_le_succ fun m =>
    PatchFormMass.formPieceMass_mono_of_image_subset a fun i =>
      subset_trans
        (Set.subset_iUnion (fun j => ((H m).patch j).toManifold '' (H m).piece j) i)
        (hmono m)

/-- **The regular-piece supremum is a LIMIT along the exhaustion.**  Monotone
convergence in `ℝ≥0∞`: the masses of the exhausting families increase to the
supremum over all families.  Two smooth two-forms can therefore be compared by
comparing two convergent sequences indexed by the same exhaustion. -/
theorem tendsto_formPieceMass_of_exhaustion {avoid : Set M} (havoid : IsClosed avoid)
    {H : ℕ → RegularPieceFamily V avoid}
    (hmono : ∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
      Disjoint K avoid → ∃ m, K ⊆ coveredRegion (H m))
    (a : SmoothRealForm n M 2) :
    Tendsto (fun m : ℕ => PatchFormMass.formPieceMass a (H m)) atTop
      (𝓝 (⨆ F : RegularPieceFamily V avoid, PatchFormMass.formPieceMass a F)) := by
  rw [← iSup_formPieceMass_eq_iSup_of_exhaustion havoid hexh a]
  exact tendsto_atTop_iSup (monotone_formPieceMass hmono a)

end

end SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion
