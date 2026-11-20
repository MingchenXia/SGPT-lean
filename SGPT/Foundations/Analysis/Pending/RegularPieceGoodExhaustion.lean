import SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion
import SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential

set_option autoImplicit false

/-!
# An exhaustion of `V_reg` whose pieces are small enough to carry a local potential

`Pending.RegularPieceExhaustion.exists_exhaustion` produces one monotone sequence of
finite regular-piece families absorbing every compact part of `V_reg`, and
`iSup_formPieceMass_eq_iSup_of_exhaustion` shows it computes the regular-piece supremum
of every smooth real two-form.  Its pieces are, however, arbitrary measurable subsets of
the whole parameter domain of their patch, whereas the local description of the Stokes
defect produced by `Pending.PatchDensityLocalPotential` lives on a neighbourhood of a
SINGLE parameter: the local `dd`-bar potential of the background is only defined there.

This module removes that mismatch, once and for all forms and for all local data.  The
input is a *local piece property* — a predicate on pairs (patch, parameter set) that is

* downward closed in the set, and
* satisfied by some open neighbourhood of every parameter of every patch —

and the output is an exhaustion with the same two properties as before, all of whose
pieces satisfy it.  Nothing is assumed about the property beyond those two clauses, so
the same theorem serves the background potential, the potential of a second form, a
bound on a chart expression, or any local smallness condition a later round needs.

The construction is the Lindelöf argument of `RegularPieceExhaustion`, with one extra
shrinking step: the parameter ball around a regular point is intersected with the good
neighbourhood of the parameter over that point, and the ambient trap is rebuilt for the
smaller ball by `Pending.PatchParameterNull`.  Goodness then survives the two family
constructors used to assemble the sequence (`singletonFamily` keeps the piece,
`unionFamily` keeps `F`'s pieces and shrinks `G`'s), hence survives the running union.

`exists_exhaustion_localTelescopePotential` is the instance the Stokes obligation needs:
every piece of every family lies in one open set carrying a smooth local potential
`φ` of `β` in the parameters, on which `v ∘ P` is smooth as well and on which the
difference of the two parameter densities is the sum of the `dim V` mixed
Monge--Ampère densities of the telescope families of `φ` and `v ∘ P`.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **A local piece property.**  A predicate on (patch, parameter set) pairs that is
inherited by subsets and holds on some open neighbourhood of every parameter of every
patch.  These are exactly the two clauses the refinement of the exhaustion needs. -/
structure LocalPieceProperty (V : ClosedIrreducibleAnalyticSubvariety n M) where
  /-- The predicate itself. -/
  good : RegularPatch V → Set (ComplexModel V.dim) → Prop
  /-- Downward closed in the parameter set. -/
  mono : ∀ (P : RegularPatch V) {S S' : Set (ComplexModel V.dim)},
    good P S → S' ⊆ S → good P S'
  /-- Satisfied near every parameter. -/
  nhds : ∀ (P : RegularPatch V) {w : ComplexModel V.dim}, w ∈ P.parameterDomain →
    ∃ Ω : Set (ComplexModel V.dim),
      IsOpen Ω ∧ w ∈ Ω ∧ Ω ⊆ P.parameterDomain ∧ good P Ω

/-- Every piece of a family satisfies the property. -/
def IsGoodFamily (p : LocalPieceProperty V) {avoid : Set M}
    (F : RegularPieceFamily V avoid) : Prop :=
  ∀ i, p.good (F.patch i) (F.piece i)

theorem isGoodFamily_emptyFamily (p : LocalPieceProperty V) (avoid : Set M) :
    IsGoodFamily p (RegularPieceCompactCover.emptyFamily V avoid) := fun i => Fin.elim0 i

theorem isGoodFamily_singletonFamily (p : LocalPieceProperty V) {avoid : Set M}
    (P : RegularPatch V) (S : Set (ComplexModel V.dim)) (hS : MeasurableSet S)
    (hsub : S ⊆ P.parameterDomain) (havoid : Disjoint (P.toManifold '' S) avoid)
    (hgood : p.good P S) :
    IsGoodFamily p (RegularPieceCompactCover.singletonFamily P S hS hsub havoid) :=
  fun _ => hgood

theorem isGoodFamily_unionFamily (p : LocalPieceProperty V) {avoid : Set M}
    {F G : RegularPieceFamily V avoid} (hF : IsGoodFamily p F) (hG : IsGoodFamily p G) :
    IsGoodFamily p (PatchFormMass.unionFamily F G) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · rw [PatchFormMass.unionFamily_patch_castAdd, PatchFormMass.unionFamily_piece_castAdd]
    exact hF i
  · rw [PatchFormMass.unionFamily_patch_natAdd, PatchFormMass.unionFamily_piece_natAdd]
    exact p.mono (G.patch j) (hG j) (PatchFormMass.freshParameters_subset F G j)

theorem isGoodFamily_runningUnion (p : LocalPieceProperty V) {avoid : Set M}
    {G : ℕ → RegularPieceFamily V avoid} (hG : ∀ N, IsGoodFamily p (G N)) :
    ∀ N, IsGoodFamily p (runningUnion G N)
  | 0 => hG 0
  | (N + 1) => isGoodFamily_unionFamily p (isGoodFamily_runningUnion p hG N) (hG (N + 1))

/-- **Finitely many GOOD pieces are covered by one good family.**  The good analogue of
`RegularPieceCompactCover.exists_family_iUnion_image_superset`: the disjointification only
ever shrinks pieces and never changes their patch, so it preserves the property. -/
theorem exists_goodFamily_iUnion_image_superset (p : LocalPieceProperty V) {avoid : Set M} :
    ∀ (N : ℕ) (P : Fin N → RegularPatch V) (S : Fin N → Set (ComplexModel V.dim)),
      (∀ i, MeasurableSet (S i)) → (∀ i, S i ⊆ (P i).parameterDomain) →
      (∀ i, Disjoint ((P i).toManifold '' S i) avoid) → (∀ i, p.good (P i) (S i)) →
      ∃ F : RegularPieceFamily V avoid, IsGoodFamily p F ∧
        ∀ i, (P i).toManifold '' S i ⊆ coveredRegion F := by
  intro N
  induction N with
  | zero =>
      exact fun P S _ _ _ _ =>
        ⟨RegularPieceCompactCover.emptyFamily V avoid,
          isGoodFamily_emptyFamily p avoid, fun i => Fin.elim0 i⟩
  | succ N ih =>
      intro P S hmeas hsub hav hgood
      obtain ⟨F, hFgood, hF⟩ := ih (fun j => P j.castSucc) (fun j => S j.castSucc)
        (fun j => hmeas _) (fun j => hsub _) (fun j => hav _) (fun j => hgood _)
      set L : RegularPieceFamily V avoid :=
        RegularPieceCompactCover.singletonFamily (P (Fin.last N)) (S (Fin.last N))
          (hmeas _) (hsub _) (hav _) with hL
      refine ⟨PatchFormMass.unionFamily F L,
        isGoodFamily_unionFamily p hFgood
          (isGoodFamily_singletonFamily p _ _ _ _ _ (hgood (Fin.last N))), ?_⟩
      refine Fin.lastCases ?_ ?_
      · exact PatchFormMass.image_subset_iUnion_image_unionFamily' F L ⟨0, Nat.one_pos⟩
      · intro j
        exact (hF j).trans
          (RegularPieceCompactCover.iUnion_image_subset_unionFamily_left F L)

/-- The same statement for an arbitrary finite index type. -/
theorem exists_goodFamily_iUnion_image_superset' (p : LocalPieceProperty V) {avoid : Set M}
    {iota : Type*} [Fintype iota] (P : iota → RegularPatch V)
    (S : iota → Set (ComplexModel V.dim)) (hmeas : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ (P i).parameterDomain)
    (hav : ∀ i, Disjoint ((P i).toManifold '' S i) avoid)
    (hgood : ∀ i, p.good (P i) (S i)) :
    ∃ F : RegularPieceFamily V avoid, IsGoodFamily p F ∧
      ∀ i, (P i).toManifold '' S i ⊆ coveredRegion F := by
  obtain ⟨F, hFgood, hF⟩ :=
    exists_goodFamily_iUnion_image_superset p (avoid := avoid) (Fintype.card iota)
      (fun j => P ((Fintype.equivFin iota).symm j)) (fun j => S ((Fintype.equivFin iota).symm j))
      (fun j => hmeas _) (fun j => hsub _) (fun j => hav _) (fun j => hgood _)
  refine ⟨F, hFgood, fun i => ?_⟩
  simpa using hF (Fintype.equivFin iota i)

/-- **The local step, with the property.**  At a regular point off the closed set `avoid`
there is a regular patch, a parameter ball whose image consists of regular points off
`avoid` AND which satisfies the given local property, and an ambient open set trapping it.
The ball is the one of `RegularPieceExhaustion.exists_localPatchData` intersected with a
good neighbourhood of a parameter over the point; the ambient trap is rebuilt for the
smaller ball. -/
theorem exists_localPatchData_good (p : LocalPieceProperty V) {avoid : Set M}
    (havoid : IsClosed avoid) {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) (hxa : x ∉ avoid) :
    ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (U : Set M),
      IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧
        P.toManifold '' Ω ⊆ regularLocus (n := n) V.carrier V.dim ∧
        Disjoint (P.toManifold '' Ω) avoid ∧
        IsOpen U ∧ x ∈ U ∧ V.carrier ∩ U ⊆ P.toManifold '' Ω ∧ p.good P Ω := by
  obtain ⟨P, Ω, U, hΩopen, hΩsub, hΩreg, hΩavoid, hUopen, hxU, hUtrace⟩ :=
    exists_localPatchData (V := V) havoid hx hxa
  obtain ⟨w₀, hw₀Ω, hw₀⟩ := hUtrace ⟨FirstPass.regularLocus_subset _ _ hx, hxU⟩
  obtain ⟨Ωg, hΩgopen, hw₀g, hΩgsub, hgood⟩ := p.nhds P (hΩsub hw₀Ω)
  refine ⟨P, Ω ∩ Ωg, ?_⟩
  obtain ⟨U', hU'open, hsubU', hU'trace⟩ :=
    PatchParameterNull.exists_isOpen_carrier_inter_subset_image P (hΩopen.inter hΩgopen)
      (inter_subset_left.trans hΩsub)
  refine ⟨U', hΩopen.inter hΩgopen, inter_subset_left.trans hΩsub,
    (Set.image_mono inter_subset_left).trans hΩreg,
    hΩavoid.mono_left (Set.image_mono inter_subset_left), hU'open, ?_, hU'trace,
    p.mono P hgood inter_subset_right⟩
  exact hsubU' ⟨w₀, ⟨hw₀Ω, hw₀g⟩, hw₀⟩

/-- **The exhaustion of `V_reg ∖ avoid` by GOOD regular-piece families.**  One monotone
sequence of finite families absorbing every compact part of the regular locus off
`avoid`, every piece of which satisfies the given local property.  With the trivial
property this is `RegularPieceExhaustion.exists_exhaustion`. -/
theorem exists_exhaustion_good (p : LocalPieceProperty V) {avoid : Set M}
    (havoid : IsClosed avoid) :
    ∃ H : ℕ → RegularPieceFamily V avoid,
      (∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1))) ∧
      (∀ m, IsGoodFamily p (H m)) ∧
      ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        Disjoint K avoid → ∃ m, K ⊆ coveredRegion (H m) := by
  classical
  set S : Set M := regularLocus (n := n) V.carrier V.dim \ avoid with hSdef
  have hKS : ∀ K : Set M, K ⊆ regularLocus (n := n) V.carrier V.dim → Disjoint K avoid →
      K ⊆ S := fun K hKreg hKavoid x hx =>
    ⟨hKreg hx, fun hxa => (Set.disjoint_left.mp hKavoid hx) hxa⟩
  rcases eq_empty_or_nonempty S with hSe | hSne
  · refine ⟨fun _ => RegularPieceCompactCover.emptyFamily V avoid, fun _ => subset_rfl,
      fun _ => isGoodFamily_emptyFamily p avoid, ?_⟩
    intro K _ hKreg hKavoid
    exact ⟨0, ((hKS K hKreg hKavoid).trans hSe.subset).trans (empty_subset _)⟩
  · have hdata : ∀ x : S, ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (U : Set M),
        IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧
          P.toManifold '' Ω ⊆ regularLocus (n := n) V.carrier V.dim ∧
          Disjoint (P.toManifold '' Ω) avoid ∧
          IsOpen U ∧ (x : M) ∈ U ∧ V.carrier ∩ U ⊆ P.toManifold '' Ω ∧ p.good P Ω :=
      fun x => exists_localPatchData_good p havoid x.2.1 x.2.2
    choose P Ω U hΩopen hΩsub hΩreg hΩavoid hUopen hxU hUtrace hgood using hdata
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUopen
    have hScov : S ⊆ ⋃ i ∈ T, U i := by
      intro x hx
      rw [hTU]
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hSne
      obtain ⟨i, hiT, -⟩ := mem_iUnion₂.1 (hScov hx)
      exact ⟨i, hiT⟩
    obtain ⟨q, hq⟩ := hTc.exists_eq_range hTne
    have hfam : ∀ N : ℕ, ∃ F : RegularPieceFamily V avoid, IsGoodFamily p F ∧
        ∀ i : Fin (N + 1), (P (q i)).toManifold '' Ω (q i) ⊆ coveredRegion F :=
      fun N => exists_goodFamily_iUnion_image_superset' p
        (fun i : Fin (N + 1) => P (q i)) (fun i : Fin (N + 1) => Ω (q i))
        (fun i => (hΩopen (q i)).measurableSet) (fun i => hΩsub (q i))
        (fun i => hΩavoid (q i)) (fun i => hgood (q i))
    choose G hGgood hG using hfam
    refine ⟨runningUnion G, coveredRegion_runningUnion_subset_succ G,
      isGoodFamily_runningUnion p hGgood, ?_⟩
    intro K hK hKreg hKavoid
    have hKcov : K ⊆ ⋃ m : ℕ, U (q m) := by
      intro x hx
      obtain ⟨i, hiT, hiU⟩ := mem_iUnion₂.1 (hScov (hKS K hKreg hKavoid hx))
      rw [hq] at hiT
      obtain ⟨m, rfl⟩ := hiT
      exact mem_iUnion.2 ⟨m, hiU⟩
    obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun m : ℕ => U (q m))
      (fun m => hUopen (q m)) hKcov
    obtain ⟨N, hN⟩ := I.exists_le
    refine ⟨N, ?_⟩
    refine subset_trans ?_ (coveredRegion_subset_runningUnion G N)
    intro x hx
    obtain ⟨m, hmI, hmU⟩ := mem_iUnion₂.1 (hI hx)
    have hmN : m < N + 1 := Nat.lt_succ_of_le (hN m hmI)
    refine hG N ⟨m, hmN⟩ ?_
    exact hUtrace _ ⟨(FirstPass.regularLocus_subset _ _) (hKS K hKreg hKavoid hx).1, hmU⟩

/-- **The two-form comparison along a GOOD exhaustion.**  An identity of regular-piece
suprema that is false family by family may be proved along ONE monotone sequence of finite
families absorbing every compact part of `V_reg ∖ avoid` and all of whose pieces satisfy a
prescribed local property.  This is `RegularPieceExhaustion.iSup_formPieceMass_eq_iSup_of_exhaustion`
with the extra certificate carried along: both sides are computed by the same sequence, so
the sequence may be chosen before either form is looked at. -/
theorem iSup_formPieceMass_eq_of_good_exhaustion (p : LocalPieceProperty V)
    {avoid : Set M} (havoid : IsClosed avoid) (a b : SmoothRealForm n M 2)
    (hstokes : ∀ H : ℕ → RegularPieceFamily V avoid,
      (∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1))) →
      (∀ m, IsGoodFamily p (H m)) →
      (∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        Disjoint K avoid → ∃ m, K ⊆ coveredRegion (H m)) →
      (⨆ m : ℕ, PatchFormMass.formPieceMass a (H m)) =
        ⨆ m : ℕ, PatchFormMass.formPieceMass b (H m)) :
    (⨆ F : RegularPieceFamily V avoid, PatchFormMass.formPieceMass a F) =
      ⨆ F : RegularPieceFamily V avoid, PatchFormMass.formPieceMass b F := by
  obtain ⟨H, hmono, hgood, hexh⟩ := exists_exhaustion_good p (V := V) havoid
  rw [← iSup_formPieceMass_eq_iSup_of_exhaustion havoid hexh a,
    ← iSup_formPieceMass_eq_iSup_of_exhaustion havoid hexh b]
  exact hstokes H hmono hgood hexh

/-! ## The local property behind the Stokes obligation -/

variable {beta : KahlerBackground n M}

/-- **Carrying a local telescope potential.**  A parameter set `S` of a regular patch `P`
is *small enough for Stokes* when it lies in one open subset `Ω` of the parameter domain
on which the background has a smooth potential `φ` read in the parameters, on which the
ambient potential `v` restricted to the branch is smooth, and on which the difference of
the two parameter densities is the sum of the `dim V` mixed Monge--Ampère densities of the
telescope families of `φ` and `v ∘ P`.

This is exactly the conclusion of
`Pending.PatchDensityLocalPotential.exists_localPotential_patchFormDensity_currentForm_sub`,
turned from a statement about ONE parameter into a property of a SET of parameters. -/
def HasLocalTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (P : RegularPatch V) (S : Set (ComplexModel V.dim)) : Prop :=
  ∃ (Omega : Set (ComplexModel V.dim)) (phi : ComplexModel V.dim → ℝ),
    S ⊆ Omega ∧ IsOpen Omega ∧ Omega ⊆ P.parameterDomain ∧
      ContDiffOn ℝ ∞ phi Omega ∧
      ContDiffOn ℝ ∞ (fun y => v (P.toManifold y)) Omega ∧
      ∀ w' ∈ Omega,
        PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w' -
            PatchFormMass.patchFormDensity beta.form.val P w' =
          ∑ j : Fin V.dim, MixedMongeAmpere.mixedDensity
            (PatchDensityLocalPotential.telescopeFunctions phi
              (fun y => v (P.toManifold y)) j) w'

/-- `HasLocalTelescopePotential` is a local piece property: it is inherited by subsets,
and the local `dd`-bar lemma in patch parameters supplies it near every parameter. -/
def localTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v) :
    LocalPieceProperty V where
  good := HasLocalTelescopePotential q hvs
  mono := by
    rintro P S S' ⟨Omega, phi, hSO, hrest⟩ hS'
    exact ⟨Omega, phi, hS'.trans hSO, hrest⟩
  nhds := by
    intro P w hw
    obtain ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hpsi, heq⟩ :=
      PatchDensityLocalPotential.exists_localPotential_patchFormDensity_currentForm_sub
        beta q hq hvs P hw
    exact ⟨Omega, hOopen, hwO, hOsub,
      ⟨Omega, phi, subset_rfl, hOopen, hOsub, hphi, hpsi, heq⟩⟩

/-- **The exhaustion the Stokes obligation needs.**  One monotone sequence of finite
regular-piece families absorbing every compact part of `V_reg`, every piece of which lies
inside a single open set carrying a local potential of `β` in the parameters: on that set
the Stokes defect IS a sum of mixed Monge--Ampère densities of smooth real functions of
`dim V` complex variables, which is the shape integration by parts is proved for in
`Pending.MixedHessian`. -/
theorem exists_exhaustion_localTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v) :
    ∃ H : ℕ → RegularPieceFamily V (∅ : Set M),
      (∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1))) ∧
      (∀ m i, HasLocalTelescopePotential q hvs ((H m).patch i) ((H m).piece i)) ∧
      ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        ∃ m, K ⊆ coveredRegion (H m) := by
  obtain ⟨H, hmono, hgood, hexh⟩ :=
    exists_exhaustion_good (localTelescopePotential q hq hvs) (V := V) isClosed_empty
  exact ⟨H, hmono, fun m i => hgood m i,
    fun K hK hKreg => hexh K hK hKreg (Set.disjoint_empty K)⟩

end

end SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion
