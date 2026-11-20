import SGPT.Foundations.Analysis.Pending.LocalPotentials
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

set_option autoImplicit false

/-!
# A flat compact complex torus: the hypotheses of the main theorem are satisfiable

Non-vacuity witness for `NakamayeMainTheorem.nonKahlerLocus_eq_nullLocus`.

Let `Λ ⊂ ℂⁿ` be the integer span of a real basis of `ℂⁿ` and `X = ℂⁿ / Λ`.
The projection `ℂⁿ → X` is a covering map (mathlib:
`AddSubgroup.isQuotientCoveringMap_of_comm`, since `Λ` is discrete), so the local
inverses of the projection form an atlas (`IsLocalHomeomorph.chartedSpace`).
Every chart is a local inverse of the projection, so a chart transition `T`
satisfies `T z - z ∈ Λ`; being continuous with values in the discrete group `Λ`,
`T z - z` is locally constant, i.e. every transition is locally a translation.
Hence:

* `X` is a complex manifold (`IsComplexManifold n X`): the transitions are
  holomorphic, `X` is Hausdorff (`Λ` is closed) and second countable;
* `X` is compact (the range of a `Λ`-periodic continuous map,
  `IsZLattice.isCompact_range_of_periodic`), connected and nonempty;
* the constant standard form `ω = (i/2) Σ dz_j ∧ dz̄_j` in every chart satisfies
  the tensor transformation law (every transition derivative is the identity),
  and is closed, of type `(1,1)` and strictly positive: a `KahlerBackground`;
* the classes `0` and `{ω}` are pseudoeffective (potential `0`).

`exists_mainTheorem_hypotheses` packages these: for every `n ≥ 1` there is a
nonempty, compact, connected complex manifold of dimension `n` with a Kähler
background and a pseudoeffective class, i.e. data satisfying every hypothesis of
`nonKahlerLocus_eq_nullLocus`.  This module does not import the main theorem; the
application itself is `FlatComplexTorusNakamaye`.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FlatComplexTorus

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable (n : ℕ)

/-- The period lattice `Λ ⊂ ℂⁿ`: the integer span of a real basis of `ℂⁿ`. -/
abbrev periodLattice : AddSubgroup (ComplexModel n) :=
  (Submodule.span ℤ (Set.range (Module.finBasis ℝ (ComplexModel n)))).toAddSubgroup

/-- The flat compact complex torus `ℂⁿ / Λ`. -/
abbrev Torus : Type := ComplexModel n ⧸ periodLattice n

/-- The projection `ℂⁿ → ℂⁿ / Λ`. -/
abbrev proj : ComplexModel n → Torus n := QuotientAddGroup.mk

theorem isDiscrete_periodLattice :
    IsDiscrete ((periodLattice n : AddSubgroup (ComplexModel n)) : Set (ComplexModel n)) :=
  SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance

/-- The projection is a local homeomorphism (indeed a covering map). -/
theorem isLocalHomeomorph_proj : IsLocalHomeomorph (proj n) :=
  ((periodLattice n).isAddQuotientCoveringMap_of_comm
    (isDiscrete_periodLattice n)).isCoveringMap.isLocalHomeomorph

/-- The atlas of local inverses of the projection. -/
instance instChartedSpace : ChartedSpace (ComplexModel n) (Torus n) :=
  (isLocalHomeomorph_proj n).chartedSpace QuotientAddGroup.mk_surjective

variable {n}

/-- Every chart of the atlas is a local inverse of the projection. -/
theorem coe_symm_of_mem_atlas {c : OpenPartialHomeomorph (Torus n) (ComplexModel n)}
    (hc : c ∈ atlas (ComplexModel n) (Torus n)) : ⇑c.symm = proj n := by
  obtain ⟨q, rfl⟩ := hc
  funext z
  simp [chartAt_self_eq]

/-- A chart transition commutes with the projection. -/
theorem proj_transition {c c' : OpenPartialHomeomorph (Torus n) (ComplexModel n)}
    (hc : c ∈ atlas (ComplexModel n) (Torus n)) (hc' : c' ∈ atlas (ComplexModel n) (Torus n))
    {z : ComplexModel n} (hz : z ∈ (c.symm ≫ₕ c').source) :
    proj n ((c.symm ≫ₕ c') z) = proj n z := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  have h1 := c'.left_inv hz.2
  rw [coe_symm_of_mem_atlas hc'] at h1
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, h1, coe_symm_of_mem_atlas hc]

/-- A chart transition moves points by lattice vectors. -/
theorem transition_sub_mem {c c' : OpenPartialHomeomorph (Torus n) (ComplexModel n)}
    (hc : c ∈ atlas (ComplexModel n) (Torus n)) (hc' : c' ∈ atlas (ComplexModel n) (Torus n))
    {z : ComplexModel n} (hz : z ∈ (c.symm ≫ₕ c').source) :
    (c.symm ≫ₕ c') z - z ∈ periodLattice n := by
  have h := QuotientAddGroup.eq.mp (proj_transition hc hc' hz)
  have h' := neg_mem h
  rwa [neg_add, neg_neg, ← sub_eq_add_neg] at h'

/-- Every chart transition is, near each point of its source, a translation by a
fixed lattice vector. -/
theorem eventually_transition_eq {c c' : OpenPartialHomeomorph (Torus n) (ComplexModel n)}
    (hc : c ∈ atlas (ComplexModel n) (Torus n)) (hc' : c' ∈ atlas (ComplexModel n) (Torus n))
    {z : ComplexModel n} (hz : z ∈ (c.symm ≫ₕ c').source) :
    (c.symm ≫ₕ c') =ᶠ[𝓝 z] fun w => w + ((c.symm ≫ₕ c') z - z) := by
  set T := c.symm ≫ₕ c'
  have hsrc : T.source ∈ 𝓝 z := T.open_source.mem_nhds hz
  set g : ComplexModel n → ComplexModel n := fun w => (T w - w) - (T z - z) with hg
  have hcont : Tendsto g (𝓝 z) (𝓝 0) := by
    have : ContinuousAt g z :=
      ((T.continuousAt hz).sub continuousAt_id).sub continuousAt_const
    simpa [hg] using this.tendsto
  have hmem : ∀ᶠ w in 𝓝 z, g w ∈ ((periodLattice n : AddSubgroup _) : Set (ComplexModel n)) :=
    eventually_of_mem hsrc fun w hw =>
      sub_mem (transition_sub_mem hc hc' hw) (transition_sub_mem hc hc' hz)
  have htend : Tendsto g (𝓝 z) (𝓝[((periodLattice n : AddSubgroup _) : Set (ComplexModel n))] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont, hmem⟩
  rw [(isDiscrete_periodLattice n).nhdsWithin 0 (zero_mem _)] at htend
  filter_upwards [tendsto_pure.mp htend] with w hw
  have hw' : T w - w - (T z - z) = 0 := hw
  rw [sub_eq_zero] at hw'
  rw [← hw']
  abel

/-- Chart transitions are holomorphic. -/
theorem contDiffOn_transition {c c' : OpenPartialHomeomorph (Torus n) (ComplexModel n)}
    (hc : c ∈ atlas (ComplexModel n) (Torus n)) (hc' : c' ∈ atlas (ComplexModel n) (Torus n)) :
    ContDiffOn ℂ ∞ (c.symm ≫ₕ c') (c.symm ≫ₕ c').source := by
  intro z hz
  exact ((contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (eventually_transition_eq hc hc' hz)).contDiffWithinAt

variable (n)

instance instIsManifold : IsManifold 𝓘(ℂ, ComplexModel n) ∞ (Torus n) :=
  isManifold_of_contDiffOn _ _ _ fun _ _ hc hc' => by
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
      Function.id_comp, preimage_id, range_id, inter_univ] using contDiffOn_transition hc hc'

instance instIsComplexManifold : IsComplexManifold n (Torus n) where

instance instCompactSpace : CompactSpace (Torus n) := by
  refine ⟨?_⟩
  have h := IsZLattice.isCompact_range_of_periodic
    (Submodule.span ℤ (Set.range (Module.finBasis ℝ (ComplexModel n)))) (proj n)
    continuous_quotient_mk' fun z w hw => by
      refine (QuotientAddGroup.eq.mpr ?_).symm
      simpa using hw
  rwa [QuotientAddGroup.mk_surjective.range_eq] at h

instance instConnectedSpace : ConnectedSpace (Torus n) :=
  QuotientAddGroup.mk_surjective.connectedSpace continuous_quotient_mk'

instance instNonempty : Nonempty (Torus n) := ⟨0⟩

variable {n}

/-- On the torus every chart-transition derivative is the identity. -/
theorem chartTransitionDerivative_eq_id (e f : ComplexChart n (Torus n)) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    chartTransitionDerivative e f z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  unfold chartTransitionDerivative chartTransition
  rw [(eventually_transition_eq e.property f.property hz).fderiv_eq]
  simp

variable (n)

/-- The flat form: the standard fundamental form in every chart. It satisfies the
genuine tensor transformation law because every transition is locally a
translation. -/
def flatForm : SmoothRealForm n (Torus n) 2 where
  coeff := fun _ _ => Kahler.fundamentalFormAlt
  smooth := fun _ => contDiffOn_const
  compatible := by
    intro e f z hz v
    simp only [chartTransitionDerivative_eq_id e f hz, ContinuousLinearMap.id_apply]

theorem flatForm_isKahler : (flatForm n).IsKahler :=
  ⟨fun _ _ _ => ⟨flatFundamentalForm_isOneOne n, flatFundamentalForm_isStrictlyPositive n⟩,
    fun _ z _ => Kahler.extDeriv_fundamentalFormAlt z⟩

/-- The flat Kähler background of the torus. -/
def flatKahlerBackground : KahlerBackground n (Torus n) where
  form := ⟨flatForm n, (flatForm_isKahler n).2, fun _ _ _ => flatFundamentalForm_isOneOne n⟩
  isKahler := flatForm_isKahler n

/-- The zero class of the torus is pseudoeffective (potential `0`). -/
theorem classPseudoeffectiveViaPotentials_zero :
    ClassPseudoeffectiveViaPotentials (0 : RealBottChern n (Torus n)) :=
  ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff 0).mpr fun _ _ _ _ => le_rfl⟩

/-- The Kähler class `{ω}` of the torus is pseudoeffective (potential `0`). -/
theorem classPseudoeffectiveViaPotentials_kahler :
    ClassPseudoeffectiveViaPotentials
      (RealBottChern.ofRepresentative (flatKahlerBackground n).form) :=
  ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (flatKahlerBackground n).isSemipositive⟩

/-- **Non-vacuity of the main theorem's hypotheses.** For every `n ≥ 1` there is a
nonempty compact connected complex manifold of dimension `n` (the flat torus
`ℂⁿ / Λ`) carrying a Kähler background and a pseudoeffective class: every
hypothesis of `NakamayeMainTheorem.nonKahlerLocus_eq_nullLocus` is satisfied. -/
theorem exists_mainTheorem_hypotheses (hn : 0 < n) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : ChartedSpace (ComplexModel n) X)
      (_ : IsComplexManifold n X), Nonempty X ∧ CompactSpace X ∧ ConnectedSpace X ∧ 0 < n ∧
      ∃ (_ : KahlerBackground n X) (alpha : RealBottChern n X),
        ClassPseudoeffectiveViaPotentials alpha :=
  ⟨Torus n, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hn, flatKahlerBackground n, 0, classPseudoeffectiveViaPotentials_zero n⟩

end

end SGPT.Foundations.Analysis.Pending.FlatComplexTorus
