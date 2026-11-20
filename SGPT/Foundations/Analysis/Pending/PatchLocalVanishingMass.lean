import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.BedfordTaylorGauge

set_option autoImplicit false

/-!
# Vanishing of the global non-pluripolar measure, tested patch by patch

`Pending.PatchLocalBoundedMeasure` puts the glued measure `globalMixedMeasure`
into honest Bedford--Taylor form on any patch on whose *source* the potentials
are bounded — no bound on `M` is required.  This module turns that
identification into the two forms the local theory is stated in:

* `exists_isBTLimit_of_boundedOn` — the `IsBTLimit` form, which is what
  every local Bedford--Taylor theorem of this workspace consumes
  (`Pending.PolydiskPshMollifierData.eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn`,
  `Pending.BedfordTaylorDecreasingLimit`, …).  Compare
  `Pending.GlobalSlotStokes.SlotChart.exists_isBTLimit`, whose hypothesis is a
  bound on all of `M`.
* `globalMixedMeasure_eq_zero_of_locally_canonical_eq_zero` — the vanishing
  criterion: a set on each of whose points some bounded patch carries no
  Bedford--Taylor mass is null for the global measure.  This is the shape of
  Xia's (2.21): the conclusion is about an open subset `U` of
  `X \ nK({theta})`, and the hypothesis is supplied one holomorphic ball at a
  time.

The covering step is genuinely needed and is isolated as
`measure_eq_zero_of_locally_eq_zero`; it uses second countability of `M`, the
same hypothesis `Pending.GlobalSlotStokes.measure_eq_of_restrict_eq_of_openCover`
already relies on.  Nothing here assumes the test set is measurable, open, or
contained in a single chart.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.GlobalPotentialPatches
open MixedMongeAmpere MixedNonPluripolar GlobalNonPluripolar BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

noncomputable section

/-! ### The covering step -/

/-- **A measure that vanishes on a neighbourhood of each point of `S` vanishes
on `S`.**  No measurability of `S` is assumed: second countability reduces the
family of witnessing open sets to a countable subfamily, whose union is null and
contains `S`. -/
theorem measure_eq_zero_of_locally_eq_zero {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] (μ : Measure X) {S : Set X}
    (h : ∀ x ∈ S, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μ V = 0) : μ S = 0 := by
  classical
  set 𝒰 : Set (Set X) := {V : Set X | IsOpen V ∧ μ V = 0} with h𝒰
  obtain ⟨T, hTc, hTS, hTU⟩ :=
    TopologicalSpace.isOpen_sUnion_countable 𝒰 fun V hV => hV.1
  have hTnull : μ (⋃₀ T) = 0 := by
    rw [sUnion_eq_biUnion]
    exact measure_biUnion_null_iff hTc |>.mpr fun V hV => (hTS hV).2
  refine le_antisymm (le_trans (measure_mono ?_) hTnull.le) bot_le
  intro x hx
  obtain ⟨V, hVopen, hxV, hVnull⟩ := h x hx
  rw [hTU]
  exact ⟨V, ⟨hVopen, hVnull⟩, hxV⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-! ### The `IsBTLimit` form of the local model -/

/-- **The local Bedford--Taylor model of the global non-pluripolar measure, from
a bound on one patch.**  This is
`Pending.GlobalSlotStokes.SlotChart.exists_isBTLimit` with the global
`IsBoundedPotential` replaced by a bound on `P.source`.  The corrected
potentials are real there, so the truncation limit which *defines*
`globalMixedMeasure` on this patch is an honest Bedford--Taylor limit. -/
theorem exists_isBTLimit_of_boundedOn
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u)
    (hb : ∀ i, IsBoundedPotentialOn (u i) P.source) :
    ∃ μ : Measure (ComplexModel n), IsBTLimit P.domain (correctedReal P) μ ∧
      (globalMixedMeasure θ u hu).restrict (P.source : Set M) = P.pushMeasure μ := by
  refine ⟨canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
    (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb),
    IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (canonicalMixedBedfordTaylorMeasure_spec P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hb)),
    globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn hu P hb⟩

/-! ### The vanishing criterion -/

/-- One bounded patch carrying no Bedford--Taylor mass makes its whole source
null for the global measure. -/
theorem globalMixedMeasure_source_eq_zero_of_boundedOn
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) (P : Patch θ u)
    (hb : ∀ i, IsBoundedPotentialOn (u i) P.source)
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit P.domain (correctedReal P) μ)
    (hzero : μ = 0) :
    globalMixedMeasure θ u hu (P.source : Set M) = 0 := by
  obtain ⟨ν, hν, hres⟩ := exists_isBTLimit_of_boundedOn hu P hb
  have hνμ : ν = μ := hν.unique hμ
  have hkey : (globalMixedMeasure θ u hu).restrict (P.source : Set M)
      (P.source : Set M) = 0 := by
    rw [hres, P.pushMeasure_apply, hνμ, hzero]
    simp
  rwa [Measure.restrict_apply P.source.isOpen.measurableSet, inter_self] at hkey

/-- **The vanishing criterion (the shape of Xia's (2.21)).**  If every point of
`S` lies in the source of a patch on which the potentials are bounded and whose
Bedford--Taylor limit is zero, then `S` is null for the global non-pluripolar
measure.  `S` need not be measurable, open, or inside one chart. -/
theorem globalMixedMeasure_eq_zero_of_locally_isBTLimit_zero
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) {S : Set M}
    (h : ∀ x ∈ S, ∃ P : Patch θ u, x ∈ P.source ∧
      (∀ i, IsBoundedPotentialOn (u i) P.source) ∧
      ∀ μ : Measure (ComplexModel n), IsBTLimit P.domain (correctedReal P) μ → μ = 0) :
    globalMixedMeasure θ u hu S = 0 := by
  refine measure_eq_zero_of_locally_eq_zero _ fun x hx => ?_
  obtain ⟨P, hxP, hb, hzero⟩ := h x hx
  obtain ⟨μ, hμ, -⟩ := exists_isBTLimit_of_boundedOn hu P hb
  exact ⟨(P.source : Set M), P.source.isOpen, hxP,
    globalMixedMeasure_source_eq_zero_of_boundedOn hu P hb hμ (hzero μ hμ)⟩

/-! ### The diagonal case -/

open SGPT.Foundations.Analysis.Pending.DiagonalMass

/-- The diagonal reading of the criterion: the non-pluripolar Monge--Ampère
measure `theta^n_w` of a single `theta`-PSH potential.  This is the form Xia's
Lemma 2.4.3 asserts. -/
theorem diagonalPotentialMeasure_eq_zero_of_locally_isBTLimit_zero
    {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (h : ∀ x ∈ S, ∃ P : Patch (fun _ : Fin n => theta) (fun _ => w), x ∈ P.source ∧
      (∀ _i : Fin n, IsBoundedPotentialOn w P.source) ∧
      ∀ μ : Measure (ComplexModel n), IsBTLimit P.domain (correctedReal P) μ → μ = 0) :
    diagonalPotentialMeasure theta w hw S = 0 :=
  globalMixedMeasure_eq_zero_of_locally_isBTLimit_zero (fun _ => hw.1) h

end

end SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass
