import SGPT.NPP.KahlerCapacityBigControl
import SGPT.PSH.CountablePluripolar
import SGPT.PSH.Components
import SGPT.Foundations.Analysis.Pending.ClosedNullOuterCapacity
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.Pending.ActualClopenCapacityRestriction
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-!
# Pluripolar sets and sets of capacity zero

Source `thm:pp_cap` (chapter `chapter_npp.tex`, Section "Quasi-continuous
functions"): on a compact Kähler manifold `X` with `θ` a closed smooth real
`(1,1)`-form in a big class, a Borel set `A ⊆ X` is pluripolar iff
`Cap_θ(A) = 0`.

Proved here:
* (1) ⇒ (2) for every subset `A` (no Borel or bigness hypothesis is needed):
  `sourceThetaCapacity_eq_zero_of_locallyPluripolar`;
* (2) ⇒ (1) for closed `A` (no connectedness hypothesis, every dimension):
  `locallyPluripolar_of_isClosed_of_sourceThetaCapacity_eq_zero`, and more
  generally for `F_σ` sets: `locallyPluripolar_of_isFSigma_of_sourceThetaCapacity_eq_zero`.

The converse for arbitrary Borel sets needs the outer regularity
(capacitability) of the capacity on Borel sets, which is not available.

Pluripolarity is the source `def:pluripolarsets`
(`SGPT.PSH.VariableComplexAtlas.LocallyPluripolar`), capacity is the source
`def:cap` (`sourceThetaCapacity`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity DiagonalMass PluripolarCapacityZero OpensRestriction OpensRestrictionMeasure
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The source pluripolar predicate gives the native chartwise one. -/
theorem manifoldLocallyPluripolar_of_source {S : Set M}
    (hS : (ofFixedModel n M).LocallyPluripolar S) : ManifoldLocallyPluripolar (n := n) S :=
  fun e => hS.in_chart e

/-- The native chartwise pluripolar predicate gives the source one. -/
theorem source_locallyPluripolar_of_manifold {S : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S) : (ofFixedModel n M).LocallyPluripolar S :=
  SGPT.PSH.VariableComplexAtlas.locallyPluripolar_of_in_chart (A := ofFixedModel n M)
    (fun e => hS e)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Source `thm:pp_cap`, (1) ⇒ (2): a pluripolar set has `θ`-capacity zero, for
every closed smooth real `(1,1)`-form `θ` and every subset. -/
theorem sourceThetaCapacity_eq_zero_of_locallyPluripolar
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {A : Set M}
    (hA : (ofFixedModel n M).LocallyPluripolar A) : sourceThetaCapacity θ A = 0 := by
  rw [sourceThetaCapacity_eq_native]
  exact thetaCapacity_eq_zero_of_manifoldLocallyPluripolar _
    (manifoldLocallyPluripolar_of_source hA)


/-- A set of Kähler capacity zero is null for the non-pluripolar measure of
every bounded `ω`-psh potential. -/
theorem diagonalPotentialMeasure_eq_zero_of_kahlerCapacity_eq_zero
    (ω : KahlerBackground n M) {F : Set M}
    (hF : thetaCapacity ω.form (fun _ => 0) F = 0)
    (w : M → EReal) (hw : IsThetaPshPotential ω.form.val w)
    (hb : BoundedGlobalProduct.IsBoundedPotential w) :
    diagonalPotentialMeasure ω.form w hw F = 0 := by
  obtain ⟨a, b, hab⟩ := hb
  let u : M → EReal := fun x => w x - (b : EReal)
  have hu : IsThetaPshPotential ω.form.val u := hw.sub_const b
  have hu0 : u ≤ (fun _ => (0 : EReal)) := by
    intro x
    change w x - (b : EReal) ≤ 0
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot b))
      (Or.inl (EReal.coe_ne_top b))).mpr
    simpa only [zero_add] using (hab x).2
  have hlb : ∀ x, (fun _ => (0 : EReal)) x ≤ u x + ((max 1 (b - a) : ℝ) : EReal) := by
    intro x
    have hlo := (hab x).1
    have hhi := (hab x).2
    have hne : w x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) hlo
    have hnt : w x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) hhi
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w x = (r : EReal) := ⟨(w x).toReal, (EReal.coe_toReal hnt hne).symm⟩
    rw [hr] at hlo hhi
    have har : a ≤ r := EReal.coe_le_coe_iff.mp hlo
    change (0 : EReal) ≤ w x - (b : EReal) + ((max 1 (b - a) : ℝ) : EReal)
    rw [hr, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    have := le_max_right 1 (b - a)
    linarith
  have h := diagonalPotentialMeasure_eq_zero_of_thetaCapacity_eq_zero
    (PluripolarCapacityDichotomy.isThetaPshPotential_zero ω) hu (le_max_left 1 (b - a))
    hu0 hlb hF
  have heq : diagonalPotentialMeasure ω.form u hu = diagonalPotentialMeasure ω.form w hw :=
    GlobalMeasureInvariance.globalMixedMeasure_sub_const (fun _ : Fin n => hw.1) (fun _ => b)
  rw [← heq]
  exact h

/-- On a connected compact Kähler manifold, a closed set of Kähler capacity zero
is pluripolar (native chartwise form), in every dimension. -/
theorem manifoldLocallyPluripolar_of_isClosed_of_kahlerCapacity_eq_zero_connected
    [ConnectedSpace M] (ω : KahlerBackground n M) {F : Set M} (hF : IsClosed F)
    (h0 : thetaCapacity ω.form (fun _ => 0) F = 0) :
    ManifoldLocallyPluripolar (n := n) F := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hFe : F = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
      have hz := PluripolarCapacityDichotomy.isThetaPshPotential_zero ω
      have hle := diagonalPotentialMeasure_le_thetaCapacity hz (le_refl _)
        (fun x => by simp) F
      rw [h0] at hle
      have hcount := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
        (M := M) (fun _ => ω.form) (fun _ => fun _ => (0 : EReal)) (fun _ => hz.1)).1
      have hdiag : diagonalPotentialMeasure ω.form (fun _ => (0 : EReal)) hz = Measure.count :=
        hcount
      rw [hdiag, Measure.count_apply hF.measurableSet] at hle
      have h1 : (1 : ℕ∞) ≤ F.encard := Set.one_le_encard_iff_nonempty.mpr ⟨x, hx⟩
      have h2 : ((F.encard : ℕ∞) : ℝ≥0∞) = 0 := le_antisymm hle zero_le
      have h3 : F.encard = 0 := by exact_mod_cast h2
      rw [h3] at h1
      exact absurd h1 (by norm_num)
    rw [hFe]
    have hz := PluripolarCapacityDichotomy.isThetaPshPotential_zero ω
    exact (quasiPsh_poles_manifoldLocallyPluripolar hz.quasiPshPotential).mono
      (empty_subset _)
  · exact KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero' hn ω
      (ClosedNullOuterCapacity.outerCapacityZero_of_isClosed hn ω hF
        (fun w hw hb => diagonalPotentialMeasure_eq_zero_of_kahlerCapacity_eq_zero ω h0 w hw hb))

/-- On a compact Kähler manifold (not necessarily connected), a closed set of
Kähler capacity zero is pluripolar in the source sense. -/
theorem locallyPluripolar_of_isClosed_of_kahlerCapacity_eq_zero
    (ω : KahlerBackground n M) {F : Set M} (hF : IsClosed F)
    (h0 : thetaCapacity ω.form (fun _ => 0) F = 0) :
    (ofFixedModel n M).LocallyPluripolar F := by
  classical
  let _ : LocallyConnectedSpace M := OpensRestrictionMeasure.locallyConnectedSpace n M
  have hcomp : ∀ x : M, (ofFixedModel n M).LocallyPluripolar (F ∩ (componentOpens x : Set M)) := by
    intro x
    let U := componentOpens x
    have hU : IsClopen (U : Set M) := isClopen_componentOpens x
    have hFU : IsClosed ((Subtype.val : U → M) ⁻¹' F) := hF.preimage continuous_subtype_val
    have hcapU := ActualClopenCapacityRestriction.thetaCapacity_restrict_le
      (n := n) (M := M) ω U hU hF.measurableSet
    change thetaCapacity (restrictKahler U ω).form (fun _ => 0)
      ((Subtype.val : U → M) ⁻¹' F) ≤ thetaCapacity ω.form (fun _ => 0) F at hcapU
    rw [h0] at hcapU
    have h0U : thetaCapacity (restrictKahler U ω).form (fun _ => 0)
        ((Subtype.val : U → M) ⁻¹' F) = 0 := le_antisymm hcapU zero_le
    have hpolU := manifoldLocallyPluripolar_of_isClosed_of_kahlerCapacity_eq_zero_connected
      (M := U) (restrictKahler U ω) hFU h0U
    have himg := manifoldLocallyPluripolar_image_val (n := n) hU hpolU
    have hset : (Subtype.val '' ((Subtype.val : U → M) ⁻¹' F) : Set M) =
        F ∩ (U : Set M) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2⟩
      · rintro ⟨hyF, hyU⟩
        exact ⟨⟨y, hyU⟩, hyF, rfl⟩
    rw [hset] at himg
    exact source_locallyPluripolar_of_manifold himg
  intro x
  let U := componentOpens x
  have hUo : IsOpen (U : Set M) := U.isOpen
  obtain ⟨W, hW, hxW, w, hw, hpole⟩ := hcomp x x
  refine ⟨W ∩ U, hW.inter hUo, ⟨hxW, mem_componentOpens x⟩, w,
    hw.mono_open hW (hW.inter hUo) inter_subset_left, ?_⟩
  rintro y ⟨hyF, hyW, hyU⟩
  exact hpole y ⟨⟨hyF, hyU⟩, hyW⟩

/-- Source `thm:pp_cap`, (2) ⇒ (1) for closed sets: on a compact Kähler manifold
with `θ` in a big class, a closed set with `Cap_θ(A) = 0` is pluripolar. -/
theorem locallyPluripolar_of_isClosed_of_sourceThetaCapacity_eq_zero
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {A : Set M} (hA : IsClosed A) (h0 : sourceThetaCapacity θ A = 0) :
    (ofFixedModel n M).LocallyPluripolar A :=
  locallyPluripolar_of_isClosed_of_kahlerCapacity_eq_zero ω hA
    (kahlerCapacity_eq_zero_of_source_capacity_eq_zero ω θ hbig hA.measurableSet h0)

/-- Source `thm:pp_cap` for closed sets, as an equivalence. -/
theorem locallyPluripolar_iff_sourceThetaCapacity_eq_zero_of_isClosed
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {A : Set M} (hA : IsClosed A) :
    (ofFixedModel n M).LocallyPluripolar A ↔ sourceThetaCapacity θ A = 0 :=
  ⟨sourceThetaCapacity_eq_zero_of_locallyPluripolar θ,
    locallyPluripolar_of_isClosed_of_sourceThetaCapacity_eq_zero ω θ hbig hA⟩

/-- Source `thm:pp_cap`, (2) ⇒ (1) for `F_σ` sets (countable unions of closed
sets), with `θ` in a big class. -/
theorem locallyPluripolar_of_isFSigma_of_sourceThetaCapacity_eq_zero
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {F : ℕ → Set M} (hF : ∀ k, IsClosed (F k)) (h0 : sourceThetaCapacity θ (⋃ k, F k) = 0) :
    (ofFixedModel n M).LocallyPluripolar (⋃ k, F k) := by
  apply SGPT.PSH.VariableComplexAtlas.LocallyPluripolar.iUnion
  intro k
  apply locallyPluripolar_of_isClosed_of_sourceThetaCapacity_eq_zero ω θ hbig (hF k)
  exact le_antisymm (h0 ▸ sourceThetaCapacity_mono θ (subset_iUnion F k)) zero_le

end SGPT.NPP
