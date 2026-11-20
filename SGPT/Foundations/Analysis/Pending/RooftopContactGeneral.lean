import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.Pending.RooftopPshCriterion
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEnergyRooftopClosure

set_option autoImplicit false

/-!
# The rooftop measure lives on the contact sets, on every compact Kähler manifold

Xia's Theorem 2.4.4 at the minimum obstacle (the measure `θ^n_w` of the rooftop
`w = P_θ(min{φ, ψ})` puts no mass off `{w = φ} ∪ {w = ψ}`) is proved in
`Pending.RooftopContactConcentration` on a *connected* compact Kähler manifold: its proof splits
on the bigness of the class, which is not a local property.  This module removes the
connectedness.  The statement is local: on each connected component `C` (a clopen, connected,
compact Kähler open submanifold), the rooftop envelope of the restrictions is the restriction of
the rooftop envelope (`OpensRestrictionMeasure.rooftopEnvelope_restrict`), the measure of the
restriction is the trace of the measure (`OpensRestrictionMeasure.diagonalPotentialMeasure_restrict_apply`),
so the non-contact set has null trace on `C` by the connected theorem; and a set whose trace on
every component is null is null (`OpensRestrictionMeasure.measure_eq_zero_of_forall_connectedComponent`).

* `diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general` — the concentration,
  without `[ConnectedSpace M]`;
* `rooftopMeasure_le_contact_general` — **Xia, Lemma 3.1.1, measure form** (blueprint
  `trace:rooftop-measure-contact`): `⟨θ^n_w⟩(E) ≤ ⟨θ^n_φ⟩(E ∩ {w = φ}) + ⟨θ^n_ψ⟩(E ∩ {w = ψ})`;
* `relativeFiniteEnergyIntegral_rooftop_le_general` — the energy inequality of blueprint
  `trace:e1-rooftop-closure`, first assertion.

The proofs of the last two are those of `RooftopPshCriterion.rooftopMeasure_le_contact` and
`relativeFiniteEnergyIntegral_rooftop_le`, with the general concentration.  Sorry-free; no
existing statement is changed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopContactGeneral

open FirstPass FirstPass.PositiveClasses DiagonalMass OpensRestriction OpensRestrictionMeasure

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

theorem diagonalPotentialMeasure_congr_fun {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {θ : ClosedRealOneOneForm n X} {f g : X → EReal} (hfg : f = g)
    (hf : IsThetaPshPotential θ.val f) (hg : IsThetaPshPotential θ.val g) :
    diagonalPotentialMeasure θ f hf = diagonalPotentialMeasure θ g hg := by
  subst hfg
  rfl

/-- **Xia, Theorem 2.4.4 at the minimum obstacle, on every compact Kähler manifold.**  The
non-pluripolar measure of the rooftop `w = P_θ(min{φ, ψ})`, when `w` is a theta-PSH potential,
puts no mass on the set where `w` meets neither obstacle.  No connectedness is assumed. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw
      {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = 0 := by
  classical
  have := OpensRestrictionMeasure.locallyConnectedSpace n M
  set w := rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) with hwdef
  set N : Set M := {x | w x ≠ phi x ∧ w x ≠ psi x} with hNdef
  have hwm : Measurable w := hw.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hphim : Measurable phi := hphi.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hpsim : Measurable psi := hpsi.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hNm : MeasurableSet N :=
    (measurableSet_eq_fun hwm hphim).compl.inter (measurableSet_eq_fun hwm hpsim).compl
  apply measure_eq_zero_of_forall_connectedComponent
  intro x _
  have : Nonempty M := ⟨x⟩
  set C := componentOpens x with hC
  have hCclopen : IsClopen (C : Set M) := isClopen_componentOpens x
  -- the trace on `C` is the measure of the restriction
  have htrace := diagonalPotentialMeasure_restrict_apply (U := C) hw hNm
  change diagonalPotentialMeasure theta w hw (N ∩ (C : Set M)) = 0
  rw [← htrace]
  -- on `C`, the restriction of the rooftop is the rooftop of the restrictions
  have hne := rooftopCompetitors_nonempty_of_isThetaPshPotential hw
  have henv : rooftopEnvelope (restrictForm C theta).val
      (fun y : C => min (phi y) (psi y)) = fun y : C => w y :=
    rooftopEnvelope_restrict (θ := theta.val) (f := fun x => min (phi x) (psi x)) hCclopen hne
  have hwC : IsThetaPshPotential (restrictForm C theta).val
      (rooftopEnvelope (restrictForm C theta).val (fun y : C => min (phi y) (psi y))) := by
    rw [henv]; exact isThetaPshPotential_restrict hw
  have hconn := RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero
    (restrictKahler C omega) (restrictForm C theta) (isThetaPshPotential_restrict hphi)
    (isThetaPshPotential_restrict hpsi) hwC
  rw [diagonalPotentialMeasure_congr_fun henv hwC (isThetaPshPotential_restrict hw)] at hconn
  convert hconn using 2
  ext y
  simp only [hNdef, mem_preimage, mem_ofPred_eq, henv]

/-- **The rooftop measure lives on the two contact sets** (Xia, Lemma 3.1.1, measure form;
blueprint `trace:rooftop-measure-contact`), on every compact Kähler manifold.  For theta-PSH
`φ, ψ` whose rooftop `w = P_θ(min{φ, ψ})` is theta-PSH with `w ≤ φ`, `w ≤ ψ`, and every
measurable `E`: `⟨θ^n_w⟩(E) ≤ ⟨θ^n_φ⟩(E ∩ {w = φ}) + ⟨θ^n_ψ⟩(E ∩ {w = ψ})`. -/
theorem rooftopMeasure_le_contact_general (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))))
    (hwu : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u)
    (hwv : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v)
    {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hw E ≤
      diagonalPotentialMeasure theta u hu
          (E ∩ {x | rooftopEnvelope theta.val (fun y => min (u y) (v y)) x = u x}) +
        diagonalPotentialMeasure theta v hv
          (E ∩ {x | rooftopEnvelope theta.val (fun y => min (u y) (v y)) x = v x}) := by
  set w := rooftopEnvelope theta.val (fun x => min (u x) (v x)) with hwdef
  have hN : diagonalPotentialMeasure theta w hw {x | w x ≠ u x ∧ w x ≠ v x} = 0 :=
    diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general omega theta hu hv hw
  have hsub : E ⊆ ((E ∩ {x | w x = u x}) ∪ (E ∩ {x | w x = v x})) ∪
      {x | w x ≠ u x ∧ w x ≠ v x} := by
    intro x hx
    by_cases h1 : w x = u x
    · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · by_cases h2 : w x = v x
      · exact Or.inl (Or.inr ⟨hx, h2⟩)
      · exact Or.inr ⟨h1, h2⟩
  calc diagonalPotentialMeasure theta w hw E
      ≤ diagonalPotentialMeasure theta w hw (((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) ∪ {x | w x ≠ u x ∧ w x ≠ v x}) := measure_mono hsub
    _ ≤ diagonalPotentialMeasure theta w hw ((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) +
        diagonalPotentialMeasure theta w hw {x | w x ≠ u x ∧ w x ≠ v x} :=
        measure_union_le _ _
    _ = diagonalPotentialMeasure theta w hw ((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) := by rw [hN, add_zero]
    _ ≤ diagonalPotentialMeasure theta w hw (E ∩ {x | w x = u x}) +
        diagonalPotentialMeasure theta w hw (E ∩ {x | w x = v x}) := measure_union_le _ _
    _ ≤ _ := add_le_add (MaxMassDecomposition.contact_measure_le omega hw hu hwu hE)
        (MaxMassDecomposition.contact_measure_le omega hw hv hwv hE)

/-- **The energy inequality for rooftops** (blueprint `trace:e1-rooftop-closure`, first
assertion), on every compact Kähler manifold: for `w = P_θ(min{u, v})` theta-PSH below both
obstacles, `∫ |φ - w| θ^n_w ≤ ∫ |φ - u| θ^n_u + ∫ |φ - v| θ^n_v`. -/
theorem relativeFiniteEnergyIntegral_rooftop_le_general (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))))
    (hwu : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u)
    (hwv : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v) :
    relativeFiniteEnergyIntegral theta phi
        (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hw ≤
      relativeFiniteEnergyIntegral theta phi u hu +
        relativeFiniteEnergyIntegral theta phi v hv := by
  set w : M → EReal := rooftopEnvelope theta.val (fun x => min (u x) (v x)) with hwdef
  set μw := diagonalPotentialMeasure theta w hw with hμw
  set A : Set M := {x | w x = u x} with hAdef
  set B : Set M := {x | w x = v x} with hBdef
  have hwm : Measurable w := hw.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum : Measurable u := hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hA : MeasurableSet A := measurableSet_eq_fun hwm hum
  have hB : MeasurableSet B := measurableSet_eq_fun hwm hvm
  have hN : μw {x | w x ≠ u x ∧ w x ≠ v x} = 0 :=
    diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general omega theta hu hv hw
  have hrestr : μw.restrict (A ∪ B) = μw := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null (fun x hx => ?_) hN
    have hx' : ¬ (x ∈ A ∪ B) := hx
    simp only [hAdef, hBdef, mem_union, mem_ofPred_eq, not_or] at hx'
    exact hx'
  have hcmpA : μw.restrict A ≤ (diagonalPotentialMeasure theta u hu).restrict A := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact MaxMassDecomposition.contact_measure_le omega hw hu hwu hs
  have hcmpB : μw.restrict B ≤ (diagonalPotentialMeasure theta v hv).restrict B := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact MaxMassDecomposition.contact_measure_le omega hw hv hwv hs
  have hpieceA : ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw ≤
      relativeFiniteEnergyIntegral theta phi u hu := by
    calc ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw
        = ∫⁻ x in A, canonicalERealAbsDiff (phi x) (u x) ∂μw :=
          setLIntegral_congr_fun hA fun x hx => by
            simp only [hAdef, mem_ofPred_eq] at hx
            rw [hx]
      _ ≤ ∫⁻ x in A, canonicalERealAbsDiff (phi x) (u x)
            ∂(diagonalPotentialMeasure theta u hu) := lintegral_mono' hcmpA le_rfl
      _ ≤ relativeFiniteEnergyIntegral theta phi u hu := setLIntegral_le_lintegral _ _
  have hpieceB : ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw ≤
      relativeFiniteEnergyIntegral theta phi v hv := by
    calc ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw
        = ∫⁻ x in B, canonicalERealAbsDiff (phi x) (v x) ∂μw :=
          setLIntegral_congr_fun hB fun x hx => by
            simp only [hBdef, mem_ofPred_eq] at hx
            rw [hx]
      _ ≤ ∫⁻ x in B, canonicalERealAbsDiff (phi x) (v x)
            ∂(diagonalPotentialMeasure theta v hv) := lintegral_mono' hcmpB le_rfl
      _ ≤ relativeFiniteEnergyIntegral theta phi v hv := setLIntegral_le_lintegral _ _
  calc relativeFiniteEnergyIntegral theta phi w hw
      = ∫⁻ x, canonicalERealAbsDiff (phi x) (w x) ∂μw := rfl
    _ = ∫⁻ x in A ∪ B, canonicalERealAbsDiff (phi x) (w x) ∂μw := by rw [hrestr]
    _ ≤ ∫⁻ x in A, canonicalERealAbsDiff (phi x) (w x) ∂μw +
          ∫⁻ x in B, canonicalERealAbsDiff (phi x) (w x) ∂μw := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add hpieceA hpieceB

end

end SGPT.Foundations.Analysis.Pending.RooftopContactGeneral
