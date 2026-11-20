import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-!
# Step 2 of Xia's Theorem 3.1.3: the truncated diamond for model potentials

Xia, SGPT, Theorem 3.1.3 (`xia-sgpt:page-0108`, inequality (3.19)) is the mass
diamond

  `int theta_phi^n + int theta_psi^n <= int theta_{phi \/ psi}^n + int theta_{phi /\ psi}^n`.

Its proof has two steps.  **Step 1** (`xia-sgpt:page-0108`) replaces `phi`,
`psi` by their `P`-envelopes, using Proposition 3.1.3, Corollary 2.4.1, Theorem
2.4.3 and Lemma 3.1.2.  **Step 2** (`xia-sgpt:page-0108`--`page-0109`) proves
the inequality for **model** potentials by a truncation, and it is Step 2 that
this module carries out, for every truncation level, with no limit taken.

Write `gamma = phi \/ psi` and, for `C > 0`,

  `phi_C = phi \/ (gamma - C)`,   `psi_C = psi \/ (gamma - C)`,
  `w_C   = P_theta(min {phi_C, psi_C})`.

The theorem proved here is Xia's chain (3.20)--(3.21) and the displayed
integral inequality, in the exact form

  `int theta_phi^n + int theta_psi^n
     <= int theta_gamma^n + theta^n_{w_C}({w_C = 0})`.        (*)

What remains of Theorem 3.1.3 after (*) is exactly what the source does next:
let `C -> infinity` and apply Corollary 2.4.2 (`xia-sgpt:page-0077`), the upper
semicontinuity of the contact mass `int_{{u=0}} theta_u^n` along an `L^1`
convergent net of nonpositive potentials.  Corollary 2.4.2 is absent from this
workspace; so is Step 1.  Neither is used below.

## How Step 2 runs here

* `phi_C ~ gamma ~ psi_C ~ w_C`: all four sit between `gamma - C` and `gamma`,
  so `Pending.diagonalPotentialMass_mono_of_kahler` in both directions gives
  them all the mass of `gamma` (Xia's "Note that `phi_C ~ psi_C ~ gamma`").
* **The model hypothesis is used exactly once**, through Xia's Theorem 3.1.1
  (`Pending.SingularityEnvelopeContact`): `theta^n_phi` gives no mass to
  `{phi < 0}`.  Since `gamma <= 0` and `C > 0`, the truncation locus
  `{phi <= gamma - C}` is inside `{phi < 0}`, which is what makes (3.20)
  collapse to `theta^n_{phi_C} = theta^n_phi + 1_{{phi <= gamma - C}}
  theta^n_{phi_C}`.
* Plurifine locality (Xia's Proposition 2.2.1(1),
  `Pending.MaxMassDecomposition.measure_inter_lt_left`) identifies
  `theta^n_{phi_C}` with `theta^n_phi` on `{gamma - C < phi}`.
* Xia's Lemma 3.1.1, i.e. `Pending.RooftopContactConcentration`'s (3.2), bounds
  `theta^n_{w_C}` on `{w_C < 0}` by the two truncation terms.
* The conclusion is then pure `ENNReal` bookkeeping, with no subtraction: all
  masses are finite because `omega` is a Kähler background.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.RooftopContactConcentration

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Xia's truncation `u \/ (gamma - C)` of `u` at level `C` above `gamma`
(`xia-sgpt:page-0108`). -/
def truncAt (gamma : M → EReal) (C : ℝ) (u : M → EReal) : M → EReal :=
  fun x => max (u x) (gamma x + ((-C : ℝ) : EReal))

@[simp] theorem truncAt_apply (gamma : M → EReal) (C : ℝ) (u : M → EReal) (x : M) :
    truncAt gamma C u x = max (u x) (gamma x + ((-C : ℝ) : EReal)) := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem shifted_le_truncAt (gamma : M → EReal) (C : ℝ) (u : M → EReal) (x : M) :
    gamma x + ((-C : ℝ) : EReal) ≤ truncAt gamma C u x := le_max_right _ _

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem truncAt_le (gamma : M → EReal) (C : ℝ) {u : M → EReal} (hC : 0 ≤ C)
    (hu : u ≤ gamma) (x : M) : truncAt gamma C u x ≤ gamma x := by
  refine max_le (hu x) ?_
  calc gamma x + ((-C : ℝ) : EReal) ≤ gamma x + ((0 : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
    _ = gamma x := by rw [EReal.coe_zero, add_zero]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Off the truncation locus the truncation is the original potential. -/
theorem truncAt_eq_self_of_lt {gamma : M → EReal} {C : ℝ} {u : M → EReal} {x : M}
    (h : gamma x + ((-C : ℝ) : EReal) < u x) : truncAt gamma C u x = u x :=
  max_eq_left h.le

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isThetaPshPotential_truncAt {theta : SmoothRealForm n M 2}
    {gamma u : M → EReal} (hgamma : IsThetaPshPotential theta gamma)
    (hu : IsThetaPshPotential theta u) (C : ℝ) :
    IsThetaPshPotential theta (truncAt gamma C u) :=
  SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu (hgamma.add_const _)

/-- Xia's `w_C = P_theta(min {phi_C, psi_C})` (`xia-sgpt:page-0108`). -/
def truncRooftop (theta : SmoothRealForm n M 2) (gamma phi psi : M → EReal) (C : ℝ) :
    M → EReal :=
  rooftopEnvelope theta (fun x => min (truncAt gamma C phi x) (truncAt gamma C psi x))

/-- The negativity locus of a `theta`-PSH potential is Borel; it is in fact
open, the potential being upper semicontinuous. -/
theorem measurableSet_lt_zero {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) : MeasurableSet {x : M | u x < 0} :=
  measurableSet_lt hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    measurable_const

/-- Every set has finite measure for a diagonal non-pluripolar measure on a
compact Kähler manifold. -/
theorem measure_ne_top (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (s : Set M) :
    diagonalPotentialMeasure theta u hu s ≠ ⊤ :=
  (SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar.globalMixedMeasure_apply_lt_top
    omega (fun _ : Fin n => hu.1) s).ne

/-- Two potentials squeezed between `gamma - C` and `gamma` have the mass of
`gamma`: this is Xia's "`phi_C ~ psi_C ~ gamma`" together with the monotonicity
theorem 2.4.3 applied in both directions. -/
theorem mass_eq_mass_of_between (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {gamma u : M → EReal}
    (hgamma : IsThetaPshPotential theta.val gamma)
    (hu : IsThetaPshPotential theta.val u) {C : ℝ}
    (hlow : ∀ x, gamma x + ((-C : ℝ) : EReal) ≤ u x)
    (hhigh : ∀ x, u x ≤ gamma x) :
    diagonalPotentialMass theta u hu = diagonalPotentialMass theta gamma hgamma := by
  refine le_antisymm
    (SGPT.Foundations.Analysis.Pending.diagonalPotentialMass_mono_of_kahler omega hu hgamma
      (MoreSingularOn.of_le fun x _ => hhigh x))
    (SGPT.Foundations.Analysis.Pending.diagonalPotentialMass_mono_of_kahler omega hgamma hu
      ⟨C, fun x _ => ?_⟩)
  have h := add_le_add (hlow x) (le_refl ((C : ℝ) : EReal))
  rwa [SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization.add_coe_neg_add
    (gamma x) C] at h

/-- **Xia, SGPT, Theorem 3.1.1 (`xia-sgpt:page-0100`), read on a model
potential.**  A potential fixed by `P_theta` gives no mass to its own
negativity locus. -/
theorem measure_lt_zero_eq_zero_of_model [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hmodel : phi = singularityEnvelope theta.val phi) :
    diagonalPotentialMeasure theta phi hphi {x | phi x < 0} = 0 := by
  have hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi) := by
    rw [← hmodel]; exact hphi
  have hset : {x : M | phi x < 0} =
      {x : M | singularityEnvelope theta.val phi x < 0} := by
    ext x
    show phi x < 0 ↔ singularityEnvelope theta.val phi x < 0
    rw [congrFun hmodel x]
  rw [diagonalPotentialMeasure_congr hphi hP hmodel, hset]
  exact SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
    omega theta hphi hP

section Step2

variable [ConnectedSpace M] (omega : KahlerBackground n M)
  (theta : ClosedRealOneOneForm n M)

/-- **Xia's (3.20)--(3.21) (`xia-sgpt:page-0109`), evaluated.**  For a model
potential `phi` below `gamma <= 0` and `C > 0`, the mass of `gamma` splits as
the mass of `phi` plus the measure the truncation `phi_C` gives to the
truncation locus `{phi <= gamma - C}`.

The model hypothesis enters only here, through Theorem 3.1.1: `theta^n_phi`
does not charge `{phi < 0}`, and the truncation locus is inside it. -/
theorem mass_gamma_eq_mass_add_truncation_measure
    (omega : KahlerBackground n M)
    {gamma phi : M → EReal}
    (hgamma : IsThetaPshPotential theta.val gamma)
    (hphi : IsThetaPshPotential theta.val phi)
    (hmodel : phi = singularityEnvelope theta.val phi)
    (hgamma0 : ∀ x, gamma x ≤ 0) (hphig : ∀ x, phi x ≤ gamma x)
    {C : ℝ} (hC : 0 < C) :
    diagonalPotentialMass theta gamma hgamma =
      diagonalPotentialMass theta phi hphi +
        diagonalPotentialMeasure theta (truncAt gamma C phi)
          (isThetaPshPotential_truncAt hgamma hphi C)
          {x | gamma x + ((-C : ℝ) : EReal) < phi x}ᶜ := by
  classical
  set hshift : IsThetaPshPotential theta.val (fun x => gamma x + ((-C : ℝ) : EReal)) :=
    hgamma.add_const _ with hshiftdef
  set hphiC : IsThetaPshPotential theta.val (truncAt gamma C phi) :=
    isThetaPshPotential_truncAt hgamma hphi C with hphiCdef
  set S : Set M := {x | gamma x + ((-C : ℝ) : EReal) < phi x} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_potential_lt hphi hshift
  -- the truncation locus sits inside the negativity locus of `phi`
  have hcompl : Sᶜ ⊆ {x : M | phi x < 0} := by
    intro x hx
    have hx' : ¬ (gamma x + ((-C : ℝ) : EReal) < phi x) := hx
    have hle : phi x ≤ gamma x + ((-C : ℝ) : EReal) := not_lt.mp hx'
    have h2 : gamma x + ((-C : ℝ) : EReal) ≤ ((-C : ℝ) : EReal) := by
      calc gamma x + ((-C : ℝ) : EReal) ≤ 0 + ((-C : ℝ) : EReal) :=
            add_le_add (hgamma0 x) le_rfl
        _ = ((-C : ℝ) : EReal) := zero_add _
    have h3 : ((-C : ℝ) : EReal) < (0 : EReal) := by
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) from EReal.coe_zero.symm]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    exact lt_of_le_of_lt (hle.trans h2) h3
  -- `theta^n_phi` is carried by `S`
  have hphiScompl : diagonalPotentialMeasure theta phi hphi Sᶜ = 0 :=
    measure_mono_null hcompl
      (measure_lt_zero_eq_zero_of_model omega theta hphi hmodel)
  have hphiS : diagonalPotentialMeasure theta phi hphi S =
      diagonalPotentialMass theta phi hphi := by
    have h := measure_add_measure_compl (μ := diagonalPotentialMeasure theta phi hphi) hSmeas
    rw [hphiScompl, add_zero] at h
    exact h
  -- plurifine locality on `S`
  have hloc : diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC S =
      diagonalPotentialMeasure theta phi hphi S := by
    have h := measure_inter_lt_left theta hphi hshift hphiC (s := univ) MeasurableSet.univ
    change diagonalPotentialMeasure theta
        (fun x => max (phi x) (gamma x + ((-C : ℝ) : EReal))) hphiC S =
      diagonalPotentialMeasure theta phi hphi S
    simpa only [univ_inter, hSdef] using h
  -- and the mass of the truncation is the mass of `gamma`
  have hmassC : diagonalPotentialMass theta (truncAt gamma C phi) hphiC =
      diagonalPotentialMass theta gamma hgamma :=
    mass_eq_mass_of_between omega hgamma hphiC (C := C)
      (fun x => shifted_le_truncAt gamma C phi x)
      (fun x => truncAt_le gamma C hC.le hphig x)
  calc diagonalPotentialMass theta gamma hgamma
      = diagonalPotentialMass theta (truncAt gamma C phi) hphiC := hmassC.symm
    _ = diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC S +
          diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC Sᶜ :=
        (measure_add_measure_compl hSmeas).symm
    _ = diagonalPotentialMass theta phi hphi +
          diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC Sᶜ := by
        rw [hloc, hphiS]

/-- The negativity locus of the truncation is charged by no more than the
truncation locus: off the truncation locus the truncation *is* `phi`, which is
carried by its contact set. -/
theorem measure_truncAt_lt_zero_le
    (omega : KahlerBackground n M)
    {gamma phi : M → EReal}
    (hgamma : IsThetaPshPotential theta.val gamma)
    (hphi : IsThetaPshPotential theta.val phi)
    (hmodel : phi = singularityEnvelope theta.val phi)
    {C : ℝ} :
    diagonalPotentialMeasure theta (truncAt gamma C phi)
        (isThetaPshPotential_truncAt hgamma hphi C)
        {x | truncAt gamma C phi x < 0} ≤
      diagonalPotentialMeasure theta (truncAt gamma C phi)
        (isThetaPshPotential_truncAt hgamma hphi C)
        {x | gamma x + ((-C : ℝ) : EReal) < phi x}ᶜ := by
  classical
  set hshift : IsThetaPshPotential theta.val (fun x => gamma x + ((-C : ℝ) : EReal)) :=
    hgamma.add_const _ with hshiftdef
  set hphiC : IsThetaPshPotential theta.val (truncAt gamma C phi) :=
    isThetaPshPotential_truncAt hgamma hphi C with hphiCdef
  set S : Set M := {x | gamma x + ((-C : ℝ) : EReal) < phi x} with hSdef
  set N : Set M := {x | truncAt gamma C phi x < 0} with hNdef
  have hNmeas : MeasurableSet N := measurableSet_lt_zero hphiC
  -- on `N ∩ S` the truncation is `phi`, so `phi < 0` there
  have hsub : N ∩ S ⊆ {x : M | phi x < 0} := by
    intro x hx
    have hxS : gamma x + ((-C : ℝ) : EReal) < phi x := hx.2
    have hxN : truncAt gamma C phi x < 0 := hx.1
    show phi x < 0
    rwa [truncAt_eq_self_of_lt hxS] at hxN
  have hloc : diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC (N ∩ S) =
      diagonalPotentialMeasure theta phi hphi (N ∩ S) := by
    have h := measure_inter_lt_left theta hphi hshift hphiC (s := N) hNmeas
    change diagonalPotentialMeasure theta
        (fun x => max (phi x) (gamma x + ((-C : ℝ) : EReal))) hphiC (N ∩ S) =
      diagonalPotentialMeasure theta phi hphi (N ∩ S)
    simpa only [hSdef] using h
  have hzero : diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC (N ∩ S) = 0 := by
    rw [hloc]
    exact measure_mono_null hsub
      (measure_lt_zero_eq_zero_of_model omega theta hphi hmodel)
  calc diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC N
      = diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC
          ((N ∩ S) ∪ (N ∩ Sᶜ)) := by rw [inter_union_compl]
    _ ≤ diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC (N ∩ S) +
          diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC (N ∩ Sᶜ) :=
        measure_union_le _ _
    _ = diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC (N ∩ Sᶜ) := by
        rw [hzero, zero_add]
    _ ≤ diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC Sᶜ :=
        measure_mono inter_subset_right

/-- **Xia, SGPT, Theorem 3.1.3, Step 2 (`xia-sgpt:page-0108`--`page-0109`), at
one truncation level.**  For model potentials `phi`, `psi` with
`gamma = phi \/ psi` and any `C > 0`,

  `int theta_phi^n + int theta_psi^n
     <= int theta_gamma^n + theta^n_{w_C}({w_C = 0})`,

where `w_C = P_theta(min {phi \/ (gamma - C), psi \/ (gamma - C)})`.

This is the whole of Step 2 except the passage `C -> infinity`, which is
Corollary 2.4.2 and is not available in this workspace.  Inside the proof the
only inputs are: Xia's Theorem 3.1.1 through the two truncation identities
above, Xia's Lemma 3.1.1 (`Pending.RooftopContactConcentration`'s (3.2)),
plurifine locality, and the monotonicity theorem 2.4.3 through
`mass_eq_mass_of_between`. -/
theorem mass_add_mass_le_mass_max_add_contact_of_model
    (omega : KahlerBackground n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    {C : ℝ} (hC : 0 < C)
    (hw : IsThetaPshPotential theta.val
      (truncRooftop theta.val (fun x => max (phi x) (psi x)) phi psi C)) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMeasure theta
            (truncRooftop theta.val (fun x => max (phi x) (psi x)) phi psi C) hw
          {x | truncRooftop theta.val (fun x => max (phi x) (psi x)) phi psi C x = 0} := by
  classical
  unfold truncRooftop at hw ⊢
  set gamma : M → EReal := fun x => max (phi x) (psi x) with hgammadef
  have hgamma : IsThetaPshPotential theta.val gamma := hmax
  have hphi0 : ∀ x, phi x ≤ 0 := by
    intro x
    have h := singularityEnvelope_le_zero theta.val phi x
    rw [← congrFun hphimodel x] at h
    simpa using h
  have hpsi0 : ∀ x, psi x ≤ 0 := by
    intro x
    have h := singularityEnvelope_le_zero theta.val psi x
    rw [← congrFun hpsimodel x] at h
    simpa using h
  have hgamma0 : ∀ x, gamma x ≤ 0 := fun x => max_le (hphi0 x) (hpsi0 x)
  have hphig : ∀ x, phi x ≤ gamma x := fun x => le_max_left _ _
  have hpsig : ∀ x, psi x ≤ gamma x := fun x => le_max_right _ _
  have hshift : IsThetaPshPotential theta.val (fun x => gamma x + ((-C : ℝ) : EReal)) :=
    hgamma.add_const _
  have hphiC : IsThetaPshPotential theta.val (truncAt gamma C phi) :=
    isThetaPshPotential_truncAt hgamma hphi C
  have hpsiC : IsThetaPshPotential theta.val (truncAt gamma C psi) :=
    isThetaPshPotential_truncAt hgamma hpsi C
  set w : M → EReal := rooftopEnvelope theta.val
    (fun x => min (truncAt gamma C phi x) (truncAt gamma C psi x)) with hwset
  -- `w_C` sits between `gamma - C` and `gamma`
  obtain ⟨hwphi, hwpsi⟩ := rooftopEnvelope_min_le_obstacles hphiC.1 hpsiC.1
  have hwphi' : ∀ x, w x ≤ truncAt gamma C phi x := by
    intro x; rw [hwset]; exact hwphi x
  have hwpsi' : ∀ x, w x ≤ truncAt gamma C psi x := by
    intro x; rw [hwset]; exact hwpsi x
  have hwgamma : ∀ x, w x ≤ gamma x := fun x =>
    (hwphi' x).trans (truncAt_le gamma C hC.le hphig x)
  have hwlow : ∀ x, gamma x + ((-C : ℝ) : EReal) ≤ w x := by
    intro x
    have hmin : ∀ y, gamma y + ((-C : ℝ) : EReal) ≤
        min (truncAt gamma C phi y) (truncAt gamma C psi y) := fun y =>
      le_min (shifted_le_truncAt gamma C phi y) (shifted_le_truncAt gamma C psi y)
    have h := FirstPass.le_rooftopEnvelope hshift
      (FirstPass.quasiEverywhere_of_forall hmin) x
    rw [hwset]
    exact h
  have hw0 : ∀ x, w x ≤ 0 := fun x => (hwgamma x).trans (hgamma0 x)
  -- the two truncation identities
  have hi := mass_gamma_eq_mass_add_truncation_measure (theta := theta) omega hgamma hphi hphimodel
    hgamma0 hphig hC
  have hii := mass_gamma_eq_mass_add_truncation_measure (theta := theta) omega hgamma hpsi hpsimodel
    hgamma0 hpsig hC
  set aC : ℝ≥0∞ := diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC
    {x | gamma x + ((-C : ℝ) : EReal) < phi x}ᶜ with haCdef
  set bC : ℝ≥0∞ := diagonalPotentialMeasure theta (truncAt gamma C psi) hpsiC
    {x | gamma x + ((-C : ℝ) : EReal) < psi x}ᶜ with hbCdef
  -- Lemma 3.1.1 at the pair of truncations, on the negativity locus of `w_C`
  set B : Set M := {x | w x < 0} with hBdef
  have hBmeas : MeasurableSet B := measurableSet_lt_zero hw
  have hL := diagonalPotentialMeasure_rooftopEnvelope_min_le omega theta hphiC hpsiC hw B
  have hLphi : diagonalPotentialMeasure theta (truncAt gamma C phi) hphiC
      (B ∩ {x | w x = truncAt gamma C phi x}) ≤ aC := by
    refine le_trans (measure_mono ?_)
      (measure_truncAt_lt_zero_le (theta := theta) omega hgamma hphi hphimodel (C := C))
    intro x hx
    have h1 : w x < 0 := hx.1
    have h2 : w x = truncAt gamma C phi x := hx.2
    change truncAt gamma C phi x < 0
    rwa [← h2]
  have hLpsi : diagonalPotentialMeasure theta (truncAt gamma C psi) hpsiC
      (B ∩ {x | w x = truncAt gamma C psi x}) ≤ bC := by
    refine le_trans (measure_mono ?_)
      (measure_truncAt_lt_zero_le (theta := theta) omega hgamma hpsi hpsimodel (C := C))
    intro x hx
    have h1 : w x < 0 := hx.1
    have h2 : w x = truncAt gamma C psi x := hx.2
    change truncAt gamma C psi x < 0
    rwa [← h2]
  have hBbound : diagonalPotentialMeasure theta w hw B ≤ aC + bC :=
    hL.trans (add_le_add hLphi hLpsi)
  -- the mass of `w_C` is the mass of `gamma`, and splits along `B`
  have hwmass : diagonalPotentialMass theta w hw =
      diagonalPotentialMass theta gamma hgamma :=
    mass_eq_mass_of_between omega hgamma hw (C := C) hwlow hwgamma
  have hBc : Bᶜ = {x : M | w x = 0} := by
    ext x
    rw [hBdef]
    show ¬ (w x < 0) ↔ w x = 0
    rw [not_lt]
    exact ⟨fun h => le_antisymm (hw0 x) h, fun h => h.ge⟩
  have hsplit : diagonalPotentialMass theta gamma hgamma =
      diagonalPotentialMeasure theta w hw B +
        diagonalPotentialMeasure theta w hw {x : M | w x = 0} := by
    rw [← hwmass, ← hBc]
    exact (measure_add_measure_compl hBmeas).symm
  -- finiteness, so that the common summand can be cancelled
  have haCfin : aC ≠ ⊤ := measure_ne_top omega hphiC _
  have hbCfin : bC ≠ ⊤ := measure_ne_top omega hpsiC _
  have hfin : aC + bC ≠ ⊤ := by
    simp [ENNReal.add_eq_top, haCfin, hbCfin]
  have hkey : (diagonalPotentialMass theta phi hphi +
      diagonalPotentialMass theta psi hpsi) + (aC + bC) ≤
      (diagonalPotentialMass theta gamma hgamma +
        diagonalPotentialMeasure theta w hw {x : M | w x = 0}) + (aC + bC) := by
    calc (diagonalPotentialMass theta phi hphi +
            diagonalPotentialMass theta psi hpsi) + (aC + bC)
        = (diagonalPotentialMass theta phi hphi + aC) +
            (diagonalPotentialMass theta psi hpsi + bC) := by ring
      _ = diagonalPotentialMass theta gamma hgamma +
            diagonalPotentialMass theta gamma hgamma := by rw [← hi, ← hii]
      _ = diagonalPotentialMass theta gamma hgamma +
            (diagonalPotentialMeasure theta w hw B +
              diagonalPotentialMeasure theta w hw {x : M | w x = 0}) := by rw [← hsplit]
      _ ≤ diagonalPotentialMass theta gamma hgamma +
            ((aC + bC) + diagonalPotentialMeasure theta w hw {x : M | w x = 0}) := by
          exact add_le_add le_rfl (add_le_add hBbound le_rfl)
      _ = (diagonalPotentialMass theta gamma hgamma +
            diagonalPotentialMeasure theta w hw {x : M | w x = 0}) + (aC + bC) := by ring
  exact (ENNReal.add_le_add_iff_right hfin).mp hkey

end Step2

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel
