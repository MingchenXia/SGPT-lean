import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel
import SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-!
# The truncation-limit bridge for Xia's rooftop mass diamond

This module supplies the hypotheses called `htrunc`, `htrunc0`, and `hL1` by
`Pending.RooftopMassDiamondLimit.model_mass_diamond_of_truncation_limit`.
For model potentials `phi`, `psi`, the finite-level rooftops

`P_theta(min {phi \/ (gamma - (j+1)), psi \/ (gamma - (j+1))})`

are genuine nonpositive theta-PSH potentials.  They decrease to
`P_theta(min {phi, psi})`; the exact pointwise infimum is proved using the
common lower competitor `P_theta(min {phi, psi})`, the obstacle-recovery
inequality for a minimum of theta-PSH functions, and closure of theta-PSH
functions under decreasing infima.  The chart-local `L¹` conclusion then uses
the proven decreasing-family theorem, rather than a new analytic interface.

Source: Xia, *Singularities in Global Pluripotential Theory*, the final
`C -> infinity` passage in the proof of Theorem 3.1.3
(`xia-sgpt:page-0109`).
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
open SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- The finite model rooftops, kept under a local name so this analytic bridge
does not need to import the endpoint mass inequality.  It is definitionally
the same expression as `RooftopMassDiamondLimit.modelTruncationRooftop`; a
thin integration module can identify the names without re-elaborating this
proof. -/
def modelTruncationRooftopData (theta : ClosedRealOneOneForm n M)
    (phi psi : M → EReal) (j : ℕ) : M → EReal :=
  truncRooftop theta.val (fun x => max (phi x) (psi x)) phi psi ((j : ℝ) + 1)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- At zero translation, the shifted two-obstacle expression used by the
rooftop comparison API is the unshifted minimum. -/
private theorem min_add_zero (u v : M → EReal) :
    (fun x => min (u x) (v x + ((0 : ℝ) : EReal))) = fun x => min (u x) (v x) := by
  funext x
  rw [EReal.coe_zero, add_zero]

/-- The model-potential normalization makes each input and their maximum
nonpositive. -/
theorem model_potentials_le_zero
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi) :
    (∀ x, phi x ≤ 0) ∧ (∀ x, psi x ≤ 0) ∧
      ∀ x, max (phi x) (psi x) ≤ 0 := by
  have hphi0 : ∀ x, phi x ≤ 0 := by
    intro x
    rw [hphimodel]
    exact singularityEnvelope_le_zero theta.val phi x
  have hpsi0 : ∀ x, psi x ≤ 0 := by
    intro x
    rw [hpsimodel]
    exact singularityEnvelope_le_zero theta.val psi x
  exact ⟨hphi0, hpsi0, fun x => max_le (hphi0 x) (hpsi0 x)⟩

/-- The translate `gamma - C` is a common theta-PSH lower competitor for both
truncated obstacles. -/
theorem model_truncation_rooftop_isThetaPshPotential
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (j : ℕ) :
    IsThetaPshPotential theta.val (modelTruncationRooftopData theta phi psi j) := by
  let gamma : M → EReal := fun x => max (phi x) (psi x)
  let C : ℝ := (j : ℝ) + 1
  have hgamma : IsThetaPshPotential theta.val gamma := hmax
  have hphiC : IsThetaPshPotential theta.val (truncAt gamma C phi) :=
    isThetaPshPotential_truncAt hgamma hphi C
  have hpsiC : IsThetaPshPotential theta.val (truncAt gamma C psi) :=
    isThetaPshPotential_truncAt hgamma hpsi C
  have hlow : IsThetaPshPotential theta.val
      (fun x => gamma x + ((-C : ℝ) : EReal)) := hgamma.add_const _
  have hmem : (fun x => gamma x + ((-C : ℝ) : EReal)) ∈
      rooftopCompetitors theta.val (fun x => min (truncAt gamma C phi x)
        (truncAt gamma C psi x)) := by
    refine mem_rooftopCompetitors_of_le hlow ?_
    intro x
    exact le_min (shifted_le_truncAt gamma C phi x)
      (shifted_le_truncAt gamma C psi x)
  change IsThetaPshPotential theta.val
    (rooftopEnvelope theta.val (fun x => min (truncAt gamma C phi x)
      (truncAt gamma C psi x)))
  apply isThetaPshPotential_rooftop_of_nonempty
  · exact ⟨_, hmem⟩
  · rw [← min_add_zero]
    exact rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta
      (truncAt gamma C phi) (truncAt gamma C psi) hphiC 0

/-- Every finite model truncation rooftop lies below zero. -/
theorem model_truncation_rooftop_le_zero
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (j : ℕ) (x : M) : modelTruncationRooftopData theta phi psi j x ≤ 0 := by
  obtain ⟨hphi0, hpsi0, hgamma0⟩ :=
    model_potentials_le_zero theta hphimodel hpsimodel
  let gamma : M → EReal := fun x => max (phi x) (psi x)
  let C : ℝ := (j : ℝ) + 1
  have hgamma : IsThetaPshPotential theta.val gamma := hmax
  have hphiC : IsThetaPshPotential theta.val (truncAt gamma C phi) :=
    isThetaPshPotential_truncAt hgamma hphi C
  have hpsiC : IsThetaPshPotential theta.val (truncAt gamma C psi) :=
    isThetaPshPotential_truncAt hgamma hpsi C
  have hphiCle : truncAt gamma C phi x ≤ 0 := by
    refine max_le (hphi0 x) ?_
    calc gamma x + ((-C : ℝ) : EReal) ≤ 0 + ((-C : ℝ) : EReal) :=
          add_le_add (hgamma0 x) le_rfl
      _ = ((-C : ℝ) : EReal) := zero_add _
      _ ≤ 0 := by
        exact_mod_cast neg_nonpos.mpr (by dsimp [C]; positivity)
  have hroof := rooftopEnvelope_min_add_const_le_obstacles hphiC.1 hpsiC.1 0
  rw [min_add_zero] at hroof
  change rooftopEnvelope theta.val
    (fun y => min (truncAt gamma C phi y) (truncAt gamma C psi y)) x ≤ 0
  exact (hroof.1 x).trans hphiCle

/-- Truncating at a larger level only lowers the truncated potential. -/
theorem truncAt_antitone_level (gamma u : M → EReal) :
    Antitone (fun C : ℝ => truncAt gamma C u) := by
  intro C D hCD x
  refine max_le_max le_rfl (add_le_add le_rfl ?_)
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg hCD)

/-- The finite model truncation rooftops form a pointwise decreasing sequence. -/
theorem modelTruncationRooftopData_antitone
    (theta : ClosedRealOneOneForm n M) (phi psi : M → EReal) :
    Antitone (modelTruncationRooftopData theta phi psi) := by
  intro j k hjk x
  change rooftopEnvelope theta.val
      (fun y => min (truncAt (fun z => max (phi z) (psi z)) ((k : ℝ) + 1) phi y)
        (truncAt (fun z => max (phi z) (psi z)) ((k : ℝ) + 1) psi y)) x ≤
    rooftopEnvelope theta.val
      (fun y => min (truncAt (fun z => max (phi z) (psi z)) ((j : ℝ) + 1) phi y)
        (truncAt (fun z => max (phi z) (psi z)) ((j : ℝ) + 1) psi y)) x
  apply rooftopEnvelope_mono
  intro y
  refine min_le_min (truncAt_antitone_level _ _ ?_ y)
    (truncAt_antitone_level _ _ ?_ y)
  · simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hjk) (1 : ℝ)
  · simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hjk) (1 : ℝ)

/-- The truncations of either model input decrease to that input.  The only
order input is `gamma ≤ 0`, supplied by model normalization. -/
theorem iInf_model_truncAt_eq
    (gamma u : M → EReal) (hgamma0 : ∀ x, gamma x ≤ 0) (x : M) :
    (⨅ j : ℕ, truncAt gamma ((j : ℝ) + 1) u x) = u x := by
  refine le_antisymm ?_ (le_iInf fun j => le_max_left _ _)
  refine le_of_le_of_eq (iInf_mono fun j => ?_)
    (SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit.iInf_max_neg_natCast (u x))
  change max (u x) (gamma x + ((-((j : ℝ) + 1) : ℝ) : EReal)) ≤
    max (u x) ((-(j : ℝ) : ℝ) : EReal)
  refine max_le_max le_rfl ?_
  calc gamma x + ((-((j : ℝ) + 1) : ℝ) : EReal)
      ≤ 0 + ((-((j : ℝ) + 1) : ℝ) : EReal) := add_le_add (hgamma0 x) le_rfl
    _ = ((-((j : ℝ) + 1) : ℝ) : EReal) := zero_add _
    _ ≤ ((-(j : ℝ) : ℝ) : EReal) := by
      exact_mod_cast (by linarith : -((j : ℝ) + 1) ≤ -(j : ℝ))

/-- The pointwise infimum of the model truncation rooftops is the ordinary
rooftop.  The proof uses no bigness assumption: the lower limit is a genuine
theta-PSH function because the ordinary rooftop is a common lower barrier. -/
theorem iInf_modelTruncationRooftopData_eq_rooftop
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) =
      rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) := by
  obtain ⟨hphi0, hpsi0, hgamma0⟩ :=
    model_potentials_le_zero theta hphimodel hpsimodel
  let gamma : M → EReal := fun x => max (phi x) (psi x)
  let w : M → EReal := rooftopEnvelope theta.val (fun x => min (phi x) (psi x))
  have htrunc : ∀ j, IsThetaPshPotential theta.val
      (modelTruncationRooftopData theta phi psi j) :=
    model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax
  have hanti : Antitone (modelTruncationRooftopData theta phi psi) :=
    modelTruncationRooftopData_antitone theta phi psi
  have hwphi : w ≤ phi := by
    intro x
    dsimp [w]
    have hobs := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    rw [min_add_zero] at hobs
    exact hobs.1 x
  have hwpsi : w ≤ psi := by
    intro x
    dsimp [w]
    have hobs := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    rw [min_add_zero] at hobs
    simpa only [EReal.coe_zero, add_zero] using hobs.2 x
  have hwle : ∀ j, w ≤ modelTruncationRooftopData theta phi psi j := by
    intro j
    apply le_rooftopEnvelope hroof
    refine quasiEverywhere_of_forall fun x => ?_
    change w x ≤ min (truncAt gamma ((j : ℝ) + 1) phi x)
      (truncAt gamma ((j : ℝ) + 1) psi x)
    exact le_min ((hwphi x).trans (le_max_left _ _))
      ((hwpsi x).trans (le_max_left _ _))
  have hWphi : (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) ≤ phi := by
    intro x
    rw [iInf_apply]
    calc (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j x)
        ≤ ⨅ j : ℕ, truncAt gamma ((j : ℝ) + 1) phi x := by
          refine le_iInf fun j => ?_
          have hobs := rooftopEnvelope_min_add_const_le_obstacles
            (isThetaPshPotential_truncAt hmax hphi ((j : ℝ) + 1)).1
            (isThetaPshPotential_truncAt hmax hpsi ((j : ℝ) + 1)).1 0
          rw [min_add_zero] at hobs
          have hstep : modelTruncationRooftopData theta phi psi j x ≤
              truncAt gamma ((j : ℝ) + 1) phi x := by
            change rooftopEnvelope theta.val
                (fun y => min (truncAt gamma ((j : ℝ) + 1) phi y)
                  (truncAt gamma ((j : ℝ) + 1) psi y)) x ≤
                truncAt gamma ((j : ℝ) + 1) phi x
            exact hobs.1 x
          exact (iInf_le (fun j : ℕ => modelTruncationRooftopData theta phi psi j x) j).trans
            hstep
      _ = phi x := iInf_model_truncAt_eq gamma phi hgamma0 x
  have hWpsi : (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) ≤ psi := by
    intro x
    rw [iInf_apply]
    calc (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j x)
        ≤ ⨅ j : ℕ, truncAt gamma ((j : ℝ) + 1) psi x := by
          refine le_iInf fun j => ?_
          have hobs := rooftopEnvelope_min_add_const_le_obstacles
            (isThetaPshPotential_truncAt hmax hphi ((j : ℝ) + 1)).1
            (isThetaPshPotential_truncAt hmax hpsi ((j : ℝ) + 1)).1 0
          rw [min_add_zero] at hobs
          have hstep : modelTruncationRooftopData theta phi psi j x ≤
              truncAt gamma ((j : ℝ) + 1) psi x := by
            change rooftopEnvelope theta.val
                (fun y => min (truncAt gamma ((j : ℝ) + 1) phi y)
                  (truncAt gamma ((j : ℝ) + 1) psi y)) x ≤
                truncAt gamma ((j : ℝ) + 1) psi x
            simpa only [EReal.coe_zero, add_zero] using hobs.2 x
          exact (iInf_le (fun j : ℕ => modelTruncationRooftopData theta phi psi j x) j).trans
            hstep
      _ = psi x := iInf_model_truncAt_eq gamma psi hgamma0 x
  have hWpsh : ThetaPlurisubharmonic theta.val
      (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) := by
    have hiInf : (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) =
        fun x => ⨅ j : ℕ, modelTruncationRooftopData theta phi psi j x := by
      ext x
      simp only [iInf_apply]
    rw [hiInf]
    exact thetaPlurisubharmonic_iInf_of_antitone (fun j => (htrunc j).1)
      (fun x j k hjk => hanti hjk x)
  have hWlower : w ≤ ⨅ j : ℕ, modelTruncationRooftopData theta phi psi j := by
    intro x
    rw [iInf_apply]
    exact le_iInf fun j => hwle j x
  have hWpot : IsThetaPshPotential theta.val
      (⨅ j : ℕ, modelTruncationRooftopData theta phi psi j) :=
    ⟨hWpsh, hroof.2.mono hWlower⟩
  apply le_antisymm ?_ ?_
  · apply le_rooftopEnvelope hWpot
    refine quasiEverywhere_of_forall fun x => le_min (hWphi x) (hWpsi x)
  · exact hWlower

/-- The full finite-truncation bridge needed at the endpoint of Xia's model
mass-diamond argument. -/
theorem modelTruncationRooftopData_limit_bridge
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    (∀ j, IsThetaPshPotential theta.val (modelTruncationRooftopData theta phi psi j)) ∧
    (∀ j x, modelTruncationRooftopData theta phi psi j x ≤ 0) ∧
    ManifoldL1LocallyTendsto (n := n) (modelTruncationRooftopData theta phi psi) atTop
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) := by
  have htrunc : ∀ j, IsThetaPshPotential theta.val
      (modelTruncationRooftopData theta phi psi j) :=
    model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax
  refine ⟨htrunc, fun j x =>
    model_truncation_rooftop_le_zero theta hphi hpsi hphimodel hpsimodel hmax j x, ?_⟩
  apply manifoldL1LocallyTendsto_of_antitone_iInf htrunc
    (modelTruncationRooftopData_antitone theta phi psi) hroof
  exact iInf_modelTruncationRooftopData_eq_rooftop theta hphi hpsi hphimodel hpsimodel hmax hroof

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge
