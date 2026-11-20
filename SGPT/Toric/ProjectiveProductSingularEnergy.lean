import SGPT.Toric.ProjectiveProductNativeTruncation
import SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ En

private theorem zero_bounded : IsBoundedPotential (fun _ : X => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩
private theorem zero_invariant : ProjectiveProductCircleInvariant (fun _ : X => (0 : EReal)) :=
  fun _ _ _ => rfl

private theorem profile_coe_eq {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) =
      projectiveProductToricCorrectedDescent u := by
  funext x
  have hf := finite_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi) x
  exact EReal.coe_toReal hf.1 hf.2

private theorem legendre_zero_le_of_nonpos {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    projectiveProductToricLegendre (fun _ : X => (0 : EReal)) ≤ projectiveProductToricLegendre u := by
  apply conjugate_antitone B
  rw [profile_coe_eq hu hi, profile_coe_eq (isThetaPshPotential_projectiveProductZero n) zero_invariant]
  intro x
  exact add_le_add (hle _) le_rfl

private theorem coe_iSup_ennreal (a : ℕ → ℝ≥0∞) :
    (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) = ⨆ j : ℕ, (a j : EReal) := by
  let s : EReal := ⨆ j : ℕ, (a j : EReal)
  have hs : 0 ≤ s := (EReal.coe_ennreal_nonneg (a 0)).trans
    (le_iSup (fun j : ℕ => (a j : EReal)) 0)
  have hall : ∀ j, a j ≤ s.toENNReal := by
    intro j
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (le_iSup (fun i : ℕ => (a i : EReal)) j)
  apply le_antisymm
  · have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iSup_le hall)
    rwa [EReal.coe_toENNReal hs] at h
  · exact iSup_le (fun j => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

private theorem iInf_neg_coe_ennreal (a : ℕ → ℝ≥0∞) :
    (⨅ j : ℕ, -(a j : EReal)) = -(((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · have hall : ∀ j : ℕ, (a j : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      intro j
      simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr (iInf_le (fun i => -(a i : EReal)) j)
    have h : (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      rw [coe_iSup_ennreal]
      exact iSup_le hall
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr h
  · apply le_iInf
    intro j
    exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

private theorem bounded_energy_eq_neg_gap {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hb : IsBoundedPotential u)
    (hle : u ≤ fun _ => (0 : EReal)) :
    (relativeEnergyOfMinimalType (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isThetaPshPotential_projectiveProductZero n) hu : EReal) =
        -((((n.factorial : ENNReal) * ∫⁻ m in euclideanUnitCube n,
          (projectiveProductToricLegendre u m -
            projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) : ENNReal) : EReal) := by
  let q : En → ℝ := fun m => (projectiveProductToricLegendre u m).toReal -
    (projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toReal
  have iq : Integrable q (volume.restrict (euclideanUnitCube n)) :=
    (projectiveProductToricLegendre_integrable_of_bounded hu hi hb).sub
      (projectiveProductToricLegendre_integrable_of_bounded
        (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded)
  have hf := projectiveProductToricLegendre_finite_of_bounded hu hi hb
  have h0 := projectiveProductToricLegendre_finite_of_bounded
    (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded
  have hqn : 0 ≤ᵐ[volume.restrict (euclideanUnitCube n)] q := by
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet] with m hm
    have h := legendre_zero_le_of_nonpos hu hi hle m
    rw [hf m hm, h0 m hm, EReal.coe_le_coe_iff] at h
    exact sub_nonneg.mpr h
  have hlin : (∫⁻ m in euclideanUnitCube n,
      (projectiveProductToricLegendre u m -
        projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) =
      ∫⁻ m, ENNReal.ofReal (q m) ∂volume.restrict (euclideanUnitCube n) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet] with m hm
    rw [hf m hm, h0 m hm, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hiq : 0 ≤ ∫ m, q m ∂volume.restrict (euclideanUnitCube n) := integral_nonneg_of_ae hqn
  have hcoe : (((∫⁻ m in euclideanUnitCube n,
      (projectiveProductToricLegendre u m -
        projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) : ENNReal) : EReal) =
      (((∫ m, q m ∂volume.restrict (euclideanUnitCube n)) : ℝ) : EReal) := by
    rw [hlin, ← ofReal_integral_eq_lintegral_ofReal iq hqn]
    simpa only [EReal.real_coe_toENNReal] using EReal.coe_toENNReal (EReal.coe_nonneg.mpr hiq)
  have hcn : (((n.factorial : ℝ) : EReal)) = ((n.factorial : ENNReal) : EReal) := by
    simpa only [ENNReal.toReal_natCast] using
      (EReal.coe_ennreal_toReal (x := (n.factorial : ENNReal)) (by simp))
  rw [projectiveProduct_relativeEnergyOfMinimalType_zero_eq_legendre hu hi hb,
    EReal.coe_ennreal_mul, ← hcn, hcoe]
  rw [show (fun m => (projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toReal -
    (projectiveProductToricLegendre u m).toReal) = fun m => -q m from by funext m; dsimp [q]; ring,
    integral_neg, ← EReal.coe_mul, ← EReal.coe_neg]
  congr 1
  ring

/-- Actual native inf-majorant energy and manufactured native truncations give
the true normalized singular energy, with literal n! and all infinite gaps retained. -/
theorem projectiveProduct_energy_eq_neg_gap_lintegral_of_nonpos {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeDarvasDistance.energy (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) (isModelPotential_projectiveProductZero n) u =
        -((((n.factorial : ENNReal) * ∫⁻ m in euclideanUnitCube n,
          (projectiveProductToricLegendre u m -
            projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) : ENNReal) : EReal) := by
  have hrel : RelativePSH (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal)) u :=
    ⟨hu, hle⟩
  have hInf := MongeAmpereEnergyDecreasing.relativeMongeAmpereEnergy_eq_iInf_truncation
    (projectiveProductFSBackground n) (projectiveProductFSBackground n).form
    (isModelPotential_projectiveProductZero n) hrel zero_bounded
  have hcut (j : ℕ) : MongeAmpereEnergyDecreasing.truncation
      (fun _ : X => (0 : EReal)) u j = projectiveProductToricTruncation u j := by
    funext p
    simp only [MongeAmpereEnergyDecreasing.truncation, projectiveProductToricTruncation,
      zero_sub, ← EReal.coe_neg]
  calc
    _ = ⨅ j : ℕ, (relativeEnergyOfMinimalType (projectiveProductFSBackground n).form
        (fun _ : X => (0 : EReal)) (projectiveProductToricTruncation u j)
        (isThetaPshPotential_projectiveProductZero n)
        (isThetaPshPotential_projectiveProductToricTruncation hu j) : EReal) := by
      rw [RelativeDarvasDistance.energy_eq hrel, hInf]
      apply iInf_congr
      intro j
      congr 1
      exact RelativePreceqClasses.relativeEnergyOfMinimalType_congr _ (hcut j) _ _
    _ = ⨅ j : ℕ, -((((n.factorial : ENNReal) * ∫⁻ m in euclideanUnitCube n,
        (projectiveProductToricLegendre (projectiveProductToricTruncation u j) m -
          projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) : ENNReal) : EReal) := by
      apply iInf_congr
      intro j
      exact bounded_energy_eq_neg_gap (isThetaPshPotential_projectiveProductToricTruncation hu j)
        (projectiveProductCircleInvariant_truncation hi j)
        (isBoundedPotential_projectiveProductToricTruncation hle j)
        (fun p => max_le (hle p) (EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg j))))
    _ = -(((⨆ j : ℕ, (n.factorial : ENNReal) * ∫⁻ m in euclideanUnitCube n,
        (projectiveProductToricLegendre (projectiveProductToricTruncation u j) m -
          projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) : ENNReal) : EReal) :=
      iInf_neg_coe_ennreal _
    _ = _ := by
      rw [← ENNReal.mul_iSup, ← projectiveProductToricLegendre_gap_lintegral_eq_iSup_truncation hu hi]

end SGPT.Toric
