import SGPT.Toric.ProjectiveProductUnnormalizedEnergy
import SGPT.Okounkov.LegendreEnergyEquality

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ En
local notation "μ" => volume.restrict (euclideanUnitCube n)

/-- Original native E1 supplies both actual extended parts. Finite lintegrals
exclude both infinities before the existing real integrability theorem is used. -/
theorem projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy
    {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u)
    (hE : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n)) :
    (∀ᵐ m ∂μ, projectiveProductToricLegendre u m ≠ ⊤ ∧
      projectiveProductToricLegendre u m ≠ ⊥) ∧
    Integrable (fun m => (projectiveProductToricLegendre u m).toReal) μ := by
  have hg : Measurable (projectiveProductToricLegendre u) := measurable_conjugate B _
  have hparts := (projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_L1 hu hi).mp hE
  rw [lintegral_add_left hg.ereal_toENNReal] at hparts
  obtain ⟨hp, hn⟩ := ENNReal.add_lt_top.mp hparts
  have hfin : ∀ᵐ m ∂μ, projectiveProductToricLegendre u m ≠ ⊤ ∧
      projectiveProductToricLegendre u m ≠ ⊥ := by
    filter_upwards [ae_lt_top' hg.ereal_toENNReal.aemeasurable hp.ne,
      ae_lt_top' hg.neg.ereal_toENNReal.aemeasurable hn.ne] with m hm hm'
    refine ⟨EReal.toENNReal_ne_top_iff.mp hm.ne, ?_⟩
    have hneg := EReal.toENNReal_ne_top_iff.mp hm'.ne
    change -projectiveProductToricLegendre u m ≠ ⊤ at hneg
    intro hbot
    exact hneg (by rw [hbot, EReal.neg_bot])
  exact ⟨hfin, SGPT.Okounkov.integrable_toReal_of_finite_parts μ _ hg hfin hp hn⟩

private theorem zero_bounded : IsBoundedPotential (fun _ : X => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩
private theorem zero_invariant : ProjectiveProductCircleInvariant (fun _ : X => (0 : EReal)) :=
  fun _ _ _ => rfl

/-- Actual native finite energy equals a finite real factorial Legendre-gap
integral. The original gap and both its extended parts are retained throughout. -/
theorem projectiveProduct_energy_eq_coe_integral_of_finiteEnergy {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u)
    (hE : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n)) :
    RelativeDarvasDistance.energy (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) (isModelPotential_projectiveProductZero n) u =
      (((n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        ((projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toReal -
          (projectiveProductToricLegendre u m).toReal) : ℝ) : EReal) := by
  let G0 := projectiveProductToricLegendre (fun _ : X => (0 : EReal))
  let G := projectiveProductToricLegendre u
  let H : En → EReal := fun m => G0 m - G m
  let h : En → ℝ := fun m => (G0 m).toReal - (G m).toReal
  obtain ⟨hfin, hG⟩ := projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy hu hi hE
  have hG0 : Integrable (fun m => (G0 m).toReal) μ :=
    projectiveProductToricLegendre_integrable_of_bounded
      (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded
  have h0fin := projectiveProductToricLegendre_finite_of_bounded
    (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded
  have hH : Measurable H := (measurable_conjugate B _).sub (measurable_conjugate B _)
  have hcoe : H =ᵐ[μ] fun m => (h m : EReal) := by
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet,
      hfin] with m hm hfm
    change G0 m - G m = ((G0 m).toReal - (G m).toReal : ℝ)
    dsimp only [G0, G]
    rw [h0fin m hm, ← EReal.coe_toReal hfm.1 hfm.2]
    simp only [EReal.toReal_coe, EReal.coe_sub]
  have hHfin : ∀ᵐ m ∂μ, H m ≠ ⊤ ∧ H m ≠ ⊥ := by
    filter_upwards [hcoe] with m hm
    rw [hm]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hreal : (fun m => (H m).toReal) =ᵐ[μ] h := by
    filter_upwards [hcoe] with m hm
    rw [hm, EReal.toReal_coe]
  have hHint : Integrable (fun m => (H m).toReal) μ := (hG0.sub hG).congr hreal.symm
  have hp : (∫⁻ m, (H m).toENNReal ∂μ) < ⊤ := by
    have heq : (fun m => (H m).toENNReal) =ᵐ[μ] fun m => ENNReal.ofReal (H m).toReal := by
      filter_upwards [hcoe] with m hm
      rw [hm, EReal.toReal_coe, EReal.real_coe_toENNReal]
    rw [lintegral_congr_ae heq]
    exact hHint.lintegral_lt_top
  have hn : (∫⁻ m, (-H m).toENNReal ∂μ) < ⊤ := by
    have heq : (fun m => (-H m).toENNReal) =ᵐ[μ] fun m => ENNReal.ofReal (-(H m).toReal) := by
      filter_upwards [hcoe] with m hm
      rw [hm, EReal.toReal_coe, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    rw [lintegral_congr_ae heq]
    exact hHint.neg.lintegral_lt_top
  rw [projectiveProduct_energy_eq_extendedSignedIntegral hu hi,
    SGPT.Okounkov.signedIntegral_eq_coe_integral_of_finite_parts μ H hH hHfin hp hn,
    integral_congr_ae hreal, ← EReal.coe_mul]

/-- Real readback of the original native energy is justified by the preceding
finite extended equality, rather than by converting any infinite conjugate. -/
theorem projectiveProduct_energy_toReal_eq_integral_of_finiteEnergy {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u)
    (hE : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n)) :
    (RelativeDarvasDistance.energy (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) (isModelPotential_projectiveProductZero n) u).toReal =
      (n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        ((projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toReal -
          (projectiveProductToricLegendre u m).toReal) := by
  rw [projectiveProduct_energy_eq_coe_integral_of_finiteEnergy hu hi hE, EReal.toReal_coe]

end SGPT.Toric
