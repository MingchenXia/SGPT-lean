import SGPT.Toric.ProjectiveProductNativeRooftop
import SGPT.Toric.ProjectiveProductNativeLegendreL1

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "μ" => volume.restrict (euclideanUnitCube n)

private theorem native_ne_bot {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) : u ≠ ⊥ := by
  intro h
  let x : X := (projectiveProductCoordinates n).symm (fun _ => projectiveOrigin)
  obtain ⟨y, _, hy⟩ := hu.2 x univ isOpen_univ (mem_univ x)
  exact hy (congrFun h y)

/-- The existing native E1 rooftop theorem applies to the actual connected
product; arbitrary-native circle pullback then supplies genuine invariance. -/
theorem projectiveProductRooftop_mem_finiteEnergy_and_invariant {u v : X → EReal}
    (hEu : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n))
    (hEv : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n))
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) (rooftop (projectiveProductFSBackground n).form u v)
      (isModelPotential_projectiveProductZero n) ∧
    ProjectiveProductCircleInvariant (rooftop (projectiveProductFSBackground n).form u v) := by
  have hR := relativeFiniteEnergyPreceq_rooftop (projectiveProductFSBackground n) hEu hEv
  exact ⟨hR, projectiveProductRooftop_circleInvariant hEu.1.plurisubharmonic
    hEv.1.plurisubharmonic hiu hiv (native_ne_bot hR.1.plurisubharmonic)⟩

/-- The pointwise extended rooftop identity is read as a real maximum only
after original native E1 has supplied genuine AE finiteness of both endpoints. -/
theorem projectiveProductToricLegendre_rooftop_toReal_ae {u v : X → EReal}
    (hEu : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n))
    (hEv : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n))
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    (fun m => (projectiveProductToricLegendre (rooftop (projectiveProductFSBackground n).form u v) m).toReal)
      =ᵐ[μ] fun m => max (projectiveProductToricLegendre u m).toReal
        (projectiveProductToricLegendre v m).toReal := by
  have hR := (projectiveProductRooftop_mem_finiteEnergy_and_invariant hEu hEv hiu hiv).1
  have hmax := projectiveProductToricLegendre_rooftop hEu.1.plurisubharmonic
    hEv.1.plurisubharmonic hiu hiv (native_ne_bot hR.1.plurisubharmonic)
  have huf := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy
    hEu.1.plurisubharmonic hiu hEu).1
  have hvf := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy
    hEv.1.plurisubharmonic hiv hEv).1
  filter_upwards [huf, hvf] with m hm hn
  rw [congrFun hmax m]
  have hucoe := (EReal.coe_toReal hm.1 hm.2).symm
  have hvcoe := (EReal.coe_toReal hn.1 hn.2).symm
  conv_lhs => rw [hucoe, hvcoe]
  rcases le_total (projectiveProductToricLegendre u m).toReal
      (projectiveProductToricLegendre v m).toReal with h | h
  · simp only [max_eq_right (EReal.coe_le_coe h), EReal.toReal_coe, max_eq_right h]
  · simp only [max_eq_left (EReal.coe_le_coe h), EReal.toReal_coe, max_eq_left h]

/-- Both literal source Darvas integrands are genuinely integrable; the real
representatives here have already been produced from original extended E1 data. -/
theorem projectiveProductToricDarvas_integrands_integrable {u v : X → EReal}
    (hEu : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n))
    (hEv : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n))
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    Integrable (fun m => 2 * max (projectiveProductToricLegendre u m).toReal
        (projectiveProductToricLegendre v m).toReal -
      (projectiveProductToricLegendre u m).toReal - (projectiveProductToricLegendre v m).toReal) μ ∧
    Integrable (fun m => |(projectiveProductToricLegendre u m).toReal -
      (projectiveProductToricLegendre v m).toReal|) μ := by
  have hu := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy
    hEu.1.plurisubharmonic hiu hEu).2
  have hv := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy
    hEv.1.plurisubharmonic hiv hEv).2
  exact ⟨(((hu.sup hv).const_mul 2).sub hu).sub hv, (hu.sub hv).abs⟩

/-- The original native Darvas functional is exactly the factorial integral
of the original real Legendre maximum defect, including dimension zero. -/
theorem projectiveProduct_relativeD1_eq_legendre_max {u v : X → EReal}
    (hEu : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n))
    (hEv : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n))
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    relativeD1 (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal))
      (isModelPotential_projectiveProductZero n) u v =
      (n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        (2 * max (projectiveProductToricLegendre u m).toReal (projectiveProductToricLegendre v m).toReal -
          (projectiveProductToricLegendre u m).toReal - (projectiveProductToricLegendre v m).toReal) := by
  obtain ⟨hRE, hiR⟩ := projectiveProductRooftop_mem_finiteEnergy_and_invariant hEu hEv hiu hiv
  have hu := hEu.1.plurisubharmonic
  have hv := hEv.1.plurisubharmonic
  have hR := hRE.1.plurisubharmonic
  have hIu := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy hu hiu hEu).2
  have hIv := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy hv hiv hEv).2
  have hIR := (projectiveProductToricLegendre_ae_finite_and_integrable_of_finiteEnergy hR hiR hRE).2
  have hI0 := projectiveProductToricLegendre_integrable_of_bounded
    (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl)
    (show IsBoundedPotential (fun _ : X => (0 : EReal)) from ⟨0, 0, fun _ => by simp⟩)
  have hIM : Integrable (fun m => max (projectiveProductToricLegendre u m).toReal
      (projectiveProductToricLegendre v m).toReal) μ := hIu.sup hIv
  have hItwo : Integrable (fun m => 2 * max (projectiveProductToricLegendre u m).toReal
      (projectiveProductToricLegendre v m).toReal) μ := hIM.const_mul 2
  have hIsub : Integrable (fun m => 2 * max (projectiveProductToricLegendre u m).toReal
      (projectiveProductToricLegendre v m).toReal - (projectiveProductToricLegendre u m).toReal) μ :=
    hItwo.sub hIu
  have hRM := integral_congr_ae (projectiveProductToricLegendre_rooftop_toReal_ae hEu hEv hiu hiv)
  rw [relativeD1,
    projectiveProduct_energy_toReal_eq_integral_of_finiteEnergy hu hiu hEu,
    projectiveProduct_energy_toReal_eq_integral_of_finiteEnergy hv hiv hEv,
    projectiveProduct_energy_toReal_eq_integral_of_finiteEnergy hR hiR hRE,
    integral_sub hI0 hIu, integral_sub hI0 hIv, integral_sub hI0 hIR, hRM,
    integral_sub hIsub hIv,
    integral_sub hItwo hIu, integral_const_mul]
  ring

/-- The actual original native product Darvas distance equals n! times the
L1 distance of its genuine Legendre representatives on the actual unit cube. -/
theorem projectiveProduct_relativeD1_eq_legendre_L1 {u v : X → EReal}
    (hEu : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n))
    (hEv : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n))
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    relativeD1 (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal))
      (isModelPotential_projectiveProductZero n) u v =
      (n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        |(projectiveProductToricLegendre u m).toReal - (projectiveProductToricLegendre v m).toReal| := by
  rw [projectiveProduct_relativeD1_eq_legendre_max hEu hEv hiu hiv]
  congr 1
  apply setIntegral_congr_fun (isCompact_euclideanUnitCube n).isClosed.measurableSet
  intro m _
  have h := max_add_min (projectiveProductToricLegendre u m).toReal
    (projectiveProductToricLegendre v m).toReal
  dsimp only
  have hab := max_sub_min_eq_abs (projectiveProductToricLegendre u m).toReal
    (projectiveProductToricLegendre v m).toReal
  rw [abs_sub_comm] at hab
  linarith

end SGPT.Toric
