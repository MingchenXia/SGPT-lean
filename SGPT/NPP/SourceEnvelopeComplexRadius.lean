import SGPT.NPP.SourceEnvelopeRadialFamily
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

/-!
# Actual holomorphic-exponential integrands of source-envelope smoothing

Complete blueprint: `blueprint/src/dnt-big-complex-radius.tex`, written
first. The exact Haar rotation identity puts the already defined actual
source smoothing into its holomorphic-complex-radius integral form. Each
actual integrand is jointly PSH by genuine holomorphic pullback. Joint PSH
of the actual parameter integral remains a separate averaging obligation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ}

/-- Exact unitary rotation turns the real logarithmic radius into an actual
holomorphic exponential in the same radial integral. -/
theorem radialRegularization_exp_re_eq_complexIntegral {ρ : ComplexModel n → ℝ}
    (hρ : IsRadialKernel ρ) (u : ComplexModel n → EReal) (z : ComplexModel n) (τ : ℂ) :
    radialRegularization ρ u (Real.exp τ.re) z =
      ∫ ζ, (u (z + Complex.exp τ • ζ)).toReal * ρ ζ := by
  let r : ℝ := Real.exp τ.re
  have hr : 0 < r := Real.exp_pos _
  let a : ℂ := (r : ℂ)⁻¹ * Complex.exp τ
  have ha : ‖a‖ = 1 := by
    simp only [a, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
    exact inv_mul_cancel₀ hr.ne'
  have hra : (r : ℂ) * a = Complex.exp τ := by
    dsimp only [a]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hr.ne'), one_mul]
  have hsm (ζ : ComplexModel n) : r • (a • ζ) = Complex.exp τ • ζ := by
    rw [← smul_assoc, Complex.real_smul, hra]
  have hrot := (measurePreserving_smul_of_norm_eq_one volume a ha).integral_comp
    (complexRotation a ha).toHomeomorph.measurableEmbedding
    (fun ζ : ComplexModel n => (u (z + r • ζ)).toReal * ρ ζ)
  change (∫ ζ, (u (z + r • (a • ζ))).toReal * ρ (a • ζ)) =
    ∫ ζ, (u (z + r • ζ)).toReal * ρ ζ at hrot
  simp_rw [hρ.circle_invariant a ha, hsm] at hrot
  rw [radialRegularization_eq_dilate hρ u hr]
  exact hrot.symm

/-- The actual common joint domain where the whole unit-ball kernel fits
inside the original chart domain. -/
def radialJointDomain (W : Set (ComplexModel n)) : Set (ComplexModel n × ℂ) :=
  {p | p.1 ∈ innerDomain W (Real.exp p.2.re)}

/-- Every actual exponential-radius integrand is a holomorphic pullback,
with the actual buffered-radius containment proved numerically. -/
theorem plurisubharmonicOn_complexRadiusPullback {W : Set (ComplexModel n)}
    (hW : IsOpen W) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u W)
    (ζ : ComplexModel n) (hζ : ‖ζ‖ ≤ 1) :
    PlurisubharmonicOn (fun p : ComplexModel n × ℂ => u (p.1 + Complex.exp p.2 • ζ))
      (radialJointDomain W) := by
  let e := stripModelEquiv n
  let F : ComplexModel n × ℂ → ComplexModel n := fun p => p.1 + Complex.exp p.2 • ζ
  let G : ComplexModel (n + 1) → ComplexModel n := fun q => F (e q)
  have hG : Differentiable ℂ G := e.differentiable.fst.add
    (e.differentiable.snd.cexp.smul_const ζ)
  have hp := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (hW.preimage hG.continuous) hG.differentiableOn (fun q hq => hq) hu
  have hback := hp.comp_continuousLinearMap
    (e.symm : (ComplexModel n × ℂ) →L[ℂ] ComplexModel (n + 1))
  have hfull : PlurisubharmonicOn (fun p => u (F p)) (F ⁻¹' W) := by
    convert hback using 1
    · funext p
      change u (F p) = u (F (e (e.symm p)))
      rw [e.apply_symm_apply]
    · ext p
      change F p ∈ W ↔ F (e (e.symm p)) ∈ W
      rw [e.apply_symm_apply]
  apply hfull.mono
  intro p hp
  obtain ⟨d, hrd, hdW⟩ := hp
  apply hdW
  change dist (p.1 + Complex.exp p.2 • ζ) p.1 < d
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_exp]
  have hexp := Real.exp_pos p.2.re
  nlinarith

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The literal source-envelope smoothing equals the actual
holomorphic-exponential integral, with the same background added back. -/
theorem sourceChartRadialSmoothing_exp_eq_complexIntegral {ρ : ComplexModel n → ℝ}
    (hρ : IsRadialKernel ρ) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (g : Y → ℝ) (e : ComplexChart n Y) (ψ : ComplexModel n → ℝ)
    (z : ComplexModel n) (τ : ℂ) :
    sourceChartRadialSmoothing ρ θ g e ψ (Real.exp τ.re) z + ψ z =
      ∫ ζ, (sourceEnvelopeChartPotential θ g e ψ (z + Complex.exp τ • ζ)).toReal * ρ ζ := by
  simp only [sourceChartRadialSmoothing, sub_add_cancel]
  exact radialRegularization_exp_re_eq_complexIntegral hρ _ z τ

/-- Actual source-envelope integrands have joint PSH on the common actual
radius domain; the source PSH property is produced from big-class data. -/
theorem sourceEnvelopeChartPotential_complexRadiusPullback
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    (ζ : ComplexModel n) (hζ : ‖ζ‖ ≤ 1) :
    PlurisubharmonicOn
      (fun p : ComplexModel n × ℂ =>
        sourceEnvelopeChartPotential θ g e ψ (p.1 + Complex.exp p.2 • ζ))
      (radialJointDomain W) := by
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hPn := SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg hφ
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact hPn
  have hp : PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W := by
    change PlurisubharmonicOn
      (fun z => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e z + (ψ z : EReal)) W
    exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hP.1 e hψ
  exact plurisubharmonicOn_complexRadiusPullback hψ.1 hp ζ hζ

end SGPT.NPP.DNTBig
