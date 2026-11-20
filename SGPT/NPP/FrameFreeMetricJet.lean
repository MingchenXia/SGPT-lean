import SGPT.NPP.MetricJetUnitaryFrame
import SGPT.Envelopes.TosC11cMetric
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Actual quadratic metric jets without varying normalizing frames

Auxiliary producer for the DNT23 smoothing route. The coefficient below is
the literal inverse metric applied to its actual Koszul covector. Its joint
smoothness and coordinate law are properties of this same formula, not
assumed curvature or overlap bounds. The polynomial jet is kept distinct
from Demailly's full formal holomorphic Chern exponential.

Blueprint: `dnt-big-frame-free-metric-jet.tex`.
-/

set_option autoImplicit false
-- Three nested continuous-linear-map spaces occur in the actual metric derivative.
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.PSH.VariableComplexAtlas
open SGPT.Analysis.CZ
open SGPT.Analysis.KahlerNormal
open SGPT.Envelopes

variable {n : ℕ}

/-- The literal covector of the actual derivative of a metric. -/
def metricKoszulCovector
    (D : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (p u : ComplexModel n) : ComplexModel n →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (D p u + D u p - (D.flip p).flip u)

@[simp] theorem metricKoszulCovector_apply
    (D : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (p u v : ComplexModel n) :
    metricKoszulCovector D p u v = (D p u v + D u p v - D v p u) / 2 := by
  simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

/-- The actual inverse metric applied to the actual Koszul covector. -/
def metricConnection
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z p u : ComplexModel n) : ComplexModel n :=
  TosC11c.gradVec (g z) (metricKoszulCovector (fderiv ℝ g z) p u)

/-- The same explicit local quadratic metric jet in the chart tangent vector. -/
def metricQuadraticJet
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z ζ : ComplexModel n) : ComplexModel n :=
  z + ζ - (1 / 2 : ℝ) • metricConnection g z ζ ζ

/-- The actual positive inverse metric represents the existing actual Koszul form. -/
theorem metricConnection_pairing
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {z : ComplexModel n} (hg : DifferentiableAt ℝ g z)
    (hpos : ∀ v, v ≠ 0 → 0 < g z v v) (p u v : ComplexModel n) :
    g z v (metricConnection g z p u) = TosC11b.koszul g z p u v := by
  rw [metricConnection, TosC11c.apply_gradVec hpos, metricKoszulCovector_apply,
    TosC11c.koszul_eq hg]

/-- Joint smoothness of the actual coefficient, obtained by smooth actual
inverse-metric evaluation rather than a varying choice of normalizing frame. -/
theorem contDiffOn_metricConnection
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hpos : ∀ z ∈ U, ∀ v, v ≠ 0 → 0 < g z v v) :
    ContDiffOn ℝ ∞ (fun q : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      metricConnection g q.1 q.2.1 q.2.2) (U ×ˢ univ) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
  intro q hq
  have hz : q.1 ∈ U := hq.1
  have hgq : ContDiffAt ℝ ∞ (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      g t.1) q := (hg.contDiffAt (hU.mem_nhds hz)).comp q contDiffAt_fst
  have hDq : ContDiffAt ℝ ∞ (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      fderiv ℝ g t.1) q := (hD.contDiffAt (hU.mem_nhds hz)).comp q contDiffAt_fst
  have hp : ContDiffAt ℝ ∞ (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      t.2.1) q := contDiffAt_fst.comp q contDiffAt_snd
  have hu : ContDiffAt ℝ ∞ (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      t.2.2) q := contDiffAt_snd.comp q contDiffAt_snd
  have hflip : ContDiffAt ℝ ∞ (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
      (g t.1).flip) q :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.contDiff.contDiffAt.comp q hgq
  have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (g q.1).flip := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)
      (TosC11c.flipEquiv (g q.1) (hpos q.1 hz))
    rwa [TosC11c.coe_flipEquiv] at h
  have hDflip : ContDiffAt ℝ ∞
      (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
        (fderiv ℝ g t.1).flip) q :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n)
      (ComplexModel n →L[ℝ] ℝ)).toContinuousLinearEquiv.contDiff.contDiffAt.comp q hDq
  have hDpflip : ContDiffAt ℝ ∞
      (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
        ((fderiv ℝ g t.1).flip t.2.1).flip) q :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.contDiff.contDiffAt.comp q (hDflip.clm_apply hp)
  have hL : ContDiffAt ℝ ∞
      (fun t : ComplexModel n × (ComplexModel n × ComplexModel n) =>
        metricKoszulCovector (fderiv ℝ g t.1) t.2.1 t.2.2) q := by
    exact (((hDq.clm_apply hp).clm_apply hu).add
      ((hDq.clm_apply hu).clm_apply hp) |>.sub (hDpflip.clm_apply hu)).const_smul _
  exact ((hinv.comp q hflip).clm_apply hL).contDiffWithinAt

/-- The actual polynomial metric jet is smooth in the actual base and tangent variables. -/
theorem contDiffOn_metricQuadraticJet
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hpos : ∀ z ∈ U, ∀ v, v ≠ 0 → 0 < g z v v) :
    ContDiffOn ℝ ∞ (fun q : ComplexModel n × ComplexModel n =>
      metricQuadraticJet g q.1 q.2) (U ×ˢ univ) := by
  have hΓ := contDiffOn_metricConnection hU hg hpos
  have hdiag : ContDiffOn ℝ ∞
      (fun q : ComplexModel n × ComplexModel n => (q.1, (q.2, q.2))) (U ×ˢ univ) :=
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_snd)).contDiffOn
  have hcomp := hΓ.comp hdiag (fun q hq => ⟨hq.1, mem_univ _⟩)
  exact (contDiff_fst.contDiffOn.add contDiff_snd.contDiffOn).sub (hcomp.const_smul _)

/-- The actual inverse-metric coefficient obeys the actual Koszul coordinate law. -/
theorem metricConnection_pullback
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {w : ComplexModel n}
    (hg : DifferentiableAt ℝ g (φ w))
    (hpos : ∀ v, v ≠ 0 → 0 < g (φ w) v v)
    (hsym : ∀ v t, g (φ w) v t = g (φ w) t v)
    (hφ : ContDiffAt ℝ 2 φ w)
    (L : ComplexModel n ≃L[ℝ] ComplexModel n)
    (hL : fderiv ℝ φ w = L.toContinuousLinearMap) (p u : ComplexModel n) :
    L (metricConnection (TosC11b.pullbackBilin g φ) w p u) =
      metricConnection g (φ w) (L p) (L u) + fderiv ℝ (fderiv ℝ φ) w p u := by
  have hφ1 : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgc := hg.comp w hφ1
  have hflip1 : DifferentiableAt ℝ
      (fun x => ((g (φ x)).comp (fderiv ℝ φ x)).flip) w :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.differentiableAt.comp w
      (hgc.clm_comp hφ2)
  have hpb : DifferentiableAt ℝ (TosC11b.pullbackBilin g φ) w :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.differentiableAt.comp w
      (hflip1.clm_comp hφ2)
  have hpbpos : ∀ v, v ≠ 0 → 0 < TosC11b.pullbackBilin g φ w v v := by
    intro v hv
    change 0 < g (φ w) (fderiv ℝ φ w v) (fderiv ℝ φ w v)
    rw [hL]
    apply hpos
    simpa using L.injective.ne hv
  apply (TosC11c.flip_bijective hpos).1
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨t, rfl⟩ := L.surjective v
  change g (φ w) (L t) (L (metricConnection (TosC11b.pullbackBilin g φ) w p u)) =
    g (φ w) (L t) (metricConnection g (φ w) (L p) (L u) +
      fderiv ℝ (fderiv ℝ φ) w p u)
  have hp := metricConnection_pairing hpb hpbpos p u t
  change g (φ w) (fderiv ℝ φ w t)
    (fderiv ℝ φ w (metricConnection (TosC11b.pullbackBilin g φ) w p u)) = _ at hp
  rw [hL] at hp
  calc
    _ = TosC11b.koszul (TosC11b.pullbackBilin g φ) w p u t := by
      simpa only [ContinuousLinearEquiv.coe_coe] using hp
    _ = _ := by
      rw [TosC11b.koszul_pullback hg hsym hφ, hL]
      simp only [ContinuousLinearEquiv.coe_coe]
      rw [map_add, metricConnection_pairing hg hpos,
        hsym (fderiv ℝ (fderiv ℝ φ) w p u) (L t)]

/-- The literal inverse-metric coefficient is the existing actual metric-derived
normal-coordinate coefficient in every supplied actual normalizing frame. -/
theorem metricConnection_normalQuad
    {α : ComplexModel n → CoordinateRealTwoForm n} {z : ComplexModel n}
    (hα : DifferentiableAt ℝ α z) (h11 : ∀ᶠ x in 𝓝 z, IsOneOne (α x))
    (hcl : extDeriv α z = 0)
    (hpos : ∀ v, v ≠ 0 → 0 < α z ![v, Complex.I • v])
    (A : ComplexModel n ≃L[ℂ] ComplexModel n)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) (p u : ComplexModel n) :
    metricConnection (fun x => TosC11c.twoFormMetric (α x)) z (A p) (A u) =
      A (normalQuad (normalizedDeriv α z A) (normalizedDeriv_isOneOne hα h11 A) p u) := by
  let c := normalQuad (normalizedDeriv α z A) (normalizedDeriv_isOneOne hα h11 A)
  let Φ := normalCoord z (A : ComplexModel n →L[ℂ] ComplexModel n) c
  let g := fun x => TosC11c.twoFormMetric (α x)
  have hc : ∀ p u v, inner ℂ v (c p u) =
      (Real.pi : ℂ) * dHol (normalizedDeriv α z A) p u v := by
    intro p u v
    exact inner_quadFun _ _ _ _
  have hnormal := kahlerNormal_of_normalizing z
    (A : ComplexModel n →L[ℂ] ComplexModel n) c hα h11 hcl hA hc
  have hsymc := hnormal.1
  have hΦ : ContDiff ℝ 2 Φ := by
    have hq : ContDiff ℂ 2 (fun v : ComplexModel n => c v v) :=
      c.contDiff.clm_apply contDiff_id
    have h : ContDiff ℂ 2 Φ :=
      contDiff_const.add (A.contDiff.comp (contDiff_id.sub (hq.const_smul (1 / 2 : ℂ))))
    exact h.restrict_scalars ℝ
  have hpbEq : TosC11b.pullbackBilin g Φ =
      fun v => TosC11c.twoFormMetric (pullbackField Φ α v) := by
    funext v
    apply ContinuousLinearMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro b
    simp only [TosC11b.pullbackBilin_apply, g, TosC11c.twoFormMetric_apply,
      pullbackField, compContinuousLinearMap_apply_two]
    simp only [Φ, fderiv_normalCoord z _ c hsymc, ContinuousLinearMap.coe_restrictScalars',
      map_smul]
  have hmetric0 : HasFDerivAt (TosC11b.pullbackBilin g Φ)
      (0 : ComplexModel n →L[ℝ] _) 0 := by
    rw [hpbEq]
    have h := TosC11c.isBoundedLinearMap_twoFormMetric.hasFDerivAt.comp 0 hnormal.2.2
    simpa only [ContinuousLinearMap.comp_zero, Function.comp_def, Φ] using h
  have hΓ0 : metricConnection (TosC11b.pullbackBilin g Φ) 0 p u = 0 := by
    unfold metricConnection
    rw [hmetric0.fderiv]
    simp [metricKoszulCovector, TosC11c.gradVec]
  have hD0 : fderiv ℝ Φ 0 = (A.restrictScalars ℝ).toContinuousLinearMap := by
    simp only [Φ, fderiv_normalCoord z _ c hsymc]
    apply ContinuousLinearMap.ext
    intro v
    simp
  have hD20 : fderiv ℝ (fderiv ℝ Φ) 0 p u = -(A (c p u)) := by
    rw [show Φ = normalCoord z (A : ComplexModel n →L[ℂ] ComplexModel n) c from rfl,
      (hasFDerivAt_fderiv_normalCoord z _ c hsymc 0).fderiv]
    rfl
  have hg : DifferentiableAt ℝ g z :=
    TosC11c.isBoundedLinearMap_twoFormMetric.differentiableAt.comp z hα
  have hgp : ∀ v, v ≠ 0 → 0 < g (Φ 0) v v := by
    simpa only [Φ, normalCoord_zero, g, TosC11c.twoFormMetric_apply] using hpos
  have hgs : ∀ v t, g (Φ 0) v t = g (Φ 0) t v := by
    intro v t
    simpa only [Φ, normalCoord_zero, g] using
      TosC11c.twoFormMetric_symm h11.self_of_nhds v t
  have H := metricConnection_pullback (g := g) (φ := Φ) (w := 0)
    (by simpa only [Φ, normalCoord_zero] using hg) hgp hgs hΦ.contDiffAt
    (A.restrictScalars ℝ) hD0 p u
  have H' : metricConnection g z (A p) (A u) - A (c p u) = 0 := by
    simpa only [hΓ0, map_zero, Φ, normalCoord_zero, hD20,
      ContinuousLinearEquiv.restrictScalars_apply, sub_eq_add_neg] using H.symm
  exact sub_eq_zero.mp H'

/-- Equality of the actual polynomial maps, with no varying frame choice. -/
theorem metricQuadraticJet_eq_normalCoord
    {α : ComplexModel n → CoordinateRealTwoForm n} {z : ComplexModel n}
    (hα : DifferentiableAt ℝ α z) (h11 : ∀ᶠ x in 𝓝 z, IsOneOne (α x))
    (hcl : extDeriv α z = 0)
    (hpos : ∀ v, v ≠ 0 → 0 < α z ![v, Complex.I • v])
    (A : ComplexModel n ≃L[ℂ] ComplexModel n)
    (hA : ∀ p u, α z ![A p, A u] = flatForm n ![p, u]) (ζ : ComplexModel n) :
    metricQuadraticJet (fun x => TosC11c.twoFormMetric (α x)) z (A ζ) =
      normalCoord z (A : ComplexModel n →L[ℂ] ComplexModel n)
        (normalQuad (normalizedDeriv α z A) (normalizedDeriv_isOneOne hα h11 A)) ζ := by
  rw [metricQuadraticJet, metricConnection_normalQuad hα h11 hcl hpos A hA]
  simp only [normalCoord, map_sub, map_smul]
  rw [add_sub_assoc]
  congr 1
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
  simp only [ContinuousLinearEquiv.coe_coe]

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The same actual source-envelope average can use the literal smooth
frame-free quadratic jet; no smoothing or curvature estimate is inferred. -/
theorem sourceQuadraticMetricJetMean_eq_frameFreeIntegral
    (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n ≃L[ℂ] ComplexModel n) (r : ℝ)
    (hA : ∀ p u, w.form.val.coeff e z ![A p, A u] = flatForm n ![p, u]) :
    sourceQuadraticMetricJetMean w θ g e z hz
        (A : ComplexModel n →L[ℂ] ComplexModel n) r =
      ∫ ζ : ComplexModel n,
        (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
          (e.val.symm (metricQuadraticJet (TosC11c.chartMetric w e) z (A (r • ζ))))).toReal *
          explicitRadialKernel 1 one_pos 0 ζ := by
  have hα : DifferentiableAt ℝ (w.form.val.coeff e) z :=
    ((w.form.val.smooth e).differentiableOn (by simp)).differentiableAt
      (e.val.open_target.mem_nhds hz)
  have h11 : ∀ᶠ x in 𝓝 z, IsOneOne (w.form.val.coeff e x) := by
    filter_upwards [e.val.open_target.mem_nhds hz] with x hx
    exact (w.isKahler.1 e x hx).1
  unfold sourceQuadraticMetricJetMean
  apply integral_congr_ae
  exact Eventually.of_forall fun ζ => by
    have h := metricQuadraticJet_eq_normalCoord hα h11 (w.isKahler.2 e z hz)
      (w.isKahler.1 e z hz).2 A hA (r • ζ)
    exact congrArg (fun t =>
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))
        (e.val.symm t)).toReal * explicitRadialKernel 1 one_pos 0 ζ) h.symm

end SGPT.NPP.DNTBig
