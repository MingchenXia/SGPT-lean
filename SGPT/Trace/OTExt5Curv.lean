import SGPT.Trace.OTExt5Weight

/-!
# The twisted curvature of `ψ = Φ + q log R` in every chart

Blueprint `claude-ot-ext5.tex`, nodes `claude-ot-ext5:levi`, `claude-ot-ext5:curvature`.  Xia,
*Foundations of pluripotential theory*, q07, proof of `thm:compact-submanifold-extension`, Step 1,
display `eq:global-normal-twisted-curvature`.

* `leviForm_frameWeight_add_ge`: for `Φ ∈ PSH(X, θ_V - N ω)` with `θ_V = c₁(V, h₀)` (own Chern
  form) which is a smooth function `g` near a chart point, `Levi(-log |e|²_{h₀} + g) ≥ π N ω`.
* `twistedCurvature_poleWeight_ge`: with `N₀ = 1 + b_K/π + (q + 2) b` (`b_K` the Ricci constant of
  `exists_leviForm_log_chartDensity_le`, `b` the Levi constant of the normal pole `R`), for gentle
  `Φ ∈ PSH(X, θ_V - N₀ ω)`, in every chart `c`, frame `e` and density `ρ` of `μ`, at every point
  off the poles of `ψ = Φ + q log R`, the twisted curvature of the full local weight
  `-log |e|² + ψ - log ρ` for the twist functions `a_ε, b_ε` satisfies
  `H_ε(v) ≥ π ω(v, iv) + (ε / R) |∂ log(ε + R)(v)|²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm frameWeight contDiffOn_frameWeight)
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem two_le_infty' : ((2 : ℕ) : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

theorem isOpen_chartFrameDomain (V : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (e : AtlasFrame V) : IsOpen (chartFrameDomain V c e) :=
  c.val.isOpen_inter_preimage_symm e.val.open_baseSet

/-- **Levi lower bound of the local weights**: for `Φ ∈ PSH(X, θ_V - N ω)`, `θ_V = c₁(V, h₀)`, equal
near `z` to a smooth function `g`, `Levi(-log |e|²_{h₀} + g)(v) ≥ π N ω(v, iv)`. -/
theorem leviForm_frameWeight_add_ge (ωb : KahlerBackground n X)
    {V : HermitianHolomorphicLineBundle.{0, 0} n X} (hV : IsSourceSmoothHermitianMetric V)
    {θV : ClosedRealOneOneForm n X} (hθV : IsOwnFirstChernForm V θV) {N : ℝ} {Φ : X → EReal}
    (hΦ : IsThetaPshPotential (θV - N • ωb.form).val Φ) (c : ComplexChart n X) (e : AtlasFrame V)
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain V c e) {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hzU : z ∈ U) {g : ComplexModel n → ℝ} (hgs : ContDiffOn ℝ ∞ g U)
    (hgΦ : ∀ y ∈ U, Φ (c.val.symm y) = (g y : EReal)) (v : ComplexModel n) :
    Real.pi * (N * kahlerQuad ωb c z v) ≤ leviForm (fun y => frameWeight e c y + g y) z v := by
  obtain ⟨W, ρl, hzW, hρl, hpsh⟩ := hΦ.1 c z hz.1
  set O := W ∩ U with hO
  have hOo : IsOpen O := hρl.1.inter hU
  have hzO : z ∈ O := ⟨hzW, hzU⟩
  have hsm : ContDiffOn ℝ ∞ (fun y => g y + ρl y) O :=
    (hgs.mono inter_subset_right).add (hρl.2.2.1.mono inter_subset_left)
  have hpshO : PlurisubharmonicOn (fun y => ((g y + ρl y : ℝ) : EReal)) O := by
    refine plurisubharmonicOn_congr hOo (hpsh.mono inter_subset_left) fun y hy => ?_
    simp only [chartFunction, hgΦ y hy.2, EReal.coe_add]
  have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := ⟨O, hOo⟩) hsm hpshO hzO v
  have hg2 : ContDiffAt ℝ 2 g z := (hgs.contDiffAt (hU.mem_nhds hzU)).of_le two_le_infty'
  have hρ2 : ContDiffAt ℝ 2 ρl z := (hρl.2.2.1.contDiffAt (hρl.1.mem_nhds hzW)).of_le two_le_infty'
  have hf2 : ContDiffAt ℝ 2 (frameWeight e c) z :=
    ((contDiffOn_frameWeight hV e c).contDiffAt
      ((isOpen_chartFrameDomain V c e).mem_nhds hz)).of_le two_le_infty'
  have hadd1 : leviForm (fun y => g y + ρl y) z v = leviForm g z v + leviForm ρl z v :=
    leviForm_add hg2 hρ2 v
  have hadd2 : leviForm (fun y => frameWeight e c y + g y) z v =
      leviForm (frameWeight e c) z v + leviForm g z v := leviForm_add hf2 hg2 v
  have hρL := smoothDDC_complexDiagonal_eq_leviForm hρ2 v
  rw [hρl.2.2.2 hzW, SGPT.PSH.GlobalL2.coeff_sub_smul] at hρL
  have hθL := smoothDDC_complexDiagonal_eq_leviForm hf2 v
  have hθe : θV.val.coeff c z = smoothDDC (frameWeight e c) z := hθV c e z hz.1 hz.2
  rw [← hθe] at hθL
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at hρL
  have hpi := Real.pi_pos
  have e1 : leviForm ρl z v = Real.pi * (θV.val.coeff c z ![v, Complex.I • v] -
      N * kahlerQuad ωb c z v) := by
    rw [kahlerQuad, hρL]; field_simp
  have e2 : leviForm (frameWeight e c) z v = Real.pi * θV.val.coeff c z ![v, Complex.I • v] := by
    rw [hθL]; field_simp
  rw [hadd2, e2]
  rw [hadd1, e1] at h0
  nlinarith

variable [MeasurableSpace X] [BorelSpace X]

/-- **The twisted curvature of `ψ = Φ + q log R`** (FPT `eq:global-normal-twisted-curvature`) in every
chart, frame and chart density, off the poles of `ψ`. -/
theorem twistedCurvature_poleWeight_ge (ωb : KahlerBackground n X) {W : Set X} {R : X → ℝ}
    (hR : IsGlobalNormalPole ωb W R) {b : ℝ} (hb0 : 0 ≤ b)
    (hbR : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
      ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi +
          b * kahlerQuad ωb c z v)
    {μ : Measure X} {bK : ℝ}
    (hRic : ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        leviForm (fun y => Real.log (ρ y)) z v ≤ bK * kahlerQuad ωb c z v)
    {V : HermitianHolomorphicLineBundle.{0, 0} n X} (hV : IsSourceSmoothHermitianMetric V)
    {θV : ClosedRealOneOneForm n X} (hθV : IsOwnFirstChernForm V θV) {q : ℕ} (hq : 0 < q)
    {Φ : X → EReal}
    (hΦ : IsThetaPshPotential (θV - (1 + bK / Real.pi + ((q : ℝ) + 2) * b) • ωb.form).val Φ)
    {c₀ : ℚ} {𝔞 : GermIdeal n X} (hgen : HasGentleAnalyticSingularitiesOfType (n := n) Φ c₀ 𝔞)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4))
    (c : ComplexChart n X) (e : AtlasFrame V) (ρ : ComplexModel n → ℝ) (hρ : IsChartDensity μ c ρ)
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain V c e)
    (hψ : poleWeight Φ q R (c.val.symm z) ≠ ⊥) (v : ComplexModel n) :
    Real.pi * kahlerQuad ωb c z v +
        ε / R (c.val.symm z) * holDerivSq (fun y => Real.log (ε + R (c.val.symm y))) z v ≤
      twistedCurvature (fun y => twistA ε R (c.val.symm y)) (fun y => twistBX ε R (c.val.symm y))
        (localWeight V c e ρ fun x => (poleWeight Φ q R x).toReal) z v := by
  have hΦt : ∀ x, Φ x ≠ ⊤ := hΦ.1.quasiPlurisubharmonic.ne_top
  have hc₀ : 0 < c₀ := hgen.2.1.1
  have hEs : ChartSmooth (n := n) (gentleExp Φ c₀) := hgen.2.2.2.1
  rw [ne_eq, poleWeight_eq_bot_iff hq, not_or] at hψ
  have hRz : 0 < R (c.val.symm z) :=
    hR.pos_of_notMem fun h => hψ.2 ((hR.pole.eq_bot_iff _).mpr h)
  have hEz : 0 < gentleExp Φ c₀ (c.val.symm z) := (gentleExp_pos_iff hc₀ hΦt _).mpr hψ.1
  -- the open set of good points
  set U₁ := c.val.target ∩ (fun y => gentleExp Φ c₀ (c.val.symm y)) ⁻¹' Ioi 0 with hU₁
  have hU₁o : IsOpen U₁ := (hEs c).continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
  set U₂ := c.val.target ∩ (fun y => R (c.val.symm y)) ⁻¹' Ioi 0 with hU₂
  have hU₂o : IsOpen U₂ :=
    (hR.smooth c).continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
  have hzU₁ : z ∈ U₁ := ⟨hz.1, hEz⟩
  have hzU₂ : z ∈ U₂ := ⟨hz.1, hRz⟩
  set g : ComplexModel n → ℝ := fun y => (c₀ : ℝ) * Real.log (gentleExp Φ c₀ (c.val.symm y))
  have hgs : ContDiffOn ℝ ∞ g U₁ := by
    intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    exact contDiffAt_const.mul (ContDiffAt.log (f := fun y => gentleExp Φ c₀ (c.val.symm y))
      ((hEs c).contDiffAt (c.val.open_target.mem_nhds hy.1)) hy.2.ne')
  have hgΦ : ∀ y ∈ U₁, Φ (c.val.symm y) = (g y : EReal) := by
    intro y hy
    have hΦy : Φ (c.val.symm y) ≠ ⊥ := (gentleExp_pos_iff hc₀ hΦt _).mp hy.2
    rw [← EReal.coe_toReal (hΦt _) hΦy, toReal_eq_of_gentleExp hc₀ hΦt hΦy]
  -- the local weight off the poles
  set p₀ : ComplexModel n → ℝ := fun y => (frameWeight e c y + g y) + -Real.log (ρ y) with hp₀
  set Rc : ComplexModel n → ℝ := fun y => R (c.val.symm y) with hRc
  have hev : localWeight V c e ρ (fun x => (poleWeight Φ q R x).toReal) =ᶠ[𝓝 z]
      fun y => p₀ y + (q : ℝ) * Real.log (Rc y) := by
    filter_upwards [(hU₁o.inter hU₂o).mem_nhds ⟨hzU₁, hzU₂⟩] with y hy
    have hΦy : Φ (c.val.symm y) ≠ ⊥ := (gentleExp_pos_iff hc₀ hΦt _).mp hy.1.2
    have hRy : 0 < R (c.val.symm y) := hy.2.2
    simp only [localWeight, poleWeight, hp₀, hRc, frameWeight, frameNormSq]
    rw [← EReal.coe_toReal (hΦt _) hΦy, logPole_of_pos hRy, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.toReal_coe, toReal_eq_of_gentleExp hc₀ hΦt hΦy]
    ring
  -- smoothness
  have hg2 : ContDiffAt ℝ 2 g z := (hgs.contDiffAt (hU₁o.mem_nhds hzU₁)).of_le two_le_infty'
  have hf2 : ContDiffAt ℝ 2 (frameWeight e c) z :=
    ((contDiffOn_frameWeight hV e c).contDiffAt
      ((isOpen_chartFrameDomain V c e).mem_nhds hz)).of_le two_le_infty'
  have hρ2 : ContDiffAt ℝ 2 (fun y => Real.log (ρ y)) z :=
    ((hρ.1.contDiffAt (c.val.open_target.mem_nhds hz.1)).log (hρ.2.1 z hz.1).ne').of_le
      two_le_infty'
  have hp₀2 : ContDiffAt ℝ 2 p₀ z := (hf2.add hg2).add hρ2.neg
  have hR2 : ContDiffAt ℝ 2 Rc z :=
    ((hR.smooth c).contDiffAt (c.val.open_target.mem_nhds hz.1)).of_le two_le_infty'
  -- the Levi bounds
  set N₀ : ℝ := 1 + bK / Real.pi + ((q : ℝ) + 2) * b with hN₀
  have hpi := Real.pi_pos
  have hkq : 0 ≤ kahlerQuad ωb c z v := kahlerQuad_nonneg ωb c hz.1 v
  have hL1 := leviForm_frameWeight_add_ge ωb hV hθV hΦ c e hz hU₁o hzU₁ hgs hgΦ v
  have hLρ := hRic c ρ hρ z hz.1 v
  have hLp : leviForm p₀ z v =
      leviForm (fun y => frameWeight e c y + g y) z v - leviForm (fun y => Real.log (ρ y)) z v := by
    have h := leviForm_add (hf2.add hg2) hρ2.neg v
    have hn : leviForm (fun y => -Real.log (ρ y)) z v = -leviForm (fun y => Real.log (ρ y)) z v :=
      leviForm_neg (fun y => Real.log (ρ y)) z v
    simp only [Pi.add_def] at h
    rw [show p₀ = fun y => (frameWeight e c y + g y) + -Real.log (ρ y) from rfl, h]
    change _ + leviForm (fun y => -Real.log (ρ y)) z v = _
    rw [hn]; ring
  have hpA : (Real.pi + Real.pi * (((q : ℝ) + 2) * b)) * kahlerQuad ωb c z v ≤ leviForm p₀ z v := by
    rw [hLp]
    have : Real.pi * (N₀ * kahlerQuad ωb c z v) =
        (Real.pi + Real.pi * (((q : ℝ) + 2) * b)) * kahlerQuad ωb c z v +
          bK * kahlerQuad ωb c z v := by
      rw [hN₀]; field_simp; ring
    linarith
  have hψB : -(Real.pi * b * kahlerQuad ωb c z v) ≤ leviForm (fun y => Real.log (Rc y)) z v := by
    have h := hbR c z hz.1 hRz v
    have : -(b * kahlerQuad ωb c z v) ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v /
        Real.pi := by linarith
    rw [le_div_iff₀ hpi] at this
    linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqA : (q : ℝ) * (Real.pi * b) ≤ Real.pi + Real.pi * (((q : ℝ) + 2) * b) := by nlinarith
  have hmain := twistedCurvature_normal_pole_ge hp₀2 hR2 hRz (hR.lt_exp _) hε hε4 hq0 v hkq
    (by positivity : 0 ≤ Real.pi * b) hqA hpA hψB
  have hcongr : twistedCurvature (fun y => twistA ε R (c.val.symm y))
      (fun y => twistBX ε R (c.val.symm y))
      (localWeight V c e ρ fun x => (poleWeight Φ q R x).toReal) z v =
      twistedCurvature (fun y => twistMu ε (Real.log (ε + Rc y)))
        (fun y => twistB (Real.log (ε + Rc y))) (fun y => p₀ y + (q : ℝ) * Real.log (Rc y)) z v := by
    simp only [twistedCurvature, leviForm_congr_ev hev v]
    rfl
  rw [hcongr]
  have hlin : (Real.pi + Real.pi * (((q : ℝ) + 2) * b) - ((q : ℝ) + 2) * (Real.pi * b)) *
      kahlerQuad ωb c z v = Real.pi * kahlerQuad ωb c z v := by ring
  rw [hlin] at hmain
  exact hmain

end SGPT.Trace.OTExt5
