import SGPT.NPP.DN2KiselmanLimit
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
import SGPT.Foundations.Analysis.FirstPass.BottChern
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# The Kiselman minimum over log radii on a complex manifold

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, the two applications of
`lem:varying-log-radius-minimum` "in the variable `s = log t`".  On a complex manifold `Y` with a
Kähler form `ω`, an open `U ⊆ Y`, a function `F(x, t)` smooth in charts for `0 < t < r₀` and an end
point `β(x) < log r₀` on `U` with `i∂∂̄β ≤ C_β ω`, the hypotheses of
`lem:varying-log-radius-minimum` in every chart (`LogRadiusData`) give that

  `ψ(x) = min_{s ≤ β(x)} (F(x, eˢ) - c s)`

is attained (at a point where `∂_s F(x, eˢ) ≤ c`), continuous on `U`, and `(θ' + c C_β ω)`-psh on
`U` (`LogRadiusData.thetaPshOff`), where `θ'` is the background in the joint Levi hypothesis.

## Main results

* `logRadiusInf`, `LogRadiusData`;
* `LogRadiusData.exists_isMinOn`, `LogRadiusData.logRadiusInf_le`;
* `LogRadiusData.continuousOn`;
* `LogRadiusData.thetaPshOff`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- `ψ(x) = inf_{s ≤ β(x)} (F(x, eˢ) - c s)`. -/
def logRadiusInf (F : Y → ℝ → ℝ) (β : Y → ℝ) (c : ℝ) (x : Y) : ℝ :=
  sInf ((fun s => F x (Real.exp s) - c * s) '' Iic (β x))

/-- **The hypotheses of FPT `lem:varying-log-radius-minimum` on a manifold, in log radii.** -/
structure LogRadiusData (wY : KahlerBackground N Y) (θ' : ClosedRealOneOneForm N Y) (U : Set Y)
    (F : Y → ℝ → ℝ) (r₀ : ℝ) (β : Y → ℝ) (c Cβ : ℝ) : Prop where
  isOpen_U : IsOpen U
  r₀_pos : 0 < r₀
  c_pos : 0 < c
  Cβ_nonneg : 0 ≤ Cβ
  smooth_F : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞
    (fun p : ComplexModel N × ℝ => F (e.val.symm p.1) p.2) (e.val.target ×ˢ Ioo 0 r₀)
  β_lt : ∀ x ∈ U, β x < Real.log r₀
  smooth_β : ∀ e : ComplexChart N Y, ContDiffOn ℝ ∞ (fun z => β (e.val.symm z))
    (e.val.target ∩ e.val.symm ⁻¹' U)
  levi_β : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
    e.val.symm z ∈ U → ∀ v : ComplexModel N,
      leviForm (fun z => β (e.val.symm z)) z v ≤
        Cβ * (Real.pi * wY.form.val.coeff e z ![v, Complex.I • v])
  deriv_nonneg : ∀ x ∈ U, ∀ s ≤ β x, 0 ≤ deriv (fun s => F x (Real.exp s)) s
  deriv2_pos : ∀ x ∈ U, ∀ s ≤ β x, 0 < deriv (deriv (fun s => F x (Real.exp s))) s
  lower : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ m : ℝ, ∀ y ∈ V, y ∈ U → ∀ s ≤ β y, m ≤ F y (Real.exp s)
  levi : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → e.val.symm z ∈ U →
    ∀ s ≤ β (e.val.symm z), deriv (fun s => F (e.val.symm z) (Real.exp s)) s ≤ c →
    ∀ (W : Set (ComplexModel N)) (ρ : ComplexModel N → ℝ), z ∈ W →
      IsSmoothLocalPotential θ'.val e W ρ → ∀ (v : ComplexModel N) (η : ℂ),
        0 ≤ leviForm (fun p : ComplexModel N × ℂ => F (e.val.symm p.1) (Real.exp p.2.re) + ρ p.1)
          (z, (s : ℂ)) (v, η)

/-- The Levi form of a smooth local potential is `π` times the form on complex lines. -/
theorem leviForm_eq_pi_mul_coeff' {a : SmoothRealForm N Y 2} {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ} (hpot : IsSmoothLocalPotential a e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) (v : ComplexModel N) :
    leviForm ρ z v = Real.pi * a.coeff e z ![v, Complex.I • v] := by
  have h2 : ContDiffAt ℝ 2 ρ z :=
    ((hpot.2.2.1.contDiffAt (hpot.1.mem_nhds hz)).of_le two_le_infty)
  rw [← hpot.2.2.2 hz, smoothDDC_complexDiagonal_eq_leviForm h2]
  field_simp

theorem kahler_coeff_nonneg (wY : KahlerBackground N Y) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) (v : ComplexModel N) :
    0 ≤ wY.form.val.coeff e z ![v, Complex.I • v] := by
  by_cases hv : v = 0
  · subst hv
    rw [(wY.form.val.coeff e z).map_coord_zero (0 : Fin 2) (by simp)]
  · exact ((wY.isKahler.1 e z hz).2 v hv).le

namespace LogRadiusData

variable {wY : KahlerBackground N Y} {θ' : ClosedRealOneOneForm N Y} {U : Set Y} {F : Y → ℝ → ℝ}
  {r₀ : ℝ} {β : Y → ℝ} {c Cβ : ℝ}

/-- The chart expression `H(z, s) = F(e⁻¹ z, eˢ) + ρ(z)`. -/
def chartH (F : Y → ℝ → ℝ) (e : ComplexChart N Y) (ρ : ComplexModel N → ℝ) :
    ComplexModel N × ℝ → ℝ :=
  fun p => F (e.val.symm p.1) (Real.exp p.2) + ρ p.1

theorem isOpen_target_inter (P : LogRadiusData wY θ' U F r₀ β c Cβ) (e : ComplexChart N Y) :
    IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
  e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target P.isOpen_U

/-- **The chart data**: in a chart `e`, near a point over `U`, the hypotheses of
`VaryingEndpointData` hold with `H = chartH`, `b = β ∘ e⁻¹`, `Q = C_β ρ_ω`. -/
theorem varyingEndpointData (P : LogRadiusData wY θ' U F r₀ β c Cβ) (e : ComplexChart N Y)
    {W₁ W₂ : Set (ComplexModel N)} {ρ₁ ρ₂ : ComplexModel N → ℝ}
    (h₁ : IsSmoothLocalPotential θ'.val e W₁ ρ₁) (h₂ : IsSmoothLocalPotential wY.form.val e W₂ ρ₂) :
    VaryingEndpointData (W₁ ∩ W₂ ∩ (e.val.target ∩ e.val.symm ⁻¹' U))
      ((W₁ ∩ e.val.target) ×ˢ Iio (Real.log r₀)) (chartH F e ρ₁) (fun z => β (e.val.symm z))
      (fun z => Cβ * ρ₂ z) c := by
  set D := W₁ ∩ W₂ ∩ (e.val.target ∩ e.val.symm ⁻¹' U) with hD
  have hDopen : IsOpen D := (h₁.1.inter h₂.1).inter (P.isOpen_target_inter e)
  have hslice : ∀ z, (fun t => chartH F e ρ₁ (z, t)) =
      fun t => F (e.val.symm z) (Real.exp t) + ρ₁ z := fun z => rfl
  have hderiv : ∀ z, deriv (fun t => chartH F e ρ₁ (z, t)) =
      deriv (fun t => F (e.val.symm z) (Real.exp t)) := by
    intro z; funext t; rw [hslice]; exact deriv_add_const _
  refine ⟨hDopen, (h₁.1.inter e.val.open_target).prod isOpen_Iio, ?_, ?_, ?_, ?_, P.c_pos,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz s hs
    exact ⟨⟨hz.1.1, hz.2.1⟩, lt_of_le_of_lt hs (P.β_lt _ hz.2.2)⟩
  · -- smoothness of `H`
    have hmaps : MapsTo (fun p : ComplexModel N × ℝ => (p.1, Real.exp p.2))
        ((W₁ ∩ e.val.target) ×ˢ Iio (Real.log r₀)) (e.val.target ×ˢ Ioo 0 r₀) := by
      intro p hp
      refine ⟨hp.1.2, Real.exp_pos _, ?_⟩
      have := hp.2
      rw [mem_Iio] at this
      calc Real.exp p.2 < Real.exp (Real.log r₀) := Real.exp_lt_exp.mpr this
        _ = r₀ := Real.exp_log P.r₀_pos
    have h1 : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => F (e.val.symm p.1) (Real.exp p.2))
        ((W₁ ∩ e.val.target) ×ˢ Iio (Real.log r₀)) :=
      (P.smooth_F e).comp (contDiff_fst.prodMk (Real.contDiff_exp.comp contDiff_snd)).contDiffOn
        hmaps
    have h2 : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ℝ => ρ₁ p.1)
        ((W₁ ∩ e.val.target) ×ˢ Iio (Real.log r₀)) :=
      h₁.2.2.1.comp contDiff_fst.contDiffOn fun p hp => hp.1.1
    exact h1.add h2
  · exact (P.smooth_β e).mono fun z hz => hz.2
  · exact contDiffOn_const.mul (h₂.2.2.1.mono fun z hz => hz.1.2)
  · intro z hz s hs
    rw [hderiv]; exact P.deriv_nonneg _ hz.2.2 s hs
  · intro z hz s hs
    rw [hderiv]; exact P.deriv2_pos _ hz.2.2 s hs
  · -- the lower bound
    intro z hz
    obtain ⟨V, hV, m, hm⟩ := P.lower _ hz.2.2
    have hsymm : ContinuousAt e.val.symm z :=
      e.val.continuousOn_symm.continuousAt (e.val.open_target.mem_nhds hz.2.1)
    have hρ : ContinuousAt ρ₁ z :=
      (h₁.2.2.1.continuousOn).continuousAt (h₁.1.mem_nhds hz.1.1)
    have hρev : ∀ᶠ y in 𝓝 z, ρ₁ z - 1 < ρ₁ y :=
      hρ.eventually (lt_mem_nhds (by linarith))
    refine ⟨{y | e.val.symm y ∈ V} ∩ {y | ρ₁ z - 1 < ρ₁ y}, inter_mem (hsymm.preimage_mem_nhds hV)
      hρev, m + (ρ₁ z - 1), fun y hy hyD s hs => ?_⟩
    have := hm _ hy.1 hyD.2.2 s hs
    show m + (ρ₁ z - 1) ≤ F (e.val.symm y) (Real.exp s) + ρ₁ y
    linarith [hy.2.out]
  · intro z hz s hs hc v η
    rw [hderiv] at hc
    exact P.levi e z hz.2.1 hz.2.2 s hs hc W₁ ρ₁ hz.1.1 h₁ v η
  · intro z hz v
    have hρ2 : ContDiffAt ℝ 2 ρ₂ z :=
      ((h₂.2.2.1.contDiffAt (h₂.1.mem_nhds hz.1.2)).of_le two_le_infty)
    rw [show (fun z => Cβ * ρ₂ z) = Cβ • ρ₂ from rfl, leviForm_smul hρ2,
      leviForm_eq_pi_mul_coeff' h₂ hz.1.2]
    exact mul_nonneg P.Cβ_nonneg (mul_nonneg Real.pi_pos.le (kahler_coeff_nonneg wY hz.2.1 v))
  · intro z hz v
    have hρ2 : ContDiffAt ℝ 2 ρ₂ z :=
      ((h₂.2.2.1.contDiffAt (h₂.1.mem_nhds hz.1.2)).of_le two_le_infty)
    rw [show (fun z => Cβ * ρ₂ z) = Cβ • ρ₂ from rfl, leviForm_smul hρ2,
      leviForm_eq_pi_mul_coeff' h₂ hz.1.2]
    exact P.levi_β e z hz.2.1 hz.2.2 v

/-- The fibre `s ↦ F(x, eˢ)` is smooth for `s < log r₀`. -/
theorem contDiffOn_fibre (P : LogRadiusData wY θ' U F r₀ β c Cβ) (x : Y) :
    ContDiffOn ℝ ∞ (fun s => F x (Real.exp s)) (Iio (Real.log r₀)) := by
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hxe : e.val.symm (e.val x) = x := e.val.left_inv hx
  have hmaps : MapsTo (fun s : ℝ => ((e.val x, Real.exp s) : ComplexModel N × ℝ))
      (Iio (Real.log r₀)) (e.val.target ×ˢ Ioo 0 r₀) := by
    intro s hs
    refine ⟨e.val.map_source hx, Real.exp_pos _, ?_⟩
    calc Real.exp s < Real.exp (Real.log r₀) := Real.exp_lt_exp.mpr hs
      _ = r₀ := Real.exp_log P.r₀_pos
  have h := (P.smooth_F e).comp (contDiff_const.prodMk Real.contDiff_exp).contDiffOn hmaps
  simpa only [Function.comp_def, hxe] using h

/-- On each fibre over `U` the one-variable hypotheses hold. -/
theorem profile (P : LogRadiusData wY θ' U F r₀ β c Cβ) {x : Y} (hx : x ∈ U) :
    ∃ m, LogRadiusProfile (fun s => F x (Real.exp s)) (β x) c m := by
  obtain ⟨V, hV, m, hm⟩ := P.lower x hx
  have hsm := P.contDiffOn_fibre x
  have hd : ∀ s ≤ β x, ContDiffAt ℝ ∞ (fun s => F x (Real.exp s)) s := fun s hs =>
    hsm.contDiffAt (isOpen_Iio.mem_nhds (lt_of_le_of_lt hs (P.β_lt x hx)))
  have hd2 : ContDiffOn ℝ ∞ (deriv fun s => F x (Real.exp s)) (Iio (Real.log r₀)) :=
    hsm.deriv_of_isOpen isOpen_Iio (by simp)
  refine ⟨m, P.c_pos, fun s hs => (hd s hs).differentiableAt (by simp), fun s hs => ?_,
    P.deriv_nonneg x hx, P.deriv2_pos x hx, fun s hs => hm x (mem_of_mem_nhds hV) hx s hs⟩
  exact (hd2.contDiffAt (isOpen_Iio.mem_nhds (lt_of_le_of_lt hs (P.β_lt x hx)))).differentiableAt
    (by simp)

/-- **The minimum over log radii is attained**, at a point where the slope is at most `c`. -/
theorem exists_isMinOn (P : LogRadiusData wY θ' U F r₀ β c Cβ) {x : Y} (hx : x ∈ U) :
    ∃ s ≤ β x, IsMinOn (fun s => F x (Real.exp s) - c * s) (Iic (β x)) s ∧
      logRadiusInf F β c x = F x (Real.exp s) - c * s ∧
      deriv (fun s => F x (Real.exp s)) s ≤ c := by
  obtain ⟨m, Px⟩ := P.profile hx
  obtain ⟨s, hs, hmin, hd⟩ := Px.exists_isMinOn
  refine ⟨s, hs, hmin, ?_, hd⟩
  unfold logRadiusInf
  have hleast : IsLeast ((fun s => F x (Real.exp s) - c * s) '' Iic (β x))
      (F x (Real.exp s) - c * s) := ⟨⟨s, hs, rfl⟩, fun y ⟨t, ht, hty⟩ => hty ▸ hmin ht⟩
  exact hleast.csInf_eq

theorem logRadiusInf_le (P : LogRadiusData wY θ' U F r₀ β c Cβ) {x : Y} (hx : x ∈ U) {s : ℝ}
    (hs : s ≤ β x) : logRadiusInf F β c x ≤ F x (Real.exp s) - c * s := by
  obtain ⟨s', -, hmin, heq, -⟩ := P.exists_isMinOn hx
  rw [heq]; exact hmin hs

/-- The chart minimum is the manifold minimum plus the potential. -/
theorem logRadiusMin_chartH (P : LogRadiusData wY θ' U F r₀ β c Cβ) (e : ComplexChart N Y)
    (ρ : ComplexModel N → ℝ) {z : ComplexModel N} (hz : e.val.symm z ∈ U) :
    logRadiusMin (chartH F e ρ) (fun z => β (e.val.symm z)) c z =
      logRadiusInf F β c (e.val.symm z) + ρ z := by
  obtain ⟨s, hs, hmin, heq, -⟩ := P.exists_isMinOn hz
  rw [heq]
  unfold logRadiusMin chartH
  have hleast : IsLeast ((fun t => F (e.val.symm z) (Real.exp t) + ρ z - c * t) ''
      Iic (β (e.val.symm z))) (F (e.val.symm z) (Real.exp s) - c * s + ρ z) := by
    refine ⟨⟨s, hs, by ring⟩, fun y ⟨t, ht, hty⟩ => ?_⟩
    rw [← hty]
    have := hmin ht
    simp only [mem_setOf_eq] at this
    linarith
  exact hleast.csInf_eq

/-- Local potentials of `θ'` and of `ω` combine to a local potential of `θ' + (c C_β) ω`. -/
theorem isSmoothLocalPotential_add_smul {e : ComplexChart N Y} {W : Set (ComplexModel N)}
    {ρ₁ ρ₂ : ComplexModel N → ℝ} (h₁ : IsSmoothLocalPotential θ'.val e W ρ₁)
    (h₂ : IsSmoothLocalPotential wY.form.val e W ρ₂) (a : ℝ) :
    IsSmoothLocalPotential (θ' + a • wY.form).val e W (fun y => ρ₁ y + a * ρ₂ y) := by
  have h₂' : ContDiffOn ℝ ∞ (fun y => a • ρ₂ y) W := h₂.2.2.1.const_smul a
  refine ⟨h₁.1, h₁.2.1, h₁.2.2.1.add (contDiffOn_const.mul h₂.2.2.1), fun z hz => ?_⟩
  have hsum := smoothDDC_add h₁.1 h₁.2.2.1 h₂' hz
  have hsm := smoothDDC_smul h₁.1 h₂.2.2.1 a hz
  simp only [smul_eq_mul] at hsum hsm
  rw [hsum, hsm, h₁.2.2.2 hz, h₂.2.2.2 hz, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul]

/-- **`ψ` is `(θ' + c C_β ω)`-psh on `U`** (FPT `lem:varying-log-radius-minimum` on a manifold). -/
theorem thetaPshOff (P : LogRadiusData wY θ' U F r₀ β c Cβ) :
    ThetaPshOff (θ' + (c * Cβ) • wY.form).val Uᶜ
      (fun x => ((logRadiusInf F β c x : ℝ) : EReal)) := by
  intro e z hz hzU
  have hzU' : e.val.symm z ∈ U := by simpa using hzU
  obtain ⟨W₁, ρ₁, hz₁, h₁⟩ := Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ' e z hz
  obtain ⟨W₂, ρ₂, hz₂, h₂⟩ := Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials wY.form e z hz
  set D := W₁ ∩ W₂ ∩ (e.val.target ∩ e.val.symm ⁻¹' U) with hD
  have hDopen : IsOpen D := (h₁.1.inter h₂.1).inter (P.isOpen_target_inter e)
  have V := P.varyingEndpointData e h₁ h₂
  have hpsh := V.plurisubharmonicOn_logRadiusMin
  have hpotD : IsSmoothLocalPotential (θ' + (c * Cβ) • wY.form).val e D
      (fun y => ρ₁ y + (c * Cβ) * ρ₂ y) :=
    isSmoothLocalPotential_add_smul (h₁.mono hDopen fun y hy => hy.1.1)
      (h₂.mono hDopen fun y hy => hy.1.2) (c * Cβ)
  refine ⟨D, fun y => ρ₁ y + (c * Cβ) * ρ₂ y, ⟨⟨hz₁, hz₂⟩, hz, hzU'⟩, hpotD, ?_⟩
  intro x hx
  obtain ⟨U', hU', hxU', hdisc⟩ := hpsh x hx
  refine ⟨U' ∩ D, hU'.inter hDopen, ⟨hxU', hx⟩, (hdisc.mono inter_subset_left).congr ?_⟩
  intro y hy
  have hyU : e.val.symm y ∈ U := hy.2.2.2
  simp only [chartFunction]
  rw [P.logRadiusMin_chartH e ρ₁ hyU, ← EReal.coe_add]
  congr 1
  ring

/-- **`ψ` is continuous on `U`.** -/
theorem continuousOn (P : LogRadiusData wY θ' U F r₀ β c Cβ) :
    ContinuousOn (logRadiusInf F β c) U := by
  intro x hx
  set e := complexChartAt (n := N) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hxe : e.val.symm (e.val x) = x := e.val.left_inv hxs
  obtain ⟨W₁, ρ₁, hz₁, h₁⟩ :=
    Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ' e (e.val x) hz
  obtain ⟨W₂, ρ₂, hz₂, h₂⟩ :=
    Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials wY.form e (e.val x) hz
  set D := W₁ ∩ W₂ ∩ (e.val.target ∩ e.val.symm ⁻¹' U) with hD
  have hDopen : IsOpen D := (h₁.1.inter h₂.1).inter (P.isOpen_target_inter e)
  have hxD : e.val x ∈ D := ⟨⟨hz₁, hz₂⟩, hz, by rw [mem_preimage, hxe]; exact hx⟩
  have V := P.varyingEndpointData e h₁ h₂
  have hcont : ContinuousOn (fun z => logRadiusMin (chartH F e ρ₁) (fun z => β (e.val.symm z)) c z
      - ρ₁ z) D :=
    V.continuousOn_logRadiusMin.sub (h₁.2.2.1.continuousOn.mono fun y hy => hy.1.1)
  have hcontAt : ContinuousAt (fun z => logRadiusInf F β c (e.val.symm z)) (e.val x) := by
    refine ((hcont.continuousAt (hDopen.mem_nhds hxD)).congr ?_)
    filter_upwards [hDopen.mem_nhds hxD] with y hy
    rw [P.logRadiusMin_chartH e ρ₁ hy.2.2]; ring
  have he : ContinuousAt e.val x := e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hxs)
  have := hcontAt.comp he
  refine (this.congr ?_).continuousWithinAt
  filter_upwards [e.val.open_source.mem_nhds hxs] with y hy
  simp [e.val.left_inv hy]

end LogRadiusData

end SGPT.NPP.DN2
