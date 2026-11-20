import SGPT.NPP.DNNefApprox
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Envelopes in the classes `{θ + εω}`: Kähler representatives and comparison

Lane DN (`thm:DNT23_C11bar`, nef and big classes).  Source: Berman 2019
(`references/berman19-zero-temperature`), proof of Proposition 3.5: a nef class is approximated
by the Kähler classes `{θ + εω}`; the envelopes `P_{θ+εω}(F)` decrease to `P_θ(F)`, and the
convergence is uniform on compact subsets of the ample locus because of a Kähler current
`θ + ddᶜψ ≥ ω₀ ≥ c₀ω`: `(1 - s) P_{θ+εω}(F) + s ψ` is `θ`-psh for `s = ε/(ε + c₀)`.

* `exists_isKahler_of_nef`: `θ + εω + ddᶜh` is a Kähler form for some smooth `h`.
* `isThetaPshPotential_add_semipositive`: adding a semipositive form.
* `rooftopEnvelope_le_of_le_add`: `F ≤ G + c ⇒ P_θ(F) ≤ P_θ(G) + c`.
* `rooftopEnvelope_le_add_smul`: `P_θ(F) ≤ P_{θ+εω}(F)`.
* `sub_le_rooftopEnvelope_of_kahlerCurrent`: `v - s(v - ψ) ≤ P_θ(F)` for a `(θ+εω)`-psh `v ≤ F`,
  `s = ε/(ε + c₀)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DNNef

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- Coefficients of `θ + ε ω + ddᶜh`. -/
theorem coeff_add_smul_add_ddc (θ : ClosedRealOneOneForm N Y) (w : KahlerBackground N Y) (ε : ℝ)
    {h : Y → ℝ} (hh : ChartSmooth (n := N) h) (e : ComplexChart N Y) (z : ComplexModel N) :
    (θ + ε • w.form + ddcClosedForm h hh).val.coeff e z =
      θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z + ε • w.form.val.coeff e z := by
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ddcClosedForm_coeff]
  abel

/-- **Kähler representatives of `{θ + εω}` for a nef class**: if `{θ}` is nef, then for every
`ε > 0` there is a smooth `h` with `θ + εω + ddᶜh` Kähler. -/
theorem exists_isKahler_of_nef (w : KahlerBackground N Y) {θ : ClosedRealOneOneForm N Y}
    (hnef : NefWithRespectTo w θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : Y → ℝ) (hh : ChartSmooth (n := N) h),
      (θ + ε • w.form + ddcClosedForm h hh).val.IsKahler := by
  obtain ⟨h, hh, hpos⟩ := hnef (ε / 2) (by positivity)
  refine ⟨h, hh, ⟨fun e z hz => ⟨(θ + ε • w.form + ddcClosedForm h hh).property.2 e z hz,
    fun v hv => ?_⟩, (θ + ε • w.form + ddcClosedForm h hh).property.1⟩⟩
  rw [coeff_add_smul_add_ddc]
  have h1 := hpos e z hz v
  have h2 := (w.isKahler.1 e z hz).2 v hv
  have hsplit : (θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z +
      ε • w.form.val.coeff e z) ![v, Complex.I • v] =
      (θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z +
        (ε / 2) • w.form.val.coeff e z) ![v, Complex.I • v] +
        (ε / 2) * w.form.val.coeff e z ![v, Complex.I • v] := by
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hsplit]
  have : 0 < ε / 2 * w.form.val.coeff e z ![v, Complex.I • v] := mul_pos (by positivity) h2
  linarith

/-- Adding a semipositive form keeps a potential plurisubharmonic. -/
theorem isThetaPshPotential_add_semipositive {θ η : ClosedRealOneOneForm N Y}
    (hη : η.val.IsSemipositive) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsThetaPshPotential (θ + η).val u :=
  SGPT.Foundations.Analysis.FirstPass.LocalPotentials.isThetaPshPotential_add_of_zero hu
    ((LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη).1

/-- **Lipschitz dependence on the obstacle**: `F ≤ G + c` gives `P_θ(F) ≤ P_θ(G) + c`. -/
theorem rooftopEnvelope_le_of_le_add (θ : SmoothRealForm N Y 2) {F G : Y → ℝ} {c : ℝ}
    (h : ∀ x, F x ≤ G x + c) (x : Y) :
    rooftopEnvelope θ (fun y => (F y : EReal)) x ≤
      rooftopEnvelope θ (fun y => (G y : EReal)) x + (c : EReal) := by
  have h1 : rooftopEnvelope θ (fun y => (F y : EReal)) ≤
      rooftopEnvelope θ (fun y => (G y : EReal) + (c : EReal)) :=
    rooftopEnvelope_mono fun y => by
      rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (h y)
  rw [RooftopEnvelopeNormalization.rooftopEnvelope_add_const] at h1
  exact h1 x

variable [CompactSpace Y]

/-- **Monotonicity in the class**: `P_θ(F) ≤ P_{θ+η}(F)` for semipositive `η`. -/
theorem rooftopEnvelope_le_add_semipositive [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (w : KahlerBackground N Y) (θ η : ClosedRealOneOneForm N Y) (hη : η.val.IsSemipositive)
    {φ : Y → EReal} (hφ : IsThetaPshPotential θ.val φ) {F : Y → ℝ} (hF : Continuous F) :
    rooftopEnvelope θ.val (fun y => (F y : EReal)) ≤
      rooftopEnvelope (θ + η).val (fun y => (F y : EReal)) := by
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous w θ hF hφ
  exact le_rooftopEnvelope (isThetaPshPotential_add_semipositive hη hP)
    (quasiEverywhere_of_forall (rooftopEnvelope_le_of_isThetaPshPotential hF hP))

omit [CompactSpace Y] in
/-- **The comparison with a Kähler current** (Berman 2019, proof of Proposition 3.5).  Let
`ψ` be `(θ - ω₀)`-psh with `ω₀ ≥ c₀ ω`, `ψ ≤ F`, and let `v ≤ F` be real-valued and
`(θ + εω)`-psh.  With `s = ε/(ε + c₀)`, `(1 - s)v + sψ` is a `θ`-psh competitor, so at every point
where `ψ = r` is finite, `v - s(v - r) ≤ P_θ(F)`. -/
theorem sub_le_rooftopEnvelope_of_kahlerCurrent (w ω₀ : KahlerBackground N Y)
    (θ : ClosedRealOneOneForm N Y) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hω₀ : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v : ComplexModel N,
      c₀ * w.form.val.coeff e z ![v, Complex.I • v] ≤ ω₀.form.val.coeff e z ![v, Complex.I • v])
    {ψ : Y → EReal} (hψ : IsThetaPshPotential (θ - ω₀.form).val ψ) {ε : ℝ} (hε : 0 < ε)
    {F : Y → ℝ} (hψF : ∀ x, ψ x ≤ (F x : EReal)) {v : Y → ℝ}
    (hv : IsThetaPshPotential (θ + ε • w.form).val (fun x => (v x : EReal)))
    (hvF : ∀ x, v x ≤ F x) {x : Y} {r : ℝ} (hr : ψ x = (r : EReal)) :
    ((v x - ε / (ε + c₀) * (v x - r) : ℝ) : EReal) ≤
      rooftopEnvelope θ.val (fun y => (F y : EReal)) x := by
  set s : ℝ := ε / (ε + c₀) with hsdef
  have hs0 : 0 < s := div_pos hε (by linarith)
  have hs1 : s < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have h1s : 0 < 1 - s := by linarith
  -- the two scaled potentials
  have hv' := RestrictedApproximantComparison.isThetaPshPotential_smul hv h1s
  have hψ' := RestrictedApproximantComparison.isThetaPshPotential_smul hψ hs0
  set u : Y → EReal := fun y => (((1 - s) * v y : ℝ) : EReal) + (s : EReal) * ψ y with hudef
  have hsum : ThetaPlurisubharmonic ((1 - s) • (θ + ε • w.form) + s • (θ - ω₀.form)).val u := by
    have h := SGPT.Foundations.Analysis.FirstPass.LocalPotentials.thetaPlurisubharmonic_add hv'.1
      hψ'.1
    have hfun : (fun x => ((1 - s : ℝ) : EReal) * ((v x : ℝ) : EReal) + (s : EReal) * ψ x) = u := by
      funext y; rw [hudef]; simp only; rw [EReal.coe_mul]
    rwa [hfun] at h
  -- the defect `s(ω₀ - c₀ ω)` is semipositive
  set η : ClosedRealOneOneForm N Y := s • (ω₀.form - c₀ • w.form) with hηdef
  have hη : η.val.IsSemipositive := by
    intro e z hz v
    rw [hηdef, ClosedRealOneOneForm.coeff_smul, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul]
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, smul_eq_mul]
    have := hω₀ e z hz v
    nlinarith
  have hform : ((1 - s) • (θ + ε • w.form) + s • (θ - ω₀.form)) + η = θ := by
    have hsc : (1 - s) * ε = s * c₀ := by
      rw [hsdef]; field_simp; ring
    rw [hηdef, smul_sub, smul_add, smul_sub, smul_smul, smul_smul, hsc]
    module
  have hpsh : ThetaPlurisubharmonic θ.val u := by
    have := SGPT.Foundations.Analysis.FirstPass.LocalPotentials.thetaPlurisubharmonic_add_of_zero
      hsum ((LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη).1
    rwa [hform] at this
  have hnd : LocallyNondegenerate u := by
    intro y U hU hyU
    obtain ⟨y', hy'U, hy'⟩ := hψ.2 y U hU hyU
    refine ⟨y', hy'U, ?_⟩
    rw [hudef]
    simp only
    have htop : ψ y' ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top y'
    have hsψ : (s : EReal) * ψ y' ≠ ⊥ := by
      rw [← EReal.coe_toReal htop hy', ← EReal.coe_mul]
      exact EReal.coe_ne_bot _
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hsψ⟩
  have hcomp : u ≤ rooftopEnvelope θ.val (fun y => (F y : EReal)) := by
    refine le_rooftopEnvelope ⟨hpsh, hnd⟩ (quasiEverywhere_of_forall fun y => ?_)
    rw [hudef]
    simp only
    have hψy := hψF y
    by_cases hb : ψ y = ⊥
    · rw [hb, EReal.coe_mul_bot_of_pos hs0, EReal.add_bot]
      exact bot_le
    · have htop : ψ y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hψy
      rw [← EReal.coe_toReal htop hb] at hψy ⊢
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := EReal.coe_le_coe_iff.mp hψy
      have h2 := hvF y
      nlinarith
  have hx := hcomp x
  rw [hudef] at hx
  simp only at hx
  rw [hr, ← EReal.coe_mul, ← EReal.coe_add] at hx
  refine le_trans (le_of_eq ?_) hx
  congr 1
  ring

end SGPT.NPP.DNNef
