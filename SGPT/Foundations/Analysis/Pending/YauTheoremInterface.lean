import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Foundations.Analysis.Pending.TopBidimensionCurrents
import SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictionPositivity
import SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
import SGPT.Foundations.Analysis.Pending.YauContinuityMethod
import SGPT.Foundations.Analysis.Pending.YauHolderBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Yau's theorem (Calabi--Yau), and the two forms its consumers use

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Theorem 3.14 (Yau)
(`szekelyhidi-extremal:page-0064`, printed p. 47), the theorem of S.-T. Yau (Comm. Pure Appl. Math.
31 (1978)) in the `e^F` normalisation, as quoted by Demailly--Păun, Theorem 2.5
(`dp04-kahler-cone:2.5`); Boucksom, Theorem 3.4 (`bou02-volume:3.4`) is the special case proved
below as `exists_kahler_mongeAmpere_eq_smul`.  Blueprint `bou:yau`.  The source states
`ω + √-1 ∂∂̄φ > 0` and `(ω + √-1 ∂∂̄φ)ⁿ = e^F ωⁿ`; the project's `ddᶜ` differs by a positive constant,
which is absorbed in `φ`; uniqueness up to constants is not claimed (not needed).

**Status: PROVED** (TN.4 B5).  `exists_kahler_mongeAmpere_eq_exp` was a temporary named input
(human decisions I-0797 and I-0902 item 4) and is now proved by the continuity method of
Székelyhidi, GSM 152, §3.4 (the textbook proof chosen by the human, I-0902 C-0001), along the path
`(A + ddᶜφ)^N = e^{tF + εφ} A^N`, `t ∈ [0, 1]`, followed by `ε → 0`:
`YauContinuityMethod.exists_kahler_mongeAmpere_eq_exp_of_holderBound` (closedness and the limit
`ε → 0`: `YauClosedness`, `YauContinuityMethod`; openness: `YauSmoothOpenness`; regularity:
`MongeAmpereRegularity`; the estimates: `MongeAmpereSupBound` (`C⁰` at fixed `ε`),
`YauUniformEstimate` (Błocki's `C⁰` estimate), `AubinYauEstimate` (`C²`),
`CalabiThirdOrderEstimate` (`C³`), `YauHolderBound` (uniform `C^{2,r}`), `YauNormalizingConstant`
(the normalising constant vanishes)).  The statement is TN23's plan §1b verbatim, agreed on I-0831
(C-0036, confirmed C-0039) and frozen; it was not changed by the proof.

Let `Y` be a compact connected complex manifold of dimension `N > 0` with a Kähler form `A`, and
`F` a smooth function with `∫_Y e^F A^N = ∫_Y A^N`.  Then there is a smooth `φ` with `A + ddᶜφ`
Kähler and `(A + ddᶜφ)^N = e^F A^N`.

* `[ConnectedSpace Y]` is necessary (on `Y₁ ⊔ Y₂` the normalisation must hold on each component);
  `0 < N` excludes the normalisation question on a point.
* `kahlerVolume A` has chart density exactly `actualTopPowerDensity (A.coeff)`, so `hnorm` reads
  `∫ e^F A^N = ∫ A^N`; it is necessary by class invariance and sufficient by Yau's theorem.
* Reverse test: the consumers (`YauHypothesis` → the nef core
  `NefCoreKahlerCurrent.exists_kahlerCurrent_of_nef` → Boucksom 4.8 → bigness) conclude the
  existence of Kähler CURRENTS; none yields a smooth solution of a Monge--Ampère equation, so the
  statement does not follow from its consumers.

## Consequences proved here (no new content)

* `exists_kahler_mongeAmpere_eq_smul` — (Y-bou02), `bou02-volume:3.4`: for Kähler `A`, `ω'` there is
  `φ` with `A + ddᶜφ` Kähler and `(A + ddᶜφ)^N = c ω'^N`, `c = vol(A) / vol(ω')`
  (`F = log(c · ω'^N / A^N)`, the ratio being chart-independent).
* `yauHypothesis_of_nef` — `NefCoreKahlerCurrent.YauHypothesis w b` for every nef `b` on a compact
  connected `X`: the nef correction `h` of `b` at `ε/2` gives the Kähler form
  `B = b + εω + ddᶜh ≥ (ε/2) ω`, and (Y-bou02) on `X × X` for `p₁^*B + p₂^*B` with
  `g = h ∘ p₁ + h ∘ p₂ + φ`.
* `exists_kahlerCurrent_of_nef`, `isBigClass_of_nef` — the nef core (dp04 2.12) with Yau's theorem
  no longer a hypothesis.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.YauTheorem

noncomputable section

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses IntegrationCurrent
  TopDegreeDensity ManifoldTubePositivity ProductComplexManifold ProductTestForms

/-! ### Yau's theorem -/

/-- **Yau's theorem** (`dp04-kahler-cone:2.5`, Yau 1978; proved by the continuity method,
`YauContinuityMethod.exists_kahler_mongeAmpere_eq_exp_of_holderBound`).  On a compact connected
complex manifold `Y` of dimension `N > 0` with a Kähler form `A`,
for every chart-smooth `F` with `∫_Y e^F A^N = ∫_Y A^N` there is a chart-smooth `φ` with
`A + ddᶜφ` Kähler and `(A + ddᶜφ)^N = e^F A^N` in every chart. -/
theorem exists_kahler_mongeAmpere_eq_exp {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (hN : 0 < N)
    (A : KahlerBackground N Y) {F : Y → ℝ} (hF : ChartSmooth (n := N) F)
    (hnorm : ∫ y, Real.exp (F y) ∂(IntegrationCurrent.kahlerVolume A) = (IntegrationCurrent.kahlerVolume A).real univ) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (F (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z) := by
  obtain ⟨HA⟩ := HolderAtlas.nonempty (n := N) (M := Y)
  have hr0 : (0 : NNReal) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe]; norm_num
  exact YauContinuityMethod.exists_kahler_mongeAmpere_eq_exp_of_holderBound hN A hF hnorm HA hr0 hr1
    (YauHolderBound.exists_norm_ofChartSmooth_le A HA hr0 hr1 hF)

/-! ### (Y-bou02): the target `c ω'^N` -/

section Bou02

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The density of a Kähler form is positive in every chart. -/
theorem actualTopPowerDensity_pos (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    0 < actualTopPowerDensity (A.form.val.coeff e z) := by
  have h := topDensity_formPow_pos A.isKahler.1 hz
  rwa [formPow_coeff, topDensity_formPower] at h

/-- The ratio `ω'^N / A^N` read in a chart. -/
theorem topRatio_formPow_symm_eq (A ω' : KahlerBackground N Y) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    topRatio A.form.val (formPow ω'.form.val N) (e.val.symm z) =
      actualTopPowerDensity (ω'.form.val.coeff e z) /
        actualTopPowerDensity (A.form.val.coeff e z) := by
  rw [topRatio_eq_chartRatio A.isKahler.1 _ (e.val.map_target hz), e.val.right_inv hz, chartRatio,
    formPow_coeff, formPow_coeff, topDensity_formPower, topDensity_formPower]

/-- `∫_Y (ω'^N / A^N) A^N = ∫_Y ω'^N`. -/
theorem integral_topRatio_formPow_eq (A ω' : KahlerBackground N Y) :
    ∫ y, topRatio A.form.val (formPow ω'.form.val N) y ∂(kahlerVolume A) =
      (kahlerVolume ω').real univ := by
  have hθ : ∀ _ : Fin N, ThetaPlurisubharmonic ω'.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff ω'.form).mpr ω'.isSemipositive).1
  have h := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral A
    (fun _ => ω'.form) hθ
  have hvol : kahlerVolume ω' =
      GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin N => ω'.form) (fun _ _ => 0) hθ := rfl
  rw [hvol, h]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    NefCoreKahlerCurrent.topRatio_formPow_eq_slotForm' A ω'.form y)

/-- The constant `vol(A) / vol(ω')` of (Y-bou02) is positive. -/
theorem kahlerVolume_div_pos [ConnectedSpace Y] (hN : 0 < N) (A ω' : KahlerBackground N Y) :
    0 < (kahlerVolume A).real univ / (kahlerVolume ω').real univ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact div_pos (NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A)
    (NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω')

/-- **(Y-bou02)**, `bou02-volume:3.4`: for Kähler forms `A`, `ω'` on a compact connected `Y` of
dimension `N > 0` there is a chart-smooth `φ` with `A + ddᶜφ` Kähler and
`(A + ddᶜφ)^N = c ω'^N` in every chart, `c = vol(A) / vol(ω')`.  Proved from Yau's theorem with
`F = log(c · ω'^N / A^N)`. -/
theorem exists_kahler_mongeAmpere_eq_smul [ConnectedSpace Y] (hN : 0 < N)
    (A ω' : KahlerBackground N Y) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          ((kahlerVolume A).real univ / (kahlerVolume ω').real univ) *
            actualTopPowerDensity (ω'.form.val.coeff e z) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  set c : ℝ := (kahlerVolume A).real univ / (kahlerVolume ω').real univ with hcdef
  have hA := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A
  have hω := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω'
  have hc : 0 < c := div_pos hA hω
  set R : Y → ℝ := topRatio A.form.val (formPow ω'.form.val (m + 1)) with hRdef
  have hRpos : ∀ y, 0 < R y := NefCoreKahlerCurrent.topRatio_formPow_pos A ω'.isKahler
  have hRs : ChartSmooth (n := m + 1) R :=
    TopBidimensionCurrents.chartSmooth_topRatio A.isKahler.1 _
  set F : Y → ℝ := fun y => Real.log (c * R y) with hFdef
  have hFs : ChartSmooth (n := m + 1) F := fun e =>
    (contDiffOn_const.mul (hRs e)).log fun z _ => (mul_pos hc (hRpos _)).ne'
  have hexp : ∀ y, Real.exp (F y) = c * R y := fun y => Real.exp_log (mul_pos hc (hRpos y))
  have hnorm : ∫ y, Real.exp (F y) ∂(kahlerVolume A) = (kahlerVolume A).real univ := by
    simp_rw [hexp]
    rw [integral_const_mul, hRdef, integral_topRatio_formPow_eq, hcdef, div_mul_cancel₀ _ hω.ne']
  obtain ⟨φ, hφ, hK, hMA⟩ := exists_kahler_mongeAmpere_eq_exp (Nat.succ_pos m) A hFs hnorm
  refine ⟨φ, hφ, hK, fun e z hz => ?_⟩
  rw [hMA e z hz, hexp, hRdef, topRatio_formPow_symm_eq A ω' hz]
  have hpos := actualTopPowerDensity_pos A hz
  field_simp

end Bou02

/-! ### `YauHypothesis` for a nef class -/

section Nef

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `ddᶜ` is additive on chart targets. -/
theorem ddcClosedForm_coeff_add {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {f g : M → ℝ}
    (hf : ChartSmooth (n := N) f) (hg : ChartSmooth (n := N) g)
    (hfg : ChartSmooth (n := N) (fun x => f x + g x)) (e : ComplexChart N M)
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    (ddcClosedForm (fun x => f x + g x) hfg).val.coeff e z =
      (ddcClosedForm f hf).val.coeff e z + (ddcClosedForm g hg).val.coeff e z := by
  simp only [ddcClosedForm_coeff]
  exact smoothDDC_add e.val.open_target (hf e) (hg e) hz

/-- **Yau's theorem gives `YauHypothesis` for every nef class** (TN23's (hYau), plan §1c): for
`0 < ε ≤ 1` and a Kähler form `ω'` on `X × X`, the nef correction `h` of `b` at `ε/2` makes
`B = b + ddᶜh + εω` Kähler, and (Y-bou02) on `X × X` for the Kähler form `p₁^*B + p₂^*B` and the
target `ω'` gives `φ`; then `g = h ∘ p₁ + h ∘ p₂ + φ`. -/
theorem yauHypothesis_of_nef [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (hnef : NefWithRespectTo w b) :
    NefCoreKahlerCurrent.YauHypothesis w b := by
  intro ε hε _ ω' hω'
  obtain ⟨h, hh, hpos⟩ := hnef (ε / 2) (half_pos hε)
  -- `θ = b + ddᶜh + (ε/2) ω` is semipositive, so `B = θ + (ε/2) ω = (b + εω) + ddᶜh` is Kähler
  set θ : ClosedRealOneOneForm (q + 1) X := b + ddcClosedForm h hh + (ε / 2) • w.form with hθdef
  have hθ : θ.val.IsSemipositive := fun e z hz v => by
    have := hpos e z hz v
    simpa [hθdef, ddcClosedForm_coeff] using this
  have hBeq : θ + (ε / 2) • w.form = (b + ε • w.form) + (1 : ℝ) • ddcClosedForm h hh := by
    apply ClosedRealOneOneForm.ext
    intro e z
    simp only [hθdef, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, one_smul]
    module
  have hBK : ((b + ε • w.form) + (1 : ℝ) • ddcClosedForm h hh).val.IsKahler := by
    rw [← hBeq]
    exact NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive w hθ (half_pos hε)
  set A : KahlerBackground ((q + 1) + (q + 1)) (X × X) :=
    prodKahlerBackground ⟨_, hBK⟩ ⟨_, hBK⟩ with hAdef
  obtain ⟨φ, hφ, hK, hMA⟩ :=
    exists_kahler_mongeAmpere_eq_smul (by omega) A (⟨ω', hω'⟩ : KahlerBackground ((q + 1) + (q + 1)) (X × X))
  -- the potential `g = h ∘ p₁ + h ∘ p₂ + φ`
  have hh1 : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : X × X => h p.1) :=
    chartSmooth_comp contMDiff_fst hh
  have hh2 : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : X × X => h p.2) :=
    chartSmooth_comp contMDiff_snd hh
  have hh12 : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : X × X => h p.1 + h p.2) :=
    fun e => (hh1 e).add (hh2 e)
  have hg : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : X × X => (h p.1 + h p.2) + φ p) :=
    fun e => (hh12 e).add (hφ e)
  -- the two forms have the same coefficients on every chart target
  have key : ∀ (e : ComplexChart ((q + 1) + (q + 1)) (X × X))
      (z : ComplexModel ((q + 1) + (q + 1))), z ∈ e.val.target →
        (prodForm (b + ε • w.form) (b + ε • w.form) + ddcClosedForm _ hg).val.coeff e z =
          (A.form + ddcClosedForm φ hφ).val.coeff e z := by
    intro e z hz
    have hd1 :=
      SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff contMDiff_fst hh e hz
    have hd2 :=
      SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff contMDiff_snd hh e hz
    have e1 : (ddcClosedForm (fun p : X × X => (h p.1 + h p.2) + φ p) hg).val.coeff e z =
        (ddcClosedForm (fun p : X × X => h p.1) hh1).val.coeff e z +
          (ddcClosedForm (fun p : X × X => h p.2) hh2).val.coeff e z +
          (ddcClosedForm φ hφ).val.coeff e z := by
      rw [ddcClosedForm_coeff_add hh12 hφ hg e hz, ddcClosedForm_coeff_add hh1 hh2 hh12 e hz]
    have hA : A.form = prodForm (b + ε • w.form) (b + ε • w.form) +
        (1 : ℝ) • prodForm (ddcClosedForm h hh) (ddcClosedForm h hh) := by
      rw [hAdef, prodKahlerBackground_form]
      exact NefCoreKahlerCurrent.prodForm_add_smul _ _ _ _ 1
    simp only [ClosedRealOneOneForm.coeff_add, hA, one_smul, e1]
    simp only [prodForm, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val, hd1,
      hd2]
    abel
  refine ⟨fun p => (h p.1 + h p.2) + φ p, hg, (kahlerVolume A).real univ /
      (kahlerVolume (⟨ω', hω'⟩ : KahlerBackground ((q + 1) + (q + 1)) (X × X))).real univ, ?_, ?_, ?_⟩
  · exact kahlerVolume_div_pos (by omega) A _
  · refine ⟨fun e z hz => ?_, (prodForm (b + ε • w.form) (b + ε • w.form) +
      ddcClosedForm _ hg).property.1⟩
    rw [key e z hz]
    exact hK.1 e z hz
  · intro e z hz
    rw [key e z hz]
    exact hMA e z hz

/-- **The nef core with Yau's theorem** (dp04 2.12, Boucksom 4.8 at `μ = id`): a nef
class of positive volume on a compact connected Kähler manifold contains a Kähler current. -/
theorem exists_kahlerCurrent_of_nef [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (hnef : NefWithRespectTo w b)
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w)) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative b), K.representative = b :=
  NefCoreKahlerCurrent.exists_kahlerCurrent_of_nef w b hnef hvol (yauHypothesis_of_nef w b hnef)

/-- A nef class of positive volume on a compact connected Kähler manifold is big. -/
theorem isBigClass_of_nef [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (hnef : NefWithRespectTo w b)
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w)) :
    NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative b) :=
  NefCoreKahlerCurrent.isBigClass_of_nef w b hnef hvol (yauHypothesis_of_nef w b hnef)

end Nef

end

end SGPT.Foundations.Analysis.Pending.YauTheorem
