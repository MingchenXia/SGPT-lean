import SGPT.Foundations.Analysis.Pending.FibrePotentialKahlerLimit
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.SubmanifoldMassConcentration
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.DiagonalLowerBound
import SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The nef core of Boucksom 4.8: a nef class of positive volume is big (given Yau's theorem)

Source: Demailly--Păun, Theorem 2.12 (`dp04-kahler-cone:2.12`) and Proposition 2.6; Boucksom,
Lemmas 4.10--4.12 and the proof of Theorem 4.8 (`bou02-volume:4.8`).  Blueprint
`bou:concentrated-current`, `bou:uniform-diagonal-domination` and `bou:pushforward-lower-bound`
with the modification `μ = id` (no resolution of singularities).  TN.4 plan, step B6, the nef core
(N) (the proof of Boucksom's mass estimate, §1 F6 "B6 SKELETON"); exact statement posted on
the statement under discussion before coding.

Let `X` be a compact connected complex manifold of dimension `n = q + 1` with a Kähler form `ω`,
and `b` a smooth closed real `(1,1)`-form which is nef with `∫_X bⁿ > 0`.

**Yau's theorem is a hypothesis** (`YauHypothesis`, never an interface): for `0 < ε ≤ 1` and every
Kähler form `ω'` on `X × X` there are a chart-smooth `g` and `c > 0` with
`α = p₁^*(b + εω) + p₂^*(b + εω) + ddᶜg` Kähler and `α^{2n} = c ω'^{2n}`.  This is the Calabi--Yau
theorem (`dp04-kahler-cone:2.5`, `bou02-volume:3.4`) in the Kähler class `{p₁^*b + p₂^*b} + ε{ω̃}`
(Kähler because `b` is nef), in the form of TN23's (hYau) (`scratch/tn23-yau-plan-0149.md` §1c).

## The proof (dp04 2.12, Boucksom 4.8 with `μ = id`)

On `X̃ = X × X` with `ω̃ = p₁^*ω + p₂^*ω` (`W`):
1. TN23's concentration of mass on the diagonal (`exists_diagonal_massConcentration`): `f_ε`, tubes
   `V_ε`, `ω_ε = ω̃ + ddᶜf_ε ≥ ω̃/2`, `δ ≤ ∫_{V_ε} ω_ε^n ∧ ω̃^n`.
2. Yau at `ε_k = 1/(k+1)` with `ω' = ω_{ε_k}`: Kähler `α_k`, `α_k^{2n} = c_k ω_{ε_k}^{2n}`; integrating and
   by class invariance, `c_k ∫ ω̃^{2n} = P(ε_k)`, `P(ε) = ∫ (p₁^*b_ε + p₂^*b_ε)^{2n}`, a polynomial in `ε`,
   positive on `[0, 1]` (`P(0) = C(2n, n)(∫ bⁿ)²`, and `α` Kähler for `ε > 0`).
3. The integration step (`le_mixedMeasure_of_mongeAmpere`, `p = n`): `∫_{V_{ε_k}} α_k^n ∧ ω̃^n ≥ δ'`.
4. `Θ_k = [X̃] ∧ α_k^n` have bounded masses; a weak limit `Θ` along an ultrafilter; TN23's
   `DiagonalLowerBound` gives `Θ ≥ λ[Δ]`, `λ > 0`.
5. `FibrePotentialKahlerLimit.exists_kahlerCurrent_of_tendsto_prodForm`: a Kähler current in
   `{c · b}`, `c = n ∫ b^{n-1} ∧ ω > 0` (`NefMixedMass.fibreIntegral_pos_of_nef`); scale by `1/c`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  PositiveProductCurrents IntegrationCurrent TopDegreeDensity SmoothCurrentTraceMeasure
  ManifoldTubePositivity MixedMassClassInvariance NefMixedMass FibrePushforwardProductForm
  DiagonalFibreIntegration GlobalNonPluripolar
open scoped ProductComplexManifold
open ProductComplexManifold

/-! ### Algebra of closed forms -/

section Algebra

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open scoped Manifold in
theorem pullback_add_smul {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a c : ClosedRealOneOneForm n M) (t : ℝ) :
    ClosedRealOneOneForm.pullback hf (a + t • c) =
      ClosedRealOneOneForm.pullback hf a + t • ClosedRealOneOneForm.pullback hf c := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- `p₁^*(a + t c) + p₂^*(b + t d) = (p₁^*a + p₂^*b) + t (p₁^*c + p₂^*d)`. -/
theorem prodForm_add_smul {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (a c : ClosedRealOneOneForm n M) (b d : ClosedRealOneOneForm m Y) (t : ℝ) :
    prodForm (a + t • c) (b + t • d) = prodForm a b + t • prodForm c d := by
  rw [prodForm, prodForm, prodForm, pullback_add_smul, pullback_add_smul, smul_add]
  abel

/-- A semipositive form plus a positive multiple of a Kähler form is Kähler. -/
theorem isKahler_add_smul_of_isSemipositive (w : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive) {t : ℝ} (ht : 0 < t) :
    (θ + t • w.form).val.IsKahler := by
  refine ⟨fun e z hz => ⟨fun a b => (θ + t • w.form).property.2 e z hz a b, fun v hv => ?_⟩,
    (θ + t • w.form).property.1⟩
  have h1 := hθ e z hz v
  have h2 := (w.isKahler.1 e z hz).2 v hv
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
  nlinarith

theorem topRatio_formPow_eq_slotForm' (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (x : M) :
    topRatio w.form.val (formPow θ.val n) x = topRatio w.form.val (slotForm fun _ => θ) x := by
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff, formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]

/-- The density ratio of the top power of a Kähler form is positive. -/
theorem topRatio_formPow_pos (w : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    (hθ : θ.val.IsKahler) (x : M) : 0 < topRatio w.form.val (formPow θ.val n) x := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  exact div_pos (topDensity_formPow_pos hθ.1 hz) (topDensity_formPow_pos w.isKahler.1 hz)

/-- `α^n = c ω'^n` pointwise reads `α^n / ωⁿ = c ω'^n / ωⁿ`. -/
theorem topRatio_formPow_eq_mul (w : KahlerBackground n M) {α ω' : ClosedRealOneOneForm n M}
    {c : ℝ} (hMA : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      actualTopPowerDensity (α.val.coeff e z) = c * actualTopPowerDensity (ω'.val.coeff e z))
    (x : M) :
    topRatio w.form.val (formPow α.val n) x = c * topRatio w.form.val (formPow ω'.val n) x := by
  have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  simp only [topRatio, chartRatio, formPow_coeff, topDensity_formPower]
  rw [hMA _ _ hz, mul_div_assoc]

end Algebra

/-! ### Slot integrals with `ddᶜ` corrections on two blocks -/

section Blocks

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem ddcClosedForm_zero :
    ddcClosedForm (n := N) (fun _ : M => (0 : ℝ)) (fun _ => contDiffOn_const) = 0 := by
  apply ClosedRealOneOneForm.ext
  intro e z
  exact smoothDDC_zero z

/-- Class invariance for the families `(A + ddᶜg, …, A + ddᶜg, B + ddᶜf, …)`. -/
theorem slotIntegral_ite_add_ddc (w : KahlerBackground N M) (m : ℕ)
    (A B : ClosedRealOneOneForm N M) {g f : M → ℝ} (hg : ChartSmooth (n := N) g)
    (hf : ChartSmooth (n := N) f) :
    slotIntegral w (fun i : Fin N => if (i : ℕ) < m then A + ddcClosedForm g hg
      else B + ddcClosedForm f hf) =
      slotIntegral w (fun i : Fin N => if (i : ℕ) < m then A else B) := by
  classical
  have hfi : ∀ i : Fin N, ChartSmooth (n := N) (if (i : ℕ) < m then g else f) := by
    intro i
    by_cases hi : (i : ℕ) < m
    · rw [if_pos hi]; exact hg
    · rw [if_neg hi]; exact hf
  rw [← slotIntegral_add_ddc w (fun i : Fin N => if (i : ℕ) < m then A else B)
    (fun i => if (i : ℕ) < m then g else f) hfi]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < m
  · simp only [if_pos hi]
  · simp only [if_neg hi]

end Blocks

/-! ### The nef core -/

section Nef

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Yau's theorem in the form the nef core consumes** (a HYPOTHESIS of the theorems below, never
an interface): for `0 < ε ≤ 1` and every Kähler form `ω'` on `X × X` there are a chart-smooth `g` and
`c > 0` with `α = p₁^*(b + εω) + p₂^*(b + εω) + ddᶜg` Kähler and `α^{2n} = c ω'^{2n}` pointwise.  For a
nef `b` this is the Calabi--Yau theorem (`dp04-kahler-cone:2.5`, `bou02-volume:3.4`) on `X × X` in the
Kähler class `{p₁^*b + p₂^*b} + ε{ω̃}`, `c = vol / vol` (TN23's (hYau), I-0831 C-0028). -/
def YauHypothesis (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ ω' : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X),
    ω'.val.IsKahler →
      ∃ (g : X × X → ℝ) (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (c : ℝ), 0 < c ∧
        (prodForm (b + ε • w.form) (b + ε • w.form) + ddcClosedForm g hg).val.IsKahler ∧
        ∀ (e : ComplexChart ((q + 1) + (q + 1)) (X × X)) (z : ComplexModel ((q + 1) + (q + 1))),
          z ∈ e.val.target →
            actualTopPowerDensity
                ((prodForm (b + ε • w.form) (b + ε • w.form) + ddcClosedForm g hg).val.coeff e z) =
              c * actualTopPowerDensity (ω'.val.coeff e z)

/-- `P(ε) = ∫_{X×X} (p₁^*b + p₂^*b + ε ω̃)^{2n}`. -/
def volPoly (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) : ℝ :=
  slotIntegral (prodKahlerBackground w w) fun _ =>
    prodForm b b + ε • (prodKahlerBackground w w).form

/-- `Q(ε) = ∫_{X×X} (p₁^*b + p₂^*b + ε ω̃)^n ∧ ω̃^n`. -/
def massPoly (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) : ℝ :=
  slotIntegral (prodKahlerBackground w w) fun i : Fin ((q + 1) + (q + 1)) =>
    if (i : ℕ) < q + 1 then prodForm b b + ε • (prodKahlerBackground w w).form
    else (prodKahlerBackground w w).form

theorem prodForm_add_smul_form (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (ε : ℝ) :
    prodForm (b + ε • w.form) (b + ε • w.form) =
      prodForm b b + ε • (prodKahlerBackground w w).form := by
  rw [prodForm_add_smul, prodKahlerBackground_form]

theorem continuous_volPoly (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) :
    Continuous (volPoly w b) :=
  continuous_slotIntegral_add_smul (prodKahlerBackground w w) (fun _ => prodForm b b)
    fun _ => (prodKahlerBackground w w).form

theorem continuous_massPoly (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) : Continuous (massPoly w b) := by
  have h := continuous_slotIntegral_add_smul (prodKahlerBackground w w)
    (fun i : Fin ((q + 1) + (q + 1)) =>
      if (i : ℕ) < q + 1 then prodForm b b else (prodKahlerBackground w w).form)
    (fun i => if (i : ℕ) < q + 1 then (prodKahlerBackground w w).form else 0)
  convert h using 1
  funext ε
  rw [massPoly]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < q + 1
  · simp only [if_pos hi]
  · simp only [if_neg hi, smul_zero, add_zero]

theorem volPoly_zero (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) :
    volPoly w b 0 = ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) *
      (∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w)) ^ 2 := by
  rw [← integral_formPow_prodForm, volPoly]
  simp only [zero_smul, add_zero]
  rw [slotIntegral]
  exact integral_congr_ae (Eventually.of_forall fun z => (topRatio_formPow_eq_slotForm' _ _ z).symm)

/-- The Kähler volume of a nonempty compact manifold is positive. -/
theorem kahlerVolume_real_univ_pos {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M] (w : KahlerBackground (m + 1) M) :
    0 < (kahlerVolume w).real univ := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have h := ClosedTopCurrents.integral_kahlerVolume_pos w (h := fun _ => (1 : ℝ))
    (fun _ => contDiffOn_const) (fun _ => zero_le_one) (x := x) one_pos
  simpa [integral_const] using h

/-- The integral of a positive continuous function against a charged Kähler volume is positive. -/
theorem integral_pos_of_forall_pos {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (w : KahlerBackground N M)
    (hμ : kahlerVolume w univ ≠ 0) {f : M → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    0 < ∫ x, f x ∂(kahlerVolume w) := by
  have hint : Integrable f (kahlerVolume w) := hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hint]
  have hsupp : Function.support f = univ :=
    Set.eq_univ_of_forall fun x => Function.mem_support.mpr (hpos x).ne'
  rw [hsupp]
  exact pos_iff_ne_zero.mpr hμ

/-- The Kähler volume of `X × X` charges `X × X`. -/
theorem kahlerVolume_prod_univ_ne_zero [Nonempty X] (w : KahlerBackground (q + 1) X) :
    kahlerVolume (prodKahlerBackground w w) univ ≠ 0 := by
  have h := kahlerVolume_real_univ_pos w
  rw [measureReal_def] at h
  have hX : kahlerVolume w univ ≠ 0 := (ENNReal.toReal_pos_iff.mp h).1.ne'
  rw [kahlerVolume_prodKahlerBackground, Measure.smul_apply, ← Set.univ_prod_univ,
    Measure.prod_prod, smul_eq_mul]
  refine mul_ne_zero ?_ (mul_ne_zero hX hX)
  exact_mod_cast (Nat.choose_pos (by omega)).ne'

/-- `P(ε) > 0` for `0 < ε ≤ 1`: `P(ε) = ∫ α^{2n}` for the Kähler `α` of the Yau hypothesis. -/
theorem volPoly_pos [Nonempty X] (w : KahlerBackground (q + 1) X)
    {b : ClosedRealOneOneForm (q + 1) X} (hYau : YauHypothesis w b) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) : 0 < volPoly w b ε := by
  obtain ⟨g, hg, c, -, hαK, -⟩ := hYau ε hε hε1 (prodKahlerBackground w w).form
    (prodKahlerBackground w w).isKahler
  rw [volPoly, ← prodForm_add_smul_form,
    ← slotIntegral_add_ddc (prodKahlerBackground w w) _ (fun _ => g) (fun _ => hg), slotIntegral]
  simp_rw [← topRatio_formPow_eq_slotForm']
  exact integral_pos_of_forall_pos (prodKahlerBackground w w) (kahlerVolume_prod_univ_ne_zero w)
    (continuous_topRatio (prodKahlerBackground w w).isKahler.1 _)
    (topRatio_formPow_pos (prodKahlerBackground w w) hαK)

/-- `P ≥ P₀ > 0` on `[0, 1]` (compactness; `P(0) = C(2n, n)(∫ bⁿ)²`). -/
theorem exists_pos_le_volPoly [Nonempty X] (w : KahlerBackground (q + 1) X)
    {b : ClosedRealOneOneForm (q + 1) X}
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w))
    (hYau : YauHypothesis w b) :
    ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ ε ∈ Icc (0 : ℝ) 1, P₀ ≤ volPoly w b ε := by
  obtain ⟨ε₀, hε₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    (continuous_volPoly w b).continuousOn
  refine ⟨volPoly w b ε₀, ?_, fun ε hε => hmin hε⟩
  rcases eq_or_lt_of_le hε₀.1 with h0 | hpos
  · rw [← h0, volPoly_zero]
    have hC : (0 : ℝ) < ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    exact mul_pos hC (pow_pos hvol 2)
  · exact volPoly_pos w hYau hpos hε₀.2

/-- **The Yau constant is the volume ratio**: `c ∫ ω̃^{2n} = P(ε)`. -/
theorem mul_vol_eq_volPoly (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X)
    {ε : ℝ} {g : X × X → ℝ} (hg : ChartSmooth (n := (q + 1) + (q + 1)) g)
    {f : X × X → ℝ} (hf : ChartSmooth (n := (q + 1) + (q + 1)) f) {c : ℝ}
    (hMA : ∀ (e : ComplexChart ((q + 1) + (q + 1)) (X × X)) (z : ComplexModel ((q + 1) + (q + 1))),
      z ∈ e.val.target →
        actualTopPowerDensity
            ((prodForm (b + ε • w.form) (b + ε • w.form) + ddcClosedForm g hg).val.coeff e z) =
          c * actualTopPowerDensity
            (((prodKahlerBackground w w).form + ddcClosedForm f hf).val.coeff e z)) :
    c * (kahlerVolume (prodKahlerBackground w w)).real univ = volPoly w b ε := by
  set W := prodKahlerBackground w w with hWdef
  have h1 := integral_congr_ae (μ := kahlerVolume W)
    (Eventually.of_forall (topRatio_formPow_eq_mul W hMA))
  rw [integral_const_mul] at h1
  have hL : ∫ x, topRatio W.form.val (formPow (prodForm (b + ε • w.form) (b + ε • w.form) +
      ddcClosedForm g hg).val ((q + 1) + (q + 1))) x ∂(kahlerVolume W) = volPoly w b ε := by
    simp_rw [topRatio_formPow_eq_slotForm']
    rw [← slotIntegral, slotIntegral_add_ddc W (fun _ => _) (fun _ => g) (fun _ => hg),
      prodForm_add_smul_form]
    rfl
  have hR : ∫ x, topRatio W.form.val (formPow (W.form + ddcClosedForm f hf).val
      ((q + 1) + (q + 1))) x ∂(kahlerVolume W) = (kahlerVolume W).real univ := by
    simp_rw [topRatio_formPow_eq_slotForm']
    rw [← slotIntegral, slotIntegral_add_ddc W (fun _ => _) (fun _ => f) (fun _ => hf), slotIntegral]
    simp_rw [← topRatio_formPow_eq_slotForm', topRatio_formPow W.isKahler.1]
    simp [integral_const]
  rw [hL, hR] at h1
  exact h1.symm

/-- `Q ≤ M₀` on `[0, 1]`. -/
theorem exists_massPoly_le (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ ε ∈ Icc (0 : ℝ) 1, massPoly w b ε ≤ M₀ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_massPoly w b).continuousOn (s := Icc (0 : ℝ) 1)
  refine ⟨|C| + 1, by positivity, fun ε hε => ?_⟩
  have := hC ε hε
  rw [Real.norm_eq_abs] at this
  linarith [le_abs_self (massPoly w b ε), le_abs_self C]

/-- **The nef core of Boucksom 4.8** (dp04 2.12; Boucksom's proof of 4.8 with `μ = id`): on a compact
connected Kähler manifold `(X, ω)` of dimension `n = q + 1`, a smooth closed real `(1,1)`-form `b` which
is nef with `∫_X bⁿ > 0` is the representative of a Kähler current, provided Yau's theorem holds in the
Kähler classes `{p₁^*b + p₂^*b} + ε{ω̃}` on `X × X` (`YauHypothesis`, a hypothesis). -/
theorem exists_kahlerCurrent_of_nef [ConnectedSpace X] [Nonempty X]
    (w : KahlerBackground (q + 1) X) (b : ClosedRealOneOneForm (q + 1) X)
    (hnef : NefWithRespectTo w b)
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w))
    (hYau : YauHypothesis w b) :
    ∃ K : NonKahlerLocus.KahlerCurrent (RealBottChern.ofRepresentative b), K.representative = b := by
  classical
  set W := prodKahlerBackground w w with hWdef
  obtain ⟨x₀⟩ := ‹Nonempty X›
  -- 1. concentration of mass on the diagonal (TN23, dp04 2.1)
  obtain ⟨f, hf, V, -, hVmono, hVΔ, hhalf, hconc⟩ :=
    SubmanifoldMassConcentration.exists_diagonal_massConcentration w x₀
  obtain ⟨δ, hδ, hδV⟩ := hconc univ Filter.univ_mem
  -- the parameters `ε_k = 1/(k+1)`
  set εs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεsdef
  have hεpos : ∀ k, 0 < εs k := fun k => by positivity
  have hεle : ∀ k, εs k ≤ 1 := fun k => by
    simp only [hεsdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hεanti : ∀ j k, j ≤ k → εs k ≤ εs j := fun j k hjk => by
    simp only [hεsdef]
    apply one_div_le_one_div_of_le (by positivity)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have hhalf' : ∀ k, ((1 / 2 : ℝ) • W.form + ddcClosedForm (f (εs k)) (hf (εs k))).val.IsSemipositive :=
    fun k => hhalf (εs k) ⟨hεpos k, hεle k⟩
  have hωεK : ∀ k, (W.form + ddcClosedForm (f (εs k)) (hf (εs k))).val.IsKahler := by
    intro k
    have h := isKahler_add_smul_of_isSemipositive W (hhalf' k) (t := 1 / 2) (by norm_num)
    have heq : (1 / 2 : ℝ) • W.form + ddcClosedForm (f (εs k)) (hf (εs k)) + (1 / 2 : ℝ) • W.form =
        W.form + ddcClosedForm (f (εs k)) (hf (εs k)) := by
      module
    rwa [heq] at h
  -- 2. Yau at `ε_k` with `ω' = ω_{ε_k}`
  choose g hg c hc hαK hMA using fun k =>
    hYau (εs k) (hεpos k) (hεle k) (W.form + ddcClosedForm (f (εs k)) (hf (εs k))) (hωεK k)
  set α : ℕ → ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X) := fun k =>
    prodForm (b + εs k • w.form) (b + εs k • w.form) + ddcClosedForm (g k) (hg k) with hαdef
  have hαpsh : ∀ k, ThetaPlurisubharmonic (α k).val (fun _ => 0) := fun k =>
    (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (KahlerBackground.isSemipositive ⟨α k, hαK k⟩)
  have hWpsh : ThetaPlurisubharmonic W.form.val (fun _ => 0) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr W.isSemipositive
  -- the Yau constants are bounded below, the masses above
  obtain ⟨P₀, hP₀, hP₀le⟩ := exists_pos_le_volPoly w hvol hYau
  set vol := (kahlerVolume W).real univ with hvoldef
  have hvolpos : 0 < vol := by
    have h := integral_pos_of_forall_pos W (kahlerVolume_prod_univ_ne_zero w)
      (f := fun _ => (1 : ℝ)) continuous_const fun _ => one_pos
    simpa [integral_const] using h
  have hck : ∀ k, P₀ / vol ≤ c k := by
    intro k
    rw [div_le_iff₀ hvolpos]
    have h := mul_vol_eq_volPoly w b (hg k) (hf (εs k)) (hMA k)
    calc P₀ ≤ volPoly w b (εs k) := hP₀le _ ⟨(hεpos k).le, hεle k⟩
      _ = c k * vol := h.symm
  obtain ⟨M₀, hM₀, hM₀le⟩ := exists_massPoly_le w b
  -- 3. the integration step (bou02 4.12): uniform mass of `α_k^n ∧ ω̃^n` on the tubes
  set δ' : ℝ := (P₀ / vol) * δ ^ 2 /
    (4 * 2 ^ ((q + 1) + (q + 1) - (q + 1)) * ((q + 1) + (q + 1)).factorial * M₀) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  set θ : ℕ → Fin ((q + 1) + (q + 1)) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X) :=
    fun k i => if (i : ℕ) < q + 1 then α k else W.form with hθdef
  have hθpsh : ∀ k i, ThetaPlurisubharmonic (θ k i).val (fun _ => 0) := by
    intro k i
    simp only [hθdef]
    split_ifs
    · exact hαpsh k
    · exact hWpsh
  have hlowk : ∀ k, ENNReal.ofReal δ' ≤
      globalMixedMeasure (θ k) (fun _ _ => 0) (hθpsh k) (V (εs k)) := by
    intro k
    have h₃ : ∀ i : Fin ((q + 1) + (q + 1)), ThetaPlurisubharmonic
        ((fun i : Fin ((q + 1) + (q + 1)) => if (i : ℕ) < (q + 1) + (q + 1) - (q + 1) then α k
          else W.form + ddcClosedForm (f (εs k)) (hf (εs k))) i).val (fun _ => 0) := by
      intro i
      dsimp only
      split_ifs
      · exact hαpsh k
      · exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
          (KahlerBackground.isSemipositive ⟨_, hωεK k⟩)
    have hup : globalMixedMeasure (fun i : Fin ((q + 1) + (q + 1)) =>
        if (i : ℕ) < (q + 1) + (q + 1) - (q + 1) then α k
          else W.form + ddcClosedForm (f (εs k)) (hf (εs k))) (fun _ _ => 0) h₃
          (univ ∩ V (εs k)) ≤ ENNReal.ofReal M₀ := by
      have := ProductMixedMeasure.isFiniteMeasure_globalMixedMeasure h₃
      refine (measure_mono (subset_univ _)).trans ?_
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      apply ENNReal.ofReal_le_ofReal
      rw [globalMixedMeasure_real_univ_eq_integral W _ h₃, ← slotIntegral]
      have hfam : slotIntegral W (fun i : Fin ((q + 1) + (q + 1)) =>
          if (i : ℕ) < (q + 1) + (q + 1) - (q + 1) then α k
            else W.form + ddcClosedForm (f (εs k)) (hf (εs k))) = massPoly w b (εs k) := by
        simp only [Nat.add_sub_cancel, hαdef]
        rw [slotIntegral_ite_add_ddc, massPoly, prodForm_add_smul_form]
      rw [hfam]
      exact hM₀le _ ⟨(hεpos k).le, hεle k⟩
    have hωε : ((W.form + ddcClosedForm (f (εs k)) (hf (εs k))) -
        (1 / 2 : ℝ) • W.form).val.IsSemipositive := by
      have heq : W.form + ddcClosedForm (f (εs k)) (hf (εs k)) - (1 / 2 : ℝ) • W.form =
          (1 / 2 : ℝ) • W.form + ddcClosedForm (f (εs k)) (hf (εs k)) := by
        module
      rw [heq]
      exact hhalf' k
    have hconcK := hδV (εs k) ⟨hεpos k, hεle k⟩
      (SubmanifoldMassConcentration.thetaPlurisubharmonic_concentrationSlot W (hf (εs k)) (q + 1)
        (hhalf' k))
    have hmain := ConcentrationMassComparison.le_mixedMeasure_of_mongeAmpere W
      (W.form + ddcClosedForm (f (εs k)) (hf (εs k))) (α k) hωε (hαK k) (hc k) (hMA k)
      (p := q + 1) (by omega)
      (SubmanifoldMassConcentration.thetaPlurisubharmonic_concentrationSlot W (hf (εs k)) (q + 1)
        (hhalf' k)) (hθpsh k) h₃ hδ hM₀ hconcK hup
    rw [univ_inter] at hmain
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
    rw [hδ'def]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hck k) (by positivity)
  -- 4. the currents `Θ_k = [X̃] ∧ α_k^n`, their trace measures and masses
  set T : ℕ → ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1) := fun k =>
    smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => α k) with hTdef
  have hTpos : ∀ k, IsPositive (T k) := fun k => isPositive_smoothCurrent W _ fun _ => hαpsh k
  have hTclosed : ∀ k, ClosedProductCurrents.IsClosedCurrent (T k) := fun k =>
    SmoothCurrentClosedness.isClosedCurrent_smoothCurrent W _
  have hcongr : ∀ (S S' : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)) (hS : IsPositive S)
      (hS' : IsPositive S'), S = S' → CurrentTraceMeasure.traceMeasure W S hS =
        CurrentTraceMeasure.traceMeasure W S' hS' := by
    rintro S S' hS hS' rfl
    rfl
  have htrace : ∀ k, CurrentTraceMeasure.traceMeasure W (T k) (hTpos k) =
      globalMixedMeasure (θ k) (fun _ _ => 0) (hθpsh k) := by
    intro k
    have h := traceMeasure_smoothCurrent_eq_of_slots W (θ k) (hθpsh k) fun i hi => by
      simp only [hθdef]
      rw [if_neg (by omega)]
    rw [← h]
    refine hcongr _ _ _ _ ?_
    simp only [hTdef]
    congr 1
    funext j
    simp only [hθdef]
    rw [if_pos (by rw [Fin.val_castLE]; exact j.isLt)]
  have hTmass : ∀ k, mass W (T k) ≤ M₀ := by
    intro k
    rw [← CurrentTraceMeasure.traceMeasure_real_univ W (T k) (hTpos k), htrace k,
      globalMixedMeasure_real_univ_eq_integral W _ (hθpsh k), ← slotIntegral]
    have h0 := slotIntegral_ite_add_ddc W (q + 1)
      (prodForm (b + εs k • w.form) (b + εs k • w.form)) W.form (hg k)
      (f := fun _ => (0 : ℝ)) (fun _ => contDiffOn_const)
    rw [ddcClosedForm_zero, add_zero] at h0
    have hθk : θ k = fun i : Fin ((q + 1) + (q + 1)) =>
        if (i : ℕ) < q + 1 then prodForm (b + εs k • w.form) (b + εs k • w.form) +
          ddcClosedForm (g k) (hg k) else W.form := by
      simp only [hθdef, hαdef]
    rw [hθk, h0, prodForm_add_smul_form]
    exact hM₀le _ ⟨(hεpos k).le, hεle k⟩
  -- a weak limit along an ultrafilter (B2)
  obtain ⟨U, Θ, hUle, hΘpos, -, hlim⟩ :=
    exists_ultrafilter_tendsto W (atTop : Filter ℕ) T hTpos (Eventually.of_forall hTmass)
  -- 5. `Θ ≥ λ [Δ]` (TN23's DiagonalLowerBound) along the closed sets `closure V_{ε_j} ∪ Δ`
  set F : ℕ → Set (X × X) := fun j => closure (V (εs j)) ∪ Set.diagonal X with hFdef
  have hFc : ∀ j, IsClosed (F j) := fun j => isClosed_closure.union isClosed_diagonal
  have hFanti : Antitone F := fun j k hjk =>
    union_subset_union_left _ (closure_mono (hVmono _ _ (hεpos k) (hεanti j k hjk)))
  have hFΔ : ⋂ j, F j = Set.diagonal X := by
    apply Subset.antisymm
    · intro z hz
      rw [mem_iInter] at hz
      by_cases hzΔ : z ∈ Set.diagonal X
      · exact hzΔ
      · apply hVΔ
        rw [mem_iInter₂]
        intro ε hε
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε.1
        exact closure_mono (hVmono _ _ (hεpos j) hj.le) ((hz j).resolve_right hzΔ)
    · exact subset_iInter fun j => subset_union_right
  have hδF : ∀ j, ∀ᶠ k in (U : Filter ℕ),
      δ' ≤ (CurrentTraceMeasure.traceMeasure W (T k) (hTpos k)).real (F j) := by
    intro j
    filter_upwards [hUle (eventually_ge_atTop j)] with k hk
    rw [htrace k]
    have := ProductMixedMeasure.isFiniteMeasure_globalMixedMeasure (hθpsh k)
    have hsub : V (εs k) ⊆ F j := (subset_closure.trans
      (closure_mono (hVmono _ _ (hεpos k) (hεanti j k hk)))).trans subset_union_left
    rw [measureReal_def, ← ENNReal.toReal_ofReal hδ'pos.le]
    exact ENNReal.toReal_mono (measure_ne_top _ _) ((hlowk k).trans (measure_mono hsub))
  obtain ⟨lam, -, hlamlow, hΘlam⟩ :=
    DiagonalLowerBound.exists_isPositive_sub_smul_diagonalCurrent_of_tendsto w
      (l := (U : Filter ℕ)) hTpos hTclosed hΘpos (Eventually.of_forall hTmass) hlim hFc hFanti
      hFΔ hδF
  have hlampos : 0 < lam := by
    have := kahlerVolume_real_univ_pos w
    exact lt_of_lt_of_le (by positivity) hlamlow
  -- 6. the limit (F6): a Kähler current in `{c₀ b}`, `c₀ = n ∫ b^{n-1} ∧ ω`
  have hε0 : Tendsto εs (U : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hUle
  set c₀ := ((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val with hc₀def
  obtain ⟨K₀, hK₀rep, hK₀low⟩ := FibrePotentialKahlerLimit.exists_kahlerCurrent_of_tendsto_prodForm
    w b U εs (fun k => ⟨(hεpos k).le, hεle k⟩) hε0 g hg hαpsh hlim hlampos hΘlam
  -- 7. `c₀ > 0` (nef) and the scaling `{c₀ b} → {b}`
  have hc₀ : 0 < c₀ := mul_pos (by positivity) (fibreIntegral_pos_of_nef w hnef hvol)
  have hs := K₀.strictlyPsh
  rw [hK₀rep, hK₀low, KahlerBackground.smul_form] at hs
  have hs' := PotentialMassComparison.isThetaPshPotential_smul hs (inv_pos.mpr hc₀)
  have hform : c₀⁻¹ • (c₀ • b - lam • w.form) = b - (lam / c₀) • w.form := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hc₀.ne', one_smul, inv_mul_eq_div]
  rw [hform] at hs'
  refine ⟨⟨b, rfl, fun x => ((c₀⁻¹ : ℝ) : EReal) * K₀.potential x,
    KahlerBackground.smul (div_pos hlampos hc₀) w, ?_⟩, rfl⟩
  rw [KahlerBackground.smul_form]
  exact hs'

/-- **A nef class of positive volume is big**, given Yau's theorem (`YauHypothesis`). -/
theorem isBigClass_of_nef [ConnectedSpace X] [Nonempty X] (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) (hnef : NefWithRespectTo w b)
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w))
    (hYau : YauHypothesis w b) : NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative b) :=
  let ⟨K, _⟩ := exists_kahlerCurrent_of_nef w b hnef hvol hYau
  ⟨K⟩

end Nef

end SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
