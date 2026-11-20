import SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.Pending.FibrePushforwardProductForm
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Mixed integrals of smooth closed `(1,1)`-forms: polynomial dependence, nef positivity, products

Source: Demailly--Păun, Section 2 (`dp04-kahler-cone:2.12`: `∫(b + εω)ⁿ ≥ ∫ bⁿ` for nef `b`,
`∫_{X×X} (p₁^*b + p₂^*b)^{2n} = C(2n,n) (∫_X bⁿ)²`); Boucksom, proof of 4.8 (`bou02-volume:4.8`).
Blueprint `pc:domination-intersection` (2), (3) in the smooth case, `bou:product-mixed-measure` (2).
TN.4 plan, step B6, the nef core (the proof of Boucksom's mass estimate, §1 F6).

For smooth closed real `(1,1)`-forms `θ₀, …, θ_{N-1}` on a compact Kähler manifold `(M, ω)` of
dimension `N`, `slotIntegral w θ = ∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}` (no positivity assumed).

* `slotIntegral_add_smul_eq_sum`, `continuous_slotIntegral_add_smul`: `t ↦ ∫ (A + tB)` is a
  polynomial in `t` (multilinearity of the mixed density), hence continuous.
* `slotIntegral_nonneg`: `≥ 0` for semipositive slots; `slotIntegral_add_ddc`: class invariance
  (`MixedMassClassInvariance.integral_topRatio_slotForm_add_ddc`).
* `slotIntegral_nonneg_of_nef`: `≥ 0` for NEF slots (approximate by `θᵢ + tω + ddᶜhᵢ ≥ 0`, class
  invariance, `t → 0`).
* `integral_formPow_prodForm`: `∫_{X×X} (p₁^*a + p₂^*a)^{2n} = C(2n, n) (∫_X aⁿ)²`.
* `fibreIntegral_pos_of_nef`: for nef `b` on `X` (dimension `n`) with `∫ bⁿ > 0`,
  `∫_X b^{n-1} ∧ ω > 0` (`C ∫ b^{n-1} ∧ ω - ∫ bⁿ = ∫ b^{n-1} ∧ (Cω - b) ≥ 0` for `Cω - b ≥ 0`).
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NefMixedMass

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses IntegrationCurrent TopDegreeDensity
  ProductTestForms MixedMassClassInvariance ManifoldTubePositivity

/-! ### Slot integrals -/

section General

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The pointwise expansion of `(A + tB)` in every slot. -/
theorem topDensity_slotForm_add_smul (A B : Fin N → ClosedRealOneOneForm N M) (t : ℝ)
    (e : ComplexChart N M) (z : ComplexModel N) :
    topDensity ((slotForm fun i => A i + t • B i).coeff e z) =
      ∑ s : Finset (Fin N), (∏ i, if i ∈ s then (1 : ℝ) else t) *
        topDensity ((slotForm (s.piecewise A B)).coeff e z) := by
  classical
  rw [topDensity_slotForm_coeff]
  have hsplit : (fun i => (A i + t • B i).val.coeff e z) =
      (fun i => (A i).val.coeff e z) + fun i => t • (B i).val.coeff e z := by
    funext i
    simp [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
  rw [hsplit, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => (A i).val.coeff e z) (fun i => t • (B i).val.coeff e z) =
      fun i => (if i ∈ s then (1 : ℝ) else t) • (s.piecewise A B i).val.coeff e z := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hpw, MultilinearMap.map_smul_univ, smul_eq_mul, topDensity_slotForm_coeff]
  rfl

theorem topRatio_slotForm_add_smul (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M) (t : ℝ) (x : M) :
    topRatio w.form.val (slotForm fun i => A i + t • B i) x =
      ∑ s : Finset (Fin N), (∏ i, if i ∈ s then (1 : ℝ) else t) *
        topRatio w.form.val (slotForm (s.piecewise A B)) x := by
  simp only [topRatio, chartRatio, topDensity_slotForm_add_smul, Finset.sum_div, mul_div_assoc]

/-- Semipositive slots give a nonnegative density ratio. -/
theorem topRatio_slotForm_nonneg (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} (hθ : ∀ i, (θ i).val.IsSemipositive) (x : M) :
    0 ≤ topRatio w.form.val (slotForm θ) x := by
  have hz := (complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x)
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff]
  exact div_nonneg (actualMixedTopDensity_nonneg fun i =>
    SmoothMixedMeasureDensity.isSemipositiveOneOne_coeff
      ((LocalPotentials.thetaPlurisubharmonic_zero_iff (θ i)).mpr (hθ i)) hz)
    (topDensity_formPow_pos w.isKahler.1 hz).le

/-- `NefWithRespectTo` in the language of closed forms: `θ + tω + ddᶜh ≥ 0`. -/
theorem exists_isSemipositive_of_nef {w : KahlerBackground N M} {θ : ClosedRealOneOneForm N M}
    (h : NefWithRespectTo w θ) {t : ℝ} (ht : 0 < t) :
    ∃ (f : M → ℝ) (hf : ChartSmooth (n := N) f),
      (θ + t • w.form + ddcClosedForm f hf).val.IsSemipositive := by
  obtain ⟨f, hf, hsemi⟩ := h t ht
  refine ⟨f, hf, fun e z hz v => ?_⟩
  have h1 := hsemi e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, ddcClosedForm_coeff,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
  linarith

/-- A semipositive form is nef. -/
theorem nefWithRespectTo_of_isSemipositive {w : KahlerBackground N M}
    {θ : ClosedRealOneOneForm N M} (h : θ.val.IsSemipositive) : NefWithRespectTo w θ := by
  intro t ht
  refine ⟨fun _ => 0, fun _ => contDiffOn_const, fun e z hz v => ?_⟩
  have h1 := h e z hz v
  have h2 := KahlerDomination.lineValue_nonneg_of_isHermitian w.isKahler.1 e hz v
  have h0 : smoothDDC (fun y : ComplexModel N => (fun _ : M => (0 : ℝ)) (e.val.symm y)) z = 0 :=
    smoothDDC_zero z
  rw [h0, add_zero]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  nlinarith

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- `∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}` for smooth closed real `(1,1)`-forms (no positivity). -/
def slotIntegral (w : KahlerBackground N M) (θ : Fin N → ClosedRealOneOneForm N M) : ℝ :=
  ∫ x, topRatio w.form.val (slotForm θ) x ∂(kahlerVolume w)

theorem integrable_topRatio (w : KahlerBackground N M) (Φ : SmoothRealForm N M (2 * N)) :
    Integrable (topRatio w.form.val Φ) (kahlerVolume w) :=
  (continuous_topRatio w.isKahler.1 Φ).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- **The slot integral is a polynomial in `t`.** -/
theorem slotIntegral_add_smul_eq_sum (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M) (t : ℝ) :
    slotIntegral w (fun i => A i + t • B i) =
      ∑ s : Finset (Fin N), (∏ i, if i ∈ s then (1 : ℝ) else t) *
        slotIntegral w (s.piecewise A B) := by
  classical
  rw [slotIntegral]
  simp_rw [topRatio_slotForm_add_smul]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  · intro s _
    exact (integrable_topRatio w _).const_mul _

theorem continuous_slotIntegral_add_smul (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M) :
    Continuous fun t : ℝ => slotIntegral w (fun i => A i + t • B i) := by
  classical
  simp_rw [slotIntegral_add_smul_eq_sum]
  exact continuous_finsetSum _ fun s _ => Continuous.mul (continuous_finsetProd _ fun i _ =>
    continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id) continuous_const

theorem slotIntegral_nonneg (w : KahlerBackground N M) {θ : Fin N → ClosedRealOneOneForm N M}
    (hθ : ∀ i, (θ i).val.IsSemipositive) : 0 ≤ slotIntegral w θ :=
  integral_nonneg (topRatio_slotForm_nonneg w hθ)

/-- **Class invariance** of slot integrals. -/
theorem slotIntegral_add_ddc (w : KahlerBackground N M) (θ : Fin N → ClosedRealOneOneForm N M)
    (f : Fin N → M → ℝ) (hf : ∀ i, ChartSmooth (n := N) (f i)) :
    slotIntegral w (fun i => θ i + ddcClosedForm (f i) (hf i)) = slotIntegral w θ :=
  integral_topRatio_slotForm_add_ddc w θ f hf

/-- **Mixed integrals of nef forms are nonnegative.** -/
theorem slotIntegral_nonneg_of_nef (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} (hθ : ∀ i, NefWithRespectTo w (θ i)) :
    0 ≤ slotIntegral w θ := by
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ slotIntegral w (fun i => θ i + t • w.form) := by
    intro t ht
    choose f hf hsemi using fun i => exists_isSemipositive_of_nef (hθ i) ht
    rw [← slotIntegral_add_ddc w (fun i => θ i + t • w.form) f hf]
    exact slotIntegral_nonneg w hsemi
  have hcont := (continuous_slotIntegral_add_smul w θ fun _ => w.form).continuousWithinAt
    (s := Ioi (0 : ℝ)) (x := 0)
  have h0 : slotIntegral w (fun i => θ i + (0 : ℝ) • w.form) = slotIntegral w θ := by
    simp only [zero_smul, add_zero]
  rw [← h0]
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hpos t ht

end General

/-! ### Linearity in the last slot, top powers -/

section Last

variable {q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem topDensity_slotForm_snoc_sub_smul (B : Fin q → ClosedRealOneOneForm (q + 1) M)
    (u v : ClosedRealOneOneForm (q + 1) M) (C : ℝ) (e : ComplexChart (q + 1) M)
    (z : ComplexModel (q + 1)) :
    topDensity ((slotForm (Fin.snoc B (C • u - v))).coeff e z) =
      C * topDensity ((slotForm (Fin.snoc B u)).coeff e z) -
        topDensity ((slotForm (Fin.snoc B v)).coeff e z) := by
  classical
  simp only [topDensity_slotForm_coeff]
  have hfam : ∀ c : ClosedRealOneOneForm (q + 1) M,
      (fun i => ((Fin.snoc B c : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M) i).val.coeff e z) =
        Function.update (fun i => ((Fin.snoc B 0 : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M)
          i).val.coeff e z) (Fin.last q) (c.val.coeff e z) := by
    intro c
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Function.update, Fin.castSucc_ne_last]
  rw [hfam (C • u - v), hfam u, hfam v, ← actualMixedTopDensityMultilinear_apply,
    ← actualMixedTopDensityMultilinear_apply, ← actualMixedTopDensityMultilinear_apply]
  have hcv : (C • u - v).val.coeff e z = C • u.val.coeff e z + (-1 : ℝ) • v.val.coeff e z := by
    rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_neg]
    congr 1
    ext w
    simp
  rw [hcv, MultilinearMap.map_update_add, MultilinearMap.map_update_smul,
    MultilinearMap.map_update_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem slotIntegral_snoc_sub_smul (w : KahlerBackground (q + 1) M)
    (B : Fin q → ClosedRealOneOneForm (q + 1) M) (u v : ClosedRealOneOneForm (q + 1) M) (C : ℝ) :
    slotIntegral w (Fin.snoc B (C • u - v)) =
      C * slotIntegral w (Fin.snoc B u) - slotIntegral w (Fin.snoc B v) := by
  have hpt : ∀ x, topRatio w.form.val (slotForm (Fin.snoc B (C • u - v))) x =
      C * topRatio w.form.val (slotForm (Fin.snoc B u)) x -
        topRatio w.form.val (slotForm (Fin.snoc B v)) x := by
    intro x
    simp only [topRatio, chartRatio, topDensity_slotForm_snoc_sub_smul, sub_div, mul_div_assoc]
  rw [slotIntegral, integral_congr_ae (Eventually.of_forall hpt),
    integral_sub ((integrable_topRatio w _).const_mul C) (integrable_topRatio w _),
    integral_const_mul]
  rfl

/-- The top power read as a slot form. -/
theorem topRatio_formPow_eq_slotForm (w : KahlerBackground (q + 1) M)
    (θ : ClosedRealOneOneForm (q + 1) M) (x : M) :
    topRatio w.form.val (formPow θ.val (q + 1)) x =
      topRatio w.form.val (slotForm fun _ => θ) x := by
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff, formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]

theorem integral_formPow_eq_slotIntegral (w : KahlerBackground (q + 1) M)
    (θ : ClosedRealOneOneForm (q + 1) M) :
    ∫ x, topRatio w.form.val (formPow θ.val (q + 1)) x ∂(kahlerVolume w) =
      slotIntegral w fun _ => θ := by
  simp_rw [topRatio_formPow_eq_slotForm]
  rfl

end Last

/-! ### The fibre constant of a nef class is positive -/

section Fibre

open FibrePushforwardProductForm

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem fibreIntegral_eq_slotIntegral (w : KahlerBackground (q + 1) X)
    (b β : ClosedRealOneOneForm (q + 1) X) :
    fibreIntegral w b β.val = slotIntegral w (Fin.snoc (fun _ : Fin q => b) β) := by
  rw [fibreIntegral, slotIntegral]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [topRatio, chartRatio]
  congr 1
  rw [topDensity_slotForm_coeff, wedgeTwo_coeff, formPow_coeff, formPower_eq_wedgeProd,
    ← wedgeProd_snoc, topDensity_wedgeProd]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- **`∫_X b^q ∧ ω > 0` for nef `b` with `∫ b^{q+1} > 0`** (blueprint `bou:pushforward-lower-bound`,
`0 < n bⁿ / C' ≤ m`): with `Cω - b ≥ 0`, `C ∫ b^q ∧ ω - ∫ b^{q+1} = ∫ b^q ∧ (Cω - b) ≥ 0`. -/
theorem fibreIntegral_pos_of_nef (w : KahlerBackground (q + 1) X)
    {b : ClosedRealOneOneForm (q + 1) X} (hnef : NefWithRespectTo w b)
    (hvol : 0 < ∫ x, topRatio w.form.val (formPow b.val (q + 1)) x ∂(kahlerVolume w)) :
    0 < fibreIntegral w b w.form.val := by
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (-b)
  have hsemi' : (C • w.form - b).val.IsSemipositive := by
    rw [show C • w.form - b = -b + C • w.form by abel]
    exact hsemi
  have hnn : 0 ≤ slotIntegral w (Fin.snoc (fun _ : Fin q => b) (C • w.form - b)) := by
    refine slotIntegral_nonneg_of_nef w fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      exact nefWithRespectTo_of_isSemipositive hsemi'
    · rw [Fin.snoc_castSucc]
      exact hnef
  rw [slotIntegral_snoc_sub_smul] at hnn
  have hb : Fin.snoc (fun _ : Fin q => b) b = fun _ : Fin (q + 1) => b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hb, ← integral_formPow_eq_slotIntegral] at hnn
  rw [fibreIntegral_eq_slotIntegral]
  by_contra hle
  rw [not_lt] at hle
  nlinarith

end Fibre

/-! ### The top power of a product form -/

section Product

open scoped ProductComplexManifold
open ProductComplexManifold ProductMixedMeasure FibrePushforwardProductForm

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X]

/-- `(p₁^*a + p₂^*a)^{2n}` over `(p₁^*ω + p₂^*ω)^{2n}` at `(x, y)` is the product of the ratios. -/
theorem topRatio_formPow_prodForm (w : KahlerBackground (q + 1) X)
    (a : ClosedRealOneOneForm (q + 1) X) (x y : X) :
    topRatio (prodKahlerBackground w w).form.val
        (formPow (prodForm a a).val ((q + 1) + (q + 1))) (x, y) =
      topRatio w.form.val (formPow a.val (q + 1)) x *
        topRatio w.form.val (formPow a.val (q + 1)) y := by
  set e := complexChartAt (n := q + 1) x
  set e' := complexChartAt (n := q + 1) y
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hz' : e'.val y ∈ e'.val.target := e'.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := (q + 1) + (q + 1)) (x, y) = prodComplexChart e e' := rfl
  have hEx : (prodComplexChart e e').val (x, y) =
      prodModelEquiv (q + 1) (q + 1) (e.val x, e'.val y) := rfl
  simp only [topRatio, chartRatio]
  rw [hE, hEx, prodKahlerBackground_form, topDensity_formPow_prodForm a a e e' hz hz',
    topDensity_formPow_prodForm w.form w.form e e' hz hz']
  have hC : ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  rw [mul_assoc, mul_assoc, mul_div_mul_left _ _ hC, mul_div_mul_comm]

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **`∫_{X×X} (p₁^*a + p₂^*a)^{2n} = C(2n, n) (∫_X aⁿ)²`** (blueprint `bou:product-mixed-measure`
(2) for smooth representatives). -/
theorem integral_formPow_prodForm (w : KahlerBackground (q + 1) X)
    (a : ClosedRealOneOneForm (q + 1) X) :
    ∫ z, topRatio (prodKahlerBackground w w).form.val
        (formPow (prodForm a a).val ((q + 1) + (q + 1))) z
        ∂(kahlerVolume (prodKahlerBackground w w)) =
      ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) *
        (∫ x, topRatio w.form.val (formPow a.val (q + 1)) x ∂(kahlerVolume w)) ^ 2 := by
  rw [kahlerVolume_prodKahlerBackground, integral_smul_measure]
  have h : ∀ z : X × X, topRatio (prodKahlerBackground w w).form.val
      (formPow (prodForm a a).val ((q + 1) + (q + 1))) z =
      topRatio w.form.val (formPow a.val (q + 1)) z.1 *
        topRatio w.form.val (formPow a.val (q + 1)) z.2 := fun z =>
    topRatio_formPow_prodForm w a z.1 z.2
  simp_rw [h]
  rw [integral_prod_mul, ENNReal.toReal_natCast, smul_eq_mul, sq]

end Product

end SGPT.Foundations.Analysis.Pending.NefMixedMass
