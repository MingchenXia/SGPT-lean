import SGPT.NPP.LogConcavityMixedDiscriminant
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

/-!
# The Khovanskii–Teissier inequality for nef classes

Support for the log-concavity of mixed masses (source `thm:logconc`; Xia, *Foundations of
pluripotential theory*, `cor:nef-mixed-intersection-geometric-mean`). On a compact connected
Kähler manifold `M` of dimension `N = q + 1`, for smooth closed real `(1,1)`-forms `θᵢ` that are
nef,

`∫_M θ₀ ∧ ⋯ ∧ θ_{N-1} ≥ ∏ᵢ (∫_M θᵢᴺ)^{1/N}`.

## Proof

Our route differs from the source (which uses the mixed Hodge index theorem). For Kähler
forms `κᵢ`, Yau's theorem (TN `YauTheorem.exists_kahler_mongeAmpere_eq_smul`, proved by the
continuity method) gives Kähler forms `κᵢ' = κᵢ + ddᶜφᵢ` with `κᵢ'ᴺ = cᵢ ωᴺ`,
`cᵢ = vol(κᵢ)/vol(ω)`. The pointwise geometric-mean inequality for mixed discriminants
(`factorial_mul_prod_det_rpow_le_mixedCoefficient_re`) gives
`κ₀' ∧ ⋯ ∧ κ_{N-1}' ≥ ∏ cᵢ^{1/N} ωᴺ`; integrating and using class invariance of slot integrals
gives the Kähler case. For nef `θᵢ`, the forms `θᵢ + εω + ddᶜfᵢ` are Kähler for suitable smooth
`fᵢ`, and both sides are polynomials, hence continuous, in `ε → 0`.

## Main results

* `prod_actualTopPowerDensity_rpow_le_actualMixedTopDensity`: the pointwise inequality for
  strictly positive `(1,1)`-forms.
* `prod_slotIntegral_rpow_le_slotIntegral_kahler`: the Kähler case.
* `prod_slotIntegral_rpow_le_slotIntegral_of_nef`: the nef case.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NPP.LogConcavity

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.NefMixedMass SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

/-! ### The pointwise inequality -/

section Pointwise

variable {N : ℕ}

/-- **Pointwise mixed inequality.** For strictly positive real `(1,1)`-forms `Aᵢ` on `ℂᴺ`,
`∏ᵢ (Aᵢᴺ)^{1/N} ≤ A₀ ∧ ⋯ ∧ A_{N-1}` (densities in the standard frame). -/
theorem prod_actualTopPowerDensity_rpow_le_actualMixedTopDensity (hN : 0 < N)
    (A : Fin N → CoordinateRealTwoForm N) (hA1 : ∀ i, IsOneOne (A i)) (hA2 : ∀ i, IsStrictlyPositive (A i)) :
    ∏ i, (actualTopPowerDensity (A i)) ^ ((N : ℝ)⁻¹) ≤ actualMixedTopDensity A := by
  rw [ConcentrationMassComparison.actualMixedTopDensity_eq_re hA1]
  simp_rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det (hA1 _)]
  set H : Fin N → Matrix (Fin N) (Fin N) ℂ := fun i =>
    normalizedHermitianMatrix (A i) with hHdef
  have hH : ∀ i, (H i).PosDef := fun i =>
    ConcentrationMassComparison.normalizedHermitianMatrix_posDef (hA1 i) (hA2 i)
  have hkey := factorial_mul_prod_det_rpow_le_mixedCoefficient_re N H hH
  set a : ℝ := (N.factorial : ℝ) / Real.pi ^ N with ha
  have hapos : 0 < a := div_pos (by exact_mod_cast Nat.factorial_pos N) (pow_pos Real.pi_pos N)
  have hdet : ∀ i, 0 ≤ (H i).det.re := fun i => (det_re_pos (hH i)).le
  have hsplit : ∏ i, (a * (H i).det.re) ^ ((N : ℝ)⁻¹) =
      a * ∏ i, (H i).det.re ^ ((N : ℝ)⁻¹) := by
    simp_rw [Real.mul_rpow hapos.le (hdet _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_natCast, ← Real.rpow_mul hapos.le, inv_mul_cancel₀ (by exact_mod_cast hN.ne'),
      Real.rpow_one]
  rw [hsplit, ha, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (pow_pos Real.pi_pos N)]
  exact hkey

end Pointwise

/-! ### Kähler classes -/

section Kahler

variable {q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The pure slot integral of a Kähler form is its volume. -/
theorem slotIntegral_const_eq_kahlerVolume (w κ : KahlerBackground (q + 1) M) :
    slotIntegral w (fun _ => κ.form) = (kahlerVolume κ).real univ := by
  rw [← integral_formPow_eq_slotIntegral]
  exact YauTheorem.integral_topRatio_formPow_eq w κ

variable [ConnectedSpace M]

/-- **Khovanskii–Teissier for Kähler classes**: for Kähler forms `κᵢ`,
`∏ᵢ (∫ κᵢᴺ)^{1/N} ≤ ∫ κ₀ ∧ ⋯ ∧ κ_{N-1}`. -/
theorem prod_slotIntegral_rpow_le_slotIntegral_kahler (w : KahlerBackground (q + 1) M)
    (κ : Fin (q + 1) → KahlerBackground (q + 1) M) :
    ∏ i, (slotIntegral w (fun _ => (κ i).form)) ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      slotIntegral w (fun i => (κ i).form) := by
  classical
  set r : ℝ := ((q + 1 : ℕ) : ℝ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  choose φ hφ hK hMA using fun i =>
    YauTheorem.exists_kahler_mongeAmpere_eq_smul (Nat.succ_pos q) (κ i) w
  set V : ℝ := (kahlerVolume w).real univ with hV
  have hVpos : 0 < V := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos w
  set c : Fin (q + 1) → ℝ := fun i => (kahlerVolume (κ i)).real univ / V with hc
  have hcpos : ∀ i, 0 < c i := fun i =>
    div_pos (NefCoreKahlerCurrent.kahlerVolume_real_univ_pos (κ i)) hVpos
  rw [← slotIntegral_add_ddc w (fun i => (κ i).form) φ hφ]
  set κ' : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M := fun i =>
    (κ i).form + ddcClosedForm (φ i) (hφ i) with hκ'
  -- the pointwise lower bound for the density ratio
  have hpt : ∀ x, ∏ i, c i ^ r ≤ topRatio w.form.val (slotForm κ') x := by
    intro x
    set e := complexChartAt (n := q + 1) x
    have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    rw [topRatio, chartRatio, topDensity_slotForm_coeff, ProductTestForms.formPow_coeff,
      topDensity_formPower]
    have hd := YauTheorem.actualTopPowerDensity_pos w hz
    rw [le_div_iff₀ hd]
    have h := prod_actualTopPowerDensity_rpow_le_actualMixedTopDensity (Nat.succ_pos q)
      (fun i => (κ' i).val.coeff e (e.val x)) (fun i => ((hK i).1 e (e.val x) hz).1)
      (fun i => ((hK i).1 e (e.val x) hz).2)
    refine le_trans (le_of_eq ?_) h
    have hMA' : ∀ i, actualTopPowerDensity ((κ' i).val.coeff e (e.val x)) =
        c i * actualTopPowerDensity (w.form.val.coeff e (e.val x)) := fun i => hMA i e (e.val x) hz
    simp_rw [hMA']
    rw [← hr]
    simp_rw [Real.mul_rpow (hcpos _).le hd.le]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_natCast (actualTopPowerDensity _ ^ r), ← Real.rpow_mul hd.le, hr,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  have hint : (∏ i, c i ^ r) * V ≤ slotIntegral w κ' := by
    have h := integral_mono (integrable_const (∏ i, c i ^ r)) (NefMixedMass.integrable_topRatio w (slotForm κ'))
      hpt
    rw [integral_const, smul_eq_mul, mul_comm] at h
    exact h
  refine le_trans (le_of_eq ?_) hint
  simp_rw [slotIntegral_const_eq_kahlerVolume w]
  have hvol : ∀ i, (kahlerVolume (κ i)).real univ = c i * V := fun i => by
    rw [hc]; field_simp
  simp_rw [hvol, Real.mul_rpow (hcpos _).le hVpos.le]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast (V ^ r), ← Real.rpow_mul hVpos.le, hr,
    inv_mul_cancel₀ (by positivity), Real.rpow_one]

end Kahler

/-! ### Nef classes -/

section Nef

variable {q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- The inequality for the Kähler perturbations `θᵢ + εω` of nef forms. -/
theorem prod_slotIntegral_rpow_le_slotIntegral_add_smul (w : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M) (hθ : ∀ i, NefWithRespectTo w (θ i))
    {ε : ℝ} (hε : 0 < ε) :
    ∏ i, (slotIntegral w (fun _ => θ i + ε • w.form)) ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      slotIntegral w (fun i => θ i + ε • w.form) := by
  classical
  choose f hf hsemi using fun i => exists_isSemipositive_of_nef (hθ i) (half_pos hε)
  set κ : Fin (q + 1) → KahlerBackground (q + 1) M := fun i =>
    ⟨θ i + (ε / 2) • w.form + ddcClosedForm (f i) (hf i) + (ε / 2) • w.form,
      NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive w (hsemi i) (half_pos hε)⟩ with hκ
  have hform : ∀ i, (κ i).form = (θ i + ε • w.form) + ddcClosedForm (f i) (hf i) := by
    intro i
    simp only [hκ]
    have : ε • w.form = (ε / 2) • w.form + (ε / 2) • w.form := by
      rw [← add_smul, add_halves]
    rw [this]
    abel
  have h := prod_slotIntegral_rpow_le_slotIntegral_kahler w κ
  simp_rw [hform] at h
  rw [slotIntegral_add_ddc w (fun i => θ i + ε • w.form) f hf] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  exact (slotIntegral_add_ddc w (fun _ => θ i + ε • w.form) (fun _ => f i) (fun _ => hf i)).symm

/-- **Khovanskii–Teissier for nef classes** (`cor:nef-mixed-intersection-geometric-mean` of the
foundations): for nef smooth closed real `(1,1)`-forms `θᵢ`,
`∏ᵢ (∫ θᵢᴺ)^{1/N} ≤ ∫ θ₀ ∧ ⋯ ∧ θ_{N-1}`. -/
theorem prod_slotIntegral_rpow_le_slotIntegral_of_nef (w : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M) (hθ : ∀ i, NefWithRespectTo w (θ i)) :
    ∏ i, (slotIntegral w (fun _ => θ i)) ^ (((q + 1 : ℕ) : ℝ)⁻¹) ≤ slotIntegral w θ := by
  classical
  set r : ℝ := ((q + 1 : ℕ) : ℝ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hmixed : Tendsto (fun t : ℝ => slotIntegral w (fun i => θ i + t • w.form))
      (𝓝[>] 0) (𝓝 (slotIntegral w θ)) := by
    have h := (continuous_slotIntegral_add_smul w θ fun _ => w.form).continuousWithinAt
      (s := Ioi (0 : ℝ)) (x := 0)
    simpa only [zero_smul, add_zero] using h.tendsto
  have hpure : ∀ i, Tendsto (fun t : ℝ => slotIntegral w (fun _ => θ i + t • w.form))
      (𝓝[>] 0) (𝓝 (slotIntegral w (fun _ => θ i))) := by
    intro i
    have h := (continuous_slotIntegral_add_smul w (fun _ => θ i) fun _ => w.form).continuousWithinAt
      (s := Ioi (0 : ℝ)) (x := 0)
    simpa only [zero_smul, add_zero] using h.tendsto
  have hprod : Tendsto (fun t : ℝ => ∏ i, (slotIntegral w (fun _ => θ i + t • w.form)) ^ r)
      (𝓝[>] 0) (𝓝 (∏ i, (slotIntegral w (fun _ => θ i)) ^ r)) := by
    refine tendsto_finsetProd _ fun i _ => ?_
    exact ((Real.continuousAt_rpow_const _ r (Or.inr hr0.le)).tendsto).comp (hpure i)
  refine le_of_tendsto_of_tendsto hprod hmixed ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact prod_slotIntegral_rpow_le_slotIntegral_add_smul w θ hθ ht

end Nef

end SGPT.NPP.LogConcavity
