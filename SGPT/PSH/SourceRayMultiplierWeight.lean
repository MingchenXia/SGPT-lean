import SGPT.Foundations.Analysis.FirstPass.MultiplierIdeals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The one-variable estimates behind the He--Testorf--Wang formula

Source `prop:mis_RWN` (chapter `chapter_testcurve`). For a function
`F : ℝ → [-∞, ∞]` (the values `t ↦ ℓ_t(x)` of a geodesic ray at one point) we
compare the Legendre-type infimum `ℓ^*_τ(x) = inf_{t>0} (ℓ_t(x) - tτ)` with the
weight `∫_0^∞ exp(-ℓ_t(x) + tτ) dt`:

* `multiplierWeight_iInf_le_rayWeight`: if `t ↦ F t - t m` is decreasing on
  `[0,∞)` and `τ < m`, then `exp(-ℓ^*_τ) ≤ e^{1+m-τ} ∫_0^∞ exp(-ℓ_t + tτ) dt`
  (Step 1 of the source proof);
* `rayWeight_le_multiplierWeight_iInf`: for every `τ' > τ`,
  `∫_0^∞ exp(-ℓ_t + tτ) dt ≤ (τ' - τ)⁻¹ exp(-ℓ^*_{τ'})` (Step 2).

All values are extended reals; poles are retained (`exp(+∞) = ∞`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.RayMultiplier

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis

/-- The weight `t ↦ exp(-(F t - tτ))`, the integrand of the source formula. -/
def rayIntegrand (F : ℝ → EReal) (τ t : ℝ) : ℝ≥0∞ :=
  multiplierWeight 1 (F t - ((t * τ : ℝ) : EReal))

/-- The source weight `∫_0^∞ exp(-F t + tτ) dt`. -/
def rayWeight (F : ℝ → EReal) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), rayIntegrand F τ t

/-- The Legendre-type infimum `inf_{t>0} (F t - tτ)`. -/
def rayInverse (F : ℝ → EReal) (τ : ℝ) : EReal :=
  ⨅ t : Ioi (0 : ℝ), F t.1 - ((t.1 * τ : ℝ) : EReal)

theorem multiplierWeight_one (a : EReal) : multiplierWeight 1 a = EReal.exp (-a) := by
  simp [multiplierWeight]

private theorem sub_coe_add_coe (x : EReal) (p q : ℝ) :
    x - (p : EReal) + (q : EReal) = x + ((q - p : ℝ) : EReal) := by
  rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
  congr 2
  ring

private theorem sub_coe_eq (x : EReal) (p q : ℝ) :
    x - (p : EReal) = x - (q : EReal) + ((q - p : ℝ) : EReal) := by
  rw [sub_coe_add_coe, sub_eq_add_neg, ← EReal.coe_neg]
  congr 2
  ring

/-- The lower bound for the weight in terms of a near-minimizing time. -/
theorem ofReal_exp_le_rayWeight {F : ℝ → EReal} {m τ : ℝ} (hτ : τ < m)
    (hanti : AntitoneOn (fun t => F t - ((t * m : ℝ) : EReal)) (Ici 0))
    {b : ℝ} (hb : rayInverse F τ < b) :
    ENNReal.ofReal (Real.exp (-(b + (m - τ)))) ≤ rayWeight F τ := by
  obtain ⟨t₀, ht₀⟩ := iInf_lt_iff.mp hb
  have ht₀pos : 0 < t₀.1 := t₀.2
  have hbound : ∀ t ∈ Icc t₀.1 (t₀.1 + 1),
      F t - ((t * τ : ℝ) : EReal) ≤ ((b + (m - τ) : ℝ) : EReal) := by
    intro t ht
    have ht0 : t₀.1 ≤ t := ht.1
    have hmono := hanti (show t₀.1 ∈ Ici (0 : ℝ) from le_of_lt ht₀pos)
      (show t ∈ Ici (0 : ℝ) from le_trans (le_of_lt ht₀pos) ht0) ht0
    simp only at hmono
    calc F t - ((t * τ : ℝ) : EReal)
        = F t - ((t * m : ℝ) : EReal) + ((t * m - t * τ : ℝ) : EReal) := sub_coe_eq _ _ _
      _ ≤ F t₀.1 - ((t₀.1 * m : ℝ) : EReal) + ((t * m - t * τ : ℝ) : EReal) := by
          gcongr
      _ = F t₀.1 - ((t₀.1 * τ : ℝ) : EReal) + (((t - t₀.1) * (m - τ) : ℝ) : EReal) := by
          rw [sub_coe_add_coe, sub_coe_add_coe]
          congr 2
          ring
      _ ≤ (b : EReal) + ((m - τ : ℝ) : EReal) := by
          have h1 : t - t₀.1 ≤ 1 := by linarith [ht.2]
          have h2 : 0 ≤ m - τ := by linarith
          have h3 : (t - t₀.1) * (m - τ) ≤ m - τ := by nlinarith
          exact add_le_add ht₀.le (EReal.coe_le_coe_iff.mpr h3)
      _ = ((b + (m - τ) : ℝ) : EReal) := by rw [EReal.coe_add]
  calc ENNReal.ofReal (Real.exp (-(b + (m - τ))))
      = ∫⁻ _t in Icc t₀.1 (t₀.1 + 1), ENNReal.ofReal (Real.exp (-(b + (m - τ)))) := by
        rw [setLIntegral_const, Real.volume_Icc]
        simp
    _ ≤ ∫⁻ t in Icc t₀.1 (t₀.1 + 1), rayIntegrand F τ t := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [rayIntegrand, multiplierWeight_one, ← EReal.exp_coe]
        apply EReal.exp_monotone
        rw [EReal.coe_neg]
        exact EReal.neg_le_neg_iff.mpr (hbound t ht)
    _ ≤ rayWeight F τ := by
        apply lintegral_mono_set
        intro t ht
        exact lt_of_lt_of_le ht₀pos ht.1

/-- Step 1 of the source proof of `prop:mis_RWN`:
`exp(-ℓ^*_τ) ≤ e^{1+m-τ} ∫_0^∞ exp(-ℓ_t + tτ) dt` whenever `t ↦ ℓ_t - tm` is
decreasing and `τ < m`. -/
theorem multiplierWeight_iInf_le_rayWeight {F : ℝ → EReal} {m τ : ℝ} (hτ : τ < m)
    (hanti : AntitoneOn (fun t => F t - ((t * m : ℝ) : EReal)) (Ici 0)) :
    multiplierWeight 1 (rayInverse F τ) ≤
      ENNReal.ofReal (Real.exp (1 + (m - τ))) * rayWeight F τ := by
  induction h : rayInverse F τ using EReal.rec with
  | bot =>
    rw [multiplierWeight_bot one_pos]
    have hW : rayWeight F τ = ⊤ := by
      by_contra hne
      have hlt : rayWeight F τ < ⊤ := lt_top_iff_ne_top.mpr hne
      set w := (rayWeight F τ).toReal
      have hb : rayInverse F τ < ((-(Real.log (w + 1)) - (m - τ) : ℝ) : EReal) := by
        rw [h]; exact EReal.bot_lt_coe _
      have hle := ofReal_exp_le_rayWeight hτ hanti hb
      have he : Real.exp (-((-(Real.log (w + 1)) - (m - τ)) + (m - τ))) = w + 1 := by
        rw [show -((-(Real.log (w + 1)) - (m - τ)) + (m - τ)) = Real.log (w + 1) by ring]
        exact Real.exp_log (by positivity)
      rw [he] at hle
      have := (ENNReal.ofReal_le_iff_le_toReal hne).mp hle
      linarith
    rw [hW, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | top =>
    rw [multiplierWeight_top one_pos]
    exact bot_le
  | coe r =>
    have hb : rayInverse F τ < ((r + 1 : ℝ) : EReal) := by
      rw [h]; exact_mod_cast (by linarith : r < r + 1)
    have hle := ofReal_exp_le_rayWeight hτ hanti hb
    rw [multiplierWeight_coe]
    calc ENNReal.ofReal (Real.exp (-(1 * r)))
        = ENNReal.ofReal (Real.exp (1 + (m - τ))) *
            ENNReal.ofReal (Real.exp (-(r + 1 + (m - τ)))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (Real.exp (1 + (m - τ))) * rayWeight F τ := by gcongr

/-- `∫_0^∞ e^{-εt} dt = 1/ε`. -/
theorem lintegral_exp_neg_mul_Ioi {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * ε))) = ENNReal.ofReal (1 / ε) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp ((-ε) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  simp_rw [show ∀ t : ℝ, -(t * ε) = (-ε) * t from fun t => by ring]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  simp

/-- Step 2 of the source proof of `prop:mis_RWN`:
`∫_0^∞ exp(-ℓ_t + tτ) dt ≤ (τ' - τ)⁻¹ exp(-ℓ^*_{τ'})` for `τ < τ'`. -/
theorem rayWeight_le_multiplierWeight_iInf (F : ℝ → EReal) {τ τ' : ℝ} (hττ' : τ < τ') :
    rayWeight F τ ≤ ENNReal.ofReal (1 / (τ' - τ)) * multiplierWeight 1 (rayInverse F τ') := by
  have hε : 0 < τ' - τ := by linarith
  calc rayWeight F τ
      ≤ ∫⁻ t in Ioi (0 : ℝ), multiplierWeight 1 (rayInverse F τ') *
          ENNReal.ofReal (Real.exp (-(t * (τ' - τ)))) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        have hinf : rayInverse F τ' ≤ F t - ((t * τ' : ℝ) : EReal) :=
          iInf_le (fun s : Ioi (0 : ℝ) => F s.1 - ((s.1 * τ' : ℝ) : EReal)) ⟨t, ht⟩
        rw [rayIntegrand, multiplierWeight_one, multiplierWeight_one, ← EReal.exp_coe,
          ← EReal.exp_add]
        apply EReal.exp_monotone
        have hsplit : F t - ((t * τ : ℝ) : EReal) =
            F t - ((t * τ' : ℝ) : EReal) + ((t * (τ' - τ) : ℝ) : EReal) := by
          rw [sub_coe_add_coe]
          rw [sub_eq_add_neg, ← EReal.coe_neg]
          congr 2
          ring
        rw [hsplit]
        calc -(F t - ((t * τ' : ℝ) : EReal) + ((t * (τ' - τ) : ℝ) : EReal))
            = -(F t - ((t * τ' : ℝ) : EReal)) + ((-(t * (τ' - τ)) : ℝ) : EReal) := by
              rw [EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)),
                sub_eq_add_neg, EReal.coe_neg]
          _ ≤ -rayInverse F τ' + ((-(t * (τ' - τ)) : ℝ) : EReal) := by
              gcongr
              exact EReal.neg_le_neg_iff.mpr hinf
    _ = multiplierWeight 1 (rayInverse F τ') *
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * (τ' - τ)))) := by
        rw [lintegral_const_mul]
        exact ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp (measurable_id.mul_const _).neg)
    _ = ENNReal.ofReal (1 / (τ' - τ)) * multiplierWeight 1 (rayInverse F τ') := by
        rw [lintegral_exp_neg_mul_Ioi hε, mul_comm]


/-- The integrand factors as `exp(-(F t - tm)) · exp(-t(m - τ))`. -/
theorem rayIntegrand_eq_mul (F : ℝ → EReal) (m τ t : ℝ) :
    rayIntegrand F τ t = EReal.exp (-(F t - ((t * m : ℝ) : EReal))) *
      ENNReal.ofReal (Real.exp (-(t * (m - τ)))) := by
  rw [rayIntegrand, multiplierWeight_one, ← EReal.exp_coe, ← EReal.exp_add, sub_coe_eq _ _ (t * m),
    EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)),
    sub_eq_add_neg, ← EReal.coe_neg]
  congr 3
  ring

/-- The source weight `y ↦ ∫_0^∞ exp(-F_y(t) + tτ) dt` is measurable as soon as
every time slice is measurable and every `t ↦ F_y(t) - tm` is decreasing on
`(0,∞)`. (A monotone function has only countably many discontinuities, so the
integrand agrees almost everywhere in `t` with its right-continuous
regularization, which is jointly measurable.) -/
theorem measurable_rayWeight {α : Type*} [MeasurableSpace α] {F : α → ℝ → EReal} {m τ : ℝ}
    (hanti : ∀ y, AntitoneOn (fun t => F y t - ((t * m : ℝ) : EReal)) (Ioi 0))
    (hmeas : ∀ t, Measurable fun y => F y t) :
    Measurable fun y => rayWeight (F y) τ := by
  let E : α → ℝ → ℝ≥0∞ := fun y t => EReal.exp (-(F y t - ((t * m : ℝ) : EReal)))
  let k : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(t * (m - τ))))
  let Eplus : α → ℝ → ℝ≥0∞ := fun y t => ⨅ q : ℚ, if t < (q : ℝ) then E y q else ⊤
  have hEmono : ∀ y, MonotoneOn (E y) (Ioi 0) := by
    intro y a ha b hb hab
    apply EReal.exp_monotone
    exact EReal.neg_le_neg_iff.mpr (hanti y ha hb hab)
  have hEmeas : ∀ q : ℝ, Measurable fun y => E y q := by
    intro q
    have h1 : Measurable fun y => F y q - ((q * m : ℝ) : EReal) := by
      simp_rw [sub_eq_add_neg]
      exact (hmeas q).add_const _
    exact EReal.measurable_exp.comp h1.neg
  have hjoint : Measurable fun p : α × ℝ => Eplus p.1 p.2 * k p.2 := by
    refine Measurable.mul ?_ ?_
    · refine Measurable.iInf fun q => ?_
      refine Measurable.ite ?_ ((hEmeas q).comp measurable_fst) measurable_const
      exact measurableSet_lt measurable_snd measurable_const
    · exact ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp ((measurable_snd.mul_const _).neg))
  have hae : ∀ y, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      rayIntegrand (F y) τ t = Eplus y t * k t := by
    intro y
    have hcount := (hEmono y).countable_not_continuousWithinAt_Ioi
    have hnull : volume {x ∈ Ioi (0 : ℝ) | ¬ContinuousWithinAt (E y) (Ioi 0 ∩ Ioi x) x} = 0 :=
      hcount.measure_zero _
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun t ht htpos => ?_
    have hcont : ContinuousWithinAt (E y) (Ioi 0 ∩ Ioi t) t := by
      by_contra hc
      exact ht ⟨htpos, hc⟩
    rw [rayIntegrand_eq_mul _ m]
    congr 1
    apply le_antisymm
    · refine le_iInf fun q => ?_
      split_ifs with hq
      · exact hEmono y htpos (lt_trans htpos hq) hq.le
      · exact le_top
    · refine le_of_forall_gt fun c hc => ?_
      have hev : ∀ᶠ s in nhdsWithin t (Ioi 0 ∩ Ioi t), E y s < c :=
        hcont.eventually (gt_mem_nhds hc)
      have hset : Ioi (0 : ℝ) ∩ Ioi t = Ioi t := by
        ext s; constructor
        · exact fun h => h.2
        · exact fun h => ⟨show (0 : ℝ) < s from lt_trans htpos h, h⟩
      rw [hset] at hev
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < u from hu)
      calc Eplus y t ≤ (if t < (q : ℝ) then E y q else ⊤) := iInf_le _ q
        _ = E y q := if_pos hq1
        _ < c := hsub ⟨hq1, hq2⟩
  have heq : (fun y => rayWeight (F y) τ) =
      fun y => ∫⁻ t, Eplus y t * k t ∂(volume.restrict (Ioi (0 : ℝ))) := by
    funext y
    exact lintegral_congr_ae (hae y)
  rw [heq]
  exact hjoint.lintegral_prod_right'

end SGPT.PSH.RayMultiplier
