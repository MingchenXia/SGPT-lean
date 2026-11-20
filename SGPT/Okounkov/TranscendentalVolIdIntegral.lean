import SGPT.Okounkov.TranscendentalVolIdShift
import SGPT.Okounkov.TranscendentalWNRestrictedContinuity

/-!
# The volume as an integral of restricted volumes

Package VOL of the formalization of `thm:Okounkovtranmain` (blueprint
`claude-okounkov-transcendental`, nodes `tok:wn-integrated` and `tok:vol-integral`; chapter
`claude-tok-volid`): Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*
(DRWNXZ), Theorem 2.10 (second point) and Proposition 7.2.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag,
`ξ = {θ}` big, `E` a unit metric of `Y₁`, and `R(t) = vol_{X|Y₁}(ξ - t{Y₁})`. **Given Witt
Nyström's Theorem C in the integrated form `WNIntegratedStatement F`** (an explicit hypothesis; package WN):

* `continuousOn_restrictedVolume_sub`: `R` is continuous on `(ν_min, ν_max)`;
* `classVolumeReal_sub_sub_eq_integral`: `vol(ξ_a) - vol(ξ_b) = n ∫_a^b R` for
  `ν_min < a < b < ν_max` (WN21 is applied only at rational endpoints, where
  `isBigMeetingFirstDivisor_sub` gives its hypotheses; the real case follows by continuity);
* `sourceClassVolume_eq_lintegral_restrictedVolume` (**`tok:vol-integral`**):
  `vol(ξ) = n ∫_{ν_min}^{ν_max} vol_{X|Y₁}(ξ - t{Y₁}) dt`, using
  `vol(ξ - ν_min{Y₁}) = vol(ξ)` and `vol(ξ - ν_max{Y₁}) = 0` (`TranscendentalVolIdShift`).

Route (blueprint `tok:wn-integrated`): the WN package publishes the integrated identity and the
continuity directly (`TranscendentalWNStatement`), so the derivation from the derivative formula
and the concavity of `vol^{1/n}` is not needed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.PSH.VariableComplexAtlas

/-! ### Real-variable helpers -/

/-- A function continuous on an open set and constant at its rational points is constant. -/
theorem eq_of_continuousOn_of_rat {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hf : ContinuousOn f I)
    {C : ℝ} (h : ∀ q : ℚ, (q : ℝ) ∈ I → f q = C) {x : ℝ} (hx : x ∈ I) : f x = C := by
  by_contra hne
  have hopen : IsOpen (I ∩ f ⁻¹' {C}ᶜ) := hf.isOpen_inter_preimage hI isOpen_compl_singleton
  obtain ⟨q, hqI, hqC⟩ := Rat.denseRange_cast.exists_mem_open hopen ⟨x, hx, hne⟩
  exact hqC (h q hqI)

/-- For `f` continuous on `[a, b]` with values `R t < ∞`, `∫⁻_{[a,b]} R = ofReal (∫_a^b R.toReal)`. -/
theorem lintegral_Icc_eq_ofReal_integral {R : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a ≤ b)
    (hR : ContinuousOn (fun t => (R t).toReal) (Icc a b)) (hfin : ∀ t, R t < ⊤) :
    ∫⁻ t in Icc a b, R t = ENNReal.ofReal (∫ t in a..b, (R t).toReal) := by
  rw [intervalIntegral.integral_of_le hab]
  have hint : IntegrableOn (fun t => (R t).toReal) (Ioc a b) :=
    (hR.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun t => ENNReal.toReal_nonneg)]
  rw [← setLIntegral_congr Ioc_ae_eq_Icc]
  refine lintegral_congr fun t => ?_
  exact (ENNReal.ofReal_toReal (hfin t).ne).symm

section Integral

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `R(t) = vol_{X|Y₁}(ξ - t{Y₁})`. -/
def shiftedRestrictedVolume (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (t : ℝ) : ℝ≥0∞ :=
  firstFlagRestrictedVolume F
    (RealBottChern.ofRepresentative θ - t • RealBottChern.ofRepresentative E.curvature)

/-- `g(s) = vol(ξ - s{Y₁})` as a real number. -/
def shiftedVolumeReal (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (s : ℝ) : ℝ :=
  classVolumeReal F
    (RealBottChern.ofRepresentative θ - s • RealBottChern.ofRepresentative E.curvature)

theorem shiftedRestrictedVolume_lt_top (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (t : ℝ) :
    shiftedRestrictedVolume θ E t < ⊤ := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := ⟨F.firstDivisor.2.1.nonempty.some⟩
  exact TranscendentalVolumeConcavity.restrictedVolume_lt_top (contMDiff_firstFlagInclusion F)
    F.tail.omega _

theorem class_sub_smul_sub_smul (α β : RealBottChern (m + 1) F.carrier) (a t : ℝ) :
    α - a • β - t • β = α - (a + t) • β := by
  rw [sub_sub, add_smul]

theorem shiftedVolumeReal_eq (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (s : ℝ) :
    shiftedVolumeReal θ E s =
      (letI : MeasurableSpace F.carrier := borel F.carrier
       sourceClassVolume (RealBottChern.ofRepresentative (θ - s • E.curvature))).toReal := by
  unfold shiftedVolumeReal classVolumeReal
  rw [ofRepresentative_sub_smul]

theorem continuous_shiftedVolumeReal (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) :
    Continuous (shiftedVolumeReal θ E) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have hc := continuous_sourceClassVolume_sub_smul θ E.curvature
  have hfin : ∀ s : ℝ, sourceClassVolume (RealBottChern.ofRepresentative (θ - s • E.curvature)) ≠
      ⊤ := fun s => (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega _).ne
  have h := (ENNReal.continuousOn_toReal.comp_continuous hc fun s => hfin s)
  refine h.congr fun s => ?_
  rw [shiftedVolumeReal_eq]
  rfl

/-- WN21 between rational parameters `a < b` of `(ν_min, ν_max)`: the integrated identity and
the continuity of `R` on `[a, b]`. -/
theorem wn_rat {θ : ClosedRealOneOneForm (m + 1) F.carrier} (hWN : WNIntegratedStatement F)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {a b : ℚ} (hab : a ≤ b) (ha : firstValuationMin F θ < a) (hb : (b : ℝ) < firstValuationMax F θ) :
    shiftedVolumeReal θ E a - shiftedVolumeReal θ E b =
        ((m + 1 : ℕ) : ℝ) * ∫ t in (a : ℝ)..b, (shiftedRestrictedVolume θ E t).toReal ∧
      ContinuousOn (fun t => (shiftedRestrictedVolume θ E t).toReal) (Icc (a : ℝ) b) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hma := isBigMeetingFirstDivisor_sub hbig hE ha (hab'.trans_lt hb)
  have hmb := isBigMeetingFirstDivisor_sub hbig hE (show firstValuationMin F θ < (b : ℝ) from
    ha.trans_le hab') hb
  set α := RealBottChern.ofRepresentative θ
  set β := RealBottChern.ofRepresentative E.curvature
  have hc : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr hab'
  have hmb' : IsBigMeetingFirstDivisor F (α - (a : ℝ) • β - ((b : ℝ) - a) • β) := by
    rw [class_sub_smul_sub_smul, add_sub_cancel]; exact hmb
  have hI := hWN (α - (a : ℝ) • β) E hE ((b : ℝ) - a) hc hma hmb'
  have hC := wnContinuity F (α - (a : ℝ) • β) E hE ((b : ℝ) - a) hc hma hmb'
  have hfun : (fun t : ℝ => (firstFlagRestrictedVolume F (α - (a : ℝ) • β - t • β)).toReal) =
      fun t => (shiftedRestrictedVolume θ E ((a : ℝ) + t)).toReal := by
    funext t
    rw [class_sub_smul_sub_smul]
    rfl
  rw [hfun] at hI hC
  constructor
  · rw [class_sub_smul_sub_smul, add_sub_cancel] at hI
    unfold shiftedVolumeReal
    rw [hI, intervalIntegral.integral_comp_add_left
      (fun t => (shiftedRestrictedVolume θ E t).toReal) (a : ℝ), add_zero, add_sub_cancel]
  · have hmaps : MapsTo (fun t : ℝ => t - a) (Icc (a : ℝ) b) (Icc 0 ((b : ℝ) - a)) :=
      fun t ht => ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 _⟩
    have h := hC.comp (continuousOn_id.sub continuousOn_const) hmaps
    refine h.congr fun t _ => ?_
    simp

/-- **`tok:wn-integrated`, continuity**: `t ↦ vol_{X|Y₁}(ξ - t{Y₁})` is continuous on
`(ν_min, ν_max)`. -/
theorem continuousOn_restrictedVolume_sub {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hWN : WNIntegratedStatement F) (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    ContinuousOn (fun t => (shiftedRestrictedVolume θ E t).toReal)
      (Ioo (firstValuationMin F θ) (firstValuationMax F θ)) := by
  intro t ht
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn ht.1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ht.2
  have hab : a ≤ b := by exact_mod_cast (ha2.trans hb1).le
  have h := (wn_rat hWN hbig hE hab ha1 hb2).2
  exact (h.continuousAt (Icc_mem_nhds ha2 hb1)).continuousWithinAt

/-- **`tok:wn-integrated`**: `vol(ξ_a) - vol(ξ_b) = n ∫_a^b vol_{X|Y₁}(ξ - t{Y₁}) dt` for
`ν_min < a ≤ b < ν_max`. -/
theorem classVolumeReal_sub_sub_eq_integral {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hWN : WNIntegratedStatement F) (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {a b : ℝ} (ha : a ∈ Ioo (firstValuationMin F θ) (firstValuationMax F θ))
    (hb : b ∈ Ioo (firstValuationMin F θ) (firstValuationMax F θ)) :
    shiftedVolumeReal θ E a - shiftedVolumeReal θ E b =
      ((m + 1 : ℕ) : ℝ) * ∫ t in a..b, (shiftedRestrictedVolume θ E t).toReal := by
  set I := Ioo (firstValuationMin F θ) (firstValuationMax F θ) with hIdef
  set f := fun t => (shiftedRestrictedVolume θ E t).toReal with hfdef
  have hcont : ContinuousOn f I := continuousOn_restrictedVolume_sub hWN hbig hE
  have hint : ∀ x ∈ I, ∀ y ∈ I, IntervalIntegrable f volume x y := fun x hx y hy =>
    (hcont.mono (Set.ordConnected_Ioo.uIcc_subset hx hy)).intervalIntegrable
  -- `H(s) = g(s) + n ∫_a^s f` is constant on `I`
  set H : ℝ → ℝ := fun s => shiftedVolumeReal θ E s + ((m + 1 : ℕ) : ℝ) * ∫ t in a..s, f t
    with hH
  have hHc : ContinuousOn H I := by
    refine (continuous_shiftedVolumeReal θ E).continuousOn.add (continuousOn_const.mul ?_)
    intro s hs
    obtain ⟨lo, hlo1, hlo2⟩ := exists_between hs.1
    obtain ⟨hi, hhi1, hhi2⟩ := exists_between hs.2
    have hloI : lo ∈ I := ⟨hlo1, hlo2.trans hs.2⟩
    have hhiI : hi ∈ I := ⟨hs.1.trans hhi1, hhi2⟩
    have hsub : uIcc lo hi ⊆ I := Set.ordConnected_Ioo.uIcc_subset hloI hhiI
    have haIcc := ha
    -- primitive from `lo`, then shift the base point to `a`
    have hprim := intervalIntegral.continuousOn_primitive_interval'
      (hint lo hloI hi hhiI) (left_mem_uIcc : lo ∈ uIcc lo hi)
    have hnhds : uIcc lo hi ∈ 𝓝 s := by
      rw [uIcc_of_le (hlo2.trans hhi1).le]
      exact Icc_mem_nhds hlo2 hhi1
    have hcat : ContinuousAt (fun x => ∫ t in lo..x, f t) s := hprim.continuousAt hnhds
    have heq : (fun x => ∫ t in a..x, f t) =ᶠ[𝓝 s]
        fun x => (∫ t in a..lo, f t) + ∫ t in lo..x, f t := by
      filter_upwards [hnhds] with x hx
      rw [intervalIntegral.integral_add_adjacent_intervals (hint a ha lo hloI)
        (hint lo hloI x (hsub hx))]
    exact ((continuousAt_const.add hcat).congr heq.symm).continuousWithinAt
  have hHrat : ∀ q : ℚ, (q : ℝ) ∈ I → H q = H a := by
    intro q hq
    -- compare with a rational `p` near `a`
    have hconst : ∀ p : ℚ, (p : ℝ) ∈ I → H p = H q := by
      intro p hp
      rcases le_total p q with hpq | hqp
      · obtain ⟨h1, -⟩ := wn_rat hWN hbig hE hpq hp.1 hq.2
        simp only [hH]
        rw [← intervalIntegral.integral_add_adjacent_intervals (hint a ha p hp) (hint p hp q hq)]
        linarith
      · obtain ⟨h1, -⟩ := wn_rat hWN hbig hE hqp hq.1 hp.2
        simp only [hH]
        rw [← intervalIntegral.integral_add_adjacent_intervals (hint a ha q hq) (hint q hq p hp)]
        linarith
    have hHa : H a = H q := eq_of_continuousOn_of_rat isOpen_Ioo hHc hconst ha
    exact hHa.symm
  have hHb := eq_of_continuousOn_of_rat isOpen_Ioo hHc hHrat hb
  simp only [hH, intervalIntegral.integral_same, mul_zero, add_zero] at hHb
  linarith

/-- **`tok:vol-integral`** (DRWNXZ Proposition 7.2), given `WNIntegratedStatement F`:
`vol(ξ) = n ∫_{ν_min}^{ν_max} vol_{X|Y₁}(ξ - t{Y₁}) dt`. -/
theorem sourceClassVolume_eq_lintegral_restrictedVolume
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} (hWN : WNIntegratedStatement F)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    sourceClassVolume (RealBottChern.ofRepresentative θ) =
      ((m + 1 : ℕ) : ℝ≥0∞) * ∫⁻ t in Ioo (firstValuationMin F θ) (firstValuationMax F θ),
        shiftedRestrictedVolume θ E t := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  set a := firstValuationMin F θ with ha
  set b := firstValuationMax F θ with hb
  set I := Ioo a b with hI
  set R := shiftedRestrictedVolume θ E with hR
  set g := shiftedVolumeReal θ E with hg
  have hab : a < b := firstValuationMin_lt_firstValuationMax hbig
  set d := b - a with hd
  have hd0 : 0 < d := sub_pos.mpr hab
  set δ : ℕ → ℝ := fun k => d / ((k : ℝ) + 3) with hδ
  have hδpos : ∀ k, 0 < δ k := fun k => div_pos hd0 (by positivity)
  have hδlt : ∀ k, 2 * δ k < d := fun k => by
    have h3 : (3 : ℝ) ≤ (k : ℝ) + 3 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have : δ k ≤ d / 3 := div_le_div_of_nonneg_left hd0.le (by norm_num) h3
    linarith
  have hδanti : Antitone δ := fun i j hij => by
    have : (i : ℝ) + 3 ≤ (j : ℝ) + 3 := by exact_mod_cast Nat.add_le_add_right hij 3
    exact div_le_div_of_nonneg_left hd0.le (by positivity) this
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => ((k : ℝ) + 3)) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
    simpa [hδ] using h.const_div_atTop d
  set lo : ℕ → ℝ := fun k => a + δ k with hlo
  set hi : ℕ → ℝ := fun k => b - δ k with hhi
  have hloI : ∀ k, lo k ∈ I := fun k => ⟨by simp [hlo, hδpos k], by
    simp only [hlo]; linarith [hδlt k, hδpos k]⟩
  have hhiI : ∀ k, hi k ∈ I := fun k => ⟨by simp only [hhi]; linarith [hδlt k, hδpos k], by
    simp [hhi, hδpos k]⟩
  have hlohi : ∀ k, lo k ≤ hi k := fun k => by simp only [hlo, hhi]; linarith [hδlt k]
  -- the sets `[lo k, hi k]` increase to `I`
  set K : ℕ → Set ℝ := fun k => Icc (lo k) (hi k) with hK
  have hKmono : Monotone K := fun i j hij => Icc_subset_Icc
    (by simp only [hlo]; linarith [hδanti hij]) (by simp only [hhi]; linarith [hδanti hij])
  have hKU : (⋃ k, K k) = I := by
    ext t
    simp only [mem_iUnion, hK, mem_Icc]
    constructor
    · rintro ⟨k, h1, h2⟩
      exact ⟨(hloI k).1.trans_le h1, h2.trans_lt (hhiI k).2⟩
    · intro ht
      have hpos : 0 < min (t - a) (b - t) := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
      obtain ⟨k, hk⟩ := (hδlim.eventually (gt_mem_nhds hpos)).exists
      refine ⟨k, ?_, ?_⟩
      · simp only [hlo]; linarith [min_le_left (t - a) (b - t)]
      · simp only [hhi]; linarith [min_le_right (t - a) (b - t)]
  -- the masses of `[lo k, hi k]`
  set μ := (volume : Measure ℝ).withDensity R with hμ
  have hμK : ∀ k, μ (K k) = ENNReal.ofReal ((g (lo k) - g (hi k)) / ((m + 1 : ℕ) : ℝ)) := by
    intro k
    rw [hμ, withDensity_apply _ measurableSet_Icc]
    have hcont : ContinuousOn (fun t => (R t).toReal) (Icc (lo k) (hi k)) :=
      (continuousOn_restrictedVolume_sub hWN hbig hE).mono
        (Set.ordConnected_Ioo.out (hloI k) (hhiI k))
    rw [lintegral_Icc_eq_ofReal_integral (hlohi k) hcont (shiftedRestrictedVolume_lt_top θ E)]
    congr 1
    have h := classVolumeReal_sub_sub_eq_integral hWN hbig hE (hloI k) (hhiI k)
    have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    rw [h, mul_div_cancel_left₀ _ hn.ne']
  have hlim1 : Tendsto (fun k => μ (K k)) atTop (𝓝 (μ I)) := by
    rw [← hKU]; exact tendsto_measure_iUnion_atTop hKmono
  -- the limits of `g`
  have hga : g a = (sourceClassVolume (RealBottChern.ofRepresentative θ)).toReal := by
    rw [hg, shiftedVolumeReal_eq, sourceClassVolume_sub_firstValuationMin hbig hE]
  have hgb : g b = 0 := by
    rw [hg, shiftedVolumeReal_eq, sourceClassVolume_sub_firstValuationMax hbig hE]; rfl
  have hloT : Tendsto lo atTop (𝓝 a) := by
    simpa [hlo] using (tendsto_const_nhds (x := a)).add hδlim
  have hhiT : Tendsto hi atTop (𝓝 b) := by
    simpa [hhi] using (tendsto_const_nhds (x := b)).sub hδlim
  have hgc := continuous_shiftedVolumeReal θ E
  have hlim2 : Tendsto (fun k => μ (K k)) atTop
      (𝓝 (ENNReal.ofReal ((g a - g b) / ((m + 1 : ℕ) : ℝ)))) := by
    simp only [hμK]
    refine ENNReal.tendsto_ofReal ?_
    exact (((hgc.tendsto a).comp hloT).sub ((hgc.tendsto b).comp hhiT)).div_const _
  have hμI := tendsto_nhds_unique hlim1 hlim2
  rw [hga, hgb, sub_zero] at hμI
  have hμI' : ∫⁻ t in I, R t = ENNReal.ofReal
      ((sourceClassVolume (RealBottChern.ofRepresentative θ)).toReal / ((m + 1 : ℕ) : ℝ)) := by
    rw [← hμI, hμ, withDensity_apply _ measurableSet_Ioo]
  rw [hμI']
  have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  rw [show (((m + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((m + 1 : ℕ) : ℝ) by
      rw [ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul hn.le, mul_div_cancel₀ _ hn.ne',
    ENNReal.ofReal_toReal (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega _).ne]

end Integral

end SGPT.Okounkov.TranscendentalVolId
