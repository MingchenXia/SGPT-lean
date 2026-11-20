import SGPT.TestCurve.RWNTwistedCurveToRay

/-!
# The twisted Ross–Witt Nyström correspondence (`rmk:testcurve:L815`)

Source `rmk:testcurve:L815` (chapter *Test curves*): *"One could also consider geodesic rays
emanating from another potential `Φ ∈ 𝓔(X, θ; φ)`. In this case, one can show that these
geodesic rays are in bijection with `Φ`-twisted test curves […]. The above results equally work
in the twisted setting."*

* `twistedLegendre_geodesic_closed`, `twistedLegendreRay_mem` (twisted `lma:LegsendsTCtoR`): the
  Legendre transform of a `Φ`-twisted test curve is a geodesic ray in `𝓔(X, θ; φ)` emanating
  from `Φ`.
* `twistedLegendre_supremum_whole` (twisted `lma:suplegenlinear`) and
  `twistedRay_supremum_whole` (twisted `cor:reltestcursuplinear`): `Γ*_t ≤ Φ + tΓ_max`, with
  `sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max`, and `t ↦ Γ*_t - tΓ_max` decreasing.
* `twistedConstCurve_sup_ne`: the untwisted normalisation `sup_X Γ*_t = tΓ_max` of
  `lma:suplegenlinear` fails for twisted test curves (constant curve `Γ_τ = Φ`, `sup_X Φ < 0`).
* `twistedLegendreRay_injective`, `twistedLegendre_slopeSet_sSup`: the Legendre transform is
  injective; `Γ_max` is the supremum of the slopes `τ` with `ℓ*_τ ≢ -∞`.
* **`twistedRWNStatement_holds`**: the statement `TwistedRWNStatement` of the remark, for every
  `Φ ∈ 𝓔(X, θ; φ)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.TestConf

/-- `u + p - q = u + (p - q)` in `EReal` for real `p, q`. -/
theorem ereal_add_coe_sub_coe (u : EReal) (p q : ℝ) :
    u + (p : EReal) - (q : EReal) = u + ((p - q : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot => simp
  | top => simp only [EReal.top_add_coe, EReal.top_sub_coe]
  | coe u =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring

/-- `u - p + q = u + (q - p)` in `EReal` for real `p, q`. -/
theorem ereal_sub_coe_add_coe (u : EReal) (p q : ℝ) :
    u - (p : EReal) + (q : EReal) = u + ((q - p : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot => simp
  | top => simp only [EReal.top_add_coe, EReal.top_sub_coe]
  | coe u =>
    rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {Φ : M → EReal}
  [CompactSpace M] [ConnectedSpace M]

/-! ### Supremum (twisted `lma:suplegenlinear`) -/

omit [CompactSpace M] in
/-- **Twisted `lma:suplegenlinear`**: `Γ*_t ≤ Φ + tΓ_max` for `t ≥ 0`; the bound is sharp:
for `t > 0` and `c < tΓ_max` there is `x` with `Φ(x) + c < Γ*_t(x)` (so
`sup_{Φ > -∞} (Γ*_t - Φ) = tΓ_max`); and `t ↦ Γ*_t - tΓ_max` is decreasing on `[0, ∞)`. -/
theorem twistedLegendre_supremum_whole (Γ : SourceTwistedTestCurve θ Φ) :
    (∀ (t : Ici (0 : ℝ)) (x : M),
      twistedLegendreRay Γ t x ≤ Φ x + ((t.1 * Γ.max : ℝ) : EReal)) ∧
    (∀ t : ℝ, 0 < t → ∀ c : ℝ, c < t * Γ.max →
      ∃ x, Φ x + (c : EReal) < twistedRawLegendre Γ t x) ∧
    (∀ x, AntitoneOn (fun t : ℝ ↦ sourceRayExtension (twistedLegendreRay Γ) t x -
      ((t * Γ.max : ℝ) : EReal)) (Ici 0)) := by
  refine ⟨fun t x ↦ ?_, fun t ht c hc ↦ ?_, fun x ↦ ?_⟩
  · by_cases ht : t.1 = 0
    · simp only [twistedLegendreRay, if_pos ht]
      rw [ht, zero_mul, EReal.coe_zero, add_zero]
    · rw [twistedLegendreRay_pos Γ ht]
      exact twistedRawLegendre_le Γ t.2 x
  · have hct : c / t < Γ.max := (div_lt_iff₀ ht).mpr (by linarith [mul_comm t Γ.max])
    let τ : Iio Γ.max := ⟨(c / t + Γ.max) / 2, by change (c / t + Γ.max) / 2 < Γ.max; linarith⟩
    have hτ : c < t * τ.1 := by
      have h1 : c / t < τ.1 := by change c / t < (c / t + Γ.max) / 2; linarith
      have h2 := (div_lt_iff₀ ht).mp h1
      linarith [mul_comm t τ.1]
    obtain ⟨x, hx⟩ := twisted_exists_close Γ τ (sub_pos.mpr hτ)
    refine ⟨x, ?_⟩
    calc Φ x + (c : EReal) = (Φ x + ((-(t * τ.1 - c) : ℝ) : EReal)) + ((t * τ.1 : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
          congr 2
          ring
      _ < Γ.potential τ x + ((t * τ.1 : ℝ) : EReal) := EReal.add_lt_add_right_coe hx _
      _ ≤ twistedRawLegendre Γ t x := by
          rw [add_comm]
          exact le_twistedRawLegendre Γ t τ x
  · intro s hs b hb hsb
    change sourceRayExtension (twistedLegendreRay Γ) b x - ((b * Γ.max : ℝ) : EReal) ≤
      sourceRayExtension (twistedLegendreRay Γ) s x - ((s * Γ.max : ℝ) : EReal)
    have hs0 : 0 ≤ s := hs
    rcases hs0.eq_or_lt with h0 | hspos
    · subst h0
      rw [twistedLegendre_extension_zero, zero_mul, EReal.coe_zero, sub_zero]
      rcases (show (0 : ℝ) ≤ b from hb).eq_or_lt with hb0 | hbpos
      · subst hb0
        rw [twistedLegendre_extension_zero, zero_mul, EReal.coe_zero, sub_zero]
      · rw [twistedLegendre_extension_pos Γ hbpos]
        apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
          (.inl (EReal.coe_ne_top _))).mpr
        exact twistedRawLegendre_le Γ hbpos.le x
    · rw [twistedLegendre_extension_pos Γ hspos,
        twistedLegendre_extension_pos Γ (lt_of_lt_of_le hspos hsb)]
      apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _))).mpr
      refine (twistedRawLegendre_le_add Γ hsb x).trans (le_of_eq ?_)
      rw [ereal_sub_coe_add_coe]
      congr 2
      ring

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The untwisted normalisation fails**: for `Φ` `θ`-psh with `sup_X Φ < 0`, the constant
`Φ`-twisted test curve `Γ_τ = Φ` (`τ < 0`, `Γ_max = 0`) has `sup_X Γ*_t ≠ tΓ_max` for every
`t > 0`. So the first clause of `lma:suplegenlinear` (and of `cor:reltestcursuplinear`) does not
transfer to the twisted setting; its twisted form is `twistedLegendre_supremum_whole`. -/
theorem twistedConstCurve_sup_ne (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (hneg : (⨆ x, Φ x) < 0) :
    ∃ Γ : SourceTwistedTestCurve θ Φ, Γ.max = 0 ∧
      ∀ t : ℝ, 0 < t → (⨆ x, twistedRawLegendre Γ t x) ≠ ((t * Γ.max : ℝ) : EReal) := by
  have hfix : sourceRelativeEnvelope θ Φ Φ = Φ := by
    apply le_antisymm
    · apply uscRegularization_le (sourceThetaPSH_upperSemicontinuous hΦ)
      intro x
      apply iSup_le
      intro a
      obtain ⟨-, haΦ, -⟩ := (sourceRelativeEnvelopeCompetitors_iff hΦ).mp a.2
      exact haΦ x
    · exact le_sourceRelativeEnvelope hΦ le_rfl (MoreSingularOn.refl _ univ)
  have hconc (x : M) : SGPT.Convex.IsConvex
      (sourceTestCurveNegativeTrace 0 (fun _ : Iio (0 : ℝ) ↦ Φ) x) := by
    intro p hp q hq a b ha hb hab
    have hp' : p.1 < 0 ∧ -Φ x ≤ (p.2 : EReal) := by
      change sourceTestCurveNegativeTrace 0 (fun _ : Iio (0 : ℝ) ↦ Φ) x p.1 ≤ (p.2 : EReal) at hp
      by_cases h : p.1 < 0
      · rw [sourceTestCurveNegativeTrace, dif_pos h] at hp
        exact ⟨h, hp⟩
      · rw [sourceTestCurveNegativeTrace, dif_neg h] at hp
        exact absurd hp (by simp)
    have hq' : q.1 < 0 ∧ -Φ x ≤ (q.2 : EReal) := by
      change sourceTestCurveNegativeTrace 0 (fun _ : Iio (0 : ℝ) ↦ Φ) x q.1 ≤ (q.2 : EReal) at hq
      by_cases h : q.1 < 0
      · rw [sourceTestCurveNegativeTrace, dif_pos h] at hq
        exact ⟨h, hq⟩
      · rw [sourceTestCurveNegativeTrace, dif_neg h] at hq
        exact absurd hq (by simp)
    change sourceTestCurveNegativeTrace 0 (fun _ : Iio (0 : ℝ) ↦ Φ) x (a * p.1 + b * q.1) ≤
      ((a * p.2 + b * q.2 : ℝ) : EReal)
    have hneg' : a * p.1 + b * q.1 < 0 := by
      rcases ha.eq_or_lt with ha0 | hapos
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        linarith [hq'.1]
      · nlinarith [hp'.1, hq'.1]
    rw [sourceTestCurveNegativeTrace, dif_pos hneg']
    have hmin : min p.2 q.2 ≤ a * p.2 + b * q.2 := by
      have h1 := mul_le_mul_of_nonneg_left (min_le_left p.2 q.2) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right p.2 q.2) hb
      have e : a * min p.2 q.2 + b * min p.2 q.2 = min p.2 q.2 := by
        rw [← add_mul, hab, one_mul]
      linarith
    refine le_trans ?_ (EReal.coe_le_coe hmin)
    rcases le_total p.2 q.2 with h | h
    · rw [min_eq_left h]
      exact hp'.2
    · rw [min_eq_right h]
      exact hq'.2
  let Γ : SourceTwistedTestCurve θ Φ :=
    { max := 0
      potential := fun _ ↦ Φ
      thetaPSH := fun _ ↦ hΦ
      antitone := fun _ _ _ _ ↦ le_rfl
      concave := hconc
      twistedFixedPoint := fun _ ↦ hfix
      limit_eq := by
        have : Nonempty (Iio (0 : ℝ)) := ⟨⟨-1, by norm_num⟩⟩
        change uscRegularization (fun x ↦ ⨆ _ : Iio (0 : ℝ), Φ x) = Φ
        simp only [ciSup_const]
        exact le_antisymm (uscRegularization_le (sourceThetaPSH_upperSemicontinuous hΦ) le_rfl)
          (le_uscRegularization _) }
  refine ⟨Γ, rfl, fun t ht heq ↦ ?_⟩
  have hle : (⨆ x, twistedRawLegendre Γ t x) ≤ ⨆ x, Φ x := by
    apply iSup_mono
    intro x
    have h := twistedRawLegendre_le Γ ht.le x
    change twistedRawLegendre Γ t x ≤ Φ x + ((t * 0 : ℝ) : EReal) at h
    rwa [mul_zero, EReal.coe_zero, add_zero] at h
  rw [heq] at hle
  change ((t * 0 : ℝ) : EReal) ≤ _ at hle
  rw [mul_zero, EReal.coe_zero] at hle
  exact absurd hneg (not_lt.mpr hle)

variable [MeasurableSpace M] [BorelSpace M]

/-! ### Geodesic rays (twisted `lma:LegsendsTCtoR`) -/

/-- The Legendre transform of a twisted test curve is a geodesic on every closed interval
`[a, b] ⊆ [0, ∞)` (twisted `lma:LegsendsTCtoR`). -/
theorem twistedLegendre_geodesic_closed (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ) (Γ : SourceTwistedTestCurve θ Φ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    SourceGeodesicClosedInterval omega θ a b (sourceRayExtension (twistedLegendreRay Γ)) := by
  have hsub := twistedLegendreRay_isSubgeodesic omega hΦ Γ
  have hslice (t : ℝ) (ht : 0 ≤ t) :
      (ofFixedModel n M).IsThetaPSH θ (sourceRayExtension (twistedLegendreRay Γ) t) := by
    rw [sourceRayExtension_nonneg _ _ ht]
    exact hsub.thetaPSH ⟨t, ht⟩
  rcases hab.eq_or_lt with heq | hlt
  · subst heq
    exact (sourceGeodesicClosedInterval_self_iff omega θ a _).mpr (hslice a ha)
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
  have hLlin := twistedLegendreRay_le_linear Γ hC
  let L := twistedLegendreRay Γ
  let R := perronReplacement omega θ L a b
  have hRsub : SourceIsSubgeodesicRay omega θ R := perronReplacement_isSubgeodesic hsub ha hlt
  have hRlin := perronReplacement_le_linear hsub ha hlt hLlin
  have hRbot : ∀ τ, Γ.max < τ → sourcePositiveRayInverse R τ = ⊥ :=
    fun τ hτ ↦ rayInverse_eq_bot_of_linear_bound hRlin hτ
  have hR0 : R ⟨0, by simp⟩ = Φ := by
    have h := perronReplacement_of_not_mem omega θ L a b (le_refl 0)
      (fun h ↦ (not_lt.mpr ha) h.1)
    rw [sourceRayExtension_nonneg R 0 le_rfl, twistedLegendre_extension_zero] at h
    exact h
  -- the inverse Legendre transform of the replacement is the original test curve
  have hinv : ∀ τ : Iio Γ.max, sourcePositiveRayInverse R τ.1 = Γ.potential τ := by
    intro τ
    have hΓinv := twistedInverse_eq hΦ Γ τ
    have hτm : τ.1 < Γ.max := τ.2
    let Cτ : ℝ := (b - a) * (Γ.max - τ.1)
    have hCτ : 0 ≤ Cτ := mul_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hτm.le)
    have hlow : Γ.potential τ ≤ sourcePositiveRayInverse R τ.1 := by
      intro x
      apply le_iInf
      intro t
      have h1 : Γ.potential τ x ≤ sourceRayExtension L t.1 x - ((t.1 * τ.1 : ℝ) : EReal) := by
        rw [← congrFun hΓinv x]
        exact iInf_le (fun s : Ioi (0 : ℝ) ↦
          sourceRayExtension L s.1 x - ((s.1 * τ.1 : ℝ) : EReal)) t
      exact h1.trans (EReal.sub_le_sub
        (le_perronReplacement hsub ha hlt (le_of_lt t.2) x) le_rfl)
    have hup (x : M) : sourcePositiveRayInverse R τ.1 x ≤ Γ.potential τ x + (Cτ : EReal) := by
      rw [← congrFun hΓinv x]
      change sourcePositiveRayInverse R τ.1 x ≤
        (⨅ s : Ioi (0 : ℝ), sourceRayExtension L s.1 x - ((s.1 * τ.1 : ℝ) : EReal)) + (Cτ : EReal)
      rw [← ThetaPshDecreasingLimit.iInf_add_coe]
      apply le_iInf
      intro s
      have hs : 0 < s.1 := s.2
      by_cases hsin : s.1 ∈ Ioo a b
      · have hb0 : 0 < b := lt_of_le_of_lt ha hlt
        have hbout : b ∉ Ioo a b := fun h ↦ lt_irrefl b h.2
        have h1 : sourcePositiveRayInverse R τ.1 x ≤
            sourceRayExtension L b x - ((b * τ.1 : ℝ) : EReal) := by
          have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
            sourceRayExtension R t.1 x - ((t.1 * τ.1 : ℝ) : EReal)) ⟨b, hb0⟩
          rwa [perronReplacement_of_not_mem omega θ L a b hb0.le hbout] at hh
        refine h1.trans ?_
        rw [twistedLegendre_extension_pos Γ hb0, twistedLegendre_extension_pos Γ hs]
        have h2 := twistedRawLegendre_le_add Γ (show s.1 ≤ b from le_of_lt hsin.2) x
        calc twistedRawLegendre Γ b x - ((b * τ.1 : ℝ) : EReal)
            ≤ (twistedRawLegendre Γ s.1 x + (((b - s.1) * Γ.max : ℝ) : EReal)) -
                ((b * τ.1 : ℝ) : EReal) := EReal.sub_le_sub h2 le_rfl
          _ = twistedRawLegendre Γ s.1 x + (((b - s.1) * Γ.max - b * τ.1 : ℝ) : EReal) :=
              ereal_add_coe_sub_coe _ _ _
          _ ≤ twistedRawLegendre Γ s.1 x + ((Cτ - s.1 * τ.1 : ℝ) : EReal) := by
              apply add_le_add le_rfl (EReal.coe_le_coe _)
              have h3 : (b - s.1) * (Γ.max - τ.1) ≤ (b - a) * (Γ.max - τ.1) :=
                mul_le_mul_of_nonneg_right (by linarith [hsin.1]) (sub_nonneg.mpr hτm.le)
              dsimp only [Cτ]
              nlinarith
          _ = (twistedRawLegendre Γ s.1 x - ((s.1 * τ.1 : ℝ) : EReal)) + (Cτ : EReal) :=
              (ereal_sub_coe_add_coe _ _ _).symm
      · have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
          sourceRayExtension R t.1 x - ((t.1 * τ.1 : ℝ) : EReal)) s
        rw [perronReplacement_of_not_mem omega θ L a b hs.le hsin] at hh
        exact hh.trans (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hCτ))
    obtain ⟨x₀, hx₀⟩ := thetaPSH_exists_ne_bot (Γ.thetaPSH τ)
    have hχ := rayInverse_thetaPSH_of_ne_bot hRsub τ.1 ⟨x₀, ne_bot_of_le_ne_bot hx₀ (hlow x₀)⟩
    have hχΦ : sourcePositiveRayInverse R τ.1 ≤ Φ := by
      have h := rayInverse_le_initial hRsub τ.1
      rwa [hR0] at h
    have hsing : SGPT.PSH.SingularityLE (sourcePositiveRayInverse R τ.1) (Γ.potential τ) :=
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨Cτ, hup⟩
    exact le_antisymm ((le_sourceRelativeEnvelope hχ hχΦ hsing).trans_eq
      (Γ.twistedFixedPoint τ)) hlow
  -- hence the replacement is the original ray
  have hRL : ∀ t : ℝ, 0 < t → sourceRayExtension R t = sourceRayExtension L t := by
    intro t ht
    funext x
    rw [ray_positive_inversion_Iio hRsub hRbot ht x, twistedLegendre_extension_pos Γ ht]
    apply iSup_congr
    intro σ
    rw [hinv σ]
  refine ⟨hab, fun t ht ↦ hslice t (ha.trans ht.1), hslice a ha, hslice b (ha.trans hab), ?_, ?_⟩
  · intro s hs
    apply Or.inl
    apply hslice
    exact add_nonneg (mul_nonneg hs.1.le (ha.trans hab))
      (mul_nonneg (sub_nonneg.mpr hs.2.le) ha)
  · intro s hs
    let t : ℝ := s * b + (1 - s) * a
    have ht : t ∈ Ioo a b := by
      dsimp [t]
      constructor <;> nlinarith [mul_pos hs.1 (sub_pos.mpr hlt),
        mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hlt)]
    have hpos : 0 < t := lt_of_le_of_lt ha ht.1
    have heq := hRL t hpos
    rw [perronReplacement_of_mem omega θ L a b hpos.le ht] at heq
    have htime : (t - a) / (b - a) = s := by
      dsimp [t]
      field_simp [(sub_pos.mpr hlt).ne']
      ring
    simpa only [perronSegment, htime, sourcePerronClosedSlice,
      closedSubgeodesicSlice_eq_curve hs] using heq.symm

/-- **Twisted `lma:LegsendsTCtoR`**: for `Φ ∈ 𝓔(X, θ; φ)`, the Legendre transform of a
`Φ`-twisted test curve is a geodesic ray in `𝓔(X, θ; φ)` emanating from `Φ`. -/
theorem twistedLegendreRay_mem (omega : KahlerBackground n M) {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (hΦ : SourceRelativeFullMass θ φ Φ hφ)
    (Γ : SourceTwistedTestCurve θ Φ) :
    twistedLegendreRay Γ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ := by
  refine ⟨⟨fun t ↦ ?_, fun a b ha hab ↦
    twistedLegendre_geodesic_closed omega hΦ.choose Γ a b ha hab⟩, twistedLegendreRay_zero Γ⟩
  by_cases ht : t.1 = 0
  · have ht0 : t = ⟨0, by simp⟩ := Subtype.ext ht
    rw [ht0, twistedLegendreRay_zero Γ]
    exact hΦ
  · rw [twistedLegendreRay_pos Γ ht]
    exact twistedLegendre_fullMass omega hΦ Γ (lt_of_le_of_ne t.2 (Ne.symm ht))

/-! ### Injectivity -/

omit [MeasurableSpace M] [BorelSpace M] in
/-- The cut-off `Γ_max` is the supremum of the slopes `τ` at which the inverse Legendre transform
of `Γ*` is not identically `-∞`. -/
theorem twistedLegendre_slopeSet_sSup (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ)
    (Γ : SourceTwistedTestCurve θ Φ) : sSup (raySlopeSet (twistedLegendreRay Γ)) = Γ.max := by
  have hmem : ∀ τ : ℝ, τ < Γ.max → τ ∈ raySlopeSet (twistedLegendreRay Γ) := by
    intro τ hτ
    obtain ⟨x₀, hx₀⟩ := thetaPSH_exists_ne_bot (Γ.thetaPSH ⟨τ, hτ⟩)
    exact ⟨x₀, by rw [congrFun (twistedInverse_eq hΦ Γ ⟨τ, hτ⟩) x₀]; exact hx₀⟩
  have hub : ∀ τ ∈ raySlopeSet (twistedLegendreRay Γ), τ ≤ Γ.max := by
    intro τ hτ
    by_contra hlt
    obtain ⟨x, hx⟩ := hτ
    rw [twistedInverse_eq_bot hΦ Γ (lt_of_not_ge hlt)] at hx
    exact hx rfl
  apply le_antisymm (csSup_le ⟨Γ.max - 1, hmem _ (by linarith)⟩ hub)
  by_contra hlt
  have hlt' : sSup (raySlopeSet (twistedLegendreRay Γ)) < Γ.max := lt_of_not_ge hlt
  have h1 := le_csSup ⟨Γ.max, hub⟩
    (hmem ((sSup (raySlopeSet (twistedLegendreRay Γ)) + Γ.max) / 2) (by linarith))
  linarith

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Twisted test curves with the same cut-off and the same potentials are equal. -/
theorem SourceTwistedTestCurve.ext_of_eq {Γ₁ Γ₂ : SourceTwistedTestCurve θ Φ}
    (hmax : Γ₁.max = Γ₂.max)
    (hpot : ∀ (τ : ℝ) (h₁ : τ < Γ₁.max) (h₂ : τ < Γ₂.max),
      Γ₁.potential ⟨τ, h₁⟩ = Γ₂.potential ⟨τ, h₂⟩) : Γ₁ = Γ₂ := by
  cases Γ₁
  cases Γ₂
  simp only at hmax
  subst hmax
  congr
  funext τ
  exact hpot τ.1 τ.2 τ.2

omit [MeasurableSpace M] [BorelSpace M] in
/-- The Legendre transform is injective on `Φ`-twisted test curves. -/
theorem twistedLegendreRay_injective (hΦ : (ofFixedModel n M).IsThetaPSH θ Φ) :
    Function.Injective (twistedLegendreRay : SourceTwistedTestCurve θ Φ → SourceRayFamily M) := by
  intro Γ₁ Γ₂ h
  have hmax : Γ₁.max = Γ₂.max := by
    rw [← twistedLegendre_slopeSet_sSup hΦ Γ₁, ← twistedLegendre_slopeSet_sSup hΦ Γ₂, h]
  refine SourceTwistedTestCurve.ext_of_eq hmax fun τ h₁ h₂ ↦ ?_
  rw [← twistedInverse_eq hΦ Γ₁ ⟨τ, h₁⟩, ← twistedInverse_eq hΦ Γ₂ ⟨τ, h₂⟩, h]

/-! ### Rays emanating from `Φ` (twisted `lma:LegendsRtoTC`, `cor:reltestcursuplinear`) -/

/-- **Twisted `lma:LegendsRtoTC`**: for a geodesic ray `ℓ` in `𝓔(X, θ; φ)` emanating from
`Φ ∈ 𝓔(X, θ; φ)`, the inverse Legendre transforms `ℓ*_τ`, `τ < ℓ*_max`, form a `Φ`-twisted test
curve, where `ℓ*_max` (the supremum of the slopes with `ℓ*_τ ≢ -∞`) is finite, and `ℓ*_τ ≡ -∞`
for `τ > ℓ*_max`. -/
theorem twistedRay_legendre_test_curve_whole (omega : KahlerBackground n M) {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (hΦ : SourceRelativeFullMass θ φ Φ hφ)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) :
    BddAbove (raySlopeSet ℓ) ∧
    (rayTwistedTestCurve omega h).max = sSup (raySlopeSet ℓ) ∧
    (∀ τ : Iio (rayTwistedTestCurve omega h).max,
      (rayTwistedTestCurve omega h).potential τ = sourcePositiveRayInverse ℓ τ.1) ∧
    (∀ τ : ℝ, sSup (raySlopeSet ℓ) < τ → sourcePositiveRayInverse ℓ τ = ⊥) ∧
    twistedLegendreRay (rayTwistedTestCurve omega h) = ℓ := by
  have hbdd := raySlopeSet_bddAbove hΦ h
  refine ⟨hbdd, rfl, fun _ ↦ rfl, fun τ hτ ↦ ?_, twistedLegendreRay_rayTwistedTestCurve omega hΦ h⟩
  funext x
  by_contra hx
  exact notMem_of_csSup_lt hτ hbdd ⟨x, hx⟩

/-- **Twisted `cor:reltestcursuplinear`**: for a geodesic ray `ℓ` emanating from
`Φ ∈ 𝓔(X, θ; φ)`, `ℓ_t ≤ Φ + t ℓ*_max`, `sup_{Φ > -∞} (ℓ_t - Φ) = t ℓ*_max` and
`t ↦ ℓ_t - t ℓ*_max` is decreasing on `[0, ∞)`. -/
theorem twistedRay_supremum_whole (omega : KahlerBackground n M) {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (hΦ : SourceRelativeFullMass θ φ Φ hφ)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) :
    (∀ (t : Ici (0 : ℝ)) (x : M), ℓ t x ≤ Φ x + ((t.1 * sSup (raySlopeSet ℓ) : ℝ) : EReal)) ∧
    (∀ t : Ici (0 : ℝ), 0 < t.1 → ∀ c : ℝ, c < t.1 * sSup (raySlopeSet ℓ) →
      ∃ x, Φ x + (c : EReal) < ℓ t x) ∧
    (∀ x, AntitoneOn (fun t : ℝ ↦ sourceRayExtension ℓ t x -
      ((t * sSup (raySlopeSet ℓ) : ℝ) : EReal)) (Ici 0)) := by
  have hL := twistedLegendreRay_rayTwistedTestCurve omega hΦ h
  have hS := twistedLegendre_supremum_whole (rayTwistedTestCurve omega h)
  have hmax : (rayTwistedTestCurve omega h).max = sSup (raySlopeSet ℓ) := rfl
  rw [hL, hmax] at hS
  refine ⟨hS.1, fun t ht c hc ↦ ?_, hS.2.2⟩
  obtain ⟨x, hx⟩ := hS.2.1 t.1 ht c hc
  refine ⟨x, hx.trans_le (le_of_eq ?_)⟩
  rw [← twistedLegendreRay_pos (rayTwistedTestCurve omega h) ht.ne']
  exact congrFun (congrFun hL t) x

/-! ### The correspondence -/

/-- **Source `rmk:testcurve:L815`**: for every `Φ ∈ 𝓔(X, θ; φ)`, the Legendre transform is a
bijection from `Φ`-twisted test curves onto the geodesic rays in `𝓔(X, θ; φ)` emanating from
`Φ`; the inverse map is `ℓ ↦ (ℓ*_τ)_{τ < ℓ*_max}` (`rayTwistedTestCurve`). -/
theorem twistedRWNCorrespondence (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (hΦ : SourceRelativeFullMass θ φ Φ hφ) :
    TwistedRWNCorrespondence omega θ φ hφ Φ :=
  ⟨fun Γ ↦ twistedLegendreRay_mem omega hΦ Γ, twistedLegendreRay_injective hΦ.choose,
    fun _ h ↦ ⟨rayTwistedTestCurve omega h, twistedLegendreRay_rayTwistedTestCurve omega hΦ h⟩⟩

/-- **Source `rmk:testcurve:L815`** (the statement `TwistedRWNStatement`): geodesic rays in
`𝓔(X, θ; φ)` emanating from any `Φ ∈ 𝓔(X, θ; φ)` correspond bijectively, through the Legendre
transform, to `Φ`-twisted test curves. -/
theorem twistedRWNStatement_holds (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) : TwistedRWNStatement omega θ φ hφ :=
  fun _ hΦ ↦ twistedRWNCorrespondence omega hφ hΦ

/-- The twisted Legendre transform as an equivalence between `Φ`-twisted test curves and
geodesic rays in `𝓔(X, θ; φ)` emanating from `Φ`. -/
def twistedLegendreEquiv (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (hΦ : SourceRelativeFullMass θ φ Φ hφ) :
    SourceTwistedTestCurve θ Φ ≃ sourceGeodesicRaysFrom omega θ φ hφ Φ where
  toFun Γ := ⟨twistedLegendreRay Γ, twistedLegendreRay_mem omega hΦ Γ⟩
  invFun ℓ := rayTwistedTestCurve omega ℓ.2
  left_inv Γ := twistedLegendreRay_injective hΦ.choose
    (twistedLegendreRay_rayTwistedTestCurve omega hΦ (twistedLegendreRay_mem omega hΦ Γ))
  right_inv ℓ := Subtype.ext (twistedLegendreRay_rayTwistedTestCurve omega hΦ ℓ.2)

end SGPT.TestCurve.RWNTwisted
