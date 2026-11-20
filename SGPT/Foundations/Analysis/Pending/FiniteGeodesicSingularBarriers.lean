import SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyEndpoints
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability

set_option autoImplicit false

/-!
# Actual affine endpoint barriers with common poles

Xia SGPT PDF0172, Step 2 of Proposition 4.3.3. Genuine same-type
endpoints give finite affine bounds on their actual Perron curve, as
extended inequalities on the whole space. No boundedness of the
reference or endpoints is used. Canonical real gaps retain zero at
the common poles rather than taking the real value of an infinity.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicSingularBarriers

open FirstPass FirstPass.PositiveClasses FiniteGeodesicEnergyEndpoints
  RelativeEnergyIntegrability

noncomputable section

/-- A common nonnegative finite constant for two genuine singularity inequalities. -/
theorem exists_nonneg_le_add_of_sameSingularityType {X : Type*} {u₀ u₁ : X → EReal}
    (htype : SameSingularityTypeOn u₀ u₁ univ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, u₁ x ≤ u₀ x + (C : EReal)) ∧
      ∀ x, u₀ x ≤ u₁ x + (C : EReal) := by
  obtain ⟨A, hA⟩ := htype.1
  obtain ⟨B, hB⟩ := htype.2
  refine ⟨max (max A B) 0, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · exact (hB x (mem_univ x)).trans (add_le_add le_rfl
      (EReal.coe_le_coe_iff.mpr ((le_max_right A B).trans (le_max_left _ _))))
  · exact (hA x (mem_univ x)).trans (add_le_add le_rfl
      (EReal.coe_le_coe_iff.mpr ((le_max_left A B).trans (le_max_left _ _))))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- The actual four affine barriers as extended inequalities, including common poles. -/
theorem finiteGeodesic_extended_barriers (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    (u₀ x + (((-C) * t : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ u₀ x + ((C * t : ℝ) : EReal)) ∧
    (u₁ x + (((-C) * (1 - t) : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ u₁ x + ((C * (1 - t) : ℝ) : EReal)) := by
  have hl₀ := affineRooftopLower_le_finiteGeodesic hu₀ le_rfl hC₀ t x
  have hl₁ := affineRooftopLower_right_le_finiteGeodesic hu₁ hC₁ t x
  have hch := finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
  change finiteGeodesic θ u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t at hch
  refine ⟨⟨hl₀, ?_⟩, ⟨hl₁, ?_⟩⟩
  all_goals
    by_cases hbot : u₀ x = ⊥
    · have hbot₁ : u₁ x = ⊥ := by
        have h := hC₁ x
        simpa only [hbot, EReal.bot_add, le_bot_iff] using h
      have hg : finiteGeodesic θ u₀ u₁ t x = ⊥ := by
        apply le_bot_iff.mp
        simpa only [hbot, hbot₁, eRealChord,
          EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
          EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add] using hch
      simp only [hg, hbot, hbot₁, EReal.bot_add, le_refl]
    · have hbot₁ : u₁ x ≠ ⊥ := by
        intro hb
        have h := hC₀ x
        rw [hb, EReal.bot_add, le_bot_iff] at h
        exact hbot h
      have he₀ := (EReal.coe_toReal (hu₀.1.quasiPlurisubharmonic.ne_top x) hbot).symm
      have he₁ := (EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hbot₁).symm
      rw [he₀, he₁, eRealChord, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add] at hch
      have hc₁ : (u₁ x).toReal ≤ (u₀ x).toReal + C := by
        have h := hC₁ x
        rwa [he₀, he₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      have hc₀ : (u₀ x).toReal ≤ (u₁ x).toReal + C := by
        have h := hC₀ x
        rwa [he₀, he₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      first
      | rw [he₀, ← EReal.coe_add]
        exact hch.trans (EReal.coe_le_coe_iff.mpr (by nlinarith [ht.1]))
      | rw [he₁, ← EReal.coe_add]
        exact hch.trans (EReal.coe_le_coe_iff.mpr (by nlinarith [ht.2]))

private theorem canonical_gap_le_of_barriers {a b : EReal} {R : ℝ}
    (hb : b ≠ ⊤) (hR : 0 ≤ R)
    (hl : b + ((-R : ℝ) : EReal) ≤ a) (hh : a ≤ b + (R : EReal)) :
    |canonicalERealDiffToReal a b| ≤ R := by
  by_cases hbot : b = ⊥
  · have ha : a = ⊥ := by
      simpa only [hbot, EReal.bot_add, le_bot_iff] using hh
    simpa [ha, hbot, canonicalERealDiffToReal, poleModifiedERealDiffToReal] using hR
  · have he := (EReal.coe_toReal hb hbot).symm
    rw [he, ← EReal.coe_add] at hl hh
    obtain ⟨ha, hlow, hhigh⟩ := eq_coe_toReal_of_coe_le_le hl hh
    rw [ha, he, canonicalERealDiffToReal_coe_coe]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual canonical gap from the initial endpoint is controlled even at common poles. -/
theorem canonicalDiff_finiteGeodesic_left_le (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ} (hC : 0 ≤ C)
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    |canonicalERealDiffToReal (finiteGeodesic θ u₀ u₁ t x) (u₀ x)| ≤ C * t := by
  obtain ⟨⟨hl, hh⟩, -⟩ := finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ ht x
  rw [show -C * t = -(C * t) by ring] at hl
  exact canonical_gap_le_of_barriers (hu₀.1.quasiPlurisubharmonic.ne_top x)
    (mul_nonneg hC ht.1.le) hl hh

/-- The actual canonical gap from the terminal endpoint is controlled even at common poles. -/
theorem canonicalDiff_finiteGeodesic_right_le (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ} (hC : 0 ≤ C)
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    |canonicalERealDiffToReal (finiteGeodesic θ u₀ u₁ t x) (u₁ x)| ≤ C * (1 - t) := by
  obtain ⟨-, ⟨hl, hh⟩⟩ := finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ ht x
  rw [show -C * (1 - t) = -(C * (1 - t)) by ring] at hl
  exact canonical_gap_le_of_barriers (hu₁.1.quasiPlurisubharmonic.ne_top x)
    (mul_nonneg hC (sub_nonneg.mpr ht.2.le)) hl hh

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicSingularBarriers
