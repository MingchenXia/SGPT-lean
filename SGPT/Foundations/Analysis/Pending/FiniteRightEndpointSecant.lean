import SGPT.Foundations.Analysis.Pending.FiniteUpperGapGeodesicSupremum
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsTimeConvexity

set_option autoImplicit false

/-!
# Actual terminal secants of a finite-gap Perron geodesic

Xia SGPT PDF0157--0158, Proposition 4.2.2. The true one-sided singularity
comparison produces finite endpoint gaps and a genuine terminal affine
barrier. Secants use actual EReal differences on the terminal nonpole locus.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteRightEndpointSecant

open FirstPass FiniteUpperGapGeodesicSupremum

noncomputable section

/-- The actual terminal secant; consumers restrict to its genuine finite locus. -/
def rightEndpointSecant {X : Type*} (curve : ℝ → X → EReal) (u₁ : X → EReal)
    (t : ℝ) (x : X) : EReal :=
  (((1 - t)⁻¹ : ℝ) : EReal) * (u₁ x - curve t x)

/-- Removing only bottom-valued difference terms preserves the actual supremum. -/
theorem differenceSup_eq_iSup_right_nonpole {X : Type*} {u₀ u₁ : X → EReal}
    (hmore : MoreSingularOn u₁ u₀ univ) :
    differenceSup u₁ u₀ = ⨆ x : {x // u₁ x ≠ ⊥}, u₁ x.val - u₀ x.val := by
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : u₁ x.val = ⊥
    · simp [hx]
    · exact le_iSup (fun y : {y // u₁ y ≠ ⊥} => u₁ y.val - u₀ y.val) ⟨x.val, hx⟩
  · apply iSup_le
    intro x
    have hx : u₀ x.val ≠ ⊥ := fun h =>
      x.property (hmore.eq_bot_of_eq_bot (mem_univ _) h)
    exact le_iSup (fun y : {y // u₀ y ≠ ⊥} => u₁ y.val - u₀ y.val) ⟨x.val, hx⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- A genuine terminal affine competitor produces the actual global lower barrier. -/
theorem affine_right_lower_bound [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) (t : ℝ) (x : M) :
    u₁ x + (((differenceSup u₁ u₀).toReal * t -
      (differenceSup u₁ u₀).toReal : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x := by
  let C : ℝ := (differenceSup u₁ u₀).toReal
  have hfinite := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
  have hC : (C : EReal) = differenceSup u₁ u₀ := EReal.coe_toReal hfinite.1 hfinite.2
  have hbound : u₁ ≤ fun y => u₀ y + (C : EReal) := by
    simpa only [hC] using le_add_differenceSup hu₀ hmore
  let curve := affineTranslatedCurve (fun _ : ℝ => u₁) C (-C)
  have hcurve : IsSubgeodesicFrom θ curve
      (fun y => u₁ y + ((-C : ℝ) : EReal)) u₁ := by
    simpa [curve] using (isSubgeodesicFrom_const hu₁).affineTranslated C (-C)
  have hstart : (fun y => u₁ y + ((-C : ℝ) : EReal)) ≤ u₀ := by
    intro y
    simpa only [sub_eq_add_neg, EReal.coe_neg] using EReal.sub_le_of_le_add (hbound y)
  have hmem : curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
    ⟨_, _, hcurve.left_endpoint, hu₁, hstart, le_rfl, hcurve⟩
  simpa only [curve, affineTranslatedCurve_apply, sub_eq_add_neg] using
    competitor_slice_le_finiteGeodesic hmem t x

/-- The actual terminal affine barrier excludes poles throughout interior time. -/
theorem finiteGeodesic_ne_bot_of_right_nonpole [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) (t : ℝ) :
    finiteGeodesic θ u₀ u₁ t x ≠ ⊥ := by
  have hfinite : u₁ x + (((differenceSup u₁ u₀).toReal * t -
      (differenceSup u₁ u₀).toReal : ℝ) : EReal) ≠ ⊥ := by
    rw [← EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hx, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  exact ne_bot_of_le_ne_bot hfinite (affine_right_lower_bound hu₀ hu₁ hmore t x)

/-- On the actual terminal nonpole locus, the extended secant is the finite real one. -/
theorem rightEndpointSecant_coe [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x =
      (((u₁ x).toReal - (finiteGeodesic θ u₀ u₁ t x).toReal) / (1 - t) : ℝ) := by
  rw [rightEndpointSecant,
    ← EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hx,
    ← EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ht x)
      (finiteGeodesic_ne_bot_of_right_nonpole hu₀ hu₁ hmore hx t),
    ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  simp only [div_eq_mul_inv, EReal.toReal_coe, mul_comm]

/-- Actual terminal secants lie between the true endpoint difference and finite global gap. -/
theorem rightEndpointSecant_bounds [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    u₁ x - u₀ x ≤ rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x ∧
      rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x ≤ differenceSup u₁ u₀ := by
  let C : ℝ := (differenceSup u₁ u₀).toReal
  have hfinite := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
  have hC : (C : EReal) = differenceSup u₁ u₀ := EReal.coe_toReal hfinite.1 hfinite.2
  have hx₀ : u₀ x ≠ ⊥ := fun h => hx (hmore.eq_bot_of_eq_bot (mem_univ _) h)
  have h₀ : u₀ x = ((u₀ x).toReal : EReal) :=
    (EReal.coe_toReal (hu₀.1.quasiPlurisubharmonic.ne_top x) hx₀).symm
  have h₁ : u₁ x = ((u₁ x).toReal : EReal) :=
    (EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hx).symm
  have hG : finiteGeodesic θ u₀ u₁ t x =
      ((finiteGeodesic θ u₀ u₁ t x).toReal : EReal) :=
    (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ht x)
      (finiteGeodesic_ne_bot_of_right_nonpole hu₀ hu₁ hmore hx t)).symm
  have hlow := affine_right_lower_bound hu₀ hu₁ hmore t x
  change u₁ x + ((C * t - C : ℝ) : EReal) ≤ _ at hlow
  rw [h₁, hG, ← EReal.coe_add] at hlow
  have hlowr := EReal.coe_le_coe_iff.mp hlow
  have hchord := finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
  change finiteGeodesic θ u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t at hchord
  rw [h₀, h₁, hG, SubgeodesicInfimum.eRealChord_coe_coe] at hchord
  have hchordr := EReal.coe_le_coe_iff.mp hchord
  rw [rightEndpointSecant_coe hu₀ hu₁ hmore hx ht]
  constructor
  · rw [h₀, h₁, ← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    simp only [EReal.toReal_coe]
    apply (le_div_iff₀ (sub_pos.mpr ht.2)).mpr
    nlinarith
  · rw [← hC]
    apply EReal.coe_le_coe_iff.mpr
    apply (div_le_iff₀ (sub_pos.mpr ht.2)).mpr
    nlinarith

/-- The actual supremum of every terminal secant equals the original finite endpoint gap. -/
theorem iSup_rightEndpointSecant [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (⨆ x : {x // u₁ x ≠ ⊥},
      rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x.val) = differenceSup u₁ u₀ := by
  apply le_antisymm
  · exact iSup_le fun x => (rightEndpointSecant_bounds hu₀ hu₁ hmore x.property ht).2
  · rw [differenceSup_eq_iSup_right_nonpole hmore]
    exact iSup_le fun x => (rightEndpointSecant_bounds hu₀ hu₁ hmore x.property ht).1.trans
      (le_iSup (fun y : {y // u₁ y ≠ ⊥} =>
        rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t y.val) x)

/-- The actual Perron regularization obeys the chord to its requested terminal endpoint. -/
theorem finiteGeodesic_le_eRealChord_to_right_endpoint
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) (x : M) :
    finiteGeodesic θ u₀ u₁ b x ≤
      eRealChord (finiteGeodesic θ u₀ u₁ a x) (u₁ x) ((b - a) / (1 - a)) := by
  have hs : (b - a) / (1 - a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hab) (sub_pos.mpr ha.2),
      (div_lt_one (sub_pos.mpr ha.2)).mpr (by linarith [hb.2])⟩
  have hg : UpperSemicontinuous fun y =>
      eRealChord (finiteGeodesic θ u₀ u₁ a y) (u₁ y) ((b - a) / (1 - a)) :=
    upperSemicontinuous_eRealChord (upperSemicontinuous_finiteGeodesic θ u₀ u₁ a)
      hu₁.1.quasiPlurisubharmonic.upperSemicontinuous
      (finiteGeodesic_ne_top hu₀ hu₁ ha) hu₁.1.quasiPlurisubharmonic.ne_top
      hs.1.le hs.2.le
  refine (finiteGeodesic_le_iff hg).mpr ?_ x
  intro curve hcurve
  have hcompa := competitor_slice_le_finiteGeodesic hcurve a
  obtain ⟨v₀, v₁, -, -, -, hv₁, hsub⟩ := hcurve
  have hr := hsub.closedAffineReparametrized ha.1.le (le_refl (1 : ℝ)) ha.2
  intro y
  have hchord := hr.le_eRealChord hs y
  have htime : affineTimeReparam a 1 ((b - a) / (1 - a)) = b := by
    dsimp only [affineTimeReparam]
    rw [mul_comm (1 - a), div_mul_cancel₀ _ (sub_pos.mpr ha.2).ne']
    ring
  rw [affineReparametrizedCurve_apply, htime,
    closedSubgeodesicSlice_eq_curve ha, closedSubgeodesicSlice_one] at hchord
  exact hchord.trans (eRealChord_mono (hcompa y) (hv₁ y) hs.1.le hs.2.le)

/-- True endpoint chords make the actual finite terminal secants monotone in time. -/
theorem monotoneOn_toReal_rightEndpointSecant [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {x : M} (hx : u₁ x ≠ ⊥) :
    MonotoneOn (fun t => (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ t x).toReal)
      (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with hab | hab
  · subst b
    exact le_rfl
  have hchord := finiteGeodesic_le_eRealChord_to_right_endpoint hu₀ hu₁ ha hb hab x
  have h₁ : u₁ x = ((u₁ x).toReal : EReal) :=
    (EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hx).symm
  have hGa : finiteGeodesic θ u₀ u₁ a x =
      ((finiteGeodesic θ u₀ u₁ a x).toReal : EReal) :=
    (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ha x)
      (finiteGeodesic_ne_bot_of_right_nonpole hu₀ hu₁ hmore hx a)).symm
  have hGb : finiteGeodesic θ u₀ u₁ b x =
      ((finiteGeodesic θ u₀ u₁ b x).toReal : EReal) :=
    (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ hb x)
      (finiteGeodesic_ne_bot_of_right_nonpole hu₀ hu₁ hmore hx b)).symm
  rw [h₁, hGa, hGb, SubgeodesicInfimum.eRealChord_coe_coe] at hchord
  have hchordr := EReal.coe_le_coe_iff.mp hchord
  have hmul := mul_le_mul_of_nonneg_right hchordr (sub_pos.mpr ha.2).le
  have hratio : ((b - a) / (1 - a)) * (1 - a) = b - a :=
    div_mul_cancel₀ _ (sub_pos.mpr ha.2).ne'
  have hcancel (z : ℝ) : ((b - a) / (1 - a)) * z * (1 - a) = (b - a) * z := by
    rw [mul_right_comm, hratio]
  simp only [add_mul, sub_mul, one_mul, hcancel] at hmul
  change (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ a x).toReal ≤
    (rightEndpointSecant (finiteGeodesic θ u₀ u₁) u₁ b x).toReal
  rw [rightEndpointSecant_coe hu₀ hu₁ hmore hx ha,
    rightEndpointSecant_coe hu₀ hu₁ hmore hx hb]
  simp only [EReal.toReal_coe]
  apply (div_le_div_iff₀ (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)).mpr
  nlinarith

end

end SGPT.Foundations.Analysis.Pending.FiniteRightEndpointSecant
