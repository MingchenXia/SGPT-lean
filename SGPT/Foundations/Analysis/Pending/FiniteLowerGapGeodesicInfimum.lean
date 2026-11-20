import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import Mathlib.Data.EReal.Inv

set_option autoImplicit false

/-!
# Actual finite lower gap of a Perron geodesic

Xia SGPT PDF0159 Proposition 4.2.3. Infima retain true extended-real
differences on the actual nonpole domain. Reverse singularity order
produces the finite lower gap and the genuine affine competitor.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteLowerGapGeodesicInfimum

open FirstPass

noncomputable section

/-- Positive finite multiplication preserves every actual EReal infimum,
including an empty index domain and both infinities. -/
theorem coe_mul_iInf_of_pos {ι : Sort*} (f : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * (⨅ i, f i) = ⨅ i, (c : EReal) * f i := by
  apply le_antisymm
  · exact le_iInf fun i => mul_le_mul_of_nonneg_left (iInf_le f i)
      (EReal.coe_nonneg.mpr hc.le)
  · have h : ((c⁻¹ : ℝ) : EReal) * (⨅ i, (c : EReal) * f i) ≤ ⨅ i, f i := by
      apply le_iInf
      intro i
      have h := mul_le_mul_of_nonneg_left
        (iInf_le (fun i => (c : EReal) * f i) i)
        (EReal.coe_nonneg.mpr (inv_nonneg.mpr hc.le))
      simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne',
        EReal.coe_one, one_mul] using h
    have h' := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le)
    simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne',
      EReal.coe_one, one_mul] using h'

/-- The actual lower difference infimum on the reference's nonpole locus. -/
def differenceInf {X : Type*} (u v : X → EReal) : EReal :=
  ⨅ x : {x // v x ≠ ⊥}, u x.val - v x.val

/-- Transport an actual difference infimum between identical nonpole loci;
the function being subtracted is preserved. -/
theorem differenceInf_eq_iInf_of_sameSingularityType {X : Type*} {u v φ : X → EReal}
    (hsame : SameSingularityTypeOn v φ univ) :
    differenceInf u v = ⨅ x : {x // φ x ≠ ⊥}, u x.val - v x.val := by
  have hnonpole : ∀ x, v x ≠ ⊥ ↔ φ x ≠ ⊥ := by
    intro x
    constructor
    · intro hx hφ
      exact hx (hsame.1.eq_bot_of_eq_bot (mem_univ _) hφ)
    · intro hx hu
      exact hx (hsame.2.eq_bot_of_eq_bot (mem_univ _) hu)
  apply le_antisymm
  · exact le_iInf fun x => iInf_le
      (fun y : {y // v y ≠ ⊥} => u y.val - v y.val)
      ⟨x.val, (hnonpole x.val).mpr x.property⟩
  · exact le_iInf fun x => iInf_le
      (fun y : {y // φ y ≠ ⊥} => u y.val - v y.val)
      ⟨x.val, (hnonpole x.val).mp x.property⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- Reverse genuine singularity comparison supplies the finite lower gap. -/
theorem differenceInf_ne_top_ne_bot [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₀ u₁ univ) :
    differenceInf u₁ u₀ ≠ ⊤ ∧ differenceInf u₁ u₀ ≠ ⊥ := by
  obtain ⟨K, hK⟩ := hmore
  have hbound : ∀ x, u₀ x + ((-K : ℝ) : EReal) ≤ u₁ x := by
    intro x
    apply (EReal.addLECancellable_coe K).add_le_add_iff_right.mp
    calc
      (u₀ x + ((-K : ℝ) : EReal)) + (K : EReal) = u₀ x := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
      _ ≤ u₁ x + (K : EReal) := hK x (mem_univ _)
  have hlower : ((-K : ℝ) : EReal) ≤ differenceInf u₁ u₀ := by
    apply le_iInf
    intro x
    apply (EReal.le_sub_iff_add_le (Or.inl x.property)
      (Or.inl (hu₀.1.quasiPlurisubharmonic.ne_top x.val))).mpr
    simpa only [add_comm] using hbound x.val
  obtain ⟨y, _, hybot, hytop⟩ := hu₀.quasiPshPotential.exists_finite
    (Classical.arbitrary M) isOpen_univ (mem_univ _)
  have hy₁bot : u₁ y ≠ ⊥ := by
    intro h
    exact hybot (le_bot_iff.mp (by simpa [h] using hK y (mem_univ _)))
  have hdiff : u₁ y - u₀ y ≠ ⊤ := by
    rw [← EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top y) hy₁bot,
      ← EReal.coe_toReal hytop hybot, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  exact ⟨ne_top_of_le_ne_top hdiff (iInf_le
      (fun x : {x // u₀ x ≠ ⊥} => u₁ x.val - u₀ x.val) ⟨y, hybot⟩),
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-K)) hlower⟩

/-- The actual lower infimum gives a global additive lower bound. -/
theorem add_differenceInf_le (hu₀ : IsThetaPshPotential θ u₀) :
    (fun x => u₀ x + differenceInf u₁ u₀) ≤ u₁ := by
  intro x
  by_cases hx : u₀ x = ⊥
  · simp [hx]
  · have h := iInf_le (fun y : {y // u₀ y ≠ ⊥} =>
        u₁ y.val - u₀ y.val) ⟨x, hx⟩
    have h' := (EReal.le_sub_iff_add_le (Or.inl hx)
      (Or.inl (hu₀.1.quasiPlurisubharmonic.ne_top x))).mp h
    exact (add_comm _ _).le.trans h'

/-- A genuine potential has zero actual self-difference infimum. -/
theorem differenceInf_self [Nonempty M] (hu₀ : IsThetaPshPotential θ u₀) :
    differenceInf u₀ u₀ = 0 := by
  apply le_antisymm
  · obtain ⟨y, _, hybot, hytop⟩ :=
      hu₀.quasiPshPotential.exists_finite (Classical.arbitrary M)
        isOpen_univ (mem_univ _)
    exact iInf_le_of_le ⟨y, hybot⟩ (by rw [EReal.sub_self hytop hybot])
  · exact le_iInf fun x => (EReal.sub_self
      (hu₀.1.quasiPlurisubharmonic.ne_top x.val) x.property).ge

/-- The genuine affine lower competitor and the actual chord bound give
an exact lower-gap infimum for every interior Perron slice. -/
theorem differenceInf_finiteGeodesic [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₀ u₁ univ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    differenceInf (finiteGeodesic θ u₀ u₁ t) u₀ =
      ((t * (differenceInf u₁ u₀).toReal : ℝ) : EReal) := by
  let L : ℝ := (differenceInf u₁ u₀).toReal
  have hfinite := differenceInf_ne_top_ne_bot hu₀ hu₁ hmore
  have hL : (L : EReal) = differenceInf u₁ u₀ :=
    EReal.coe_toReal hfinite.1 hfinite.2
  have hbound : (fun x => u₀ x + (L : EReal)) ≤ u₁ := by
    simpa only [hL] using add_differenceInf_le hu₀ (u₁ := u₁)
  let curve := affineTranslatedCurve (fun _ : ℝ => u₀) L 0
  have hcurve : IsSubgeodesicFrom θ curve u₀ (fun x => u₀ x + (L : EReal)) := by
    simpa [curve] using (isSubgeodesicFrom_const hu₀).affineTranslated L 0
  have hmem : curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
    ⟨_, _, hu₀, hcurve.right_endpoint, le_rfl, hbound, hcurve⟩
  have hlower : ∀ x, u₀ x + ((t * L : ℝ) : EReal) ≤
      finiteGeodesic θ u₀ u₁ t x := by
    intro x
    simpa only [curve, affineTranslatedCurve_apply, add_zero, mul_comm] using
      competitor_slice_le_finiteGeodesic hmem t x
  apply le_antisymm
  · calc
      differenceInf (finiteGeodesic θ u₀ u₁ t) u₀ ≤
          ⨅ x : {x // u₀ x ≠ ⊥}, (t : EReal) * (u₁ x.val - u₀ x.val) := by
        apply iInf_mono
        intro x
        have hx₀top := hu₀.1.quasiPlurisubharmonic.ne_top x.val
        have hx₁top := hu₁.1.quasiPlurisubharmonic.ne_top x.val
        have hx₁bot : u₁ x.val ≠ ⊥ := by
          intro h
          exact x.property (hmore.eq_bot_of_eq_bot (mem_univ _) h)
        calc
          finiteGeodesic θ u₀ u₁ t x.val - u₀ x.val ≤
              eRealChord (u₀ x.val) (u₁ x.val) t - u₀ x.val :=
            EReal.sub_le_sub (finiteGeodesic_le_eRealChord hu₀ hu₁ ht x.val) le_rfl
          _ = (t : EReal) * (u₁ x.val - u₀ x.val) := by
            rw [← EReal.coe_toReal hx₀top x.property,
              ← EReal.coe_toReal hx₁top hx₁bot,
              SubgeodesicInfimum.eRealChord_coe_coe,
              ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]
            congr 1
            ring
      _ = (t : EReal) * differenceInf u₁ u₀ :=
        (coe_mul_iInf_of_pos _ ht.1).symm
      _ = ((t * L : ℝ) : EReal) := by rw [← hL, ← EReal.coe_mul]
  · apply le_iInf
    intro x
    apply (EReal.le_sub_iff_add_le (Or.inl x.property)
      (Or.inl (hu₀.1.quasiPlurisubharmonic.ne_top x.val))).mpr
    exact (add_comm _ _).le.trans (hlower x.val)

/-- Assigning the requested endpoint values extends the lower-gap formula
to the closed time interval. -/
theorem differenceInf_closedFiniteGeodesic [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₀ u₁ univ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    differenceInf (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t) u₀ =
      ((t * (differenceInf u₁ u₀).toReal : ℝ) : EReal) := by
  by_cases h0 : t = 0
  · subst t
    simp [differenceInf_self hu₀]
  by_cases h1 : t = 1
  · subst t
    simp only [closedSubgeodesicSlice_one, one_mul]
    have hf := differenceInf_ne_top_ne_bot hu₀ hu₁ hmore
    exact (EReal.coe_toReal hf.1 hf.2).symm
  have hint : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  rw [closedSubgeodesicSlice_eq_curve hint]
  exact differenceInf_finiteGeodesic hu₀ hu₁ hmore hint

variable [MeasurableSpace M] [CompactSpace M]
  {θc : ClosedRealOneOneForm n M} {φ : M → EReal}

/-- Source Proposition 4.2.3 on the actual model nonpole domain,
for genuine bounded-relative endpoints, including assigned endpoint times. -/
theorem relative_iInf_closedFiniteGeodesic (hφ : IsModelPotential θc φ)
    (hu₀ : RelativeEInfinity θc φ u₀) (hu₁ : RelativeEInfinity θc φ u₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (⨅ x : {x // φ x ≠ ⊥},
      closedSubgeodesicSlice (finiteGeodesic θc.val u₀ u₁) u₀ u₁ t x.val - u₀ x.val) =
    ((t * (⨅ x : {x // φ x ≠ ⊥}, u₁ x.val - u₀ x.val).toReal : ℝ) : EReal) := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  rw [← differenceInf_eq_iInf_of_sameSingularityType hu₀.2,
    ← differenceInf_eq_iInf_of_sameSingularityType hu₀.2]
  exact differenceInf_closedFiniteGeodesic hu₀.1 hu₁.1
    (hu₀.2.1.trans hu₁.2.2) ht

end

end SGPT.Foundations.Analysis.Pending.FiniteLowerGapGeodesicInfimum
