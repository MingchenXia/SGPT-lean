import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum

set_option autoImplicit false

/-!
# Actual finite upper endpoint gap of a Perron geodesic

Xia SGPT PDF0157--0158 equation (4.9), with a finite one-sided
singularity gap. Differences are taken in EReal on the genuine finite
locus of the first endpoint; common poles are not assigned a zero gap.
The lower bound is produced by an actual affine Perron competitor.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteUpperGapGeodesicSupremum

open FirstPass

noncomputable section

/-- The actual extended-real difference supremum on the nonpole locus
of the reference function. -/
def differenceSup {X : Type*} (u v : X → EReal) : EReal :=
  ⨆ x : {x // v x ≠ ⊥}, u x.val - v x.val

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- A genuine one-sided singularity gap gives a finite actual difference
supremum; finite values are obtained from genuine local nondegeneracy. -/
theorem differenceSup_ne_top_ne_bot [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) :
    differenceSup u₁ u₀ ≠ ⊤ ∧ differenceSup u₁ u₀ ≠ ⊥ := by
  obtain ⟨K, hK⟩ := hmore
  have hupper : differenceSup u₁ u₀ ≤ (K : EReal) := by
    apply iSup_le
    intro x
    exact EReal.sub_le_of_le_add' (hK x.val (mem_univ _))
  obtain ⟨y, _, hybot, hytop⟩ :=
    hu₁.quasiPshPotential.exists_finite (Classical.arbitrary M)
      isOpen_univ (mem_univ _)
  have hy₀bot : u₀ y ≠ ⊥ := by
    intro h
    exact hybot (le_bot_iff.mp (by simpa [h] using hK y (mem_univ _)))
  have hdiff : u₁ y - u₀ y ≠ ⊥ := by
    rw [← EReal.coe_toReal hytop hybot,
      ← EReal.coe_toReal (hu₀.1.quasiPlurisubharmonic.ne_top y) hy₀bot,
      ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top K) hupper,
    ne_bot_of_le_ne_bot hdiff (le_iSup (fun x : {x // u₀ x ≠ ⊥} =>
      u₁ x.val - u₀ x.val) ⟨y, hy₀bot⟩)⟩

/-- The actual supremum yields a global pointwise additive bound,
including the reference poles through genuine singularity inclusion. -/
theorem le_add_differenceSup (hu₀ : IsThetaPshPotential θ u₀)
    (hmore : MoreSingularOn u₁ u₀ univ) :
    u₁ ≤ fun x => u₀ x + differenceSup u₁ u₀ := by
  intro x
  by_cases hx : u₀ x = ⊥
  · simp [hx, hmore.eq_bot_of_eq_bot (mem_univ _) hx]
  · have h := le_iSup (fun y : {y // u₀ y ≠ ⊥} =>
        u₁ y.val - u₀ y.val) ⟨x, hx⟩
    exact (add_comm _ _).le.trans' <|
      (EReal.sub_le_iff_le_add (Or.inl hx)
        (Or.inl (hu₀.1.quasiPlurisubharmonic.ne_top x))).mp h

/-- A genuine potential has zero actual self-difference supremum. -/
theorem differenceSup_self [Nonempty M] (hu₀ : IsThetaPshPotential θ u₀) :
    differenceSup u₀ u₀ = 0 := by
  apply le_antisymm
  · exact iSup_le fun x => EReal.sub_self_le_zero
  · obtain ⟨y, _, hybot, hytop⟩ :=
      hu₀.quasiPshPotential.exists_finite (Classical.arbitrary M)
        isOpen_univ (mem_univ _)
    exact le_iSup_of_le ⟨y, hybot⟩ (by rw [EReal.sub_self hytop hybot])

/-- An actual affine competitor and the chord bound produce the exact
upper-gap supremum of every interior Perron slice. -/
theorem differenceSup_finiteGeodesic [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    differenceSup (finiteGeodesic θ u₀ u₁ t) u₀ =
      ((t * (differenceSup u₁ u₀).toReal : ℝ) : EReal) := by
  let C : ℝ := (differenceSup u₁ u₀).toReal
  have hfinite := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
  have hC : (C : EReal) = differenceSup u₁ u₀ :=
    EReal.coe_toReal hfinite.1 hfinite.2
  have hbound : u₁ ≤ fun x => u₀ x + (C : EReal) := by
    simpa only [hC] using le_add_differenceSup hu₀ hmore
  let curve := affineTranslatedCurve (fun _ : ℝ => u₁) C (-C)
  have hcurve : IsSubgeodesicFrom θ curve
      (fun x => u₁ x + ((-C : ℝ) : EReal)) u₁ := by
    simpa [curve] using (isSubgeodesicFrom_const hu₁).affineTranslated C (-C)
  have hstart : (fun x => u₁ x + ((-C : ℝ) : EReal)) ≤ u₀ := by
    intro x
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      EReal.sub_le_of_le_add (hbound x)
  have hmem : curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
    ⟨_, _, hcurve.left_endpoint, hu₁, hstart, le_rfl, hcurve⟩
  have hlower : ∀ x, u₁ x + ((C * t - C : ℝ) : EReal) ≤
      finiteGeodesic θ u₀ u₁ t x := by
    intro x
    simpa only [curve, affineTranslatedCurve_apply, sub_eq_add_neg] using
      competitor_slice_le_finiteGeodesic hmem t x
  apply le_antisymm
  · apply iSup_le
    intro x
    have hupper : finiteGeodesic θ u₀ u₁ t x.val ≤
        u₀ x.val + ((t * C : ℝ) : EReal) := by
      refine (finiteGeodesic_le_eRealChord hu₀ hu₁ ht x.val).trans ?_
      refine (eRealChord_mono le_rfl (hbound x.val) ht.1.le ht.2.le).trans ?_
      change eRealChord (u₀ x.val) (u₀ x.val + (C : EReal)) t ≤
        u₀ x.val + ((t * C : ℝ) : EReal)
      have hx : u₀ x.val = ((u₀ x.val).toReal : EReal) :=
        (EReal.coe_toReal (hu₀.1.quasiPlurisubharmonic.ne_top x.val) x.property).symm
      rw [hx, ← EReal.coe_add, SubgeodesicInfimum.eRealChord_coe_coe,
        ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (le_of_eq (by ring))
    exact EReal.sub_le_of_le_add' hupper
  · calc
      ((t * C : ℝ) : EReal) =
          differenceSup u₁ u₀ + ((C * t - C : ℝ) : EReal) := by
            rw [← hC, ← EReal.coe_add]
            congr 1
            ring
      _ = ⨆ x : {x // u₀ x ≠ ⊥},
          (u₁ x.val - u₀ x.val) + ((C * t - C : ℝ) : EReal) :=
        (FirstPass.iSup_add_coe _ _).symm
      _ ≤ differenceSup (finiteGeodesic θ u₀ u₁ t) u₀ := by
        apply iSup_mono
        intro x
        calc
          (u₁ x.val - u₀ x.val) + ((C * t - C : ℝ) : EReal) =
              (u₁ x.val + ((C * t - C : ℝ) : EReal)) - u₀ x.val := by
                simp only [sub_eq_add_neg]
                ac_rfl
          _ ≤ finiteGeodesic θ u₀ u₁ t x.val - u₀ x.val :=
            EReal.sub_le_sub (hlower x.val) le_rfl

/-- Assigning the actual requested endpoints extends the same formula
to the closed interval, without using raw Perron endpoint values. -/
theorem differenceSup_closedFiniteGeodesic [Nonempty M]
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hmore : MoreSingularOn u₁ u₀ univ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    differenceSup (closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t) u₀ =
      ((t * (differenceSup u₁ u₀).toReal : ℝ) : EReal) := by
  by_cases h0 : t = 0
  · subst t
    simp [differenceSup_self hu₀]
  by_cases h1 : t = 1
  · subst t
    simp only [closedSubgeodesicSlice_one, one_mul]
    have hf := differenceSup_ne_top_ne_bot hu₀ hu₁ hmore
    exact (EReal.coe_toReal hf.1 hf.2).symm
  have hint : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  rw [closedSubgeodesicSlice_eq_curve hint]
  exact differenceSup_finiteGeodesic hu₀ hu₁ hmore hint

end

end SGPT.Foundations.Analysis.Pending.FiniteUpperGapGeodesicSupremum
