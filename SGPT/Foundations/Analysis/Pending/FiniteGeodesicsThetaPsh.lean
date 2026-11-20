import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsJointUsc

set_option autoImplicit false

/-!
# Each interior slice of the Perron finite geodesic is a genuine theta-PSH potential

`FirstPass.thetaPlurisubharmonic_uscRegularization_sSup` is stated for a
*normalized* family (`u ≤ 0`), because that is the normalization the
`thetaPshSupremum` construction carries.  The Perron competitor slices are not
normalized; they are bounded above by a real constant coming from the endpoint
chord.  This file removes that gap once and for all by translating the family,
and records the resulting statement for `finiteGeodesic`.

A lower barrier supplies local nondegeneracy: a `θ`-PSH potential below both
endpoints is below every slice (`FirstPass.le_finiteGeodesic_of_le_endpoints`),
and `LocallyNondegenerate` is monotone.

Nothing here needs compactness of `M`; the upper bound is a hypothesis, so the
caller decides where it comes from.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- Translating a family by a real constant translates its supremum. -/
private theorem sSup_shifted_slices_apply (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) (t c : ℝ) (x : M) :
    sSup {v : M → EReal | ∃ curve ∈ finiteGeodesicCompetitors θ u₀ u₁,
        v = fun y => curve t y + (c : EReal)} x =
      finiteGeodesicSliceSupremum θ u₀ u₁ t x + (c : EReal) := by
  have hlhs : sSup {v : M → EReal | ∃ curve ∈ finiteGeodesicCompetitors θ u₀ u₁,
        v = fun y => curve t y + (c : EReal)} x =
      ⨆ curve ∈ finiteGeodesicCompetitors θ u₀ u₁, (curve t x + (c : EReal)) := by
    rw [sSup_apply]
    apply le_antisymm
    · refine iSup_le fun v => ?_
      obtain ⟨curve, hcurve, hv⟩ := v.2
      simp only [hv]
      exact le_iSup_of_le curve (le_iSup_of_le hcurve le_rfl)
    · exact iSup_le fun curve => iSup_le fun hcurve =>
        le_iSup_of_le ⟨fun y => curve t y + (c : EReal), ⟨curve, hcurve, rfl⟩⟩ le_rfl
  rw [hlhs, finiteGeodesicSliceSupremum_apply,
    iSup_subtype'
      (p := fun curve : ℝ → M → EReal =>
        curve ∈ finiteGeodesicCompetitors θ u₀ u₁)
      (f := fun curve _ => curve t x + (c : EReal)),
    iSup_subtype'
      (p := fun curve : ℝ → M → EReal =>
        curve ∈ finiteGeodesicCompetitors θ u₀ u₁)
      (f := fun curve _ => curve t x)]
  exact iSup_add_coe _ _

/-- **Every interior slice of the Perron finite geodesic is `θ`-PSH.**  The
family of competitor slices is translated down by its real upper bound so that
`FirstPass.thetaPlurisubharmonic_uscRegularization_sSup` applies, and the
translation is undone afterwards; a common lower barrier gives local
nondegeneracy. -/
theorem isThetaPshPotential_finiteGeodesic_of_bounded
    (hlocal : HasSmoothLocalPotentials θ)
    (hne : (finiteGeodesicCompetitors θ u₀ u₁).Nonempty)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {C : ℝ} (hC : ∀ x, finiteGeodesic θ u₀ u₁ t x ≤ (C : EReal))
    {w : M → EReal} (hw : IsThetaPshPotential θ w) (hw₀ : w ≤ u₀)
    (hw₁ : w ≤ u₁) :
    IsThetaPshPotential θ (finiteGeodesic θ u₀ u₁ t) := by
  classical
  set F : Set (M → EReal) :=
    {v : M → EReal | ∃ curve ∈ finiteGeodesicCompetitors θ u₀ u₁,
      v = fun y => curve t y + ((-C : ℝ) : EReal)} with hF
  have hFne : F.Nonempty := by
    obtain ⟨curve, hcurve⟩ := hne
    exact ⟨fun y => curve t y + ((-C : ℝ) : EReal), ⟨curve, hcurve, rfl⟩⟩
  have hFpsh : ∀ v ∈ F, IsThetaPshPotential θ v := by
    rintro v ⟨curve, hcurve, rfl⟩
    obtain ⟨v₀, v₁, -, -, -, -, hsub⟩ := hcurve
    exact (hsub.2.2.1.thetaPshPotential ht).add_const (-C)
  have hF0 : ∀ v ∈ F, v ≤ 0 := by
    rintro v ⟨curve, hcurve, rfl⟩ x
    have hle : curve t x ≤ (C : EReal) :=
      (competitor_slice_le_finiteGeodesic hcurve t x).trans (hC x)
    calc curve t x + ((-C : ℝ) : EReal)
        ≤ (C : EReal) + ((-C : ℝ) : EReal) := add_le_add hle le_rfl
      _ = 0 := by rw [← EReal.coe_add]; norm_num
  have hpsh := thetaPlurisubharmonic_uscRegularization_sSup hlocal hFne hFpsh hF0
  have hsSup : sSup F = fun x => finiteGeodesicSliceSupremum θ u₀ u₁ t x
      + ((-C : ℝ) : EReal) := by
    funext x
    exact sSup_shifted_slices_apply θ u₀ u₁ t (-C) x
  rw [hsSup, uscRegularization_add_coe_const] at hpsh
  have hshift :=
    GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hpsh (-C)
  have hfun : (fun x => (uscRegularization (finiteGeodesicSliceSupremum θ u₀ u₁ t) x
      + ((-C : ℝ) : EReal)) - (((-C : ℝ)) : EReal)) = finiteGeodesic θ u₀ u₁ t := by
    funext x
    rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
    simp [finiteGeodesic]
  rw [hfun] at hshift
  exact ⟨hshift, hw.2.mono (le_finiteGeodesic_of_le_endpoints hw hw₀ hw₁ t)⟩

end

end SGPT.Foundations.Analysis.Pending
