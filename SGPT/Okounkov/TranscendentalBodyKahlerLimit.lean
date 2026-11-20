import SGPT.Okounkov.TranscendentalBodyHausdorff

/-!
# Perturbation of an Okounkov body by a Kähler class

Source: blueprint node `tok:kahler-limit` (DRWNXZ Proposition 3.3 (3)): if `ξ` is big, then
`Δ(ξ) = ⋂_{ε ∈ ℚ_{>0}} Δ(ξ + ε{ω})`.

## Route

The source (and the first version of the blueprint node) argues with volumes: the bodies
`Δ(ξ + ε{ω})` decrease to a compact convex set `K ⊇ Δ(ξ)` of the same volume, and a compact
convex set containing a convex body with nonempty interior and of the same volume equals it;
this needs `tok:body-interior` (poles along the flag members). Here the Hausdorff estimate of
`tok:hausdorff-continuity` is used instead, which needs neither interiors nor volumes:

* `Δ(ξ) ⊆ Δ(ξ + ε{ω})` because `0 ∈ Δ(ε{ω})` (`tradOkounkovBody_subset_add`);
* if `x ∈ Δ(ξ + ε{ω})` for all `ε`, then `dist(x, Δ(ξ)) ≤ d_Haus(Δ(ξ + ε{ω}), Δ(ξ))`, which
  tends to `0` (`exists_hausdorffDist_lt` with `η = ε ω`), and `Δ(ξ)` is closed.

## Main results

* `tradOkounkovBody_eq_iInter_add_kahler`: blueprint `tok:kahler-limit`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **Blueprint `tok:kahler-limit`** (DRWNXZ Proposition 3.3 (3)): if `{θ}` is big, then
`Δ_{Y•}(θ) = ⋂_{ε ∈ ℚ_{>0}} Δ_{Y•}(θ + ε ω)`. -/
theorem tradOkounkovBody_eq_iInter_add_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody F θ =
      ⋂ (ε : ℚ) (_ : 0 < ε), tradOkounkovBody F (θ + (ε : ℝ) • F.omega.form) := by
  apply Subset.antisymm
  · refine subset_iInter₂ fun ε hε => ?_
    have hε' : (0 : ℝ) < (ε : ℝ) / 2 := by
      have : (0 : ℝ) < ε := by exact_mod_cast hε
      linarith
    refine tradOkounkovBody_subset_add θ (κ := KahlerBackground.smul hε' F.omega) ?_
    have heq : (ε : ℝ) • F.omega.form - (KahlerBackground.smul hε' F.omega).form =
        ((ε : ℝ) / 2) • F.omega.form := by
      rw [KahlerBackground.smul_form]; module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul F.omega.isSemipositive hε'.le
  · intro x hx
    rw [mem_iInter₂] at hx
    set e := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm with he
    have hcpt : IsCompact (TranscendentalMain.euclideanImage (tradOkounkovBody F θ)) :=
      (isCompact_tradOkounkovBody θ).image e.continuous
    have hne : (TranscendentalMain.euclideanImage (tradOkounkovBody F θ)).Nonempty :=
      (tradOkounkovBody_nonempty hbig).image _
    have hzero : infDist (e x) (TranscendentalMain.euclideanImage (tradOkounkovBody F θ)) = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε' hε' => ?_) infDist_nonneg
      rw [zero_add]
      obtain ⟨r, hr, hball⟩ := exists_hausdorffDist_lt (F := F) hbig hε'
      obtain ⟨ε, hε0, hεr⟩ := exists_rat_btwn hr
      have hε0' : (0 : ℝ) < ε := hε0
      have hεq : (0 : ℚ) < ε := by exact_mod_cast hε0
      have hp : (r • F.omega.form + (ε : ℝ) • F.omega.form).val.IsSemipositive := by
        rw [← add_smul]
        exact KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by linarith)
      have hm : (r • F.omega.form - (ε : ℝ) • F.omega.form).val.IsSemipositive := by
        rw [← sub_smul]
        exact KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by linarith)
      have hdist := hball _ hp hm
      have hxε := hx ε hεq
      have hcpt' : IsCompact (TranscendentalMain.euclideanImage
          (tradOkounkovBody F (θ + (ε : ℝ) • F.omega.form))) :=
        (isCompact_tradOkounkovBody _).image e.continuous
      have hfin : hausdorffEDist (TranscendentalMain.euclideanImage
          (tradOkounkovBody F (θ + (ε : ℝ) • F.omega.form)))
          (TranscendentalMain.euclideanImage (tradOkounkovBody F θ)) ≠ ⊤ :=
        hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨e x, x, hxε, rfl⟩ hne hcpt'.isBounded
          hcpt.isBounded
      have hxmem : e x ∈ TranscendentalMain.euclideanImage
          (tradOkounkovBody F (θ + (ε : ℝ) • F.omega.form)) := ⟨x, hxε, rfl⟩
      exact (infDist_le_hausdorffDist_of_mem hxmem hfin).trans hdist.le
    have hmem : e x ∈ TranscendentalMain.euclideanImage (tradOkounkovBody F θ) := by
      have h := (mem_closure_iff_infDist_zero hne).mpr hzero
      rwa [hcpt.isClosed.closure_eq] at h
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [e.injective hyx] at hy

end SGPT.Okounkov.TranscendentalBody
