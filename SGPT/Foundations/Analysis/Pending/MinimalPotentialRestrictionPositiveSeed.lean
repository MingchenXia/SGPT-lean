import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false

/-! # Genuine positive ordinary restriction of every positive moving minimal potential -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialRestrictionPositiveSeed

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation DiagonalMass

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- A real small-error analytic QEA term and finite normalization internally
supply a genuine strict ordinary restricted lower seed for the moving minimum. -/
theorem exists_restricted_strict_lower_seed_minimal_add_smul
    (omega : KahlerBackground n M) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ s : M → EReal,
      IsThetaPshPotential (θ + e • omega.form - (e / 2) • omega.form).val s ∧
      s ≤ thetaPshSupremum (θ + e • omega.form).val ∧
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback hι (θ + e • omega.form - (e / 2) • omega.form)).val
        (fun y => s (ι y)) := by
  let : Nonempty M := Nonempty.map ι inferInstance
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  obtain ⟨a, U, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hV
  obtain ⟨j, hj⟩ := (happ.error_tendsto.eventually
    (eventually_lt_nhds (half_pos he))).exists
  have hcoeff : 0 ≤ e / 2 - a j := sub_nonneg.mpr hj.le
  have hform : θ + a j • omega.form + (e / 2 - a j) • omega.form =
      θ + e • omega.form - (e / 2) • omega.form := by module
  have hU : IsThetaPshPotential
      (θ + e • omega.form - (e / 2) • omega.form).val (U j) := by
    simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (happ.term j) (KahlerDomination.isSemipositive_smul omega.isSemipositive hcoeff)
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  have hR := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
    happ hι hgeneric j
  have hRform : ClosedRealOneOneForm.pullback hι (θ + a j • omega.form) +
      (e / 2 - a j) • ρ.form =
      ClosedRealOneOneForm.pullback hι (θ + e • omega.form - (e / 2) • omega.form) := by
    rw [← NefCoreKahlerCurrent.pullback_add_smul hι (θ + a j • omega.form)
      omega.form (e / 2 - a j), hform]
  have hRsmall : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hι (θ + e • omega.form - (e / 2) • omega.form)).val
      (fun y => U j (ι y)) := by
    simpa only [hRform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hR (KahlerDomination.isSemipositive_smul ρ.isSemipositive hcoeff)
  obtain ⟨C, hC⟩ := hU.exists_global_upper_bound
  let s : M → EReal := fun x => U j x - (C : EReal)
  have hs : IsThetaPshPotential
      (θ + e • omega.form - (e / 2) • omega.form).val s := hU.sub_const C
  have hs0 : s ≤ 0 := sub_const_nonpositive_of_le hC
  have hslarge : IsThetaPshPotential (θ + e • omega.form).val s := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hs (KahlerDomination.isSemipositive_smul omega.isSemipositive (half_pos he).le)
  exact ⟨s, hs, le_thetaPshSupremum hslarge hs0, hRsmall.sub_const C⟩

/-- Actual raw pullback, the internally produced nondegenerate seed and
positive NP slot expansion produce the genuine positive moving restriction. -/
theorem exists_positive_ordinary_restriction_minimal_add_smul
    (omega : KahlerBackground n M) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
      (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) hw := by
  let : Nonempty M := Nonempty.map ι inferInstance
  obtain ⟨s, _, hle, hR⟩ := exists_restricted_strict_lower_seed_minimal_add_smul
    omega hι hpull θ hbig hgeneric he
  let η := ClosedRealOneOneForm.pullback hι (θ + e • omega.form)
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  have hsub : θ + e • omega.form - (e / 2) • omega.form =
      (θ + e • omega.form) + (-(e / 2)) • omega.form := by module
  have hRform : ClosedRealOneOneForm.pullback hι
      (θ + e • omega.form - (e / 2) • omega.form) = η - (e / 2) • ρ.form := by
    rw [hsub, NefCoreKahlerCurrent.pullback_add_smul]
    dsimp only [η, ρ]
    module
  rw [hRform] at hR
  have hSη : IsThetaPshPotential η.val (fun y => s (ι y)) := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hR (KahlerDomination.isSemipositive_smul ρ.isSemipositive (half_pos he).le)
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hplus : IsBigClass (RealBottChern.ofRepresentative (θ + e • omega.form)) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV he
  have hW := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    (θ + e • omega.form) hplus
  have hw : IsThetaPshPotential η.val
      (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hW.1,
      hSη.2.mono (fun y => hle (ι y))⟩
  have hseedpos := RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul
    ρ (half_pos he) hR hSη
  exact ⟨hw, hseedpos.trans_le (diagonalPotentialMass_mono_of_kahler ρ hSη hw
    (MoreSingularOn.of_le fun y _ => hle (ι y)))⟩

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialRestrictionPositiveSeed
