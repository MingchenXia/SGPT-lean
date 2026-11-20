import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationPullback

set_option autoImplicit false

/-!
# Pulling admissible presentations back along holomorphic open maps

This is the non-exceptional part of the blowup pullback construction, stated
for an actual holomorphic open map.  It is useful for a global biholomorphism:
the inverse is an open holomorphic map, so an admissible presentation upstairs
can be transported downstairs once the background-form correction is supplied.

The result deliberately makes the semipositive correction explicit.  A
holomorphic map alone does not compare arbitrary Kähler backgrounds, and an
ordinary pullback along a non-open map can become identically `-∞` on an open
set.  No assertion about restricted masses is made here; that requires a
separate covariance theorem for regular-patch families.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AdmissiblePresentationHolomorphicPullback

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open AdmissiblePresentationPullback

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- An open map preserves the local non-pole condition under composition. -/
theorem locallyNondegenerate_comp_of_isOpenMap {g : Z → Y}
    (hgopen : IsOpenMap g) {v : Y → EReal} (hv : LocallyNondegenerate v) :
    LocallyNondegenerate (fun z => v (g z)) := by
  intro z U hU hzU
  obtain ⟨y, hy, hyfin⟩ := hv (g z) (g '' U) (hgopen U hU) ⟨z, hzU, rfl⟩
  obtain ⟨z', hz'U, rfl⟩ := hy
  exact ⟨z', hz'U, hyfin⟩

variable {omega : KahlerBackground n Y} {omegaZ : KahlerBackground n Z}
  {theta : ClosedRealOneOneForm n Y} {W : ClosedIrreducibleAnalyticSubvariety n Y}
  {epsilon : PositiveError} {g : Z → Y}

/-- The pullback of an admissible presentation along a holomorphic open map is
admissible after an explicit semipositive background correction. -/
def holomorphicPullbackPresentation
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hgopen : IsOpenMap g) {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg omega.form) + c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative theta) W epsilon)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : ¬ Wt.carrier ⊆ g ⁻¹' poleSet p.potential) :
    AdmissibleRestrictedCurrentPresentation omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg theta)) Wt
      ⟨c * epsilon, mul_pos hc epsilon.2⟩ where
  representative := ClosedRealOneOneForm.pullback hg p.representative
  represents := ofRepresentative_pullback_congr hg p.represents
  potential := fun z => p.potential (g z)
  potential_psh := by
    refine ⟨?_, locallyNondegenerate_comp_of_isOpenMap hgopen p.potential_psh.2⟩
    have hpull : ThetaPlurisubharmonic
        (ClosedRealOneOneForm.pullback hg p.representative +
          (epsilon : ℝ) • ClosedRealOneOneForm.pullback hg omega.form).val
        (fun z => p.potential (g z)) := by
      refine BlowupBigPullback.thetaPlurisubharmonic_of_geometricallyEq ?_
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp hg p.potential_psh.1)
      intro e z hz
      set d := complexChartAt (n := n) (g (e.val.symm z))
      have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d :=
        ⟨hz, mem_complexChartAt_source _⟩
      change (ClosedRealOneOneForm.pullback hg
        (p.representative + (epsilon : ℝ) • omega.form)).val.coeff e z = _
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
        ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hg _ e d hzd]
      ext v
      simp
    have hsemi : ((epsilon : ℝ) •
        (-(ClosedRealOneOneForm.pullback hg omega.form) + c • omegaZ.form)).val.IsSemipositive := by
      intro e z hz v
      rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      exact mul_nonneg epsilon.2.le (hD e z hz v)
    have hsum := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hpull hsemi
    have hform : ClosedRealOneOneForm.pullback hg p.representative +
        (epsilon : ℝ) • ClosedRealOneOneForm.pullback hg omega.form +
        (epsilon : ℝ) • (-(ClosedRealOneOneForm.pullback hg omega.form) + c • omegaZ.form) =
        ClosedRealOneOneForm.pullback hg p.representative +
          (c * epsilon : ℝ) • omegaZ.form := by
      rw [smul_add, smul_neg, smul_smul, mul_comm]
      abel
    rw [hform] at hsum
    exact hsum
  smoothAnalyticSingularities :=
    hasManifoldAnalyticSingularitiesSmoothOffPole_comp hg p.smoothAnalyticSingularities
  not_carrier_subset_poleSet := hWt

@[simp] theorem holomorphicPullbackPresentation_potential
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hgopen : IsOpenMap g) {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg omega.form) + c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative theta) W epsilon)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : ¬ Wt.carrier ⊆ g ⁻¹' poleSet p.potential) (z : Z) :
    (holomorphicPullbackPresentation hg hgopen hc hD p Wt hWt).potential z = p.potential (g z) := rfl

end

end SGPT.Foundations.Analysis.Pending.AdmissiblePresentationHolomorphicPullback
