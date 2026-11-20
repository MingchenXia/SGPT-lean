import SGPT.PSH.HermitianGlobalMeasure
import SGPT.PSH.HermitianExtremalLocalCapacityDomination
import SGPT.PSH.HermitianExtremalCurrentAlgebra
import SGPT.PSH.HermitianProductsRescaling
import SGPT.PSH.HermitianBalayageBackgroundMeasure
import SGPT.PSH.HermitianBalayageGlobalMassSupport
import SGPT.PSH.HermitianExtremalChartSublevels

/-!
# The actual global Hermitian capacity budget on radial sublevels

The canonical global product is read on a genuine correction patch. The
proved product rescaling and ordinary corrected-measure capacity bound
then give the inverse-level estimate. The actual extremal support theorem
turns that local budget into a budget for the whole global mass.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorCollar
  Hermitian HermitianGlobalProducts HermitianProducts HermitianBalayage
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : Background (m + 1) M}

/-- The actual global measure on an inverse-chart image is exactly the
native coordinate trace, for every subset of a genuine patch. -/
theorem globalMixedMeasure_image_patch
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) (s : Set (ComplexModel (m + 1)))
    (hs : s ⊆ P.geometry.domain) :
    globalMixedMeasure omega u hu hb (P.geometry.chart.val.symm '' s) =
      (P.current_isPositive u hu hb).traceMeasure s := by
  let E := P.geometry.chart.val.symm '' s
  have hE : E ⊆ P.geometry.source := by
    rintro x ⟨z, hz, rfl⟩
    exact P.geometry.map_target (hs hz)
  have hr : (globalMixedMeasure omega u hu hb).restrict P.geometry.source E =
      globalMixedMeasure omega u hu hb E := by
    rw [Measure.restrict_apply' P.geometry.source.isOpen.measurableSet,
      inter_eq_left.mpr hE]
  rw [← hr, globalMixedMeasure_restrict_patch u hu hb P]
  rw [CoordinatePatch.pushTraceMeasure, P.geometry.pushMeasure_apply_image,
    inter_eq_left.mpr hE]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    rwa [P.geometry.chart.val.right_inv (P.geometry.domain_le_target (hs hy))]
  · intro hz
    exact ⟨P.geometry.chart.val.symm z, ⟨z, hz, rfl⟩,
      P.geometry.chart.val.right_inv (P.geometry.domain_le_target (hs hz))⟩

def normalizedPotential (c : ℝ) (h : M → EReal) : M → EReal :=
  fun x => ((1 / c : ℝ) : EReal) * h x

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem normalizedPotential_isHermitianPSH {h : M → EReal}
    (hh : IsHermitianPSH omega h) {c : ℝ} (hc : 1 ≤ c) :
    IsHermitianPSH omega (normalizedPotential c h) := by
  unfold normalizedPotential
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hbudget : ∑ _ : Unit, (1 / c : ℝ) ≤ 1 := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact (div_le_one hcpos).mpr hc
  simpa only [Finset.univ_unique, Finset.sum_singleton] using
    HermitianExtremalCurrentAlgebra.isHermitianPSH_fintype_nonnegSum omega
      (fun _ : Unit => (1 / c : ℝ)) (fun _ => by positivity) hbudget
      (fun _ => h) (fun _ => hh)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem normalizedPotential_unit_bounds {h : M → EReal} {c : ℝ} (hc : 1 ≤ c)
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ (c : EReal)) :
    ∀ x, 0 ≤ normalizedPotential c h x ∧ normalizedPotential c h x ≤ 1 := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hcoeff : (0 : EReal) ≤ ((1 / c : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (by positivity)
  intro x
  refine ⟨mul_nonneg hcoeff (hh x).1, ?_⟩
  have h := mul_le_mul_of_nonneg_left (hh x).2 hcoeff
  simpa only [← EReal.coe_mul, one_div_mul_cancel hcpos.ne', EReal.coe_one,
    normalizedPotential] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem correctedReal_normalizedPotential (P : BackgroundPatch omega)
    (h : M → EReal) (c : ℝ) :
    P.correctedReal (normalizedPotential c h) = fun z =>
      (chartFunction h P.geometry.chart z).toReal / c + P.correction z := by
  funext z
  simp only [BackgroundPatch.correctedReal, chartFunction, normalizedPotential,
    EReal.toReal_mul, EReal.toReal_coe, one_div_mul_eq_div]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual patch measure of a bounded nonnegative potential satisfies
the proved degree-power rescaling estimate. -/
theorem backgroundDiagonalMeasure_rescale_le (P : BackgroundPatch omega)
    (h : M → EReal) (hh : IsHermitianPSH omega h) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ x, 0 ≤ h x ∧ h x ≤ (c : EReal)) :
    backgroundDiagonalMeasure P h hh ⟨0, c, hb⟩ ≤
      Real.toNNReal (c ^ (m + 1)) •
        backgroundDiagonalMeasure P (normalizedPotential c h)
          (normalizedPotential_isHermitianPSH hh hc)
          ⟨0, 1, normalizedPotential_unit_bounds hc hb⟩ := by
  let H := fun z => (chartFunction h P.geometry.chart z).toReal
  have hhB : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ h x ∧ h x ≤ (b : EReal) := ⟨0, c, hb⟩
  have hnB : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ normalizedPotential c h x ∧
      normalizedPotential c h x ≤ (b : EReal) := ⟨0, 1, normalizedPotential_unit_bounds hc hb⟩
  have hv : ∀ _ : Fin (m + 1), IsLocallyBoundedPshOn P.geometry.domain
      (fun z => H z + P.correction z) :=
    fun _ => P.correctedReal_isLocallyBoundedPshOn hh hhB
  have hw : ∀ _ : Fin (m + 1), IsLocallyBoundedPshOn P.geometry.domain
      (fun z => H z / c + P.correction z) := by
    intro i
    rw [← correctedReal_normalizedPotential P h c]
    exact P.correctedReal_isLocallyBoundedPshOn
      (normalizedPotential_isHermitianPSH hh hc) hnB
  have hdiff := isPositive_backgroundExpansion_rescale_sub (m + 1) 0
    (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1)))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun _ => H) P.smooth
    ((omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target)
    (fun z hz => ⟨omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz),
      omega.isSemipositive P.geometry.chart z (P.geometry.domain_le_target hz)⟩)
    hc hv hw (fun _ => P.factor_isPositive hh hhB)
  have hQeq : backgroundExpansion (m + 1) 0
      (fun _ z => H z / c + P.correction z) P.residual_smooth
      (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1))) =
      P.current (fun _ => normalizedPotential c h) := by
    apply backgroundExpansion_congr
    · intro i z _
      exact (congrFun (correctedReal_normalizedPotential P h c) z).symm
    · intro z _
      rfl
  change IsPositive (c ^ (m + 1) • backgroundExpansion (m + 1) 0
      (fun _ z => H z / c + P.correction z) P.residual_smooth
      (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1))) -
      P.current (fun _ => h)) at hdiff
  rw [hQeq] at hdiff
  let hP := P.current_isPositive (fun _ => h) (fun _ => hh) (fun _ => hhB)
  let hQ := P.current_isPositive (fun _ => normalizedPotential c h)
    (fun _ => normalizedPotential_isHermitianPSH hh hc) (fun _ => hnB)
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let hRight := hQ.smul (pow_nonneg hcpos.le (m + 1))
  have hle := LocalBedfordTaylorCalculus.traceMeasure_le_of_isPositive_sub hP hRight hdiff
  have heq : hRight.traceMeasure = Real.toNNReal (c ^ (m + 1)) • hQ.traceMeasure := by
    apply traceMeasure_eq_smul_of_current_eq _ _ (Real.toNNReal (c ^ (m + 1)))
    rw [Real.coe_toNNReal _ (pow_nonneg hcpos.le (m + 1))]
  rw [heq] at hle
  exact hle

omit [IsComplexManifold (m + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem chart_compactSublevel_eq_image (e : ComplexChart (m + 1) M)
    (a : ComplexModel (m + 1)) {r : ℝ} (htarget : closedBall a r ⊆ e.val.target)
    (s : ℝ) (u : ComplexModel (m + 1) → EReal) (j N : ℕ) :
    compactSublevel (chartClosedBall e a r) (chartRadialApproximation e s u) j N =
      e.val.symm '' compactSublevel (closedBall a r) (radialApproximation s u) j N := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := hx.1
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    change radialApproximation s u j z ≤ -((N : ℝ) + 1)
    have h := hx.2
    change radialApproximation s u j (e.val (e.val.symm z)) ≤ -((N : ℝ) + 1) at h
    rwa [e.val.right_inv (htarget hz)] at h
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    change radialApproximation s u j (e.val (e.val.symm z)) ≤ -((N : ℝ) + 1)
    rw [e.val.right_inv (htarget hz.1)]
    exact hz.2

/-- One actual finite budget controls the canonical global product on
every radial compact sublevel, uniformly over all bounded nonnegative
Hermitian PSH potentials and over both sequence indices. -/
theorem exists_globalMeasure_radial_compactSublevel_bound
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (Ω : Opens (ComplexModel (m + 1)))
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))))
    (htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target)
    (a : ComplexModel (m + 1)) {r R T : ℝ}
    (hR : 0 < R) (hr : r < R / 2) (hRT : 3 * R < T)
    (hΩ : closedBall a (5 * R) ⊆ Ω)
    {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u (ball a T))
    (hne : ∃ z ∈ ball a T, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a T, u z ≤ 0) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (h : M → EReal) (hh : IsHermitianPSH omega h) (S : ℝ)
        (hb : ∀ x, 0 ≤ h x ∧ h x ≤ (S : EReal)) (j N : ℕ),
        globalMixedMeasure omega (fun _ => h) (fun _ => hh) (fun _ => ⟨0, S, hb⟩)
          (compactSublevel (chartClosedBall e a r)
            (chartRadialApproximation e ((T - r) / 2) u) j (N + 1)) ≤
          ENNReal.ofReal (D * (max 1 S) ^ (m + 1) / ((N : ℝ) + 1)) := by
  obtain ⟨A, D, _, hD, hdom, hbudget⟩ :=
    exists_uniform_corrected_measure_radial_sublevel_bound omega e Ω hcompact htarget
      a hR hr hRT hΩ hu hne hnonpos
  let P : BackgroundPatch omega :=
    ⟨⟨e, Ω, subset_closure.trans htarget⟩, ballPot A a 0,
      (contDiff_ballPot A a 0).contDiffOn, hdom⟩
  have hballΩ : closedBall a r ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : r ≤ 5 * R)).trans hΩ
  have hballTarget : closedBall a r ⊆ e.val.target :=
    hballΩ.trans (subset_closure.trans htarget)
  refine ⟨D, hD, fun h hh S hb j N => ?_⟩
  let c : ℝ := max 1 S
  have hc : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hbc : ∀ x, 0 ≤ h x ∧ h x ≤ (c : EReal) :=
    fun x => ⟨(hb x).1, (hb x).2.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))⟩
  let v := normalizedPotential c h
  have hv : IsHermitianPSH omega v := normalizedPotential_isHermitianPSH hh hc
  have hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 1 := normalizedPotential_unit_bounds hc hbc
  let hbv : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v x ∧ v x ≤ (b : EReal) :=
    ⟨0, 1, fun x => ⟨by simpa only [EReal.coe_zero] using (hvb x).1,
      by simpa only [EReal.coe_one] using (hvb x).2⟩⟩
  obtain ⟨hcorr, hordinary⟩ := hbudget v hv hvb
  let K := compactSublevel (closedBall a r) (radialApproximation ((T - r) / 2) u) j (N + 1)
  have hKΩ : K ⊆ P.geometry.domain := fun z hz => hballΩ hz.1
  have hdiag : backgroundDiagonalMeasure P v hv hbv K ≤
      ENNReal.ofReal (D / ((N : ℝ) + 1)) := by
    exact (Measure.le_iff'.mp (backgroundDiagonalMeasure_le_canonical P v hv hbv) K).trans
      (hordinary j N)
  have hscale : backgroundDiagonalMeasure P h hh ⟨0, S, hb⟩ K ≤
      (Real.toNNReal (c ^ (m + 1)) • backgroundDiagonalMeasure P v hv hbv) K :=
    Measure.le_iff'.mp (backgroundDiagonalMeasure_rescale_le P h hh hc hbc) K
  calc
    _ = backgroundDiagonalMeasure P h hh ⟨0, S, hb⟩ K := by
      rw [chart_compactSublevel_eq_image e a hballTarget]
      exact globalMixedMeasure_image_patch (fun _ => h) (fun _ => hh)
        (fun _ => ⟨0, S, hb⟩) P K hKΩ
    _ ≤ (Real.toNNReal (c ^ (m + 1)) • backgroundDiagonalMeasure P v hv hbv) K := hscale
    _ ≤ ENNReal.ofReal (c ^ (m + 1)) * ENNReal.ofReal (D / ((N : ℝ) + 1)) := by
      rw [Measure.smul_apply]
      change ENNReal.ofReal (c ^ (m + 1)) * backgroundDiagonalMeasure P v hv hbv K ≤ _
      exact mul_le_mul_of_nonneg_left hdiag zero_le
    _ = ENNReal.ofReal (D * (max 1 S) ^ (m + 1) / ((N : ℝ) + 1)) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hcpos.le (m + 1))]
      congr 1
      dsimp only [c]
      ring

/-- The actual bounded extremal's whole canonical global mass has the
inverse-level budget. Support on the literal compact sublevel is produced
by the proved frozen-ball mass-support theorem. -/
theorem exists_extremal_globalMass_radial_bound
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (Ω : Opens (ComplexModel (m + 1)))
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))))
    (htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target)
    (a : ComplexModel (m + 1)) {r R T : ℝ}
    (hR : 0 < R) (hr : r < R / 2) (hRT : 3 * R < T)
    (hΩ : closedBall a (5 * R) ⊆ Ω)
    {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u (ball a T))
    (hne : ∃ z ∈ ball a T, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a T, u z ≤ 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (j N : ℕ) (S : ℝ)
      (hE : IsHermitianPSH omega (regularizedExtremal omega
        (compactSublevel (chartClosedBall e a r)
          (chartRadialApproximation e ((T - r) / 2) u) j (N + 1))))
      (hES : ∀ x, regularizedExtremal omega
        (compactSublevel (chartClosedBall e a r)
          (chartRadialApproximation e ((T - r) / 2) u) j (N + 1)) x ≤ (S : EReal)),
      globalMixedMeasure omega
        (fun _ => regularizedExtremal omega (compactSublevel (chartClosedBall e a r)
          (chartRadialApproximation e ((T - r) / 2) u) j (N + 1))) (fun _ => hE)
        (fun _ => ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega _ x, hES x⟩⟩) univ ≤
        ENNReal.ofReal (D * (max 1 S) ^ (m + 1) / ((N : ℝ) + 1)) := by
  obtain ⟨D, hD, hbudget⟩ := exists_globalMeasure_radial_compactSublevel_bound omega e Ω
    hcompact htarget a hR hr hRT hΩ hu hne hnonpos
  have hrT : r < T := by linarith
  have hballTarget : closedBall a r ⊆ e.val.target :=
    (closedBall_subset_closedBall (by linarith : r ≤ 5 * R)).trans
      (hΩ.trans (subset_closure.trans htarget))
  have hcont := (chartRadialApproximation_properties e a hrT hballTarget hu hne hnonpos).1
  refine ⟨D, hD, fun j N S hE hES => ?_⟩
  let K := compactSublevel (chartClosedBall e a r)
    (chartRadialApproximation e ((T - r) / 2) u) j (N + 1)
  have hK : IsClosed K :=
    (compactSublevel_isCompact (chartClosedBall_isCompact e a r hballTarget) hcont j (N + 1)).isClosed
  let hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ regularizedExtremal omega K x ∧
      regularizedExtremal omega K x ≤ (b : EReal) :=
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
  let μ := globalMixedMeasure omega (fun _ => regularizedExtremal omega K) (fun _ => hE) (fun _ => hb)
  have hsupp : μ Kᶜ = 0 := global_extremal_measure_compl_eq_zero omega K hK hE hES
  have hmass : μ univ = μ K := by
    have h := measure_add_measure_compl (μ := μ) hK.measurableSet
    rw [hsupp, add_zero] at h
    exact h.symm
  change μ univ ≤ _
  rw [hmass]
  exact hbudget (regularizedExtremal omega K) hE S
    (fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩) j N

end SGPT.PSH.HermitianExtremal
