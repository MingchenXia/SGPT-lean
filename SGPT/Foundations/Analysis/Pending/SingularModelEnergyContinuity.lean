import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle

set_option autoImplicit false

/-!
# Canonical dominated convergence for singular finite-type energy

Xia SGPT PDF0120--0121, the finite-type sequence case of Proposition 3.1.16.
Pointwise order produces a uniform singularity gap and actual finite mixed
measures integrate the canonical differences by dominated convergence.
The endpoint comparison squeezes the actual energy difference to zero.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyContinuity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  RelativeEnergyIntegrability SingularModelEnergyCocycle

noncomputable section

/-- Real canonical differences tend to zero even at the common pole of a same-type net. -/
theorem tendsto_canonicalDiff_of_sameSingularityType {X ι : Type*}
    {u : X → EReal} {v : ι → X → EReal} (F : Filter ι)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ j x, v j x ≠ ⊤)
    (htype : ∀ j, SameSingularityTypeOn (v j) u univ)
    (x : X) (hlim : Tendsto (fun j => v j x) F (𝓝 (u x))) :
    Tendsto (fun j => canonicalERealDiffToReal (v j x) (u x)) F (𝓝 (0 : ℝ)) := by
  by_cases hux : u x = ⊥
  · have hz : ∀ j, canonicalERealDiffToReal (v j x) (u x) = 0 := by
      intro j
      have hvx : v j x = ⊥ :=
        (sameSingularityTypeOn_eq_bot_iff (htype j) (mem_univ x)).mpr hux
      simp [hvx, hux]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) F (𝓝 0))
  · have hr : ∀ j, canonicalERealDiffToReal (v j x) (u x) =
        (v j x).toReal - (u x).toReal := fun j =>
      canonicalDiff_eq_sub_toReal (hv j x) (hu x)
        (sameSingularityTypeOn_eq_bot_iff (htype j) (mem_univ x))
    simp only [hr]
    have ht := (EReal.tendsto_toReal (hu x) hux).comp hlim
    simpa using ht.sub_const (u x).toReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual canonical mixed integrals converge by their produced uniform bounded gap. -/
theorem tendsto_integral_canonicalDiff_of_antitone (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {uk : ℕ → M → EReal}
    (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (htype : SameSingularityTypeOn (uk 0) u univ)
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x)))
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) :
    Tendsto (fun k => ∫ x, canonicalERealDiffToReal (uk k x) (u x)
      ∂globalMixedMeasure eta s hs) atTop (𝓝 (0 : ℝ)) := by
  have hle := MongeAmpereEnergyDecreasing.le_of_antitone_of_tendsto hanti hlim
  have hkType (k : ℕ) : SameSingularityTypeOn (uk k) u univ :=
    ⟨(MoreSingularOn.of_le fun x _ => hanti x (Nat.zero_le k)).trans htype.1,
      MoreSingularOn.of_le fun x _ => hle k x⟩
  let μ := globalMixedMeasure eta s hs
  let := globalMixedMeasure_isFiniteMeasure omega hs
  obtain ⟨C, _, hC⟩ := exists_abs_canonicalDiff_le_of_sameSingularityType htype
    (huk 0).1.quasiPlurisubharmonic.ne_top hu.1.quasiPlurisubharmonic.ne_top
  have h0 : (∫ _x : M, (0 : ℝ) ∂μ) = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_)
    (integrable_const C) (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · exact (measurable_canonicalERealDiffToReal.comp
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable (huk k).1).prodMk
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1))).aestronglyMeasurable
  · by_cases hux : u x = ⊥
    · have hkx : uk k x = ⊥ :=
        (sameSingularityTypeOn_eq_bot_iff (hkType k) (mem_univ x)).mpr hux
      simpa [hkx, hux] using (abs_nonneg (canonicalERealDiffToReal (uk 0 x) (u x))).trans (hC x)
    · have hkx : uk k x ≠ ⊥ := fun h =>
        hux ((sameSingularityTypeOn_eq_bot_iff (hkType k) (mem_univ x)).mp h)
      have hk0x : uk 0 x ≠ ⊥ := fun h =>
        hux ((sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp h)
      have h1 : (uk k x).toReal ≤ (uk 0 x).toReal :=
        EReal.toReal_le_toReal (hanti x (Nat.zero_le k)) hkx
          ((huk 0).1.quasiPlurisubharmonic.ne_top x)
      have h2 : (u x).toReal ≤ (uk k x).toReal :=
        EReal.toReal_le_toReal (hle k x) hux ((huk k).1.quasiPlurisubharmonic.ne_top x)
      rw [canonicalDiff_eq_sub_toReal ((huk k).1.quasiPlurisubharmonic.ne_top x)
        (hu.1.quasiPlurisubharmonic.ne_top x)
        (sameSingularityTypeOn_eq_bot_iff (hkType k) (mem_univ x)),
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h2)]
      have h3 := hC x
      rw [canonicalDiff_eq_sub_toReal ((huk 0).1.quasiPlurisubharmonic.ne_top x)
        (hu.1.quasiPlurisubharmonic.ne_top x)
        (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))] at h3
      exact (sub_le_sub_right h1 _).trans ((le_abs_self _).trans h3)
  · exact tendsto_canonicalDiff_of_sameSingularityType atTop hu.1.quasiPlurisubharmonic.ne_top
      (fun k => (huk k).1.quasiPlurisubharmonic.ne_top) hkType x (hlim x)

/-- Decreasing continuity of actual finite-type energy for singular same-type endpoints. -/
theorem relativeEnergyOfMinimalType_tendsto_of_antitone (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : SameSingularityTypeOn u φ univ) {uk : ℕ → M → EReal}
    (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (hu0φ : SameSingularityTypeOn (uk 0) φ univ)
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    Tendsto (fun k => relativeEnergyOfMinimalType θ φ (uk k) hφ (huk k)) atTop
      (𝓝 (relativeEnergyOfMinimalType θ φ u hφ hu)) := by
  have hle := MongeAmpereEnergyDecreasing.le_of_antitone_of_tendsto hanti hlim
  have hkType (k : ℕ) : SameSingularityTypeOn (uk k) φ univ :=
    ⟨(MoreSingularOn.of_le fun x _ => hanti x (Nat.zero_le k)).trans hu0φ.1,
      huφ.2.trans (MoreSingularOn.of_le fun x _ => hle k x)⟩
  have hbound := tendsto_integral_canonicalDiff_of_antitone omega hu huk (hu0φ.trans huφ.symm)
    hanti hlim (fun _ : Fin n => hu.1)
  have hsq : Tendsto (fun k => relativeEnergyOfMinimalType θ φ (uk k) hφ (huk k) -
      relativeEnergyOfMinimalType θ φ u hφ hu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun k => ?_) (fun k => ?_)
    · exact sub_nonneg.mpr
        (relativeEnergyOfMinimalType_mono omega θ hφ hu (huk k) huφ (hkType k) (hle k))
    · exact (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ (huk k) hu
        (hkType k) huφ).2
  simpa using hsq.add_const (relativeEnergyOfMinimalType θ φ u hφ hu)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyContinuity
