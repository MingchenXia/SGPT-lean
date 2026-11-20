import SGPT.Foundations.Analysis.Pending.SingularSmoothTestChartStokes
import SGPT.Foundations.Analysis.Pending.GlobalOpenLocality

set_option autoImplicit false

/-! # Actual compact Stokes defects localize to genuine finite core chart families -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalizedChartStokes

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  RelativeEnergy RelativeEnergyIntegrability GlobalSlotStokes GlobalNonPluripolar
  GlobalOpenLocality DeepCoincidenceIntegrationByParts
  SingularSmoothTestStokes SingularSmoothTestLastSlot SingularSmoothTestChartStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {α β : ClosedRealOneOneForm (n + 1) M} {W Φ : M → EReal} {g : M → ℝ}

/-- The actual last-slot test and zero measures agree on the genuine ordinary open complement of the test support. -/
theorem lastHybrid_restrict_compl_tsupport_eq
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hp : IsThetaPshPotential β.val fun x => (g x : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0) (k : Fin (n + 1)) :
    (lastHybridMixedMeasure hW hΦ hp k).restrict (tsupport g)ᶜ =
      (lastHybridMixedMeasure hW hΦ hq k).restrict (tsupport g)ᶜ := by
  apply globalMixedMeasure_update_restrict_eq_of_eqOn
    (prefixPotentialTuple k.val W Φ) (Fin.last n)
    (lastHybridThetaPlurisubharmonic hW hΦ hp k)
    (lastHybridThetaPlurisubharmonic hW hΦ hq k) (isClosed_tsupport g).isOpen_compl
  intro x hx
  simp only [image_eq_zero_of_notMem_tsupport hx, EReal.coe_zero]

private theorem integrable_continuous_mul_gap (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) {r : M → EReal}
    (hr : IsThetaPshPotential β.val r) (k : Fin (n + 1)) (f : M → ℝ) (hf : Continuous f) :
    Integrable (fun x => f x * canonicalERealDiffToReal (W x) (Φ x))
      (lastHybridMixedMeasure hW hΦ hr k) := by
  have hi := integrable_canonicalDiff_globalMixedMeasure omega hW.1 hΦ.1 hWΦ
    (lastHybridThetaPlurisubharmonic hW hΦ hr k)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact hi.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall fun x => hC x (mem_univ x))

/-- Genuine compact same-type integrability and actual test-slot open locality internally show that a continuous cutoff equal to one on the test support preserves the signed defect. -/
theorem integral_cutoff_lastHybrid_defect_eq (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hp : IsThetaPshPotential β.val fun x => (g x : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0) (k : Fin (n + 1))
    {ζ : M → ℝ} (hζ : Continuous ζ) (hζ1 : EqOn ζ (fun _ => 1) (tsupport g)) :
    (∫ x, ζ x * canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hp k) -
    (∫ x, ζ x * canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hq k) =
    (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hp k) -
    (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hq k) := by
  let F : M → ℝ := fun x => canonicalERealDiffToReal (W x) (Φ x)
  let μa := lastHybridMixedMeasure hW hΦ hp k
  let μb := lastHybridMixedMeasure hW hΦ hq k
  have hFa : Integrable F μa := integrable_canonicalDiff_globalMixedMeasure omega hW.1 hΦ.1 hWΦ
    (lastHybridThetaPlurisubharmonic hW hΦ hp k)
  have hFb : Integrable F μb := integrable_canonicalDiff_globalMixedMeasure omega hW.1 hΦ.1 hWΦ
    (lastHybridThetaPlurisubharmonic hW hΦ hq k)
  have hζFa : Integrable (fun x => ζ x * F x) μa :=
    integrable_continuous_mul_gap omega hW hΦ hWΦ hp k ζ hζ
  have hζFb : Integrable (fun x => ζ x * F x) μb :=
    integrable_continuous_mul_gap omega hW hΦ hWΦ hq k ζ hζ
  let T : M → ℝ := fun x => F x - ζ x * F x
  have hzero (x : M) (hx : x ∉ (tsupport g)ᶜ) : T x = 0 := by
    have hxK : x ∈ tsupport g := not_not.mp hx
    dsimp only [T]
    rw [hζ1 hxK]
    simp only [one_mul, sub_self]
  have heq : (∫ x, T x ∂μa) = ∫ x, T x ∂μb := by
    calc
      _ = ∫ x in (tsupport g)ᶜ, T x ∂μa :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ x in (tsupport g)ᶜ, T x ∂μb := by
        rw [lastHybrid_restrict_compl_tsupport_eq hW hΦ hp hq k]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  change (∫ x, F x - ζ x * F x ∂μa) = ∫ x, F x - ζ x * F x ∂μb at heq
  rw [integral_sub hFa hζFa, integral_sub hFb hζFb] at heq
  change (∫ x, ζ x * F x ∂μa) - (∫ x, ζ x * F x ∂μb) =
    (∫ x, F x ∂μa) - (∫ x, F x ∂μb)
  linarith

private theorem sum_chart_integral_eq_cutoff (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) {r : M → EReal}
    (hr : IsThetaPshPotential β.val r)
    {m : ℕ} (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (lastHybridForms α β) α)
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a))
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    {ζ : M → ℝ} (hχsum : ∀ x, ∑ a, χ a x = ζ x) (k : Fin (n + 1)) :
    (∑ a, ∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hr (J a) k) =
      ∫ x, ζ x * canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hr k := by
  classical
  have hip (a : Fin m) : Integrable (fun x => χ a x * canonicalERealDiffToReal (W x) (Φ x))
      (lastHybridMixedMeasure hW hΦ hr k) :=
    integrable_continuous_mul_gap omega hW hΦ hWΦ hr k (χ a)
      (ProductTestForms.ChartSmooth.continuous (hχs a))
  simp_rw [integral_chart_lastHybrid_eq_global hW hΦ hr _ k (hχJ _)]
  rw [← integral_finsetSum _ (fun a _ => hip a)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ a : Fin m, χ a x * canonicalERealDiffToReal (W x) (Φ x)) = _
    rw [← Finset.sum_mul, hχsum x]

/-- Actual subordinate core chart weights whose finite sum is a cutoff equal to one on the test support produce the uncut last-slot signed defect. -/
theorem sum_localized_chart_defect_eq_global (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hp : IsThetaPshPotential β.val fun x => (g x : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0)
    {m : ℕ} (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (lastHybridForms α β) α)
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a))
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    {ζ : M → ℝ} (hζ : Continuous ζ) (hζ1 : EqOn ζ (fun _ => 1) (tsupport g))
    (hχsum : ∀ x, ∑ a, χ a x = ζ x) (k : Fin (n + 1)) :
    (∑ a, ((∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
      (∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hq (J a) k))) =
      (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hp k) -
      (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hq k) := by
  classical
  rw [Finset.sum_sub_distrib,
    sum_chart_integral_eq_cutoff omega hW hΦ hWΦ hp χ J hχs hχJ hχsum k,
    sum_chart_integral_eq_cutoff omega hW hΦ hWΦ hq χ J hχs hχJ hχsum k]
  exact integral_cutoff_lastHybrid_defect_eq omega hW hΦ hWΦ hp hq k hζ hζ1

/-- Genuine compact singular Stokes and actual cutoff localization internally identify the finite core chart sum with the precise global diagonal test difference. -/
theorem sum_localized_chart_defect_eq_smooth_test_stokes (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hp : IsThetaPshPotential β.val fun x => (g x : EReal))
    (hq : IsThetaPshPotential β.val fun _ => 0)
    (hg : ChartSmooth (n := n + 1) g)
    {m : ℕ} (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (lastHybridForms α β) α)
    (hχs : ∀ a, ChartSmooth (n := n + 1) (χ a))
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    {ζ : M → ℝ} (hζ : Continuous ζ) (hζ1 : EqOn ζ (fun _ => 1) (tsupport g))
    (hχsum : ∀ x, ∑ a, χ a x = ζ x) :
    (∑ k : Fin (n + 1), ∑ a : Fin m,
      ((∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
       (∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hq (J a) k))) =
      (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => W) (fun _ => hW.1)) -
      (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => Φ) (fun _ => hΦ.1)) := by
  classical
  have hb := GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
    (ProductTestForms.ChartSmooth.continuous hg)
  have hz : BoundedGlobalProduct.IsBoundedPotential (fun _ : M => (0 : EReal)) :=
    ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have htype := BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb hz
  have hdiff (x : M) : canonicalERealDiffToReal (g x : EReal) 0 = g x := by
    simpa only [EReal.coe_zero, sub_zero] using canonicalERealDiffToReal_coe_coe (g x) 0
  calc
    _ = ∑ k : Fin (n + 1), ((∫ x, canonicalERealDiffToReal (W x) (Φ x)
        ∂lastHybridMixedMeasure hW hΦ hp k) -
        (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂lastHybridMixedMeasure hW hΦ hq k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact sum_localized_chart_defect_eq_global omega hW hΦ hWΦ hp hq χ J hχs hχJ
        hζ hζ1 hχsum k
    _ = _ := by
      simp_rw [← hybridUpdatedMixedMeasure_eq_last hW hΦ]
      have hs := (integral_sub_diagonal_eq_sum_hybrid omega hW hΦ hp hq hWΦ htype).symm
      simpa only [hdiff] using hs

end

end SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalizedChartStokes
