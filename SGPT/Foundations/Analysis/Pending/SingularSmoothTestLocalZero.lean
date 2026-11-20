import SGPT.Foundations.Analysis.Pending.SingularSmoothTestChartStokes

set_option autoImplicit false

/-! # Actual local canonical NP zero patches produce the zero compact finite Stokes pairing -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalZero

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  GlobalNonPluripolar MixedNonPluripolar GlobalSlotStokes
  SingularSmoothTestLastSlot SingularSmoothTestChartStokes

noncomputable section

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsComplexManifold d X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {η : Fin d → ClosedRealOneOneForm d X} {s : Fin d → X → EReal}

/-- Actual zero canonical coordinate measures around each compact-support point give zero mass to that support under the genuine global mixed measure. -/
theorem globalMixedMeasure_compact_eq_zero_of_local_np_zero
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) {K : Set X} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ P : Patch η s,
      x ∈ P.source ∧ mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic = 0) :
    globalMixedMeasure η s hs K = 0 := by
  classical
  choose P hmem hNP using fun x : K => hlocal x.1 x.2
  let μ := globalMixedMeasure η s hs
  have hzero (x : K) : μ ((P x).source : Set X) = 0 := by
    have heq : μ.restrict ((P x).source : Set X) = 0 := by
      rw [globalMixedMeasure_restrict_patch hs (P x)]
      change (P x).pushMeasure
        (mixedTruncationLimitMeasure (P x).domain (P x).corrected (P x).plurisubharmonic) = 0
      rw [hNP x]
      simp [Patch.pushMeasure]
    have h := congrArg (fun ν : Measure X => ν univ) heq
    simpa using h
  have hcover : K ⊆ ⋃ x : K, ((P x).source : Set X) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ((P x).source : Set X))
    (fun x => (P x).source.isOpen) hcover
  apply measure_mono_null ht
  apply le_antisymm _ bot_le
  calc
    μ (⋃ x ∈ t, ((P x).source : Set X)) ≤ ∑ x ∈ t, μ ((P x).source : Set X) :=
      measure_biUnion_finset_le t _
    _ = 0 := by simp only [hzero, Finset.sum_const_zero]

/-- Genuine zero canonical NP patches around a compact test support internally force the actual global test integral to vanish. -/
theorem integral_eq_zero_of_local_np_zero
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) (g : X → ℝ)
    (hgc : HasCompactSupport g)
    (hlocal : ∀ x ∈ tsupport g, ∃ P : Patch η s,
      x ∈ P.source ∧ mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic = 0) :
    (∫ x, g x ∂globalMixedMeasure η s hs) = 0 := by
  have hK := globalMixedMeasure_compact_eq_zero_of_local_np_zero hs hgc hlocal
  have hae : ∀ᵐ x ∂globalMixedMeasure η s hs, x ∉ tsupport g :=
    ae_iff.mpr (by
      change globalMixedMeasure η s hs ((tsupport g)ᶜ)ᶜ = 0
      simpa only [compl_compl] using hK)
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {α : ClosedRealOneOneForm (n + 1) M} {W Φ : M → EReal}

/-- Actual local diagonal canonical NP vanishing on the test support, combined with the genuine finite coordinate Stokes producer, yields the zero finite local pairing. -/
theorem exists_finite_chart_smooth_test_stokes_eq_zero (omega : KahlerBackground (n + 1) M)
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (g : M → ℝ) (hg : ChartSmooth (n := n + 1) g)
    (hWzero : ∀ x ∈ tsupport g, ∃ P : Patch (fun _ : Fin (n + 1) => α) (fun _ => W),
      x ∈ P.source ∧ mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic = 0)
    (hΦzero : ∀ x ∈ tsupport g, ∃ P : Patch (fun _ : Fin (n + 1) => α) (fun _ => Φ),
      x ∈ P.source ∧ mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic = 0) :
    ∃ A : ℝ, 0 < A ∧ ∃ hp : IsThetaPshPotential (A • omega.form).val (fun x => (g x : EReal)),
      ∃ hq : IsThetaPshPotential (A • omega.form).val (fun _ => 0),
      ∃ (m : ℕ) (χ : Fin m → M → ℝ)
        (J : Fin m → SlotChart (lastHybridForms α (A • omega.form)) α),
        (∀ a, ChartSmooth (n := n + 1) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
        (∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) ∧ (∀ a, HasCompactSupport (χ a)) ∧
        (∀ x, ∑ a, χ a x = 1) ∧
        (∀ a i, i ≠ Fin.last n → ∀ z, (J a).potential i z = (J a).kahler z) ∧
        (∀ k a, Integrable (chartWeight (J a) (χ a) W Φ) (lastHybridChartMeasure hW hΦ hp (J a) k) ∧
          Integrable (chartWeight (J a) (χ a) W Φ) (lastHybridChartMeasure hW hΦ hq (J a) k)) ∧
        (∑ k : Fin (n + 1), ∑ a : Fin m,
          ((∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hp (J a) k) -
           (∫ z, chartWeight (J a) (χ a) W Φ z ∂lastHybridChartMeasure hW hΦ hq (J a) k))) =
          0 := by
  have hgc : HasCompactSupport g := isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (subset_univ _)
  have hIW := integral_eq_zero_of_local_np_zero (fun _ : Fin (n + 1) => hW.1) g hgc hWzero
  have hIΦ := integral_eq_zero_of_local_np_zero (fun _ : Fin (n + 1) => hΦ.1) g hgc hΦzero
  obtain ⟨A, hA, hp, hq, m, χ, J, hχs, hχ0, hχJ, hχc, hχ1, hcommon, hInt, hstokes⟩ :=
    exists_finite_chart_smooth_test_stokes omega hW hΦ hWΦ g hg
  refine ⟨A, hA, hp, hq, m, χ, J, hχs, hχ0, hχJ, hχc, hχ1, hcommon, hInt, ?_⟩
  exact hstokes.trans (by rw [hIW, hIΦ, sub_self])

end

end SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalZero
