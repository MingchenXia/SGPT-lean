import SGPT.PSH.HermitianBalayageFrozenBall
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasing

/-!
# Increasing limits of actual zero-mass replacements

Uniform bounds and monotonicity produce the regularized PSH reader.
Almost-everywhere recovery of increasing PSH suprema and the genuine
Bedford--Taylor increasing convergence theorem then preserve zero mass.
The limit's positivity, finiteness and zero mass are conclusions.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.PSH.SourceDomainBalayageDraft
open scoped Topology Distributions

/-- A uniformly bounded increasing sequence of actual bounded PSH
zero-mass potentials has its actual regularized PSH limit and zero
canonical Bedford--Taylor measure. -/
theorem increasing_usc_reader_zero_mass {N : ℕ} {Ω : Opens (ComplexModel N)}
    (w : ℕ → ComplexModel N → ℝ) (hw : ∀ j, IsLocallyBoundedPshOn Ω (w j))
    (hmono : ∀ z ∈ Ω, Monotone fun j => w j z)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j z, z ∈ Ω → |w j z| ≤ M)
    (hzero : ∀ j,
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω (w j) (hw j) Ω = 0) :
    ∃ hW : IsLocallyBoundedPshOn Ω (fun z =>
        (uscRegularization (⨆ j, fun y => (w j y : EReal)) z).toReal),
      Measurable (fun z => (uscRegularization (⨆ j, fun y => (w j y : EReal)) z).toReal) ∧
      (∀ z ∈ Ω, |(uscRegularization (⨆ j, fun y => (w j y : EReal)) z).toReal| ≤ M) ∧
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω
        (fun z => (uscRegularization (⨆ j, fun y => (w j y : EReal)) z).toReal) hW = 0 := by
  let f : ℕ → ComplexModel N → EReal := fun j z => (w j z : EReal)
  let V := uscRegularization (⨆ j, f j)
  let W := fun z => (V z).toReal
  have hF : LocallyUniformlyBoundedAbove (range f) Ω := by
    intro z hz
    refine ⟨Ω, mem_nhdsWithin_of_mem_nhds (Ω.isOpen.mem_nhds hz), M, ?_⟩
    rintro g ⟨j, rfl⟩ y hy
    exact EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hbound j y hy.2))
  have hp : PlurisubharmonicOn V Ω := by
    have h := plurisubharmonicOn_uscRegularization_sSup Ω.isOpen (range_nonempty f)
      (fun g hg => by obtain ⟨j, rfl⟩ := hg; exact (hw j).1) hF
    simpa only [sSup_range] using h
  have hlo : ∀ z ∈ Ω, ((-M : ℝ) : EReal) ≤ V z := by
    intro z hz
    calc
      ((-M : ℝ) : EReal) ≤ f 0 z := EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hbound 0 z hz))
      _ ≤ (⨆ j, f j) z := by rw [iSup_apply]; exact le_iSup (fun j => f j z) 0
      _ ≤ V z := le_uscRegularization _ z
  have hconst : IsLocallyBoundedPshOn Ω (fun _ : ComplexModel N => -M) :=
    isLocallyBoundedPshOn_of_abs_le (C := M)
      (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)
      (fun _ _ => by simp [abs_of_nonneg hM])
  have hreader := psh_toReal_locallyBounded_of_ge_original hconst hp hlo
  have hW : IsLocallyBoundedPshOn Ω W := hreader.1
  have hWM : ∀ z ∈ Ω, |W z| ≤ M := by
    intro z hz
    have hupper : V z ≤ (M : EReal) := by
      apply uscRegularization_le_of_eventually_le upperSemicontinuousAt_const
      filter_upwards [Ω.isOpen.mem_nhds hz] with y hy
      rw [iSup_apply]
      change (⨆ j, f j y) ≤ (M : EReal)
      exact iSup_le (fun j => EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hbound j y hy)))
    apply abs_le.mpr
    constructor
    · apply EReal.coe_le_coe_iff.mp
      rw [hreader.2 z hz]
      exact hlo z hz
    · apply EReal.coe_le_coe_iff.mp
      rw [hreader.2 z hz]
      exact hupper
  have hfm : ∀ z ∈ Ω, Monotone fun j => f j z := by
    intro z hz i j hij
    exact EReal.coe_le_coe_iff.mpr (hmono z hz hij)
  obtain ⟨K, hK⟩ := exists_nat_ge M
  have hftrunc : ∀ j z, z ∈ Ω → truncationReal (f j) K z = w j z := by
    intro j z hz
    have hl : (-(K : ℝ)) ≤ w j z := (neg_le_neg hK).trans (neg_le_of_abs_le (hbound j z hz))
    simp only [truncationReal, truncation, f, max_eq_left (EReal.coe_le_coe_iff.mpr hl), EReal.toReal_coe]
  have hVtrunc : ∀ z ∈ Ω, truncationReal V K z = W z := by
    intro z hz
    have hl : ((-(K : ℝ) : ℝ) : EReal) ≤ V z :=
      (EReal.coe_le_coe_iff.mpr (neg_le_neg hK)).trans (hlo z hz)
    simp only [truncationReal, truncation, max_eq_left hl, W]
  have hae := IncreasingTruncationLimit.ae_tendsto_truncationReal_of_monotone
    (fun j => (hw j).1) hfm (show EqOn V (uscRegularization (⨆ j, f j)) Ω from fun _ _ => rfl) hp K
  have haeW : ∀ᵐ z, z ∈ Ω → Tendsto (fun j => w j z) atTop (𝓝 (W z)) := by
    filter_upwards [hae] with z hz hzΩ
    have ht := (hz hzΩ).congr (fun j => hftrunc j z hzΩ)
    rw [hVtrunc z hzΩ] at ht
    exact ht
  let μ := SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω W hW
  have hμ := isBTLimit_canonicalBedfordTaylorMeasure hW
  have hμjzero (j : ℕ) :
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω (w j) (hw j) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    apply le_antisymm _ bot_le
    calc
      _ = SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω (w j) (hw j)
          ((Ω : Set (ComplexModel N)) ∪ (Ω : Set (ComplexModel N))ᶜ) := by rw [union_compl_self]
      _ ≤ _ := measure_union_le _ _
      _ = 0 := by rw [hzero j, (isBTLimit_canonicalBedfordTaylorMeasure (hw j)).1]; simp
  have hμzero : μ = 0 := by
    apply LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq
      hμ.1 (by simp) hμ.2.1 (fun _ _ _ => by simp)
    intro φ
    have ht := (IncreasingTruncationLimit.boundedIncreasingConvergence Ω w W hw hW
      hmono haeW φ φ.continuous φ.hasCompactSupport φ.tsupport_subset).1
    simp only [hμjzero, integral_zero_measure] at ht
    have heq := tendsto_nhds_unique ht (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using heq
  refine ⟨hW, (upperSemicontinuous_uscRegularization _).measurable.ereal_toReal, hWM, hμzero⟩

/-- The actual lower and upper replacement comparisons survive upper
regularization. This is the frozen-ball gap step: the original increasing
family recovers `U`, while every replacement lies between its datum and
one common upper-semicontinuous majorant `U + η`. -/
theorem increasing_usc_reader_gap {N : ℕ} {Ω : Opens (ComplexModel N)}
    (u v : ℕ → ComplexModel N → ℝ) {U : ComplexModel N → ℝ}
    (hU : IsLocallyBoundedPshOn Ω U)
    (hUlimit : EqOn (fun z => (U z : EReal))
      (uscRegularization (⨆ j, fun y => (u j y : EReal))) Ω)
    {η : ℝ} (hlower : ∀ j z, z ∈ Ω → u j z ≤ v j z)
    (hupper : ∀ j z, z ∈ Ω → v j z ≤ U z + η) :
    ∀ z ∈ Ω,
      0 ≤ (uscRegularization (⨆ j, fun y => (v j y : EReal)) z).toReal - U z ∧
      (uscRegularization (⨆ j, fun y => (v j y : EReal)) z).toReal - U z ≤ η := by
  let V := uscRegularization (⨆ j, fun y => (v j y : EReal))
  intro z hz
  have hlo : (U z : EReal) ≤ V z := by
    have heq := hUlimit hz
    change (U z : EReal) = _ at heq
    rw [heq]
    apply uscRegularization_le_of_eventually_le (upperSemicontinuous_uscRegularization _ z)
    filter_upwards [Ω.isOpen.mem_nhds hz] with y hy
    rw [iSup_apply]
    apply iSup_le
    intro j
    have hraw := le_uscRegularization (⨆ k, fun x => (v k x : EReal)) y
    rw [iSup_apply] at hraw
    exact (EReal.coe_le_coe_iff.mpr (hlower j y hy)).trans
      ((le_iSup (fun k => (v k y : EReal)) j).trans hraw)
  have hhi : V z ≤ (U z : EReal) + (η : EReal) := by
    have hmaj : UpperSemicontinuousAt (fun y => (U y : EReal) + (η : EReal)) z :=
      (hU.1 z hz).upperSemicontinuousAt.add' upperSemicontinuousAt_const
        (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot η))
          (Or.inr (EReal.coe_ne_top η)))
    apply uscRegularization_le_of_eventually_le hmaj
    filter_upwards [Ω.isOpen.mem_nhds hz] with y hy
    rw [iSup_apply, ← EReal.coe_add]
    exact iSup_le (fun j => EReal.coe_le_coe_iff.mpr (hupper j y hy))
  have hfin : ((V z).toReal : EReal) = V z := EReal.coe_toReal
    (ne_top_of_le_ne_top (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)
  have hloR : U z ≤ (V z).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [hfin]
    exact hlo
  have hhiR : (V z).toReal ≤ U z + η := by
    apply EReal.coe_le_coe_iff.mp
    rw [hfin, EReal.coe_add]
    exact hhi
  exact ⟨sub_nonneg.mpr hloR, by change (V z).toReal - U z ≤ η; linarith⟩

end SGPT.PSH.HermitianBalayage
