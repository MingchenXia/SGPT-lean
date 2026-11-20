import SGPT.Foundations.Analysis.Pending.LocalSmoothScalarCurrents
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
import SGPT.Foundations.Analysis.Pending.MongeAmpere
import SGPT.Foundations.Analysis.FirstPass.PshRadialRegularization

set_option autoImplicit false

/-! # A nonsmooth bounded PSH reader gives the actual multiplication current -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualBoundedScalarCurrentIdentity
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorLocality LocalBedfordTaylorDecreasing
  LocalBedfordTaylorContinuity
  ScalarLeviPositiveCurrent LocalSmoothScalarCurrents

variable {n : ℕ} {Ω V : Opens (ComplexModel n)}

/-- Natural locally bounded PSH data internally supply the nonsmooth full
unit-current identity on every relatively compact open subdomain. -/
theorem scalarTopCurrent_regularDistribution_eq_mulBorel_of_locallyBoundedPsh
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hV : RelativelyCompactIn V Ω) :
    let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
    scalarTopCurrent (regularDistribution volume u
      (locallyIntegrableOn_of_plurisubharmonicOn_real huV.1)) =
      mulBorel (oneCurrent V) ((V : Set (ComplexModel n)).indicator u) := by
  classical
  let huV := isLocallyBoundedPshOn_mono hu (subset_closure.trans hV.2)
  let huL := locallyIntegrableOn_of_plurisubharmonicOn_real huV.1
  obtain ⟨f, hf⟩ := Pending.MongeAmpere.exists_decreasingApproximation hu hV
  let hfV := fun j => isLocallyBoundedPshOn_of_isSmoothPshOn (hf.1 j)
  let hfL : ∀ j, LocallyIntegrableOn (f j) V volume :=
    fun j => (hf.1 j).1.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hweak : WeakTendsto
      (fun j => mulBorel (oneCurrent V) ((V : Set (ComplexModel n)).indicator (f j)))
      (mulBorel (oneCurrent V) ((V : Set (ComplexModel n)).indicator u)) := by
    have h := weakTendsto_mulBorel_btProduct_of_antitone 0 n (oneCurrent V)
      isPositive_oneCurrent (isClosedAny_oneCurrent (n := n))
      (fun j (_ : Fin 1) => f j) (fun _ : Fin 1 => u)
      (fun j _ => hfV j) (fun _ => huV)
      (fun _ x hx => hf.2.1 x hx) (fun _ x hx => hf.2.2 x hx)
    exact h
  have hint : ∀ φ : 𝓓(V, ℝ),
      Tendsto (fun j => ∫ x, φ x * f j x ∂volume) atTop
        (𝓝 (∫ x, φ x * u x ∂volume)) := by
    intro φ
    obtain ⟨Cu, hCu, hboundu⟩ := huV.exists_compact_abs_bound φ.hasCompactSupport φ.tsupport_subset
    obtain ⟨Cf, hCf, hboundf⟩ := (hfV 0).exists_compact_abs_bound φ.hasCompactSupport φ.tsupport_subset
    let C := Cu + Cf
    have hbound : ∀ j, ∀ x ∈ tsupport φ, |f j x| ≤ C := by
      intro j x hx
      have hlow := (hf.2.1 x (φ.tsupport_subset hx)).le_of_tendsto
        (hf.2.2 x (φ.tsupport_subset hx)) j
      have hhigh := hf.2.1 x (φ.tsupport_subset hx) (Nat.zero_le j)
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (u x), hboundu x hx]
      · linarith [le_abs_self (f 0 x), hboundf x hx]
    have hm : ∀ j, Measurable (fun x => φ x * f j x) := by
      intro j
      have h := φ.continuous.measurable.mul (measurable_indicator_of_isLocallyBoundedPshOn (hfV j))
      convert h using 1
      funext x
      simp only [Pi.mul_apply]
      by_cases hx : x ∈ V
      · rw [Set.indicator_of_mem hx]
      · simp only [testFunction_eq_zero_of_notMem φ hx, zero_mul]
    have hg : Integrable (fun x => ‖φ x‖ * C) volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const C
    refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖ * C)
      (fun j => (hm j).aestronglyMeasurable) hg (fun j => ?_) ?_
    · filter_upwards with x
      by_cases hx : x ∈ tsupport φ
      · rw [norm_mul, Real.norm_eq_abs (f j x)]
        exact mul_le_mul_of_nonneg_left (hbound j x hx) (norm_nonneg _)
      · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero, le_refl]
    · filter_upwards with x
      by_cases hx : φ x = 0
      · simpa only [hx, zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · exact (hf.2.2 x (φ.tsupport_subset (subset_tsupport φ hx))).const_mul (φ x)
  ext γ φ
  have hscalar : Tendsto (fun j => scalarTopCurrent (regularDistribution volume (f j) (hfL j)) γ φ)
      atTop (𝓝 (scalarTopCurrent (regularDistribution volume u huL) γ φ)) := by
    simp only [scalarTopCurrent_apply, regularDistribution_apply]
    exact (hint φ).const_mul _
  have heq : ∀ j, scalarTopCurrent (regularDistribution volume (f j) (hfL j)) =
      mulBorel (oneCurrent V) ((V : Set (ComplexModel n)).indicator (f j)) :=
    fun j => scalarTopCurrent_regularDistribution_eq_mulBorel_of_contDiffOn (hf.1 j).1
  simp only [heq] at hscalar
  exact tendsto_nhds_unique hscalar (hweak γ φ)

end SGPT.Foundations.Analysis.Pending.ActualBoundedScalarCurrentIdentity
