import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
import Mathlib.Data.Finset.Fold
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! # Actual non-pluripolar cutoff integrals

An independently constructed finite minimum of scalar ramps vanishes on
the real truncation boundary. Actual common-strict-locus restriction then
identifies weighted ordinary BT and non-pluripolar integrals. Fixed-tuple
monotone exhaustion preserves possibly infinite nonnegative integrals.
The moving-family unbounded capacity mass liminf is a separate goal.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLocalNonPluripolarCutoffIntegrals

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  FirstPass.MixedNonPluripolar MixedNonPluripolar MixedMongeAmpere

noncomputable section

variable {n : ℕ}

/-- The finite minimum of coordinate ramps, with initial value one. -/
def cutoff (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  Finset.univ.fold min 1 (fun i => max (min (y i + (k : ℝ)) 1) 0)

/-- An actual bounded Lipschitz classifier that vanishes on a truncation boundary. -/
theorem cutoff_properties (k : ℕ) :
    LipschitzWith 1 (cutoff (n := n) k) ∧
    ∀ y : Fin n → ℝ, (0 ≤ cutoff k y ∧ cutoff k y ≤ 1) ∧
      ∀ i, y i ≤ -(k : ℝ) → cutoff k y = 0 := by
  classical
  have hLip (s : Finset (Fin n)) : LipschitzWith 1 (fun y : Fin n → ℝ =>
      s.fold min 1 (fun i => max (min (y i + (k : ℝ)) 1) 0)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (LipschitzWith.const (1 : ℝ)).weaken (zero_le_one : (0 : NNReal) ≤ 1)
    | @insert i s hi ih =>
        have hproj : LipschitzWith 1 (fun y : Fin n → ℝ => y i + (k : ℝ)) := by
          simpa using (LipschitzWith.eval i).add (LipschitzWith.const (k : ℝ))
        simpa only [Finset.fold_insert hi, max_self] using
          ((hproj.min_const 1).max_const 0).min ih
  refine ⟨hLip Finset.univ, fun y => ?_⟩
  have hzero : 0 ≤ cutoff k y := (Finset.le_fold_min 0).mpr
    ⟨zero_le_one, fun i _ => le_max_right _ _⟩
  have hone : cutoff k y ≤ 1 := (Finset.fold_min_le 1).mpr (Or.inl le_rfl)
  refine ⟨⟨hzero, hone⟩, fun i hi => le_antisymm ?_ hzero⟩
  apply (Finset.fold_min_le 0).mpr
  refine Or.inr ⟨i, Finset.mem_univ i, max_le ?_ le_rfl⟩
  exact (min_le_left _ _).trans (by linarith)

private theorem cutoff_weight_zero_compl
    {D : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (k : ℕ) (z : ComplexModel n) (hzD : z ∈ D)
    (hz : z ∉ commonStrictLocus D u k) :
    cutoff k (fun i => mixedTruncationReal u k i z) = 0 := by
  classical
  have hbad : ∃ i, u i z ≤ ((-(k : ℝ) : ℝ) : EReal) := by
    by_contra h
    apply hz
    refine ⟨hzD, fun i => ?_⟩
    exact lt_of_not_ge (fun hle => h ⟨i, hle⟩)
  obtain ⟨i, hi⟩ := hbad
  apply (cutoff_properties k).2 _ |>.2 i
  change (max (u i z) ((-(k : ℝ) : ℝ) : EReal)).toReal ≤ -(k : ℝ)
  rw [max_eq_right hi, EReal.toReal_coe]

/-- Actual Bochner definitions agree by strict-locus restriction. An arbitrary
test need not be integrable; the identity itself does not assert integrability. -/
theorem integral_cutoff_eq
    {D : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) D) (k : ℕ)
    {h : ComplexModel n → ℝ} (hzero : ∀ z, z ∉ D → h z = 0) :
    (∫ z, h z * cutoff k (fun i => mixedTruncationReal u k i z)
      ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal u k)
        (mixedTruncationReal_isLocallyBounded hu k)) =
    ∫ z, h z * cutoff k (fun i => mixedTruncationReal u k i z)
      ∂mixedTruncationLimitMeasure D u hu := by
  have hz : ∀ z, z ∉ commonStrictLocus D u k →
      h z * cutoff k (fun i => mixedTruncationReal u k i z) = 0 := by
    intro z hz
    by_cases hzD : z ∈ D
    · rw [cutoff_weight_zero_compl k z hzD hz, mul_zero]
    · rw [hzero z hzD, zero_mul]
  calc
    _ = ∫ z in commonStrictLocus D u k,
        h z * cutoff k (fun i => mixedTruncationReal u k i z)
        ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal u k)
          (mixedTruncationReal_isLocallyBounded hu k) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ = ∫ z in commonStrictLocus D u k,
        h z * cutoff k (fun i => mixedTruncationReal u k i z)
        ∂mixedTruncationLimitMeasure D u hu := by
      rw [mixedTruncationLimitMeasure_restrict_commonStrictLocus hu k]
      rfl
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hz

/-- Actual nonnegative cutoff integrals agree and are bounded by the genuine
non-pluripolar test integral, even when this upper bound is infinite. -/
theorem lintegral_cutoff_eq_le
    {D : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) D) (k : ℕ)
    {h : ComplexModel n → ℝ≥0∞} (hzero : ∀ z, z ∉ D → h z = 0) :
    (∫⁻ z, h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
      ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal u k)
        (mixedTruncationReal_isLocallyBounded hu k)) =
      (∫⁻ z, h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
        ∂mixedTruncationLimitMeasure D u hu) ∧
    (∫⁻ z, h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
      ∂mixedTruncationLimitMeasure D u hu) ≤ ∫⁻ z, h z ∂mixedTruncationLimitMeasure D u hu := by
  have hs : Function.support (fun z => h z *
      ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))) ⊆
      commonStrictLocus D u k := by
    intro z hz
    by_contra hbad
    apply hz
    change h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z)) = 0
    by_cases hzD : z ∈ D
    · rw [cutoff_weight_zero_compl k z hzD hbad, ENNReal.ofReal_zero, mul_zero]
    · rw [hzero z hzD, zero_mul]
  constructor
  · calc
      _ = ∫⁻ z in commonStrictLocus D u k,
          h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
          ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal u k)
            (mixedTruncationReal_isLocallyBounded hu k) :=
        (setLIntegral_eq_of_support_subset hs).symm
      _ = ∫⁻ z in commonStrictLocus D u k,
          h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
          ∂mixedTruncationLimitMeasure D u hu := by
        rw [mixedTruncationLimitMeasure_restrict_commonStrictLocus hu k]
        rfl
      _ = _ := setLIntegral_eq_of_support_subset hs
  · apply lintegral_mono
    intro z
    have hone : ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z)) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal ((cutoff_properties k).2 _).1.2
    calc
      _ ≤ h z * 1 := mul_le_mul_right hone (h z)
      _ = h z := mul_one _

private theorem cutoff_mono (y : Fin n → ℝ) : Monotone (fun k : ℕ => cutoff k y) := by
  intro k l hkl
  apply (Finset.le_fold_min (cutoff k y)).mpr
  refine ⟨((cutoff_properties k).2 y).1.2, fun i _ => ?_⟩
  have hi : cutoff k y ≤ max (min (y i + (k : ℝ)) 1) 0 :=
    (Finset.fold_min_le _).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)
  exact hi.trans (max_le_max (min_le_min
    (add_le_add le_rfl (Nat.cast_le.mpr hkl)) le_rfl) le_rfl)

private theorem cutoff_eventually_one (y : Fin n → ℝ) :
    ∀ᶠ k : ℕ in atTop, cutoff k y = 1 := by
  classical
  choose N hN using fun i : Fin n => exists_nat_gt (1 - y i)
  refine eventually_atTop.mpr ⟨Finset.univ.sup N, fun k hk => ?_⟩
  apply le_antisymm ((cutoff_properties k).2 y).1.2
  apply (Finset.le_fold_min 1).mpr
  refine ⟨le_rfl, fun i _ => ?_⟩
  have hi : N i ≤ k := (Finset.le_sup (Finset.mem_univ i)).trans hk
  have hir : (N i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hi
  have hh : 1 ≤ y i + (k : ℝ) := by linarith [hN i]
  rw [min_eq_right hh, max_eq_left zero_le_one]

private theorem cutoff_weight_eq_finite
    {D : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) D) {z : ComplexModel n} (hz : z ∈ D)
    (hfinite : ∀ i, u i z ≠ ⊥) (k : ℕ) :
    cutoff k (fun i => mixedTruncationReal u k i z) =
      cutoff k (fun i => (u i z).toReal) := by
  classical
  apply Finset.fold_congr
  intro i _
  have hval : ((u i z).toReal : EReal) = u i z :=
    EReal.coe_toReal ((hu i z hz).ne_top) (hfinite i)
  by_cases hi : u i z ≤ ((-(k : ℝ) : ℝ) : EReal)
  · have hreal : (u i z).toReal ≤ -(k : ℝ) := by
      apply EReal.coe_le_coe_iff.mp
      rwa [hval]
    have hlow : min ((u i z).toReal + (k : ℝ)) 1 ≤ 0 :=
      (min_le_left _ _).trans (by linarith)
    simp only [mixedTruncationReal, truncationReal, truncation, max_eq_right hi,
      EReal.toReal_coe, neg_add_cancel, min_eq_left zero_le_one, max_self,
      max_eq_right hlow]
  · simp only [mixedTruncationReal, truncationReal, truncation,
      max_eq_left (le_of_not_ge hi)]

/-- Actual nonnegative cutoff integrals monotonically exhaust the constructed
non-pluripolar test integral. No finite integral or compact mass is assumed. -/
theorem tendsto_lintegral_cutoff
    {D : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) D)
    {h : ComplexModel n → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ z, z ∉ D → h z = 0) :
    Tendsto (fun k : ℕ => ∫⁻ z,
      h z * ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
      ∂mixedTruncationLimitMeasure D u hu) atTop
      (𝓝 (∫⁻ z, h z ∂mixedTruncationLimitMeasure D u hu)) := by
  let f (k : ℕ) (z : ComplexModel n) := h z *
    ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal u k i z))
  have hmeas (k : ℕ) : Measurable (f k) := by
    let t (i : Fin n) : ComplexModel n → ℝ :=
      (D : Set (ComplexModel n)).indicator (mixedTruncationReal u k i)
    have ht (i : Fin n) : Measurable (t i) :=
      LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn
        (mixedTruncationReal_isLocallyBounded hu k i)
    have hclass : Measurable (fun z => cutoff k (fun i => t i z)) :=
      (cutoff_properties k).1.continuous.measurable.comp
        (measurable_pi_lambda _ ht)
    have hrep : f k = fun z => h z * ENNReal.ofReal (cutoff k (fun i => t i z)) := by
      funext z
      by_cases hz : z ∈ D
      · simp only [f, t, indicator_of_mem hz]
      · simp only [f, hzero z hz, zero_mul]
    rw [hrep]
    exact hh.mul hclass.ennreal_ofReal
  have hD : ∀ᵐ z ∂mixedTruncationLimitMeasure D u hu, z ∈ D :=
    ae_iff.mpr (mixedTruncationLimitMeasure_compl hu)
  have hp : ∀ᵐ z ∂mixedTruncationLimitMeasure D u hu, z ∉ componentPoleSet u := by
    apply ae_iff.mpr
    simpa using mixedTruncationLimitMeasure_poleSet hu
  have hAE : ∀ᵐ z ∂mixedTruncationLimitMeasure D u hu,
      z ∈ D ∧ ∀ i, u i z ≠ ⊥ := by
    filter_upwards [hD, hp] with z hz hzp
    exact ⟨hz, fun i hi => hzp ⟨i, hi⟩⟩
  apply lintegral_tendsto_of_tendsto_of_monotone (fun k => (hmeas k).aemeasurable)
  · filter_upwards [hAE] with z hz
    intro k l hkl
    apply mul_le_mul_right (a := h z)
    apply ENNReal.ofReal_le_ofReal
    rw [cutoff_weight_eq_finite hu hz.1 hz.2 k, cutoff_weight_eq_finite hu hz.1 hz.2 l]
    exact cutoff_mono _ hkl
  · filter_upwards [hAE] with z hz
    have hconst : (fun k : ℕ => f k z) =ᶠ[atTop] (fun _ => h z) :=
      (cutoff_eventually_one (fun i => (u i z).toReal)).mono fun k hk => by
        simp only [f, cutoff_weight_eq_finite hu hz.1 hz.2 k, hk,
          ENNReal.ofReal_one, mul_one]
    exact tendsto_const_nhds.congr' hconst.symm

end
end SGPT.Foundations.Analysis.Pending.ActualLocalNonPluripolarCutoffIntegrals
