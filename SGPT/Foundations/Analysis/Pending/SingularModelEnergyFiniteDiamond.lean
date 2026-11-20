import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondLower

set_option autoImplicit false

/-!
# Actual finite-type energy diamond inequality for singular references

Xia SGPT PDF0137, Corollary 3.1.7, equation (3.57). Genuine actual upper
and lower path estimates are summed over a uniform partition. Their
actual gap sums telescope to a finite endpoint correction tending to zero.
There is no boundedness, path differentiability, or target diamond premise.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyFiniteDiamond

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  SingularModelEnergyDiamondPaths SingularModelEnergyDiamondUpper
  SingularModelEnergyDiamondLower

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [Nonempty M]

/-- Same-type endpoints produce a genuine actual same-type rooftop. -/
theorem relativeEInfinity_rooftop {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : RelativeEInfinity θ φ u)
    (hv : RelativeEInfinity θ φ v) : RelativeEInfinity θ φ (rooftop θ u v) := by
  have h := relativeEInfinity_lowerPath hφ hu hv (t := 0) (by constructor <;> norm_num)
  simpa only [lowerPath, path_zero, rooftop] using h

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual finite energy diamond inequality on a genuine singular
same-type class; the actual maximum and rooftop witnesses are produced. -/
theorem relativeEnergyOfMinimalType_add_le_max_add_rooftop (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : RelativeEInfinity θ φ u)
    (hv : RelativeEInfinity θ φ v) :
    relativeEnergyOfMinimalType θ φ u hφ hu.1 + relativeEnergyOfMinimalType θ φ v hφ hv.1 ≤
      relativeEnergyOfMinimalType θ φ (fun x => max (u x) (v x)) hφ
        (IsThetaPshPotential.max hu.1 hv.1) +
      relativeEnergyOfMinimalType θ φ (rooftop θ u v) hφ
        (relativeEInfinity_rooftop hφ hu hv).1 := by
  let hm := IsThetaPshPotential.max hu.1 hv.1
  let hw := (relativeEInfinity_rooftop hφ hu hv).1
  let Em := relativeEnergyOfMinimalType θ φ (fun x => max (u x) (v x)) hφ hm
  let Ew := relativeEnergyOfMinimalType θ φ (rooftop θ u v) hφ hw
  let Eu := relativeEnergyOfMinimalType θ φ u hφ hu.1
  let Ev := relativeEnergyOfMinimalType θ φ v hφ hv.1
  have eA0 : RelativeEnergyDiamond.energyOf θ φ hφ (upperPath u v 0) = Eu := by
    have h : upperPath u v 0 = u := by funext x; simp [upperPath, path_zero]
    rw [h, RelativeEnergyDiamond.energyOf_eq hu.1]
  have eA1 : RelativeEnergyDiamond.energyOf θ φ hφ (upperPath u v 1) = Em := by
    have h : upperPath u v 1 = fun x => max (u x) (v x) := by
      funext x
      simp [upperPath, path_one]
    rw [h, RelativeEnergyDiamond.energyOf_eq hm]
  have eB0 : RelativeEnergyDiamond.energyOf θ φ hφ (lowerPath θ u v 0) = Ew := by
    have h : lowerPath θ u v 0 = rooftop θ u v := by simp only [lowerPath, path_zero, rooftop]
    rw [h, RelativeEnergyDiamond.energyOf_eq hw]
  have eB1 : RelativeEnergyDiamond.energyOf θ φ hφ (lowerPath θ u v 1) = Ev := by
    have h : lowerPath θ u v 1 = v := by
      simp only [lowerPath, path_one, min_self]
      exact RelativeEnergyDiamond.rooftopEnvelope_self hv.1
    rw [h, RelativeEnergyDiamond.energyOf_eq hv.1]
  have key : ∀ N : ℕ, 0 < N →
      (gap θ u v 1 - gap θ u v 0) / N ≤ (Em - Eu) - (Ev - Ew) := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let a := fun i : ℕ => RelativeEnergyDiamond.energyOf θ φ hφ (upperPath u v ((i : ℝ) / N))
    let b := fun i : ℕ => RelativeEnergyDiamond.energyOf θ φ hφ (lowerPath θ u v ((i : ℝ) / N))
    let c := fun i : ℕ => gap θ u v ((i : ℝ) / N)
    have h0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
    have h1 : ((N : ℕ) : ℝ) / N = 1 := div_self hNr.ne'
    have ha : a N - a 0 = Em - Eu := by simp only [a, h0, h1, eA0, eA1]
    have hb : b N - b 0 = Ev - Ew := by simp only [b, h0, h1, eB0, eB1]
    have hc : c N - c 0 = gap θ u v 1 - gap θ u v 0 := by simp only [c, h0, h1]
    have hstep : ∀ i ∈ Finset.range N,
        ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by
      intro i _
      push_cast
      ring
    have hI : ∀ i ∈ Finset.range N,
        0 ≤ (i : ℝ) / N ∧ (i : ℝ) / N ≤ ((i + 1 : ℕ) : ℝ) / N ∧
        0 < ((i + 1 : ℕ) : ℝ) / N ∧ ((i + 1 : ℕ) : ℝ) / N ≤ 1 := by
      intro i hi
      have hiN : i + 1 ≤ N := Finset.mem_range.mp hi
      refine ⟨by positivity, div_le_div_of_nonneg_right (by push_cast; linarith) hNr.le,
        by positivity, (div_le_one hNr).mpr ?_⟩
      exact_mod_cast hiN
    have stepA : ∀ i ∈ Finset.range N, 1 / (N : ℝ) * c (i + 1) ≤ a (i + 1) - a i := by
      intro i hi
      obtain ⟨hs, hst, ht0, ht1⟩ := hI i hi
      have h := sub_mul_gap_le_energyOf_upperPath omega θ hφ hu hv hs hst ht0 ht1
      rwa [hstep i hi] at h
    have stepB : ∀ i ∈ Finset.range N, b (i + 1) - b i ≤ 1 / (N : ℝ) * c i := by
      intro i hi
      obtain ⟨hs, hst, _, ht1⟩ := hI i hi
      have h := energyOf_lowerPath_sub_le omega θ hφ hu hv hs hst ht1
      rwa [hstep i hi] at h
    have hsa := Finset.sum_range_sub a N
    have hsb := Finset.sum_range_sub b N
    have hsc := Finset.sum_range_sub c N
    have hA := Finset.sum_le_sum stepA
    have hB := Finset.sum_le_sum stepB
    have hdiff : ∑ i ∈ Finset.range N, 1 / (N : ℝ) * c (i + 1) -
        ∑ i ∈ Finset.range N, 1 / (N : ℝ) * c i = 1 / N * (c N - c 0) := by
      rw [← Finset.sum_sub_distrib, ← hsc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [div_eq_mul_one_div, mul_comm, ← hc, ← hdiff, ← ha, ← hb, ← hsa, ← hsb]
    linarith
  have hlim : Tendsto (fun N : ℕ => (gap θ u v 1 - gap θ u v 0) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h0 : 0 ≤ (Em - Eu) - (Ev - Ew) :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => key N hN⟩)
  linarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyFiniteDiamond
