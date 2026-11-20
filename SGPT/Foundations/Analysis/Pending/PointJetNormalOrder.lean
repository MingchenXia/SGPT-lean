import SGPT.Foundations.Analysis.Pending.ActualFlatNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.PointJetNormalOrder

open FirstPass FirstPass.HolomorphicIdealSheaves
  HolomorphicGermReducednessBridge FixedGermNormalOrder ActualFlatNormalOrder

variable {n : ℕ} {i : Fin n} {F : ComplexModel n → ℂ}

/-- True whole-germ coordinate-power divisibility puts the ORIGINAL function
in the actual point-ideal power; no jet or ideal-order certificate is supplied. -/
theorem pointIdealPow_mem_of_coordinate_pow_dvd
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) {k : ℕ}
    (hdiv : (HolGerm.mk (fun z : ComplexModel n => z i)
      (eventually_differentiableAt_coordinate i)) ^ k ∣ HolGerm.mk F hF) :
    (IdealWeightPowers.idealPow (GermIdealOrder.pointIdeal n (0 : ComplexModel n)) k).mem 0 F := by
  obtain ⟨g, hg⟩ := hdiv
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk g
  have hfactor : F =ᶠ[𝓝 (0 : ComplexModel n)] fun z => z i ^ k * H z := by
    rw [← HolGerm.mk_pow, ← HolGerm.mk_mul] at hg
    exact HolGerm.mk_eq_mk_iff.mp hg
  have hcoord : HolomorphicAt n (fun z : ComplexModel n => z i) 0 :=
    (eventually_differentiableAt_coordinate i).mono fun _ hz => hz.mdifferentiableAt
  have hpoint : (GermIdealOrder.pointIdeal n (0 : ComplexModel n)).mem 0
      (fun z : ComplexModel n => z i) :=
    GermIdealOrder.mem_pointIdeal_of_apply_eq_zero hcoord (by simp)
  have hpower := OrderMultiplicativity.pow_mem_idealPow hpoint hcoord k
  have hHhol : HolomorphicAt n H (0 : ComplexModel n) :=
    hH.mono fun _ hz => hz.mdifferentiableAt
  have hproduct := GermIdealOrder.mul_mem_idealPow hHhol hpower
  apply OrderTaylor.mem_idealPow_congr hproduct
  filter_upwards [hfactor] with z hz
  exact (mul_comm (H z) (z i ^ k)).trans hz.symm

/-- Actual point-ideal powers force all lower ACTUAL iterated complex derivatives to vanish. -/
theorem iteratedFDeriv_eq_zero_of_coordinate_pow_dvd
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) {k a : ℕ}
    (hdiv : (HolGerm.mk (fun z : ComplexModel n => z i)
      (eventually_differentiableAt_coordinate i)) ^ k ∣ HolGerm.mk F hF) (ha : a < k) :
    iteratedFDeriv ℂ a F (0 : ComplexModel n) = 0 := by
  have hFhol : HolomorphicAt n F (0 : ComplexModel n) :=
    hF.mono fun _ hz => hz.mdifferentiableAt
  have hmember := pointIdealPow_mem_of_coordinate_pow_dvd hF hdiv
  have hjet := (OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv hFhol k).mp
    hmember a ha
  change iteratedFDeriv ℂ a F (0 : ComplexModel n) = 0 at hjet
  exact hjet

/-- A genuine nonzero point jet proves a finite upper bound for natural extended
coordinate multiplicity; neither finiteness nor minimality is an input. -/
theorem coordinate_emultiplicity_le_of_iteratedFDeriv_ne_zero
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (a : ℕ) (hjet : iteratedFDeriv ℂ a F (0 : ComplexModel n) ≠ 0) :
    emultiplicity (HolGerm.mk (fun z : ComplexModel n => z i)
      (eventually_differentiableAt_coordinate i)) (HolGerm.mk F hF) ≤ (a : ℕ∞) := by
  apply le_of_not_gt
  intro hlt
  have hbound : ((a + 1 : ℕ) : ℕ∞) ≤
      emultiplicity (HolGerm.mk (fun z : ComplexModel n => z i)
        (eventually_differentiableAt_coordinate i)) (HolGerm.mk F hF) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (ENat.natCast_add_one_le_iff.mpr hlt)
  have hdiv : (HolGerm.mk (fun z : ComplexModel n => z i)
      (eventually_differentiableAt_coordinate i)) ^ (a + 1) ∣ HolGerm.mk F hF :=
    pow_dvd_iff_le_emultiplicity.mpr hbound
  exact hjet (iteratedFDeriv_eq_zero_of_coordinate_pow_dvd hF hdiv (Nat.lt_succ_self a))

universe u

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {E : Set Y} {y : Y}

private theorem flat_function_near_holomorphic
    (Φ : DemaillyApproximantDivisorialLelong.DivisorFlattening (m := m) E y)
    {f : Y → ℂ} (hf : HolomorphicAt (m + 1) f y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (fun z => f (Φ.point z)) z := by
  have ht : Tendsto Φ.point (𝓝 0) (𝓝 y) := by
    simpa only [Φ.point_zero] using (Φ.mdifferentiableAt_point Φ.zero_mem_target).continuousAt.tendsto
  filter_upwards [ht.eventually hf, Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with z hzf hzT
  exact mdifferentiableAt_iff_differentiableAt.mp (hzf.comp z (Φ.mdifferentiableAt_point hzT))

/-- The original LOCAL function reader is bounded by an actual nonzero jet of
its literal flat function; no global holomorphy or chosen order identity. -/
theorem functionNormalOrder_le_of_flat_iteratedFDeriv_ne_zero
    (Φ : DemaillyApproximantDivisorialLelong.DivisorFlattening (m := m) E y)
    (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) (a : ℕ)
    (hjet : iteratedFDeriv ℂ a (fun z => f (Φ.point z)) (0 : ComplexModel (m + 1)) ≠ 0) :
    functionNormalOrder Φ f hf ≤ (a : ℕ∞) := by
  rw [functionNormalOrder_eq_flat Φ f hf]
  unfold flatFunctionGerm
  exact coordinate_emultiplicity_le_of_iteratedFDeriv_ne_zero
    (flat_function_near_holomorphic Φ hf) a hjet

end SGPT.Foundations.Analysis.Pending.PointJetNormalOrder
