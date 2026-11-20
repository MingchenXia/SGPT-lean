import SGPT.PSH.CanonicalAnalyticGrowthGerm
import SGPT.Foundations.Analysis.Pending.MonicRelationWeightedNormBound

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SGPT.PSH

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

noncomputable section

variable {n N d : ℕ}

/-- Actual monic coefficient membership forces membership in the same canonical
growth germ ideal. This fixed-centre result makes no coherence assumption. -/
theorem mem_canonicalGrowthGermIdeal_of_monic_relation
    (G : Fin N → ComplexModel n → ℂ)
    (hG : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G j) z)
    (hd : 0 < d) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (b : Fin d → HolGerm (ComplexModel n))
    (hb : ∀ i, b i ∈ canonicalGrowthGermIdeal G ^ (d - i.val))
    (hrel : HolGerm.mk F hF ^ d + ∑ i, b i * HolGerm.mk F hF ^ i.val = 0) :
    HolGerm.mk F hF ∈ canonicalGrowthGermIdeal G := by
  classical
  obtain ⟨m, H, hH, hspan, hmem, _⟩ :=
    exists_finite_canonical_growth_germ_presentation G hG
  have hHmem (j : Fin m) : HolGerm.mk (H j) (hH j) ∈ canonicalGrowthGermIdeal G :=
    hspan ▸ Ideal.subset_span ⟨j, rfl⟩
  choose A hA hboundH using fun j => (hmem (H j) (hH j)).mp (hHmem j)
  choose B hB heqB using fun i => HolGerm.exists_eq_mk (b i)
  have hbounds : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 0,
      ‖B i z‖ ≤ C * (∑ j, ‖H j z‖) ^ (d - i.val) := by
    intro i
    apply HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow H hH
      (B i) (hB i) (d - i.val)
    simpa only [hspan, ← heqB i] using hb i
  choose C hC hbound using hbounds
  let Ctotal : ℝ := ∑ i, C i
  let Atotal : ℝ := ∑ j, A j
  have hCtotal : 0 ≤ Ctotal := Finset.sum_nonneg fun i _ => hC i
  have hAtotal : 0 ≤ Atotal := Finset.sum_nonneg fun j _ => hA j
  have hCsum (i : Fin d) : C i ≤ Ctotal :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  let P : ComplexModel n → ℂ := fun z => F z ^ d + ∑ i, B i z * F z ^ i.val
  have hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ P z :=
    eventually_differentiableAt_add (eventually_differentiableAt_pow hF d)
      (eventually_differentiableAt_sum Finset.univ fun i =>
        eventually_differentiableAt_mul (hB i) (eventually_differentiableAt_pow hF i.val))
  have hmk : HolGerm.mk P hP = 0 := by
    calc
      HolGerm.mk P hP = HolGerm.mk F hF ^ d +
          ∑ i, HolGerm.mk (B i) (hB i) * HolGerm.mk F hF ^ i.val := by
        rw [show HolGerm.mk P hP =
            HolGerm.mk (fun z => F z ^ d) (eventually_differentiableAt_pow hF d) +
              HolGerm.mk (fun z => ∑ i, B i z * F z ^ i.val)
                (eventually_differentiableAt_sum Finset.univ fun i =>
                  eventually_differentiableAt_mul (hB i)
                    (eventually_differentiableAt_pow hF i.val)) from
          HolGerm.mk_add _ _ _ _]
        rw [HolGerm.mk_pow F hF d]
        congr 1
        calc
          HolGerm.mk (fun z => ∑ i, B i z * F z ^ i.val) _ =
              ∑ i, HolGerm.mk (fun z => B i z * F z ^ i.val)
                (eventually_differentiableAt_mul (hB i)
                  (eventually_differentiableAt_pow hF i.val)) := by
            simpa using HolGerm.mk_sum Finset.univ (fun i z => B i z * F z ^ i.val)
              (fun i => eventually_differentiableAt_mul (hB i)
                (eventually_differentiableAt_pow hF i.val))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [HolGerm.mk_mul _ _ (hB i) (eventually_differentiableAt_pow hF i.val),
              HolGerm.mk_pow F hF i.val]
      _ = 0 := by simpa only [← heqB] using hrel
  have hrelPoint : ∀ᶠ z in 𝓝 0, P z = 0 :=
    HolGerm.mk_eq_mk_iff.mp (hmk.trans HolGerm.mk_zero.symm)
  apply (hmem F hF).mpr
  refine ⟨((d : ℝ) * Ctotal + 1) * Atotal,
    mul_nonneg (by positivity) hAtotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound,
    Filter.eventually_all.mpr hboundH, hrelPoint] with z hzC hzH hzP
  have hcoeff (i : Fin d) :
      ‖B i z‖ ≤ Ctotal * (∑ j, ‖H j z‖) ^ (d - i.val) :=
    (hzC i).trans (mul_le_mul_of_nonneg_right (hCsum i) (by positivity))
  have hroot : ‖F z‖ ≤ ((d : ℝ) * Ctotal + 1) * ∑ j, ‖H j z‖ :=
    MonicRelationWeightedNormBound.norm_le_of_monic_relation hd (F z) (fun i => B i z)
      (Finset.sum_nonneg fun j _ => norm_nonneg (H j z)) hCtotal hcoeff hzP
  calc
    ‖F z‖ ≤ ((d : ℝ) * Ctotal + 1) * ∑ j, ‖H j z‖ := hroot
    _ ≤ ((d : ℝ) * Ctotal + 1) * ∑ j, A j * ∑ k, ‖G k z‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hzH j) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end SGPT.PSH
