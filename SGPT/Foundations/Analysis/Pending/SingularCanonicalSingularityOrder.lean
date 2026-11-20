import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay

set_option autoImplicit false

/-! # Actual additive singularity comparison and canonical-ray order -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrder

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SingularMinimalCanonicalRay SingularCanonicalCutoffConstantInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual finite normalization, genuine cutoff Perron order and actual constant invariance internally transport global additive singularity order to the complete canonical-ray functions. -/
theorem canonicalRay_le_of_moreSingularOn (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : MoreSingularOn u v univ) :
    canonicalRay θ u ≤ canonicalRay θ v := by
  obtain ⟨D, hD⟩ := huv
  obtain ⟨C, hC⟩ := hv.exists_global_upper_bound
  have hv0 : (fun x => v x - (C : EReal)) ≤ 0 := sub_const_nonpositive_of_le hC
  have hle : (fun x => u x - ((C + D : ℝ) : EReal)) ≤
      fun x => v x - (C : EReal) := by
    intro x
    calc
      u x - ((C + D : ℝ) : EReal) ≤
          (v x + (D : EReal)) - ((C + D : ℝ) : EReal) := by
        exact add_le_add (hD x (mem_univ x)) le_rfl
      _ = v x - (C : EReal) := by
        simp only [sub_eq_add_neg, ← EReal.coe_neg]
        rw [add_assoc, ← EReal.coe_add]
        exact congrArg (fun r : ℝ => v x + (r : EReal)) (by ring)
  have hu0 : (fun x => u x - ((C + D : ℝ) : EReal)) ≤ 0 := hle.trans hv0
  rw [← canonicalRay_sub_const_eq θ hu (C + D),
    ← canonicalRay_sub_const_eq θ hv C,
    canonicalRay_eq_cutoffSlice_of_nonpositive omega θ hbig (hu.sub_const (C + D)) hu0,
    canonicalRay_eq_cutoffSlice_of_nonpositive omega θ hbig (hv.sub_const C) hv0]
  exact fun s => cutoffSlice_mono_input hle s

/-- Two genuine additive singularity comparisons internally produce equality of the complete actual canonical rays, without any full-mass or finite-energy input condition. -/
theorem canonicalRay_eq_of_sameSingularityTypeOn (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : SameSingularityTypeOn u v univ) :
    canonicalRay θ u = canonicalRay θ v :=
  le_antisymm (canonicalRay_le_of_moreSingularOn omega θ hbig hu hv huv.1)
    (canonicalRay_le_of_moreSingularOn omega θ hbig hv hu huv.2)

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrder
