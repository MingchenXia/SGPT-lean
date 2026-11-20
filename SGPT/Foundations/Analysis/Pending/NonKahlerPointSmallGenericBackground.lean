import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly
import SGPT.Foundations.Analysis.Pending.DivisorialDomination

set_option autoImplicit false

/-! # A genuine smaller big generic-zero background off the non-Kahler locus -/

open Set Filter
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonKahlerPointSmallGenericBackground

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The literal non-Kahler-locus definition, compact lower-form domination
and smooth representative correction supply a smaller big generic-zero class. -/
theorem exists_pos_big_sub_smul_generic_zero_of_not_mem_nonKahlerLocus
    (omega : KahlerBackground n M) (σ : ClosedRealOneOneForm n M) (ι : Y → M)
    (hx : ∃ y : Y, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative σ)) :
    ∃ δ : ℝ, 0 < δ ∧
      IsBigClass (RealBottChern.ofRepresentative (σ - δ • omega.form)) ∧
      (⨅ y : Y, lelongNumber (n := n) (thetaPshSupremum (σ - δ • omega.form).val) (ι y)) = 0 := by
  classical
  obtain ⟨y, hy⟩ := hx
  let : Nonempty M := ⟨ι y⟩
  rw [mem_nonKahlerLocus] at hy
  obtain ⟨T, hT⟩ := not_forall.mp hy
  have hT0 : lelongNumber (n := n) T.potential (ι y) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hT)
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omega.form)
  have hAinv : (0 : ℝ) < A⁻¹ := inv_pos.mpr hA
  have hdom : (T.lowerBound.form - A⁻¹ • omega.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hsemi hAinv.le
    have heq : A⁻¹ • (-omega.form + A • T.lowerBound.form) =
        T.lowerBound.form - A⁻¹ • omega.form := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [heq] at h
  have hTp : IsThetaPshPotential (T.representative - A⁻¹ • omega.form).val T.potential := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hdom
    rwa [sub_add_sub_cancel] at h
  have hrel : ClosedRealOneOneForm.BottChernRel (T.representative - A⁻¹ • omega.form)
      (σ - A⁻¹ • omega.form) := by
    have h := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
    simpa only [sub_eq_add_neg] using
      h.add (ClosedRealOneOneForm.BottChernRel.refl (-(A⁻¹ • omega.form)))
  obtain ⟨f, hf, heq⟩ := hrel
  let u : M → EReal := fun z => T.potential z - (f z : EReal)
  have hu : IsThetaPshPotential (σ - A⁻¹ • omega.form).val u :=
    PositiveClasses.thetaPshPotential_sub_smooth hf heq hTp
  let δ : ℝ := A⁻¹ / 2
  have hδ : 0 < δ := half_pos hAinv
  let β := σ - δ • omega.form
  have hform : σ - A⁻¹ • omega.form + δ • omega.form = β := by
    dsimp only [β, δ]
    module
  have hbig : IsBigClass (RealBottChern.ofRepresentative β) := by
    have h := PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
      omega (σ - A⁻¹ • omega.form) hu hδ
    rwa [hform] at h
  have huβ : IsThetaPshPotential β.val u := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le)
    rwa [hform] at h
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum β hbig
  obtain ⟨C, hC⟩ := huβ.exists_global_upper_bound
  have hmin := le_thetaPshSupremum (huβ.sub_const C) (sub_const_nonpositive_of_le hC)
  have hpoint : lelongNumber (n := n) (thetaPshSupremum β.val) (ι y) = 0 := by
    apply le_antisymm _ zero_le
    calc
      lelongNumber (n := n) (thetaPshSupremum β.val) (ι y) ≤
          lelongNumber (n := n) (fun z => u z - (C : EReal)) (ι y) :=
        KahlerCurrentMax.lelongNumber_le_of_eventually_le
          (Eventually.of_forall fun z => hmin z)
      _ ≤ lelongNumber (n := n) u (ι y) :=
        KahlerCurrentMax.lelongNumber_sub_le continuousAt_const
      _ ≤ lelongNumber (n := n) T.potential (ι y) :=
        KahlerCurrentMax.lelongNumber_sub_le
          (KahlerCurrentMax.continuous_of_chartSmooth hf).continuousAt
      _ = 0 := hT0
  refine ⟨δ, hδ, hbig, le_antisymm ?_ zero_le⟩
  calc (⨅ z : Y, lelongNumber (n := n) (thetaPshSupremum β.val) (ι z)) ≤
        lelongNumber (n := n) (thetaPshSupremum β.val) (ι y) := iInf_le _ y
    _ = 0 := hpoint

end
end SGPT.Foundations.Analysis.Pending.NonKahlerPointSmallGenericBackground
