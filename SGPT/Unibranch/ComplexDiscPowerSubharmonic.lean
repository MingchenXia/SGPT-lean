import SGPT.Unibranch.ComplexDiscPower
import SGPT.Unibranch.ComplexPowerSubharmonic

/-! Genuine scalar finite-cover descent for the SAME original disk reader.
Blueprint: complex-disc-power-subharmonic.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set CategoryTheory AlgebraicGeometry Metric
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Actual original USC transports to the literal disk reader on its real
parameter domain. No reader regularity certificate is input. -/
theorem discPullback_upperSemicontinuousOn {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ) :
    UpperSemicontinuousOn (discPullback f φ) (ball (0 : ℂ) 1) := by
  let D : ball (0 : ℂ) 1 → (univ : Set unitDiscOpens) := fun z =>
    ⟨⟨discCoordinate z.val,discCoordinate_mem_unitDiscOpens z.property⟩,trivial⟩
  have hD : Continuous D := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact discCoordinate.continuous.comp continuous_subtype_val
  have hu : UpperSemicontinuous (fun z : ball (0 : ℂ) 1 => φ (f.hom.left.base (D z))) :=
    UpperSemicontinuous.comp hφ (f.hom.left.base.hom.continuous.comp hD)
  have heq : (fun z : ball (0 : ℂ) 1 => φ (f.hom.left.base (D z))) =
      fun z : ball (0 : ℂ) 1 => discPullback f φ z.val := by
    funext z
    unfold discPullback modelPullback
    rw [dif_pos (discCoordinate_mem_unitDiscOpens z.property)]
    rfl
  apply upperSemicontinuousOn_iff_restrict.mp
  simpa only [heq,domRestrict_eq,Function.comp_def] using hu

/-- Genuine subharmonicity descends from the SAME actual finite-power
composed original disk. Original target USC supplies all reader regularity. -/
theorem discPullback_subharmonic_of_comp_power {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ)
    (k : ℕ) (hk : 0 < k)
    (hcomp : SGPT.PSH.SubharmonicOn (discPullback (discPowerMorphism k hk ≫ f) φ)
      (ball (0 : ℂ) 1)) :
    SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1) := by
  have hdisc : SGPT.Foundations.Analysis.DiscPshOn
      (fun z : ℂ => discPullback f φ (z^k)) (ball 0 1) :=
    hcomp.discPshOn.congr (fun z hz => discPullback_comp_power f φ k hk hz)
  have hnon : ∃ z ∈ ball (0 : ℂ) 1,discPullback f φ (z^k) ≠ ⊥ := by
    obtain ⟨z,hz,hfin⟩ := hcomp.nontrivial
    exact ⟨z,hz,(discPullback_comp_power f φ k hk hz) ▸ hfin⟩
  have hpull := SGPT.PSH.subharmonicOn_of_disc hdisc hnon
  have h := RamifiedPower.subharmonicOn_of_comp_pow k hk zero_lt_one
    (by simpa only [one_pow] using discPullback_upperSemicontinuousOn f hφ) hpull
  simpa only [one_pow] using h


/-- The actual GERM version needed after shrinking a genuinely lifted disk.
No whole-unit-disk lift or target subharmonicity is assumed. -/
theorem discPullback_subharmonic_near_zero_of_comp_power {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ)
    (k : ℕ) (hk : 0 < k) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hcomp : SGPT.PSH.SubharmonicOn (discPullback (discPowerMorphism k hk ≫ f) φ)
      (ball (0 : ℂ) R)) :
    SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) (R^k)) := by
  have heq : EqOn (discPullback (discPowerMorphism k hk ≫ f) φ)
      (fun z : ℂ => discPullback f φ (z^k)) (ball 0 R) :=
    fun z hz => discPullback_comp_power f φ k hk (ball_subset_ball hR1 hz)
  have hdisc := hcomp.discPshOn.congr heq
  have hnon : ∃ z ∈ ball (0 : ℂ) R,discPullback f φ (z^k) ≠ ⊥ := by
    obtain ⟨z,hz,hfin⟩ := hcomp.nontrivial
    refine ⟨z,hz,?_⟩
    have he := heq hz
    change discPullback (discPowerMorphism k hk ≫ f) φ z = discPullback f φ (z^k) at he
    rw [← he]
    exact hfin
  have hpull := SGPT.PSH.subharmonicOn_of_disc hdisc hnon
  have hRk : R^k ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hR.le hR1 k
  exact RamifiedPower.subharmonicOn_of_comp_pow k hk hR
    ((discPullback_upperSemicontinuousOn f hφ).mono (ball_subset_ball hRk)) hpull

end SGPT.Unibranch.SourceReducedComplexSpace
