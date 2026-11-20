import SGPT.AlmostSemigroup.ConeIndependence
import SGPT.AlmostSemigroup.OkounkovComparison
import SGPT.GAGA.OkoCloseBig

/-! Genuine common ambient cones and cross-cone carrier monotonicity.
Blueprint: common-cone-monotonicity.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.AlmostSemigroup.CommonConeMonotonicity
open Set Filter Class OkounkovExtension

/-- A true common admissible cone is manufactured from the two actual compact slices. -/
theorem exists_common_admissibleCone {n : ℕ} (C D : AdmissibleCone n) :
    ∃ E : AdmissibleCone n,
      (C.cone : Set ((Fin n → ℝ) × ℝ)) ⊆ E.cone ∧
      (D.cone : Set ((Fin n → ℝ) × ℝ)) ⊆ E.cone := by
  have hCc := isCompact_heightOne C.cone C.closed C.nonnegativeHeight C.zeroHeight
  have hDc := isCompact_heightOne D.cone D.closed D.nonnegativeHeight D.zeroHeight
  obtain ⟨RC,hRC⟩ := hCc.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨RD,hRD⟩ := hDc.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max 0 (max RC RD)
  let K := Metric.closedBall (0 : Fin n → ℝ) R
  have hR : 0 ≤ R := le_max_left _ _
  have hKc : IsCompact K := isCompact_closedBall 0 R
  have hKv : Convex ℝ K := convex_closedBall 0 R
  let E := SGPT.GAGA.OkoClose.coneOver K hKc hKv
  have hzero : (0 : Fin n → ℝ) ∈ K := by
    change dist (0 : Fin n → ℝ) 0 ≤ R
    simpa only [dist_self] using hR
  have hC : heightOne C.cone ⊆ K := by
    intro x hx
    change dist x 0 ≤ R
    rw [dist_zero_right]
    exact (hRC x hx).trans ((le_max_left RC RD).trans (le_max_right 0 _))
  have hD : heightOne D.cone ⊆ K := by
    intro x hx
    change dist x 0 ≤ R
    rw [dist_zero_right]
    exact (hRD x hx).trans ((le_max_right RC RD).trans (le_max_right 0 _))
  have hin (A : AdmissibleCone n) (hA : heightOne A.cone ⊆ K) :
      (A.cone : Set ((Fin n → ℝ) × ℝ)) ⊆ E.cone := by
    intro z hz
    have ht := A.nonnegativeHeight z hz
    change 0 ≤ z.2 ∧ ∃ x ∈ K, z.1 = z.2 • x
    refine ⟨ht,?_⟩
    by_cases h0 : z.2=0
    · have hx : z.1=0 := by
        apply A.zeroHeight z.1
        change (z.1,0) ∈ (A.cone : Set ((Fin n → ℝ) × ℝ))
        rw [← h0]
        exact hz
      exact ⟨0,hzero,by rw [h0,hx,zero_smul]⟩
    · have hp : 0<z.2 := lt_of_le_of_ne ht (Ne.symm h0)
      have hn : z.2⁻¹ • z.1 ∈ heightOne A.cone := by
        have hs := A.cone.smul_mem (inv_pos.mpr hp) hz
        change (z.2⁻¹ • z.1,1) ∈ A.cone
        change (z.2⁻¹ • z.1,z.2⁻¹*z.2) ∈ A.cone at hs
        simpa only [inv_mul_cancel₀ hp.ne'] using hs
      refine ⟨z.2⁻¹ • z.1,hA hn,?_⟩
      rw [smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
  exact ⟨E,hin C hC,hin D hD⟩

/-- SAME actual carrier inclusion gives actual body inclusion across independently supplied cones. -/
theorem bodyExtension_mono_of_carrier_subset {n : ℕ} {C D : AdmissibleCone n}
    (S : Class.AlmostSpace C) (T : Class.AlmostSpace D) (hST : S.val.val ⊆ T.val.val) :
    (bodyExtension S : Set (EuclideanSpace ℝ (Fin n))) ⊆ bodyExtension T := by
  obtain ⟨E,hCE,hDE⟩ := exists_common_admissibleCone C D
  have h := OkounkovComparison.bodyExtension_mono
    (ConeIndependence.includeAlmost hCE S) (ConeIndependence.includeAlmost hDE T) hST
  simpa only [ConeIndependence.bodyExtension_includeAlmost] using h

end SGPT.AlmostSemigroup.CommonConeMonotonicity
