import Mathlib.Analysis.Convex.Body

/-! Actual compact convex body scalar stability, from actual closest points.
Blueprint: okounkov-convex-body-scaling-limit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SGPT.Okounkov.ConvexBodyScalingLimit
open Set Filter Metric
open scoped Topology Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scaled_point_distance_le (a : ℝ) (x y : E) {R : ℝ} (hy : ‖y‖≤R) :
    dist (a•x) y ≤ |a| * dist x y+|a-1| * R := by
  have he : a•x-y=a•(x-y)+(a-1)•y := by module
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖a•(x-y)‖+‖(a-1)•y‖ := norm_add_le _ _
    _ = |a| * dist x y+|a-1| * ‖y‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,dist_eq_norm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hy (abs_nonneg _))

/-- Genuine uniform Hausdorff bound for the SAME actual scaled bodies. -/
theorem hausdorffDist_smul_le (a : ℝ) (F K : ConvexBody E) {R : ℝ}
    (hR : ∀ y∈(K:Set E), ‖y‖≤R) :
    hausdorffDist (a•(F:Set E)) (K:Set E) ≤ |a| * hausdorffDist (F:Set E) (K:Set E)+|a-1| * R := by
  have hR0 : 0≤R := by obtain ⟨y,hy⟩ := K.nonempty; exact (norm_nonneg y).trans (hR y hy)
  have hfin : hausdorffEDist (F:Set E) (K:Set E)≠⊤ := ConvexBody.hausdorffEDist_ne_top
  apply hausdorffDist_le_of_mem_dist
    (add_nonneg (mul_nonneg (abs_nonneg _) hausdorffDist_nonneg) (mul_nonneg (abs_nonneg _) hR0))
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    refine ⟨y,hy,(scaled_point_distance_le a x y (hR y hy)).trans ?_⟩
    gcongr
    rw [←hxy]
    exact infDist_le_hausdorffDist_of_mem hx hfin
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := F.isCompact.exists_infDist_eq_dist F.nonempty y
    refine ⟨a•x,mem_smul_set.mpr ⟨x,hx,rfl⟩,?_⟩
    rw [dist_comm]
    apply (scaled_point_distance_le a x y (hR y hy)).trans
    gcongr
    rw [dist_comm,←hyx]
    rw [hausdorffDist_comm]
    exact infDist_le_hausdorffDist_of_mem hy (by rwa [hausdorffEDist_comm])

/-- Actual scalar and actual body limits imply the genuine SAME scaled-body Hausdorff limit. -/
theorem tendsto_hausdorffDist_smul {I : Type*} (l : Filter I)
    (F : I → ConvexBody E) (K : ConvexBody E) (a : I → ℝ)
    (hF : Tendsto (fun i => hausdorffDist ((F i):Set E) (K:Set E)) l (𝓝 0))
    (ha : Tendsto a l (𝓝 1)) :
    Tendsto (fun i => hausdorffDist ((a i)•((F i):Set E)) (K:Set E)) l (𝓝 0) := by
  obtain ⟨R,hR0,hR⟩ := K.isBounded.exists_pos_norm_le
  have hupper := (ha.abs.mul hF).add (((ha.sub_const 1).abs).mul_const R)
  have hzero : Tendsto (fun i => |a i| * hausdorffDist ((F i):Set E) (K:Set E)+|a i-1| * R) l (𝓝 0) := by
    simpa only [abs_one,mul_zero,sub_self,abs_zero,zero_mul,add_zero] using hupper
  exact squeeze_zero (fun _ => hausdorffDist_nonneg) (fun i => hausdorffDist_smul_le (a i) (F i) K hR) hzero
end SGPT.Okounkov.ConvexBodyScalingLimit
