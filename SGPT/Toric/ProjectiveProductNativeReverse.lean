import SGPT.Toric.ProjectiveProductReverseProfiles
import SGPT.Toric.ProjectiveToricReverse
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open scoped Topology RealInnerProductSpace

/-- The canonical native analytic filling of the literal original torus branch.
The raw boundary value is genuinely bottom, not a real surrogate. -/
def projectiveProductToricExtension {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    projectiveProductSpace n → EReal :=
  extensionAcross (projectiveProductTorus n)ᶜ (projectiveProductToricOffPotential f)

/-- The genuine native off-PSH branch is unchanged on the original torus. -/
theorem projectiveProductToricExtension_eq_off {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f)
    {p : projectiveProductSpace n} (hp : p ∈ projectiveProductTorus n) :
    projectiveProductToricExtension f p = projectiveProductToricOffPotential f p :=
  extensionAcross_eq_of_notMem (isOpen_projectiveProductTorus n).isClosed_compl
    (thetaPshOff_projectiveProductToricOffPotential hf) (by simpa only [mem_compl_iff, not_not] using hp)

/-- Original convex cube growth, every actual native chart and the genuine
analytic removable theorem manufacture a global strong native FS potential. -/
theorem isThetaPshPotential_projectiveProductToricExtension {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n)) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (projectiveProductToricExtension f) := by
  have hoff := thetaPshOff_projectiveProductToricOffPotential hf.1
  obtain ⟨C, hC⟩ := exists_upper_bound_projectiveProductToricOffPotential hf
  have hb : PshAnalyticSetExtension.LocallyBoundedAboveOff (projectiveProductTorus n)ᶜ
      (projectiveProductToricOffPotential f) := by
    intro p
    refine ⟨univ, Filter.univ_mem, C, fun y _ hy => ?_⟩
    exact hC y (by simpa only [mem_compl_iff, not_not] using hy)
  have hc := PshAnalyticRemovable.thetaPshLocalClosure_of_isComplexAnalyticSubset
    (SGPT.Foundations.Analysis.Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials
      (projectiveProductFSBackground n).form)
    (isComplexAnalyticSubset_projectiveProductBoundary n) hoff hb
  refine ⟨PshAnalyticSetExtension.thetaPlurisubharmonic_extensionAcross_of_localClosure
    (isOpen_projectiveProductTorus n).isClosed_compl hoff hc, ?_⟩
  intro p U hU hpU
  obtain ⟨y, hyT, hyU⟩ := (dense_projectiveProductTorus n).exists_mem_open hU ⟨p, hpU⟩
  refine ⟨y, hyU, ?_⟩
  rw [projectiveProductToricExtension_eq_off hf.1 hyT]
  exact EReal.coe_ne_bot _

/-- The original coordinatewise character action is an actual homeomorphism,
with its inverse manufactured from the proved original quotient group laws. -/
def projectiveProductTorusHomeomorph (n : ℕ) (a : Fin n → ℂˣ) :
    projectiveProductSpace n ≃ₜ projectiveProductSpace n where
  toFun := projectiveProductTorusAction n a
  invFun := projectiveProductTorusAction n (fun i => (a i)⁻¹)
  left_inv p := by
    rw [← projectiveProductTorusAction_mul]
    simpa only [inv_mul_cancel] using projectiveProductTorusAction_one n p
  right_inv p := by
    rw [← projectiveProductTorusAction_mul]
    simpa only [mul_inv_cancel] using projectiveProductTorusAction_one n p
  continuous_toFun := continuous_projectiveProductTorusAction n a
  continuous_invFun := continuous_projectiveProductTorusAction n (fun i => (a i)⁻¹)

/-- The genuine original product action preserves the original torus and boundary. -/
theorem projectiveProductTorusAction_mem_torus_iff {n : ℕ} (a : Fin n → ℂˣ)
    (p : projectiveProductSpace n) :
    projectiveProductTorusAction n a p ∈ projectiveProductTorus n ↔
      p ∈ projectiveProductTorus n := by
  rw [projectiveProductTorus_coordinates, projectiveProductTorus_coordinates]
  simp only [projectiveProductTorusAction_coordinates, projectiveTorusAction_mem_boundary_iff]

/-- Original homogeneous circle actions preserve the literal reverse branch
on the actual torus before any regularization or global PSH result is used. -/
theorem projectiveProductToricOffPotential_action {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {a : Fin n → ℂˣ}
    (ha : ∀ i, ‖(a i : ℂ)‖ = 1) {p : projectiveProductSpace n}
    (hp : p ∈ projectiveProductTorus n) :
    projectiveProductToricOffPotential f (projectiveProductTorusAction n a p) =
      projectiveProductToricOffPotential f p := by
  have hs := hp
  rw [← projectiveProductTorus_chart_source n] at hs
  let e := projectiveProductNativeChart n (fun _ => false)
  let z := e.val p
  let w : ComplexModel n := WithLp.toLp 2 (fun i => (a i : ℂ) * z i)
  have hac := projectiveProductTorusAction_chart_symm n a z
  rw [e.val.left_inv hs.1] at hac
  have ht : w ∈ e.val.target := by rw [projectiveProductNativeChart_target]; exact mem_univ _
  have hlog : tropicalization w = tropicalization z := by
    ext i
    change 2 * Real.log ‖(a i : ℂ) * z i‖ = 2 * Real.log ‖z i‖
    rw [norm_mul, ha i, one_mul]
  have hρ : projectiveProductFSPotential n w = projectiveProductFSPotential n z := by
    apply Finset.sum_congr rfl
    intro i _
    change Real.log (1 + Complex.normSq ((a i : ℂ) * z i)) = _
    simp only [← Complex.sq_norm, norm_mul, ha i, one_mul]
  rw [hac]
  change ((f (tropicalization (e.val (e.val.symm w))) -
    projectiveProductFSPotential n (e.val (e.val.symm w)) : ℝ) : EReal) =
      ((f (tropicalization z) - projectiveProductFSPotential n z : ℝ) : EReal)
  rw [e.val.right_inv ht, hlog, hρ]

/-- Actual USC covariance under the original action homeomorphism proves
circle invariance of the canonical global filling, including its boundary poles. -/
theorem projectiveProductToricExtension_circleInvariant {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ProjectiveProductCircleInvariant (projectiveProductToricExtension f) := by
  classical
  intro a ha p
  let raw : projectiveProductSpace n → EReal := fun y =>
    if y ∈ (projectiveProductTorus n)ᶜ then ⊥ else projectiveProductToricOffPotential f y
  have hraw : raw ∘ projectiveProductTorusHomeomorph n a = raw := by
    funext y
    change raw (projectiveProductTorusAction n a y) = raw y
    have hm := projectiveProductTorusAction_mem_torus_iff a y
    by_cases hy : y ∈ projectiveProductTorus n
    · have hay : projectiveProductTorusAction n a y ∈ projectiveProductTorus n := hm.mpr hy
      simpa only [raw, mem_compl_iff, hy, hay, not_true_eq_false, if_false] using
        projectiveProductToricOffPotential_action f ha hy
    · have hay : projectiveProductTorusAction n a y ∉ projectiveProductTorus n :=
        fun h => hy (hm.mp h)
      simp only [raw, mem_compl_iff, hy, hay, not_false_eq_true, if_true]
  have h := uscRegularization_comp_homeomorph_apply raw (projectiveProductTorusHomeomorph n a) p
  rw [hraw] at h
  simpa [projectiveProductToricExtension, extensionAcross, raw, projectiveProductTorusHomeomorph] using h.symm

/-- The concrete original convex cube-growth input produces every native
and source-facing field of the reverse construction, with no target premise. -/
theorem projectiveProductToricExtension_spec {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n)) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val (projectiveProductToricExtension f) ∧
      ProjectiveProductCircleInvariant (projectiveProductToricExtension f) ∧
      EqOn (projectiveProductToricExtension f) (projectiveProductToricOffPotential f)
        (projectiveProductTorus n) :=
  ⟨isThetaPshPotential_projectiveProductToricExtension hf,
    projectiveProductToricExtension_circleInvariant f,
    fun _ hp => projectiveProductToricExtension_eq_off hf.1 hp⟩

end SGPT.Toric
