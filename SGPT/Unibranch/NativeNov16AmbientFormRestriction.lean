import SGPT.Unibranch.Resolution
import SGPT.Unibranch.ComplexSpaceFormPullbackClosed
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-! Actual ambient forms on the ORIGINAL reduced analytic subspace.
Blueprint: native-nov16-ambient-form-restriction.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch.SpaceForm
variable {n k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem closedChart_toPoint_val (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x : M)
    (c : (LocalEmbedding.ofChart C hC x).carrier) :
    ((LocalEmbedding.ofChart C hC x).toPoint c).val =
      (complexChartAt (n := n) x).val.symm c.val.val := rfl

private theorem closedChart_probe_coordinate (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x y : M)
    {W : Set (ComplexModel n)} {G : ComplexModel n → ComplexModel n}
    (hG : (LocalEmbedding.ofChart C hC x).IsTransition
      (LocalEmbedding.ofChart C hC y) W G)
    {m : ℕ} {D : Set (ComplexModel m)} {h : ComplexModel m → ComplexModel n}
    (hprobe : ∀ z ∈ D, h z ∈ W ∧
      ∃ c : (LocalEmbedding.ofChart C hC x).carrier, c.val.val = h z)
    {z : ComplexModel m} (hz : z ∈ D) :
    h z ∈ (chartTransition (complexChartAt x) (complexChartAt y)).source ∧
      G (h z) = chartTransition (complexChartAt x) (complexChartAt y) (h z) := by
  let e := complexChartAt (n := n) x
  let f := complexChartAt (n := n) y
  obtain ⟨a,ha⟩ := (hprobe z hz).2
  obtain ⟨b,hb,hba⟩ := hG.2.2.2.2 a (by rw [ha]; exact (hprobe z hz).1)
  have hx : h z ∈ e.val.target := hG.2.1 (hprobe z hz).1
  have hy : G (h z) ∈ f.val.target := hG.2.2.2.1 (hprobe z hz).1
  have hpoint : f.val.symm (G (h z)) = e.val.symm (h z) := by
    have H := congrArg (fun q : (SourceReducedComplexSpace.ofClosedAnalytic C hC).obj.left =>
      q.val) hba
    rw [closedChart_toPoint_val,closedChart_toPoint_val,hb,ha] at H
    exact H
  constructor
  · change h z ∈ e.val.target ∧ e.val.symm (h z) ∈ f.val.source
    rw [← hpoint]
    exact ⟨hx,f.val.map_target hy⟩
  · change G (h z) = f.val (e.val.symm (h z))
    rw [← hpoint,f.val.right_inv hy]

private theorem ambient_pullback_germ_congr {m N p : ℕ}
    {F G : ComplexModel m → ComplexModel N} {z : ComplexModel m}
    (h : F =ᶠ[𝓝 z] G) (v : AmbientForm N p) :
    pullbackForm F v z = pullbackForm G v z := by
  simp only [pullbackForm,h.self_of_nhds,h.fderiv_eq]

private theorem closedChart_form_compatible (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (theta : SmoothRealForm n M k)
    (x y : M) (W : Set (ComplexModel n)) (G : ComplexModel n → ComplexModel n)
    (hG : (LocalEmbedding.ofChart C hC x).IsTransition
      (LocalEmbedding.ofChart C hC y) W G) :
    (LocalEmbedding.ofChart C hC x).VanishesOn W
      (theta.coeff (complexChartAt x) - pullbackForm G (theta.coeff (complexChartAt y))) := by
  intro m D h hD hd hprobe z hz
  rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero]
  let e := complexChartAt (n := n) x
  let f := complexChartAt (n := n) y
  let T := chartTransition e f
  have hp := closedChart_probe_coordinate C hC x y hG hprobe hz
  have heq : (T ∘ h) =ᶠ[𝓝 z] G ∘ h := by
    filter_upwards [hD.mem_nhds hz] with w hw
    exact (closedChart_probe_coordinate C hC x y hG hprobe hw).2.symm
  have hcoef : theta.coeff e (h z) = pullbackForm T (theta.coeff f) (h z) := by
    ext v
    exact theta.compatible e f (h z) hp.1 v
  have hh := (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have ht := ((HolomorphicMaps.chartTransition_contDiffAt e f hp.1).differentiableAt
    (by simp)).restrictScalars ℝ
  have hg := (hG.2.2.1.differentiableAt (hG.1.mem_nhds (hprobe z hz).1)).restrictScalars ℝ
  have hleft : pullbackForm h (theta.coeff e) z =
      pullbackForm h (pullbackForm T (theta.coeff f)) z := by
    change (theta.coeff e (h z)).compContinuousLinearMap (fderiv ℝ h z) = _
    rw [hcoef]
    rfl
  exact hleft.trans ((pullbackForm_comp hh ht (theta.coeff f)).trans
    ((ambient_pullback_germ_congr heq (theta.coeff f)).trans
      (pullbackForm_comp hh hg (theta.coeff f)).symm))

/-- Literal ambient coefficients on the ORIGINAL reduced closed analytic
space, compatible with EVERY actual holomorphic embedded transition. -/
def ofClosedAnalytic (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (theta : SmoothRealForm n M k) :
    SpaceForm (SourceReducedComplexSpace.ofClosedAnalytic C hC) k where
  ι := M
  chart x := LocalEmbedding.ofChart C hC x
  covers c := ⟨c.val,mem_range_chartModelMap (n := n) C c.property⟩
  rep x := theta.coeff (complexChartAt x)
  smooth x := theta.smooth (complexChartAt x)
  compatible := closedChart_form_compatible C hC theta

theorem ofClosedAnalytic_restrictsTo (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (theta : SmoothRealForm n M k) (x : M) :
    (ofClosedAnalytic C hC theta).RestrictsTo (LocalEmbedding.ofChart C hC x)
      (theta.coeff (complexChartAt x)) := by
  intro y W G hG
  exact (ofClosedAnalytic C hC theta).compatible x y W G hG

/-- The SAME local ambient representative is closed and strictly positive
of type(1,1); the complex space need not be a manifold. -/
def IsKahler {X : SourceReducedComplexSpace} (theta : SpaceForm X 2) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v : AmbientForm e.dim 2, ContDiffOn ℝ ∞ v e.ambient ∧
      (∀ z ∈ e.ambient,extDeriv v z = 0) ∧
      (∀ z ∈ e.ambient,SGPT.Foundations.Analysis.FirstPass.IsOneOne (v z) ∧
        IsStrictlyPositive (v z)) ∧
      theta.RestrictsTo e v

theorem IsKahler.isClosed {X : SourceReducedComplexSpace} {theta : SpaceForm X 2}
    (h : theta.IsKahler) : theta.IsClosed := by
  intro x
  obtain ⟨e,he,v,hv,hclosed,_hpositive,hres⟩ := h x
  exact ⟨e,he,v,hv,hclosed,hres⟩

theorem IsKahler.isOneOne {X : SourceReducedComplexSpace} {theta : SpaceForm X 2}
    (h : theta.IsKahler) : theta.IsOneOne := by
  intro x
  obtain ⟨e,he,v,hv,_hclosed,hpositive,hres⟩ := h x
  exact ⟨e,he,v,hv,fun z hz => (hpositive z hz).1,hres⟩

/-- Raw ambient Kahler data manufacture an actual locally ambient Kahler
form on the original reduced subspace, with all singular points retained. -/
theorem ofClosedAnalytic_isKahler (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (omega : KahlerBackground n M) :
    (ofClosedAnalytic C hC omega.form.val).IsKahler := by
  intro c
  refine ⟨LocalEmbedding.ofChart C hC c.val,
    mem_range_chartModelMap (n := n) C c.property,
    omega.form.val.coeff (complexChartAt c.val),omega.form.val.smooth (complexChartAt c.val),
    ?_,?_,ofClosedAnalytic_restrictsTo C hC omega.form.val c.val⟩
  · exact omega.isKahler.2 (complexChartAt c.val)
  · exact omega.isKahler.1 (complexChartAt c.val)

end SGPT.Unibranch.SpaceForm
