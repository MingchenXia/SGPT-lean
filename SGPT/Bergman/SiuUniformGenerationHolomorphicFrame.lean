import SGPT.Bergman.SiuUniformGenerationGaugeDescent

/-!
# Holomorphic frames of every original line bundle on prescribed chart balls

The actual smooth frame and its descended smooth closed logarithmic form are
both produced from the original bundle.  The scalar primitive gives the
holomorphic gauge `exp(-u) σ`.  The final section is holomorphic in the native
bundle sense, with its original fibres and original holomorphic atlas.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric Complex
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric SGPT.PSH.GlobalL2

variable {n : ℕ}

theorem dbarDir_cexp_neg {u : ComplexModel n → ℂ} {z : ComplexModel n}
    (hu : DifferentiableAt ℝ u z) (v : ComplexModel n) :
    dbarDir v (fun y => Complex.exp (-u y)) z =
      -Complex.exp (-u z) * dbarDir v u z := by
  have hder := hu.hasFDerivAt.neg.cexp.fderiv
  change fderiv ℝ (fun y => Complex.exp (-u y)) z =
    Complex.exp (-u z) • -(fderiv ℝ u z) at hder
  simp only [dbarDir, hder, smul_apply, neg_apply, smul_eq_mul]
  ring

theorem differentiableAt_complex_of_dbarCoords_eq_zero
    {f : ComplexModel n → ℂ} {z : ComplexModel n} (hf : DifferentiableAt ℝ f z)
    (hzero : ∀ j : Fin n, dbarDir (coordVec j) f z = 0) : DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_of_dbarDir_eq_zero hf
  intro v
  conv_lhs => rw [← sum_smul_coordVec v]
  rw [dbarDir_sum_dir]
  simp only [hzero, mul_zero, Finset.sum_const_zero]

theorem differentiableOn_gaugedCoefficient
    {D : Set (ComplexModel n)} (hD : IsOpen D)
    {f u : ComplexModel n → ℂ} (hf : ContDiffOn ℝ ∞ f D) (hu : ContDiffOn ℝ ∞ u D)
    (hf0 : ∀ z ∈ D, f z ≠ 0)
    (hueq : ∀ j, ∀ z ∈ D, dbarDir (coordVec j) u z = logarithmicDbar f j z) :
    DifferentiableOn ℂ (fun z => Complex.exp (-u z) * f z) D := by
  intro z hz
  have hfd := (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hud := (hu.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hexd : DifferentiableAt ℝ (fun y => Complex.exp (-u y)) z := hud.neg.cexp
  refine (differentiableAt_complex_of_dbarCoords_eq_zero (hexd.mul hfd) ?_).differentiableWithinAt
  intro j
  change dbarDir (coordVec j) (fun y => Complex.exp (-u y) * f y) z = 0
  rw [dbarDir_mul hexd hfd, dbarDir_cexp_neg hud, hueq j z hz]
  dsimp [logarithmicDbar]
  field_simp [hf0 z hz]
  ring

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {L : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- Holomorphicity of every actual atlas coefficient in one coordinate chart
is the native holomorphic-section predicate on that coordinate domain. -/
theorem isHolomorphicSectionOn_of_chart_coefficients
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hD : IsOpen D) (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs : ∀ e : AtlasFrame L, DifferentiableOn ℂ (smoothFrameCoefficient c s e)
      (D ∩ c.val.symm ⁻¹' e.val.baseSet)) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber s
      (c.val.source ∩ c.val ⁻¹' D) := by
  intro x hx
  let e := prefFrame L x
  let := e.property
  have he : x ∈ e.val.baseSet := mem_prefFrame L x
  have hU := isOpen_chart_frameDomain c hD hDt e
  have hcx : c.val x ∈ D ∩ c.val.symm ⁻¹' e.val.baseSet :=
    ⟨hx.2, by simpa only [mem_preimage, c.val.left_inv hx.1] using he⟩
  have hcont : ContDiffAt ℂ ∞ (smoothFrameCoefficient c s e) (c.val x) :=
    contDiffAt_of_differentiableOn_complex (hs e) hU hcx
  have hco : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (fun y => smoothFrameCoefficient c s e (c.val y)) x :=
    (hcont.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas c.property) hx.1)).mdifferentiableAt (by simp)
  have hev : (fun y => (e.val (TotalSpace.mk' ℂ y (s y))).2) =ᶠ[𝓝 x]
      fun y => smoothFrameCoefficient c s e (c.val y) := by
    filter_upwards [(c.val.open_source.inter e.val.open_baseSet).mem_nhds ⟨hx.1, he⟩] with y hy
    rw [smoothFrameCoefficient, c.val.left_inv hy.1,
      Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hy.2]
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e.val s he]
  exact MDifferentiableAt.congr_of_eventuallyEq hco hev

/-- Every original holomorphic line bundle on compact `X` has an actual
nonvanishing native holomorphic section on every strictly smaller prescribed
coordinate ball.  No domain of a preferred atlas frame is assumed to contain
that ball, and no norm estimate uniform in the varying bundle is required. -/
theorem exists_holomorphic_nonzero_frame_on_chartBall [CompactSpace X]
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (p : ComplexModel n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hball : ball p R ⊆ c.val.target) :
    ∃ s : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber s
        (c.val.source ∩ c.val ⁻¹' ball p r) ∧
      ∀ x ∈ c.val.source ∩ c.val ⁻¹' ball p r, s x ≠ 0 := by
  let R' : ℝ := (r + R) / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hR'R : R' < R := by dsimp [R']; linarith
  have hR' : 0 < R' := hr.trans hrR'
  have hmid : ball p R' ⊆ c.val.target := (ball_subset_ball hR'R.le).trans hball
  have hsmall : ball p r ⊆ c.val.target := (ball_subset_ball hrR.le).trans hball
  obtain ⟨σ, hσ, hσ0⟩ := exists_chartSmooth_nonzero_frame L c p hR' hR'R hball
  let α : Fin n → ComplexModel n → ℂ := smoothFrameGauge c σ
  have hα : ∀ j, ContDiffOn ℝ ∞ (α j) (ball p R') :=
    contDiffOn_smoothFrameGauge c isOpen_ball hmid σ hσ hσ0
  have hclosed : IsDbarClosedOn α (ball p R') :=
    isDbarClosedOn_smoothFrameGauge c isOpen_ball hmid σ hσ hσ0
  obtain ⟨u, hu, hueq⟩ := exists_smooth_dbar_primitive_on_ball p hr hrR' α hα hclosed
  let s : (x : X) → L.Fiber x := fun x => Complex.exp (-u (c.val x)) • σ x
  refine ⟨s, isHolomorphicSectionOn_of_chart_coefficients c isOpen_ball hsmall s ?_, ?_⟩
  · intro e
    let D : Set (ComplexModel n) := ball p r ∩ c.val.symm ⁻¹' e.val.baseSet
    have hD : IsOpen D := isOpen_chart_frameDomain c isOpen_ball hsmall e
    have hsub : D ⊆ ball p R' ∩ c.val.symm ⁻¹' e.val.baseSet :=
      fun z hz => ⟨ball_subset_ball hrR'.le hz.1, hz.2⟩
    have hf : ContDiffOn ℝ ∞ (smoothFrameCoefficient c σ e) D := (hσ e).mono hsub
    have hf0 : ∀ z ∈ D, smoothFrameCoefficient c σ e z ≠ 0 :=
      fun z hz => smoothFrameCoefficient_ne_zero c hmid σ hσ0 e (hsub hz).1 hz.2
    have heq : ∀ j, ∀ z ∈ D,
        dbarDir (coordVec j) u z = logarithmicDbar (smoothFrameCoefficient c σ e) j z := by
      intro j z hz
      exact (hueq j z hz.1).trans
        (smoothFrameGauge_eq c isOpen_ball hmid σ hσ hσ0 e j (hsub hz).1 hz.2)
    refine (differentiableOn_gaugedCoefficient hD hf (hu.mono inter_subset_left) hf0 heq).congr
      (fun z hz => ?_)
    dsimp [smoothFrameCoefficient, s]
    rw [map_smul, smul_eq_mul, c.val.right_inv (hsmall hz.1)]
  · intro x hx
    exact smul_ne_zero (Complex.exp_ne_zero _) (hσ0 x ⟨hx.1, ball_subset_ball hrR'.le hx.2⟩)

end SGPT.Bergman.SiuUniformGeneration
