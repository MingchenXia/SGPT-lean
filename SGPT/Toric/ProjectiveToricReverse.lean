import SGPT.Toric.ProjectiveToricBoundary

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- A genuine finite corrected PSH function in one actual chart covering U
supplies every original relative smooth-potential test. -/
theorem isThetaPSHOn_of_finite_single_chart
    {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal} {U : Set X}
    (i : A.Index) (hUi : U ⊆ (A.chart i).source)
    (ρ : ComplexModel (A.dimension i) → ℝ)
    (hρ : ContDiffOn ℝ ∞ ρ (A.chart i).target)
    (hform : EqOn (smoothDDC ρ) (θ.coeff i) (A.chart i).target)
    (hpsh : PlurisubharmonicOn
      (fun z ↦ A.coordinate u i z + (ρ z : EReal))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U))
    (hfinite : ∀ x ∈ U, ∃ r : ℝ, u x = (r : EReal)) : A.IsThetaPSHOn θ u U := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := hfinite x hx
    rw [hr]
    exact EReal.coe_ne_top r
  · intro V g hVU hg x hx
    let e := A.chart i
    let D := e.target ∩ e.symm ⁻¹' V
    let σ := g ∘ e.symm
    have hD : IsOpen D := e.isOpen_inter_preimage_symm hg.1
    have hρD : ContDiffOn ℝ ∞ ρ D := hρ.mono inter_subset_left
    have hσ : ContDiffOn ℝ ∞ σ D := hg.2.1 i
    have hzero : ∀ z ∈ D, smoothDDC (fun y ↦ σ y - ρ y) z = 0 := by
      intro z hz
      rw [PositiveClasses.smoothDDC_sub hD hσ hρD hz,
        hg.2.2 i hz, hform hz.1, sub_self]
    have hdifference := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hD
      (hσ.sub hρD) hzero
    have hcorrected : PlurisubharmonicOn
        (fun z ↦ A.coordinate u i z + (ρ z : EReal)) D :=
      hpsh.mono (fun _ hz ↦ ⟨hz.1, hVU hz.2⟩)
    have hlocal : PlurisubharmonicOn (A.coordinate (fun p ↦ u p + (g p : EReal)) i) D := by
      intro z hz
      apply ((hcorrected.add hdifference) z hz).congr
      exact Eventually.of_forall fun y ↦ corrected_add_sub (u (e.symm y)) (ρ y) (g (e.symm y))
    have hxS : x ∈ e.source := hUi (hVU hx)
    have hxD : e x ∈ D := ⟨e.mapsTo hxS, by simpa only [mem_preimage, e.left_inv hxS] using hx⟩
    obtain ⟨W, hW, hxW, hd⟩ := hlocal (e x) hxD
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (hW.inter hD) (e x) ⟨hxW, hxD⟩
    refine ⟨i, hxS, ball (e x) r, isOpen_ball, isConnected_ball hr,
      fun _ hz ↦ (hb hz).2, mem_ball_self hr,
      hd.mono (fun _ hz ↦ (hb hz).1), e x, mem_ball_self hr, ?_⟩
    obtain ⟨c, hc⟩ := hfinite x (hVU hx)
    change u (e.symm (e x)) + (g (e.symm (e x)) : EReal) ≠ ⊥
    rw [e.left_inv hxS, hc, ← EReal.coe_add]
    exact EReal.coe_ne_bot (c + g x)

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- Literal original reverse potential, tested only off the actual analytic boundary. -/
def projectiveToricOffPotential (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (p : Projectivization ℂ (Fin 2 → ℂ)) : EReal :=
  ((f (tropicalization (projectiveModelChart false p)) -
    projectiveFSPotential (projectiveModelChart false p) : ℝ) : EReal)

/-- Original finite convexity gives every actual relative theta-PSH test
on the genuine projective torus. -/
theorem isThetaPSHOn_projectiveToricOffPotential
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : ConvexOn ℝ univ f) :
    projectiveLineAtlas.IsThetaPSHOn projectiveFSForm (projectiveToricOffPotential f)
      projectiveToricBoundaryᶜ := by
  apply isThetaPSHOn_of_finite_single_chart (i := false)
    projectiveToricBoundary_compl_subset_finite_source projectiveFSPotential
    contDiff_projectiveFSPotential.contDiffOn (fun _ _ ↦ rfl)
  · let e := projectiveModelChart false
    let D := e.target ∩ e.symm ⁻¹' projectiveToricBoundaryᶜ
    have hD : IsOpen D := e.isOpen_inter_preimage_symm isClosed_projectiveToricBoundary.isOpen_compl
    intro z hz
    have hzT : z ∈ complexTorus 1 := (projectiveToricBoundary_chart_off_iff false z).mp hz.2
    apply (plurisubharmonicOn_tropicalPullback_of_convexOn hf z hzT).congr
    filter_upwards [hD.mem_nhds hz] with y hy
    change (f (tropicalization y) : EReal) =
      ((f (tropicalization (e (e.symm y))) - projectiveFSPotential (e (e.symm y)) : ℝ) : EReal) +
        (projectiveFSPotential y : EReal)
    rw [e.right_inv hy.1, ← EReal.coe_add]
    congr 1
    ring
  · intro p _
    exact ⟨_, rfl⟩

/-- The genuine two original logarithmic costs supply the lower partition bound. -/
theorem max_le_projectiveLineLogPartition (x : ℝ) :
    max 0 x ≤ projectiveLineLogPartition x := by
  apply max_le
  · have h := SGPT.Convex.le_logSumExp (fun b : Bool ↦ if b then x else 0) false
    simpa [SGPT.Convex.logSumExp, Fintype.sum_bool, projectiveLineLogPartition, add_comm] using h
  · have h := SGPT.Convex.le_logSumExp (fun b : Bool ↦ if b then x else 0) true
    simpa [SGPT.Convex.logSumExp, Fintype.sum_bool, projectiveLineLogPartition, add_comm] using h

/-- The original support-growth condition produces a true global finite
upper bound on the reverse potential off its actual boundary. -/
theorem exists_upper_bound_projectiveToricOffPotential
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval) :
    ∃ C : ℝ, ∀ p ∉ projectiveToricBoundary,
      projectiveToricOffPotential f p ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  refine ⟨C, fun p hp ↦ ?_⟩
  let z := projectiveModelChart false p
  have hz : z ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
  have hcost := hC (tropicalization z)
  rw [support_projectiveMomentInterval, ← EReal.coe_add] at hcost
  have hc := EReal.coe_le_coe_iff.mp hcost
  have hl := max_le_projectiveLineLogPartition (tropicalization z 0)
  rw [projectiveLineLogPartition_tropicalization (hz 0), ← projectiveFSPotential_eq] at hl
  change ((f (tropicalization z) - projectiveFSPotential z : ℝ) : EReal) ≤ (C : EReal)
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Actual finite-convex growth data produce the unique original global
Fubini--Study theta-PSH extension of the literal toric potential. -/
theorem existsUnique_projectiveToricExtension
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval) :
    ∃! u : Projectivization ℂ (Fin 2 → ℂ) → EReal,
      projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧
        EqOn u (projectiveToricOffPotential f) projectiveToricBoundaryᶜ := by
  obtain ⟨C, hC⟩ := exists_upper_bound_projectiveToricOffPotential hf
  exact exists_unique_bounded_theta_analytic_extension
    (isThetaPSHOn_projectiveToricOffPotential hf.1)
    hasAnalyticChartEquations_projectiveToricBoundary interior_projectiveToricBoundary
    (fun p _ ↦ ⟨univ, Filter.univ_mem, C, fun q _ hq ↦ hC q hq⟩)

/-- The actual homogeneous action fixes the original origin. -/
theorem projectiveTorusAction_origin (a : ℂˣ) :
    projectiveTorusAction a projectiveOrigin = projectiveOrigin := by
  simp only [projectiveOrigin, projectiveTorusAction_chart_symm, smul_zero]

/-- Both genuine original boundary points are fixed under every torus element. -/
theorem projectiveTorusAction_projectiveInfinity (a : ℂˣ) :
    projectiveTorusAction a projectiveInfinity = projectiveInfinity := by
  simp only [projectiveInfinity, projectiveTorusAction_chart_symm, smul_zero]

/-- The original analytic boundary is preserved in both directions by the actual action. -/
theorem projectiveTorusAction_mem_boundary_iff (a : ℂˣ)
    (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveTorusAction a p ∈ projectiveToricBoundary ↔ p ∈ projectiveToricBoundary := by
  have h₀ : projectiveTorusAction a p = projectiveOrigin ↔ p = projectiveOrigin := by
    constructor
    · intro h
      apply (projectiveTorusHomeomorph a).injective
      change projectiveTorusAction a p = projectiveTorusAction a projectiveOrigin
      rwa [projectiveTorusAction_origin]
    · rintro rfl
      exact projectiveTorusAction_origin a
  have hinfty : projectiveTorusAction a p = projectiveInfinity ↔ p = projectiveInfinity := by
    constructor
    · intro h
      apply (projectiveTorusHomeomorph a).injective
      change projectiveTorusAction a p = projectiveTorusAction a projectiveInfinity
      rwa [projectiveTorusAction_projectiveInfinity]
    · rintro rfl
      exact projectiveTorusAction_projectiveInfinity a
  simp only [projectiveToricBoundary, mem_ofPred_eq, h₀, hinfty]

/-- The actual finite quotient coordinate intertwines genuine torus multiplication. -/
theorem projectiveFiniteCoordinate_action (a : ℂˣ)
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    projectiveModelChart false (projectiveTorusAction a p) =
      (a : ℂ) • projectiveModelChart false p := by
  let e := projectiveModelChart false
  have h := projectiveTorusAction_chart_symm a false (e p)
  rw [e.left_inv (projectiveToricBoundary_compl_subset_finite_source hp)] at h
  change projectiveTorusAction a p = e.symm ((a : ℂ) • e p) at h
  rw [h, e.right_inv]
  simp [e, projectiveModelChart, projectiveQuotientScalarChart_target]

/-- Genuine unitary scalar multiplication leaves the literal squared-log coordinates unchanged. -/
theorem tropicalization_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) (z : ComplexModel 1) :
    tropicalization (c • z) = tropicalization z := by
  ext i
  change 2 * Real.log ‖(c • z) i‖ = 2 * Real.log ‖z i‖
  simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

/-- The independently defined literal reverse potential is actually circle invariant off the boundary. -/
theorem projectiveToricOffPotential_action
    (f : EuclideanSpace ℝ (Fin 1) → ℝ) {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1)
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    projectiveToricOffPotential f (projectiveTorusAction a p) = projectiveToricOffPotential f p := by
  simp only [projectiveToricOffPotential, projectiveFiniteCoordinate_action a hp,
    tropicalization_smul_of_norm_eq_one ha, projectiveFSPotential_smul ha]

/-- Actual extension uniqueness and proved circle pullback preserve the
original global potential, including both boundary poles. -/
theorem projectiveToricExtension_circleInvariant
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval)
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hoff : EqOn u (projectiveToricOffPotential f) projectiveToricBoundaryᶜ) :
    ProjectiveCircleInvariant u := by
  obtain ⟨v, _hv, huniq⟩ := existsUnique_projectiveToricExtension hf
  intro a ha p
  have hpull : projectiveLineAtlas.IsThetaPSH projectiveFSForm (u ∘ projectiveTorusAction a) :=
    isThetaPSH_comp_projectiveTorusAction hu ha
  have hpullOff : EqOn (u ∘ projectiveTorusAction a) (projectiveToricOffPotential f)
      projectiveToricBoundaryᶜ := by
    intro q hq
    change u (projectiveTorusAction a q) = _
    have hqa : projectiveTorusAction a q ∈ projectiveToricBoundaryᶜ :=
      fun h ↦ hq ((projectiveTorusAction_mem_boundary_iff a q).mp h)
    rw [hoff hqa, projectiveToricOffPotential_action f ha hq]
  have heq : u ∘ projectiveTorusAction a = u :=
    (huniq _ ⟨hpull, hpullOff⟩).trans (huniq _ ⟨hu, hoff⟩).symm
  exact congrFun heq p

/-- Literal exponential/logarithmic inverse laws recover the original
finite convex function from any actual reverse extension. -/
theorem projectiveToricCorrectedDescent_eq_of_extension
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hoff : EqOn u (projectiveToricOffPotential f) projectiveToricBoundaryᶜ) :
    projectiveToricCorrectedDescent u = fun x ↦ (f x : EReal) := by
  funext x
  let e := projectiveModelChart false
  let z := expCoordinates x
  have hz : z ∈ complexTorus 1 := expCoordinates_mem_complexTorus x
  have hzTarget : z ∈ e.target := by
    simp [e, projectiveModelChart, projectiveQuotientScalarChart_target]
  have hp : e.symm z = OnePoint.equivProjectivization ℂ ((z 0 : ℂ) : OnePoint ℂ) := by
    simp only [e, projectiveModelChart_symm_onePoint, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hpOff : e.symm z ∈ projectiveToricBoundaryᶜ :=
    (projectiveToricBoundary_chart_off_iff false z).mpr hz
  have hρ : projectiveLineLogPartition (x 0) = projectiveFSPotential z := by
    simpa only [z, tropicalization_expCoordinates, ← projectiveFSPotential_eq] using
      projectiveLineLogPartition_tropicalization (hz 0)
  change u (OnePoint.equivProjectivization ℂ ((z 0 : ℂ) : OnePoint ℂ)) +
    (projectiveLineLogPartition (x 0) : EReal) = (f x : EReal)
  rw [← hp, hoff hpOff]
  change ((f (tropicalization (e (e.symm z))) - projectiveFSPotential (e (e.symm z)) : ℝ) : EReal) +
    (projectiveLineLogPartition (x 0) : EReal) = (f x : EReal)
  rw [e.right_inv hzTarget, tropicalization_expCoordinates, hρ, ← EReal.coe_add]
  congr 1
  ring

/-- The true corrected descent identifies every original invariant
potential with its literal reverse formula on the actual torus. -/
theorem projectiveToricOffPotential_eq_of_descent
    {f : EuclideanSpace ℝ (Fin 1) → ℝ}
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hi : ProjectiveCircleInvariant u)
    (hdesc : projectiveToricCorrectedDescent u = fun x ↦ (f x : EReal)) :
    EqOn u (projectiveToricOffPotential f) projectiveToricBoundaryᶜ := by
  intro p hp
  let e := projectiveModelChart false
  let z := e p
  have hz : z ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
  have hs : p ∈ e.source := projectiveToricBoundary_compl_subset_finite_source hp
  have h := projectiveToricCorrectedDescent_tropicalPullback hi hz
  change projectiveToricCorrectedDescent u (tropicalization z) =
    u (e.symm z) + (projectiveFSPotential z : EReal) at h
  rw [hdesc, show e.symm z = p from e.left_inv hs] at h
  have heq := congrArg (fun q : EReal ↦ q + ((-projectiveFSPotential z : ℝ) : EReal)) h.symm
  have hcancel := corrected_add_sub (u p) (projectiveFSPotential z) 0
  simp only [zero_sub, EReal.coe_zero, add_zero] at hcancel
  rw [hcancel, ← EReal.coe_add] at heq
  change u p = ((f (tropicalization z) - projectiveFSPotential z : ℝ) : EReal)
  simpa only [sub_eq_add_neg] using heq

/-- The actual finite recovery gives the original real-valued growth
coordinate of every genuine invariant theta potential. -/
theorem projectiveToricCorrectedDescent_toReal_mem_realGrowthClass
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) (hi : ProjectiveCircleInvariant u) :
    (fun x ↦ (projectiveToricCorrectedDescent u x).toReal) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval ∧
      projectiveToricCorrectedDescent u =
        fun x ↦ ((projectiveToricCorrectedDescent u x).toReal : EReal) := by
  obtain ⟨f, hf, heq⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  have hreal : (fun x ↦ (projectiveToricCorrectedDescent u x).toReal) = f := by
    funext x
    rw [heq]
    exact EReal.toReal_coe _
  refine ⟨?_, ?_⟩
  · rw [hreal]
    refine ⟨hf, ?_⟩
    simpa only [heq] using (projectiveToricCorrectedDescent_mem_growthClass hu hi).2
  · funext x
    rw [heq]
    simp only [EReal.toReal_coe]

/-- The reverse map chooses the actually produced unique source extension. -/
def projectiveToricExtension (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval) :
    Projectivization ℂ (Fin 2 → ℂ) → EReal :=
  Classical.choose (existsUnique_projectiveToricExtension hf)

theorem projectiveToricExtension_spec (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (projectiveToricExtension f hf) ∧
      EqOn (projectiveToricExtension f hf) (projectiveToricOffPotential f) projectiveToricBoundaryᶜ :=
  (Classical.choose_spec (existsUnique_projectiveToricExtension hf)).1

/-- Actual source theta-PSH functions and original real convex growth
functions have genuine inverse maps on the original projective line. -/
def projectiveToricEquivRealGrowth :
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal //
      projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧ ProjectiveCircleInvariant u} ≃
    {f : EuclideanSpace ℝ (Fin 1) → ℝ //
      f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval} where
  toFun u := ⟨fun x ↦ (projectiveToricCorrectedDescent u.val x).toReal,
    (projectiveToricCorrectedDescent_toReal_mem_realGrowthClass u.property.1 u.property.2).1⟩
  invFun f := ⟨projectiveToricExtension f.val f.property,
    (projectiveToricExtension_spec f.val f.property).1,
    projectiveToricExtension_circleInvariant f.property
      (projectiveToricExtension_spec f.val f.property).1
      (projectiveToricExtension_spec f.val f.property).2⟩
  left_inv u := by
    apply Subtype.ext
    apply ((Classical.choose_spec (existsUnique_projectiveToricExtension
      (projectiveToricCorrectedDescent_toReal_mem_realGrowthClass u.property.1 u.property.2).1)).2
        u.val ⟨u.property.1, projectiveToricOffPotential_eq_of_descent u.property.2
          (projectiveToricCorrectedDescent_toReal_mem_realGrowthClass u.property.1 u.property.2).2⟩).symm
  right_inv f := by
    apply Subtype.ext
    funext x
    have h := projectiveToricCorrectedDescent_eq_of_extension
      (projectiveToricExtension_spec f.val f.property).2
    change (projectiveToricCorrectedDescent (projectiveToricExtension f.val f.property) x).toReal = f.val x
    rw [h]
    exact EReal.toReal_coe _

/-- The actual moment interval is compact in the original Euclidean coordinates. -/
theorem isCompact_projectiveMomentInterval : IsCompact projectiveMomentInterval := by
  let v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))
  have heq : projectiveMomentInterval = (fun r : ℝ ↦ r • v) '' Icc (0 : ℝ) 1 := by
    ext m
    constructor
    · intro hm
      refine ⟨m 0, hm, ?_⟩
      ext i
      fin_cases i
      simp [v]
    · rintro ⟨r, hr, rfl⟩
      change 0 ≤ (r • v) 0 ∧ (r • v) 0 ≤ 1
      change 0 ≤ r ∧ r ≤ 1 at hr
      simpa [v] using hr
  rw [heq]
  exact isCompact_Icc.image (by fun_prop)

/-- The actual source interval retains its genuine zero endpoint. -/
theorem nonempty_projectiveMomentInterval : projectiveMomentInterval.Nonempty :=
  ⟨0, by simp [projectiveMomentInterval]⟩

/-- Actual coordinate inequalities prove the genuine interval's convexity. -/
theorem convex_projectiveMomentInterval : Convex ℝ projectiveMomentInterval := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ (a • x + b • y) 0 ∧ (a • x + b • y) 0 ≤ 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change 0 ≤ x 0 ∧ x 0 ≤ 1 at hx
  change 0 ≤ y 0 ∧ y 0 ≤ 1 at hy
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · have hax := mul_le_mul_of_nonneg_left hx.2 ha
    have hby := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith

/-- All three original toric classes have actual inverse maps for P1;
the last step reuses the checked general Legendre equivalence. -/
def projectiveToricEquivClosedProper :
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal //
      projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧ ProjectiveCircleInvariant u} ≃
    {g : EuclideanSpace ℝ (Fin 1) → EReal // g ∈ ClosedProperOnBody projectiveMomentInterval} :=
  projectiveToricEquivRealGrowth.trans
    (realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin 1)))
      isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval convex_projectiveMomentInterval)

/-- The produced first correspondence is literally the original corrected logarithmic descent. -/
theorem projectiveToricEquivRealGrowth_apply
    (u : {u : Projectivization ℂ (Fin 2 → ℂ) → EReal //
      projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧ ProjectiveCircleInvariant u})
    (x : EuclideanSpace ℝ (Fin 1)) :
    (projectiveToricEquivRealGrowth u).val x = (projectiveToricCorrectedDescent u.val x).toReal := rfl

/-- The produced reverse map retains the exact original torus formula. -/
theorem projectiveToricEquivRealGrowth_symm_off
    (f : {f : EuclideanSpace ℝ (Fin 1) → ℝ //
      f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval})
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    (projectiveToricEquivRealGrowth.symm f).val p = projectiveToricOffPotential f.val p :=
  (projectiveToricExtension_spec f.val f.property).2 hp

/-- The third-class map is the literal original Legendre transform of the corrected descent. -/
theorem projectiveToricEquivClosedProper_apply
    (u : {u : Projectivization ℂ (Fin 2 → ℂ) → EReal //
      projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧ ProjectiveCircleInvariant u}) :
    (projectiveToricEquivClosedProper u).val = SGPT.Convex.conjugate
      (innerₗ (EuclideanSpace ℝ (Fin 1))) (projectiveToricCorrectedDescent u.val) := by
  change SGPT.Convex.conjugate (innerₗ (EuclideanSpace ℝ (Fin 1)))
      (fun x ↦ ((projectiveToricCorrectedDescent u.val x).toReal : EReal)) = _
  rw [← (projectiveToricCorrectedDescent_toReal_mem_realGrowthClass u.property.1 u.property.2).2]

/-- The inverse third-class map uses the actual reversed conjugate's finite
real values in the unchanged original torus formula. -/
theorem projectiveToricEquivClosedProper_symm_off
    (g : {g : EuclideanSpace ℝ (Fin 1) → EReal // g ∈ ClosedProperOnBody projectiveMomentInterval})
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    (projectiveToricEquivClosedProper.symm g).val p =
      (((SGPT.Convex.conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip g.val
        (tropicalization (projectiveModelChart false p))).toReal -
          projectiveFSPotential (projectiveModelChart false p) : ℝ) : EReal) := by
  let f := (realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin 1)))
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval convex_projectiveMomentInterval).symm g
  change projectiveToricExtension f.val f.property p = _
  rw [(projectiveToricExtension_spec f.val f.property).2 hp]
  rfl

end SGPT.Toric
