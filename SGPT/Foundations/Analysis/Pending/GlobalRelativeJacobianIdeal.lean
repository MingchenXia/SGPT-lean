import SGPT.Foundations.Analysis.Pending.AnalyticModificationPreferredJacobianTest
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicMultiplierGermCovariance


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps
  DivisorialChangeOfVariables AnalyticModificationLocalDiscrepancy
  BlowupFlatCoordinates

universe u

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hF : DifferentiableOn ℂ F D) :
    DifferentiableOn ℂ (complexJacobian F) D := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) D :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hD
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ D).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The literal actual coordinate determinant, read as a function on the original source. -/
def chartJacobianFunction (π : Y → X) (a : Y) (b : X) : Y → ℂ := fun z =>
  complexJacobian (coordinateMap π (complexChartAt (n := n) a) (complexChartAt (n := n) b))
    ((complexChartAt (n := n) a).val z)

/-- Dimension zero retains the literal empty determinant ONE, without a geometry premise. -/
theorem chartJacobianFunction_zero_dim {X0 Y0 : Type u}
    [TopologicalSpace X0] [ChartedSpace (ComplexModel 0) X0]
    [TopologicalSpace Y0] [ChartedSpace (ComplexModel 0) Y0]
    (π : Y0 → X0) (a : Y0) (b : X0) :
    chartJacobianFunction (n := 0) π a b = fun _ => 1 := by
  funext z
  change LinearMap.det ((fderiv ℂ
    (coordinateMap π (complexChartAt (n := 0) a) (complexChartAt (n := 0) b))
      ((complexChartAt (n := 0) a).val z)).toLinearMap) = 1
  exact LinearMap.det_eq_one_of_subsingleton _

theorem holomorphicAt_chartJacobianFunction {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (a : Y) (b : X) {y : Y}
    (hy : y ∈ (complexChartAt (n := n) a).val.source)
    (hπy : π y ∈ (complexChartAt (n := n) b).val.source) :
    HolomorphicAt n (chartJacobianFunction (n := n) π a b) y := by
  let e := complexChartAt (n := n) a
  let d := complexChartAt (n := n) b
  have hz : e.val y ∈ coordinateDomain π e d := by
    refine ⟨e.val.map_source hy, ?_⟩
    change π (e.val.symm (e.val y)) ∈ d.val.source
    simpa only [e.val.left_inv hy] using hπy
  have hD := coordinateDomain_isOpen hπ e d
  have hJ := differentiableOn_complexJacobian hD
    ((coordinateMap_contDiffOn hπ e d).differentiableOn (by simp))
  apply CartanLocalReduction.holomorphicAt_comp_chart hy
  filter_upwards [hD.mem_nhds hz] with z hzD
  exact hJ.differentiableAt (hD.mem_nhds hzD)

private def actualTransitionEquiv {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (e e' : ComplexChart n M) (y : M) (hy : y ∈ e.val.source) (hy' : y ∈ e'.val.source) :
    LocalHolomorphicEquivAt (n := n) (e.val y) where
  source := (chartTransition e e').source
  target := (chartTransition e e').target
  isOpen_source := (chartTransition e e').open_source
  isOpen_target := (chartTransition e e').open_target
  center_mem_source := by
    change e.val y ∈ e.val.target ∧ e.val.symm (e.val y) ∈ e'.val.source
    refine ⟨e.val.map_source hy, ?_⟩
    simpa only [e.val.left_inv hy] using hy'
  toFun := chartTransition e e'
  invFun := (chartTransition e e').symm
  toFun_holomorphic := fun z hz =>
    ((chartTransition_contDiffAt e e' hz).differentiableAt (by simp)).differentiableWithinAt
  invFun_holomorphic := by
    intro z hz
    have hz' : z ∈ (chartTransition e' e).source := hz
    exact ((chartTransition_contDiffAt e' e hz').differentiableAt (by simp)).differentiableWithinAt
  mapsTo_toFun := fun _ hz => (chartTransition e e').map_source hz
  mapsTo_invFun := fun _ hz => (chartTransition e e').map_target hz
  left_inv := fun _ hz => (chartTransition e e').left_inv hz
  right_inv := fun _ hz => (chartTransition e e').right_inv hz

private theorem transition_jacobian_holomorphic_and_ne_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (a a' y : M) (hy : y ∈ (complexChartAt (n := n) a).val.source)
    (hy' : y ∈ (complexChartAt (n := n) a').val.source) :
    HolomorphicAt n (fun z => complexJacobian
      (chartTransition (complexChartAt (n := n) a) (complexChartAt (n := n) a'))
      ((complexChartAt (n := n) a).val z)) y ∧
    complexJacobian (chartTransition (complexChartAt (n := n) a) (complexChartAt (n := n) a'))
      ((complexChartAt (n := n) a).val y) ≠ 0 := by
  obtain ⟨hJ, _hJinv, hJ0, _hJinv0⟩ :=
    LocalHolomorphicMultiplierGermCovariance.jacobian_units_of_local_holomorphic_equiv
      (actualTransitionEquiv (complexChartAt (n := n) a) (complexChartAt (n := n) a') y hy hy')
  exact ⟨CartanLocalReduction.holomorphicAt_comp_chart hy hJ, hJ0⟩

private theorem complexJacobian_change_target {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (e : ComplexChart n Y) (d d' : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain π e d) (hz' : z ∈ coordinateDomain π e d') :
    complexJacobian (coordinateMap π e d') z =
      complexJacobian (chartTransition d d') (coordinateMap π e d z) *
        complexJacobian (coordinateMap π e d) z := by
  have heq : coordinateMap π e d' =ᶠ[𝓝 z] (chartTransition d d') ∘ coordinateMap π e d := by
    filter_upwards [(coordinateDomain_isOpen hπ e d).mem_nhds hz] with w hw
    exact coordinateMap_change_target hw
  have hτ := (chartTransition_contDiffAt d d'
    (coordinateMap_mem_transition_source hz hz')).differentiableAt (by simp)
  have hF := (coordinateMap_contDiffAt hπ e d hz).differentiableAt (by simp)
  simp only [complexJacobian]
  rw [heq.fderiv_eq, fderiv_comp z hτ hF, ContinuousLinearMap.det]
  change LinearMap.det ((fderiv ℂ (chartTransition d d') (coordinateMap π e d z)).toLinearMap.comp
    (fderiv ℂ (coordinateMap π e d) z).toLinearMap) = _
  exact LinearMap.det_comp _ _

private theorem complexJacobian_change_source {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (e e' : ComplexChart n Y) (d : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e e').source) (hzπ : z ∈ coordinateDomain π e d) :
    complexJacobian (coordinateMap π e d) z =
      complexJacobian (coordinateMap π e' d) (chartTransition e e' z) *
        complexJacobian (chartTransition e e') z := by
  have heq : coordinateMap π e d =ᶠ[𝓝 z] (coordinateMap π e' d) ∘ chartTransition e e' := by
    filter_upwards [(chartTransition e e').open_source.mem_nhds hz] with w hw
    exact coordinateMap_change_source hw
  have hF := (coordinateMap_contDiffAt hπ e' d
    (coordinateDomain_change_source hz hzπ)).differentiableAt (by simp)
  have hτ := (chartTransition_contDiffAt e e' hz).differentiableAt (by simp)
  simp only [complexJacobian]
  rw [heq.fderiv_eq, fderiv_comp z hF hτ, ContinuousLinearMap.det]
  change LinearMap.det ((fderiv ℂ (coordinateMap π e' d) (chartTransition e e' z)).toLinearMap.comp
    (fderiv ℂ (chartTransition e e') z).toLinearMap) = _
  exact LinearMap.det_comp _ _

/-- Actual chart round trips manufacture the original holomorphic unit; J(pi) may be zero. -/
theorem exists_chartJacobian_unit_eq {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (a a' : Y) (b b' : X) (y : Y)
    (hy : y ∈ (complexChartAt (n := n) a).val.source)
    (hy' : y ∈ (complexChartAt (n := n) a').val.source)
    (hπy : π y ∈ (complexChartAt (n := n) b).val.source)
    (hπy' : π y ∈ (complexChartAt (n := n) b').val.source) :
    ∃ U : Y → ℂ, HolomorphicAt n U y ∧ U y ≠ 0 ∧
      chartJacobianFunction (n := n) π a b =ᶠ[𝓝 y] fun z => U z * chartJacobianFunction (n := n) π a' b' z := by
  let e := complexChartAt (n := n) a
  let e' := complexChartAt (n := n) a'
  let d := complexChartAt (n := n) b
  let d' := complexChartAt (n := n) b'
  let S : Y → ℂ := fun z => complexJacobian (chartTransition e e') (e.val z)
  let T : X → ℂ := fun x => complexJacobian (chartTransition d' d) (d'.val x)
  obtain ⟨hS, hS0⟩ := transition_jacobian_holomorphic_and_ne_zero a a' y hy hy'
  obtain ⟨hT, hT0⟩ := transition_jacobian_holomorphic_and_ne_zero b' b (π y) hπy' hπy
  refine ⟨fun z => T (π z) * S z,
    (hT.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt)).mul hS,
    mul_ne_zero hT0 hS0, ?_⟩
  filter_upwards [e.val.open_source.mem_nhds hy, e'.val.open_source.mem_nhds hy',
    hπ.continuous.continuousAt.eventually (d.val.open_source.mem_nhds hπy),
    hπ.continuous.continuousAt.eventually (d'.val.open_source.mem_nhds hπy')]
      with z hze hze' hzd hzd'
  have hzD : e.val z ∈ coordinateDomain π e d := by
    refine ⟨e.val.map_source hze, ?_⟩
    change π (e.val.symm (e.val z)) ∈ d.val.source
    rw [e.val.left_inv hze]
    exact hzd
  have hzD' : e.val z ∈ coordinateDomain π e d' := by
    refine ⟨e.val.map_source hze, ?_⟩
    change π (e.val.symm (e.val z)) ∈ d'.val.source
    rw [e.val.left_inv hze]
    exact hzd'
  have hzS : e.val z ∈ (chartTransition e e').source := by
    refine ⟨e.val.map_source hze, ?_⟩
    change e.val.symm (e.val z) ∈ e'.val.source
    simpa only [e.val.left_inv hze] using hze'
  have hcoord : coordinateMap π e d' (e.val z) = d'.val (π z) := by
    change d'.val (π (e.val.symm (e.val z))) = d'.val (π z)
    rw [e.val.left_inv hze]
  have hσ : chartTransition e e' (e.val z) = e'.val z := by
    change e'.val (e.val.symm (e.val z)) = e'.val z
    rw [e.val.left_inv hze]
  have ht := complexJacobian_change_target hπ e d' d hzD' hzD
  have hs := complexJacobian_change_source hπ e e' d' hzS hzD'
  change complexJacobian (coordinateMap π e d) (e.val z) =
    (complexJacobian (chartTransition d' d) (d'.val (π z)) *
      complexJacobian (chartTransition e e') (e.val z)) *
        complexJacobian (coordinateMap π e' d') (e'.val z)
  rw [ht, hcoord, hs, hσ]
  ring

/-- The original principal germ ideal, defined by literal preferred-pair Jacobians. -/
def relativeJacobianIdeal (π : Y → X) : GermIdeal n Y where
  mem y f := IsInSpanAt (n := n) (· = chartJacobianFunction (n := n) π y (π y)) y f

/-- Every actual fixed chart pair generates the SAME original whole membership stalk. -/
theorem mem_relativeJacobianIdeal_iff_chart {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (a : Y) (b : X) {y : Y}
    (hy : y ∈ (complexChartAt (n := n) a).val.source)
    (hπy : π y ∈ (complexChartAt (n := n) b).val.source) (f : Y → ℂ) :
    (relativeJacobianIdeal (n := n) π).mem y f ↔ IsInSpanAt (n := n) (· = chartJacobianFunction (n := n) π a b) y f := by
  obtain ⟨U, hU, hU0, heq⟩ := exists_chartJacobian_unit_eq (n := n) hπ y a (π y) b y
    (mem_complexChartAt_source y) hy (mem_complexChartAt_source (π y)) hπy
  change IsInSpanAt (n := n) (· = chartJacobianFunction (n := n) π y (π y)) y f ↔ _
  rw [isInSpanAt_eq_iff, isInSpanAt_eq_iff]
  constructor
  · rintro ⟨hf, c, hc, hfc⟩
    refine ⟨hf, fun z => c z * U z, hc.mul hU, ?_⟩
    filter_upwards [hfc, heq] with z hz hJ
    rw [hz, hJ]
    ring
  · rintro ⟨hf, c, hc, hfc⟩
    have hUinv : HolomorphicAt n (fun z => (U z)⁻¹) y :=
      BlowupFlatCoordinates.HolomorphicAt.inv (n := n) hU hU0
    refine ⟨hf, fun z => c z * (U z)⁻¹, hc.mul hUinv, ?_⟩
    filter_upwards [hfc, heq, hU.continuousAt.eventually_ne hU0] with z hz hJ hUne
    rw [hz, hJ]
    field_simp

theorem isCoherent_relativeJacobianIdeal {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) :
    (relativeJacobianIdeal (n := n) π).IsCoherent := by
  intro y
  let U := (complexChartAt (n := n) y).val.source ∩
    π ⁻¹' (complexChartAt (n := n) (π y)).val.source
  have hU : IsOpen U := (complexChartAt (n := n) y).val.open_source.inter
    ((complexChartAt (n := n) (π y)).val.open_source.preimage hπ.continuous)
  refine ⟨U, hU, ⟨mem_complexChartAt_source y, mem_complexChartAt_source (π y)⟩,
    1, fun _ => chartJacobianFunction (n := n) π y (π y), ?_, ?_⟩
  · intro i z hz
    exact (holomorphicAt_chartJacobianFunction (n := n) hπ y (π y) hz.1 hz.2).mdifferentiableAt.mdifferentiableWithinAt
  · intro z hz f
    simpa only [range_const, mem_singleton_iff] using
      mem_relativeJacobianIdeal_iff_chart (n := n) hπ y (π y) hz.1 hz.2 f

/-- Actual modification noncollapse gives frequent nonzero values for EVERY real chart-pair function. -/
theorem frequently_chartJacobianFunction_ne_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (a : Y) (b : X) (y : Y)
    (hy : y ∈ (complexChartAt (n := n) a).val.source)
    (hπy : π y ∈ (complexChartAt (n := n) b).val.source) :
    ∃ᶠ z in 𝓝 y, chartJacobianFunction (n := n) π a b z ≠ 0 := by
  have hlocal : ∃ᶠ z in 𝓝 y, chartJacobianFunction (n := n) π y (π y) z ≠ 0 := by
    have hJ : ∃ᶠ w in 𝓝 ((complexChartAt (n := n) y).val y),
        complexJacobian (coordinateMap π (complexChartAt (n := n) y)
          (complexChartAt (n := n) (π y))) w ≠ 0 := by
      simpa only [one_mul] using
        (AnalyticModificationPreferredJacobianTest.frequently_preferred_jacobian_test_ne_zero
          hπ y (g := fun _ => (1 : ℂ))
          (Eventually.of_forall fun _ => differentiableAt_const 1)
          ((Eventually.of_forall fun _ => one_ne_zero).frequently))
    by_contra hnone
    have hzero : ∀ᶠ z in 𝓝 y, chartJacobianFunction (n := n) π y (π y) z = 0 := by
      simpa only [not_ne_iff] using Filter.not_frequently.mp hnone
    let e := complexChartAt (n := n) y
    have ht : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
      simpa only [e.val.left_inv (mem_complexChartAt_source y)] using
        (e.val.continuousAt_symm (e.val.map_source (mem_complexChartAt_source y))).tendsto
    have hzero' : ∀ᶠ w in 𝓝 (e.val y),
        complexJacobian (coordinateMap π e (complexChartAt (n := n) (π y))) w = 0 := by
      filter_upwards [ht.eventually hzero,
        e.val.open_target.mem_nhds (e.val.map_source (mem_complexChartAt_source y))] with w hw hwT
      change complexJacobian (coordinateMap π e (complexChartAt (n := n) (π y)))
        (e.val (e.val.symm w)) = 0 at hw
      rwa [e.val.right_inv hwT] at hw
    obtain ⟨w, hw, hw0⟩ := (hJ.and_eventually hzero').exists
    exact hw hw0
  obtain ⟨U, _hU, _hU0, hEq⟩ := exists_chartJacobian_unit_eq (n := n) hπ.1 y a (π y) b y
    (mem_complexChartAt_source y) hy (mem_complexChartAt_source (π y)) hπy
  exact (hlocal.and_eventually hEq).mono fun z hz hzero => hz.1 (by
    rw [hz.2]
    change U z * chartJacobianFunction (n := n) π a b z = 0
    rw [hzero, mul_zero])

theorem isInvertible_relativeJacobianIdeal_of_isAnalyticModification {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) : (relativeJacobianIdeal (n := n) π).IsInvertible := by
  intro y
  let U := (complexChartAt (n := n) y).val.source ∩
    π ⁻¹' (complexChartAt (n := n) (π y)).val.source
  have hU : IsOpen U := (complexChartAt (n := n) y).val.open_source.inter
    ((complexChartAt (n := n) (π y)).val.open_source.preimage hπ.1.continuous)
  refine ⟨U, hU, ⟨mem_complexChartAt_source y, mem_complexChartAt_source (π y)⟩,
    chartJacobianFunction (n := n) π y (π y), ?_, ?_, ?_⟩
  · intro z hz
    exact (holomorphicAt_chartJacobianFunction (n := n) hπ.1 y (π y) hz.1 hz.2).mdifferentiableAt.mdifferentiableWithinAt
  · intro W hW hWU hWne
    obtain ⟨z, hz⟩ := hWne
    have hzU := hWU hz
    have hfreq := frequently_chartJacobianFunction_ne_zero (n := n) hπ y (π y) z hzU.1 hzU.2
    obtain ⟨w, hw, hwW⟩ := (hfreq.and_eventually (hW.mem_nhds hz)).exists
    exact ⟨w, hwW, hw⟩
  · intro z hz f
    exact mem_relativeJacobianIdeal_iff_chart (n := n) hπ.1 y (π y) hz.1 hz.2 f

/-- The actual global divisor is manufactured from the literal original ideal and genuine modification geometry. -/
def actualRelativeJacobianDivisor {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    EffectiveDivisor n Y := ⟨relativeJacobianIdeal (n := n) π, isInvertible_relativeJacobianIdeal_of_isAnalyticModification (n := n) hπ⟩

theorem actualRelativeJacobianDivisor_ideal_eq {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    (actualRelativeJacobianDivisor (n := n) hπ).ideal = relativeJacobianIdeal (n := n) π := rfl

end SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal
