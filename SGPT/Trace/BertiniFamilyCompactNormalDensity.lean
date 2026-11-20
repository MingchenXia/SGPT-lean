import SGPT.Trace.BertiniFamilyNormalPhysical
import SGPT.Trace.BertiniNativeNormalKernel

/-! Actual continuous compact physical normal tests, built from original data. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel SGPT.Trace.OptimalNormalResidueKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

def familyNormalRealDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)}, FlatData (d + 1) d (familyIncidence p i a v U) W →
      (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ) → ComplexModel (d + 1) → ℝ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun _ F S ψ z => |(fderiv ℝ F.flat.symm z).det| *
    (familyMatchedCoordinateDensity p i a v U hsm F.amb (F.flat.symm z) * ‖S (finv F z)‖ ^ 2) *
    Real.exp (-ψ (finv F z))

theorem familyNormalRealDensity_nonneg :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (ψ : familyIncidence p i a v U → ℝ) (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      0 ≤ familyNormalRealDensity p i a v U hsm L F S ψ z := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S ψ z hz
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg
    (familyMatchedCoordinateDensity_pos p i a v U hsm F.amb _ (F.flat_source_subset (F.flat.map_target hz))).le
    (sq_nonneg _))) (Real.exp_pos _).le

theorem familyNormalRealDensity_ofReal :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (ψ : familyIncidence p i a v U → ℝ) (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      ENNReal.ofReal (familyNormalRealDensity p i a v U hsm L F S ψ z) =
        familyNormalPhysicalDensity p i a v U hsm L F S (fun q => ENNReal.ofReal (Real.exp (-ψ q))) z := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S ψ z hz
  have ht := F.flat_source_subset (F.flat.map_target hz)
  have hρ := (familyMatchedCoordinateDensity_pos p i a v U hsm F.amb _ ht).le
  have hn := familyPhysicalCoordinate_norm_density p i a v U hsm L F.amb (finv F z) (finv_mem F hz).1 (S (finv F z))
  have hr : familyMatchedCoordinateDensity p i a v U hsm F.amb (F.flat.symm z) * ‖S (finv F z)‖ ^ 2 =
      ‖familyPhysicalCoordinateEquiv p i a v U hsm L F.amb (finv F z) (finv_mem F hz).1 (S (finv F z))‖ ^ 2 := by
    unfold familyMatchedCoordinateDensity
    rw [dif_pos ht, mul_comm]
    exact hn
  unfold familyNormalRealDensity familyNormalPhysicalDensity familyPhysicalCoordinateDensity
  rw [dif_pos ht, ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (mul_nonneg hρ (sq_nonneg _))),
    ENNReal.ofReal_mul (abs_nonneg _), hr, mul_assoc]
  rfl

theorem familyNormalRealDensity_continuousOn :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (ψ : familyIncidence p i a v U → ℝ), Continuous ψ →
      ContinuousOn (familyNormalRealDensity p i a v U hsm L F S ψ) F.flat.target := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS ψ hψ
  have hflat : ContDiffOn ℝ 1 F.flat.symm F.flat.target :=
    ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat_symm F.flat.open_target).restrict_scalars ℝ).of_le (by simp)
  have hfd : ContinuousOn (fderiv ℝ F.flat.symm) F.flat.target :=
    hflat.continuousOn_fderiv_of_isOpen F.flat.open_target le_rfl
  have hJ : ContinuousOn (fun z => |(fderiv ℝ F.flat.symm z).det|) F.flat.target :=
    (ContinuousLinearMap.continuous_det.continuousOn.comp hfd (mapsTo_univ _ _)).abs
  have hρ := (familyMatchedCoordinateDensity_smooth p i a v U hsm F.amb).continuousOn.comp
    F.flat.continuousOn_symm (fun z hz => F.flat_source_subset (F.flat.map_target hz))
  have hn : Continuous (fun q => ‖S q‖) := continuousOn_univ.mp
    (ContinuousFiberNorm.continuous.comp_continuousOn hS.continuousOn)
  have hSn := (hn.comp_continuousOn (continuousOn_finv F)).pow 2
  have hψn := Real.continuous_exp.comp_continuousOn
    ((hψ.comp_continuousOn (continuousOn_finv F)).neg)
  exact (hJ.mul (hρ.mul hSn)).mul hψn

def familyNormalTestDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)}, FlatData (d + 1) d (familyIncidence p i a v U) W →
      (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ) → (ComplexModel (d + 1) → ℝ) → ComplexModel (d + 1) → ℝ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun _ F S ψ χ z => if z ∈ F.flat.target then χ z * familyNormalRealDensity p i a v U hsm L F S ψ z else 0

theorem familyNormalTestDensity_continuous :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (ψ : familyIncidence p i a v U → ℝ), Continuous ψ →
      ∀ (χ : ComplexModel (d + 1) → ℝ), Continuous χ → tsupport χ ⊆ F.flat.target →
      Continuous (familyNormalTestDensity p i a v U hsm L F S ψ χ) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS ψ hψ χ hχ hsub
  have hr := familyNormalRealDensity_continuousOn p i a v U hsm L F S hS ψ hψ
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ F.flat.target
  · apply (hχ.continuousAt.mul (hr.continuousAt (F.flat.open_target.mem_nhds hz))).congr_of_eventuallyEq
    filter_upwards [F.flat.open_target.mem_nhds hz] with y hy
    exact if_pos hy
  · have hzsupport : z ∉ tsupport χ := fun h => hz (hsub h)
    apply (continuousAt_const : ContinuousAt (fun _ : ComplexModel (d + 1) => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzsupport] with y hy
    have hy0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    unfold familyNormalTestDensity
    by_cases hyt : y ∈ F.flat.target <;> simp only [hyt, ↓reduceIte, hy0, zero_mul]

theorem familyNormalTestDensity_compactSupport :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (ψ : familyIncidence p i a v U → ℝ) (χ : ComplexModel (d + 1) → ℝ),
      HasCompactSupport χ → HasCompactSupport (familyNormalTestDensity p i a v U hsm L F S ψ χ) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S ψ χ hχ
  apply HasCompactSupport.intro hχ.isCompact
  intro z hz
  have hz0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
  unfold familyNormalTestDensity
  by_cases hzt : z ∈ F.flat.target <;> simp only [hzt, ↓reduceIte, hz0, zero_mul]

theorem familyNormalTest_kernel_limit :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (ψ : familyIncidence p i a v U → ℝ), Continuous ψ →
      ∀ (χ : ComplexModel (d + 1) → ℝ), Continuous χ → HasCompactSupport χ → tsupport χ ⊆ F.flat.target →
      ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun ε : ℝ => ∫ z : ComplexModel (d + 1), residueKernel ε (z (Fin.last d) / (ρ : ℂ)) *
        familyNormalTestDensity p i a v U hsm L F S ψ χ z) (𝓝[>] 0)
        (𝓝 (Real.pi * ρ ^ 2 * ∫ u : ComplexModel d,
          familyNormalTestDensity p i a v U hsm L F S ψ χ (normalProductEquiv d (u, 0)))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS ψ hψ χ hχ hχc hsub ρ hρ
  exact tendsto_integral_native_scaled_normal hρ
    (familyNormalTestDensity_continuous p i a v U hsm L F S hS ψ hψ χ hχ hsub)
    (familyNormalTestDensity_compactSupport p i a v U hsm L F S ψ χ hχc)

end SGPT.Trace.BertiniFamilyCanonical
