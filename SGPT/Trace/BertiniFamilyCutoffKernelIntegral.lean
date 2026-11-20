import SGPT.Trace.BertiniFamilyNormalCutoffCoordinates
import SGPT.Trace.BertiniFamilyCompactNormalDensity

/-! Actual original GLOBAL matched-volume compact-cutoff kernel integral and physical limit. -/
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
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

def familyCutoffKernelEnergy :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ) → (familyIncidence p i a v U → ℝ) → ℝ → ℝ → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun S φ β ρ ε => ∫⁻ q, ENNReal.ofReal (‖S q‖ ^ 2) *
    ((ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) * ENNReal.ofReal (β q)) *
      ENNReal.ofReal (Real.exp (-φ q))) ∂familyMatchedVolume p i a v U hsm

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyNormalTestDensity_nonneg :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (φ : familyIncidence p i a v U → ℝ) (χ : ComplexModel (d + 1) → ℝ),
      (∀ z, 0 ≤ χ z) → ∀ z, 0 ≤ familyNormalTestDensity p i a v U hsm L F S φ χ z := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S φ χ hχ z
  unfold familyNormalTestDensity
  split_ifs with hz
  · exact mul_nonneg (hχ z) (familyNormalRealDensity_nonneg p i a v U hsm L F S φ z hz)
  · exact le_rfl

omit [MeasurableSpace X] [BorelSpace X] in
private theorem actualNormalDensity_mul :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (b w : familyIncidence p i a v U → ℝ≥0∞) (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      familyNormalPhysicalDensity p i a v U hsm L F S (fun q => b q * w q) z =
        b (finv F z) * familyNormalPhysicalDensity p i a v U hsm L F S w z := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S b w z hz
  rw [familyNormalPhysicalDensity_eq_value p i a v U hsm L F S _ z hz,
    familyNormalPhysicalDensity_eq_value p i a v U hsm L F S w z hz]
  ac_rfl

theorem familyCutoffKernelEnergy_eq_integral :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (φ β : familyIncidence p i a v U → ℝ), Continuous φ → Continuous β →
      HasCompactSupport β → tsupport β ⊆ F.ambSource → (∀ q, 0 ≤ β q) →
      ∀ (ρ ε : ℝ), 0 < ρ → 0 < ε →
      familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε =
        ENNReal.ofReal (∫ z : ComplexModel (d + 1), residueKernel ε (z (Fin.last d) / (ρ : ℂ)) *
          familyNormalTestDensity p i a v U hsm L F S φ (flatDataCoordinateCutoff F β) z) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S hS φ β hφ hβ hβc hβs hβ0 ρ ε hρ hε
  let χ := flatDataCoordinateCutoff F β
  let b : familyIncidence p i a v U → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) * ENNReal.ofReal (β q)
  let w : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (-φ q))
  let G : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (‖S q‖ ^ 2) * (b q * w q)
  let H : ComplexModel (d + 1) → ℝ≥0∞ := fun z => ENNReal.ofReal
    (residueKernel ε (z (Fin.last d) / (ρ : ℂ)) * familyNormalTestDensity p i a v U hsm L F S φ χ z)
  have hscalar : Continuous (fun q : familyIncidence p i a v U => scalarParameter p i a v U q / (ρ : ℂ)) :=
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm).continuous.div_const _
  have hker : Continuous (fun q : familyIncidence p i a v U => residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) := by
    unfold residueKernel normalKernel
    apply continuous_const.div ((continuous_const.add (hscalar.norm.pow 2)).pow 2)
    intro q
    exact pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg _)))
  have hb : Measurable b := (ENNReal.continuous_ofReal.comp hker).measurable.mul (ENNReal.continuous_ofReal.comp hβ).measurable
  have hw : Measurable w := (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hφ.neg)).measurable
  have hGs : Function.support G ⊆ F.ambSource := by
    intro q hq
    by_contra hqs
    have hβzero : β q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hqs (hβs h))
    exact hq (by simp only [G,b,hβzero,ENNReal.ofReal_zero,mul_zero,zero_mul])
  have hHs : Function.support H ⊆ F.flat.target := by
    intro z hz
    by_contra hzt
    exact hz (by simp only [H,familyNormalTestDensity,if_neg hzt,mul_zero,ENNReal.ofReal_zero])
  have hpoint (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) :
      familyNormalPhysicalDensity p i a v U hsm L F S (fun q => b q * w q) z = H z := by
    have hτ := hF (finv F z) (finv_mem F hz)
    rw [fcoord_finv F hz] at hτ
    rw [actualNormalDensity_mul p i a v U hsm L F S b w z hz,
      ← familyNormalRealDensity_ofReal p i a v U hsm L F S φ z hz]
    dsimp only [b,H,χ]
    rw [← hτ]
    unfold familyNormalTestDensity flatDataCoordinateCutoff
    rw [if_pos hz,if_pos hz,ENNReal.ofReal_mul (residueKernel_nonneg hε.le _),
      ENNReal.ofReal_mul (hβ0 (finv F z))]
    ac_rfl
  have hchange := familyPhysical_energy_in_flatData p i a v U hsm L F S hS (fun q => b q * w q) (hb.mul hw)
  have hmeasure : familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε = ∫⁻ z, H z ∂volume := by
    calc
      _ = ∫⁻ q in F.ambSource, G q ∂familyMatchedVolume p i a v U hsm :=
        (setLIntegral_eq_of_support_subset hGs).symm
      _ = ∫⁻ z in F.flat.target, familyNormalPhysicalDensity p i a v U hsm L F S (fun q => b q * w q) z ∂volume := hchange
      _ = ∫⁻ z in F.flat.target, H z ∂volume := setLIntegral_congr_fun F.flat.open_target.measurableSet hpoint
      _ = _ := setLIntegral_eq_of_support_subset hHs
  have hχ := flatDataCoordinateCutoff_continuous F β hβ hβc hβs
  have hχc := flatDataCoordinateCutoff_compactSupport F β hβc hβs
  have hs := flatDataCoordinateCutoff_support F β hβc hβs
  have hχs : tsupport χ ⊆ F.flat.target := hs.1.trans hs.2.2
  have hχ0 := flatDataCoordinateCutoff_nonneg F β hβ0
  have htest := familyNormalTestDensity_continuous p i a v U hsm L F S hS φ hφ χ hχ hχs
  have htestc := familyNormalTestDensity_compactSupport p i a v U hsm L F S φ χ hχc
  have hint := integrable_native_scaled_normal hρ hε htest htestc
  apply hmeasure.trans
  exact (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun z => mul_nonneg
    (residueKernel_nonneg hε.le _) (familyNormalTestDensity_nonneg p i a v U hsm L F S φ χ hχ0 z)))).symm

theorem familyCutoffKernelEnergy_limit :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (φ β : familyIncidence p i a v U → ℝ), Continuous φ → Continuous β →
      HasCompactSupport β → tsupport β ⊆ F.ambSource → (∀ q, 0 ≤ β q) →
      ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun ε : ℝ => familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.pi * ρ ^ 2 * ∫ u : ComplexModel d,
          familyNormalTestDensity p i a v U hsm L F S φ (flatDataCoordinateCutoff F β) (normalProductEquiv d (u,0))))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S hS φ β hφ hβ hβc hβs hβ0 ρ hρ
  let χ := flatDataCoordinateCutoff F β
  have hs := flatDataCoordinateCutoff_support F β hβc hβs
  have hlim := familyNormalTest_kernel_limit p i a v U hsm L F S hS φ hφ χ
    (flatDataCoordinateCutoff_continuous F β hβ hβc hβs)
    (flatDataCoordinateCutoff_compactSupport F β hβc hβs) (hs.1.trans hs.2.2) ρ hρ
  have h := (ENNReal.continuous_ofReal.tendsto _).comp hlim
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (familyCutoffKernelEnergy_eq_integral p i a v U hsm L F hF S hS φ β hφ hβ hβc hβs hβ0 ρ ε hρ hε).symm

end SGPT.Trace.BertiniFamilyCanonical
