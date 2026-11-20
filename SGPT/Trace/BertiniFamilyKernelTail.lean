import SGPT.Trace.BertiniFamilyFiniteKernelHodge
import SGPT.Trace.BertiniFamilyCompactBackground

/-! Actual original compact off-tube kernel tail, with produced finite background. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalNormalRegularization SGPT.Trace.BertiniNativeNormalKernel

theorem residueKernel_le_away (s ρ ε : ℝ) (hs : 0 < s) (hρ : 0 < ρ) (hε : 0 < ε)
    (z : ℂ) (hz : s ≤ ‖z‖) : residueKernel ε (z / (ρ : ℂ)) ≤ ε / ((s / ρ) ^ 2) ^ 2 := by
  have hmod : s / ρ ≤ ‖z / (ρ : ℂ)‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]
    exact div_le_div_of_nonneg_right hz hρ.le
  have hc : 0 < (s / ρ) ^ 2 := sq_pos_of_pos (div_pos hs hρ)
  have hR : (s / ρ) ^ 2 ≤ ‖z / (ρ : ℂ)‖ ^ 2 :=
    (sq_le_sq₀ (div_pos hs hρ).le (norm_nonneg _)).mpr hmod
  have hden : ((s / ρ) ^ 2) ^ 2 ≤ (ε + ‖z / (ρ : ℂ)‖ ^ 2) ^ 2 :=
    (sq_le_sq₀ hc.le (add_pos_of_pos_of_nonneg hε (sq_nonneg _)).le).mpr
      (hR.trans (le_add_of_nonneg_left hε.le))
  exact div_le_div_of_nonneg_left hε.le (sq_pos_of_pos hc) hden

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

omit [IsComplexManifold (d + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem norm_scalarParameter (q : familyIncidence p i a v U) :
    ‖scalarParameter p i a v U q‖ = ‖q.val.1.val‖ :=
  modelOneScalarEquiv.norm_map q.val.1.val

def familyCutoffTailEnergy :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ) → (familyIncidence p i a v U → ℝ) → ℝ → ℝ → ℝ → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun S φ β ρ s ε => ∫⁻ q in {q : familyIncidence p i a v U | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s}ᶜ,
    ENNReal.ofReal (‖S q‖ ^ 2) *
      ((ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) * ENNReal.ofReal (β q)) *
        ENNReal.ofReal (Real.exp (-φ q))) ∂familyMatchedVolume p i a v U hsm

theorem familyCutoffTailEnergy_le :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (φ β : familyIncidence p i a v U → ℝ), (∀ q, β q ≤ 1) →
      ∀ (ρ s ε : ℝ), 0 < ρ → 0 < s → 0 < ε →
      familyCutoffTailEnergy p i a v U hsm L S φ β ρ s ε ≤
        ENNReal.ofReal (ε / ((s / ρ) ^ 2) ^ 2) *
          ∫⁻ q in tsupport β, ENNReal.ofReal (‖S q‖ ^ 2 * Real.exp (-φ q)) ∂familyMatchedVolume p i a v U hsm := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ β hβ ρ s ε hρ hs hε
  let A : Set (familyIncidence p i a v U) := {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s}
  let K := tsupport β
  let C := ENNReal.ofReal (ε / ((s / ρ) ^ 2) ^ 2)
  let M : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (‖S q‖ ^ 2 * Real.exp (-φ q))
  have hA : IsOpen A := Metric.isOpen_ball.preimage
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
  have hK : MeasurableSet K := (isClosed_tsupport β).measurableSet
  have hpoint (q : familyIncidence p i a v U) (hq : q ∈ Aᶜ) :
      ENNReal.ofReal (‖S q‖ ^ 2) *
        ((ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) * ENNReal.ofReal (β q)) *
          ENNReal.ofReal (Real.exp (-φ q))) ≤ C * K.indicator M q := by
    by_cases hqK : q ∈ K
    · have hmod : s ≤ ‖scalarParameter p i a v U q‖ := by
        rw [norm_scalarParameter p i a v U]
        change ¬ q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s at hq
        simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hq
      have hk := ENNReal.ofReal_le_ofReal (residueKernel_le_away s ρ ε hs hρ hε _ hmod)
      have hb : ENNReal.ofReal (β q) ≤ 1 := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hβ q)
      rw [Set.indicator_of_mem hqK]
      dsimp only [M]
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      calc
        _ ≤ ENNReal.ofReal (‖S q‖ ^ 2) * ((C * 1) * ENNReal.ofReal (Real.exp (-φ q))) :=
          mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hk hb) le_rfl)
        _ = _ := by simp only [mul_one]; ac_rfl
    · have hz : β q = 0 := image_eq_zero_of_notMem_tsupport hqK
      simp only [hz,ENNReal.ofReal_zero,mul_zero,zero_mul,Set.indicator_of_notMem hqK]
      exact le_rfl
  calc
    _ ≤ ∫⁻ q in Aᶜ, C * K.indicator M q ∂familyMatchedVolume p i a v U hsm :=
      setLIntegral_mono' hA.measurableSet.compl hpoint
    _ ≤ ∫⁻ q, C * K.indicator M q ∂familyMatchedVolume p i a v U hsm := setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [lintegral_const_mul' C _ ENNReal.ofReal_ne_top,lintegral_indicator hK]

theorem familyCutoffTailEnergy_tendsto_zero :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ β : familyIncidence p i a v U → ℝ), Continuous φ → HasCompactSupport β → (∀ q, β q ≤ 1) →
      ∀ (ρ s : ℝ), 0 < ρ → 0 < s →
      Tendsto (fun ε : ℝ => familyCutoffTailEnergy p i a v U hsm L S φ β ρ s ε) (𝓝[>] 0) (𝓝 0) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ β hφ hβc hβ ρ s hρ hs
  let M := ∫⁻ q in tsupport β, ENNReal.ofReal (‖S q‖ ^ 2 * Real.exp (-φ q)) ∂familyMatchedVolume p i a v U hsm
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hM : M < ⊤ := familyPhysical_compact_weighted_energy_lt_top p i a v U hsm L _ hβc.isCompact S hS φ hφ
  let c : ℝ := (((s / ρ) ^ 2) ^ 2)⁻¹ * M.toReal
  have hbound (ε : ℝ) (hε : 0 < ε) : familyCutoffTailEnergy p i a v U hsm L S φ β ρ s ε ≤ ENNReal.ofReal (ε * c) := by
    calc
      _ ≤ ENNReal.ofReal (ε / ((s / ρ) ^ 2) ^ 2) * M :=
        familyCutoffTailEnergy_le p i a v U hsm L S φ β hβ ρ s ε hρ hs hε
      _ = ENNReal.ofReal (ε / ((s / ρ) ^ 2) ^ 2) * ENNReal.ofReal M.toReal :=
        congrArg (fun t => ENNReal.ofReal (ε / ((s / ρ) ^ 2) ^ 2) * t) (ENNReal.ofReal_toReal hM.ne).symm
      _ = ENNReal.ofReal (ε * c) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hε.le (sq_nonneg _))]
        congr 1
        dsimp only [c]
        rw [div_eq_mul_inv,mul_assoc]
  have hreal : Tendsto (fun ε : ℝ => ε * c) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq,zero_mul] using ((continuous_id.mul_const c).tendsto (0 : ℝ)).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hupper : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε * c)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hbound ε hε

end SGPT.Trace.BertiniFamilyCanonical
