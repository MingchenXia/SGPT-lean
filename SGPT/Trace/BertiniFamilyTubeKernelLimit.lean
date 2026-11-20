import SGPT.Trace.BertiniFamilyKernelTail

/-! Internally produced FULL actual smaller-tube kernel/Hodge limit in the ORIGINAL matched measure. -/
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
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.OptimalNormalResidueKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

def familyTubeKernelEnergy :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ) → ℝ → ℝ → ℝ → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun S φ ρ s ε => ∫⁻ q in {q : familyIncidence p i a v U | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s},
    ENNReal.ofReal (‖S q‖ ^ 2) *
      (ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) *
        ENNReal.ofReal (Real.exp (-φ q))) ∂familyMatchedVolume p i a v U hsm

theorem familyTubeKernelEnergy_add_tail :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (φ β : familyIncidence p i a v U → ℝ) (ρ s ε : ℝ),
      (∀ q, q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s → β q = 1) →
      familyTubeKernelEnergy p i a v U hsm L S φ ρ s ε + familyCutoffTailEnergy p i a v U hsm L S φ β ρ s ε =
        familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ β ρ s ε hβone
  let A : Set (familyIncidence p i a v U) := {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s}
  have hA : IsOpen A := Metric.isOpen_ball.preimage
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
  have hi : familyTubeKernelEnergy p i a v U hsm L S φ ρ s ε =
      ∫⁻ q in A, ENNReal.ofReal (‖S q‖ ^ 2) *
        ((ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) * ENNReal.ofReal (β q)) *
          ENNReal.ofReal (Real.exp (-φ q))) ∂familyMatchedVolume p i a v U hsm := by
    apply setLIntegral_congr_fun hA.measurableSet
    intro q hq
    let n : ℝ≥0∞ := ENNReal.ofReal (‖S q‖ ^ 2)
    let k : ℝ≥0∞ := ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ)))
    let w : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-φ q))
    change n * (k * w) = n * ((k * ENNReal.ofReal (β q)) * w)
    rw [hβone q hq,ENNReal.ofReal_one,mul_one]
  rw [hi]
  exact lintegral_add_compl _ hA.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyCutoffMemberHodgeEnergy_one_originalWeight :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (t : U) (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber) (u : X → ℝ),
      familyCutoffMemberHodgeEnergy p i a v U hsm L t S (fun q => u q.val.2) (fun _ => 1) =
        familyNativeMemberHodgeEnergy p i a v U hsm L (fun x => (u x : EReal)) t S := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro t S u
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))
  let S₀ := familyNativeMemberAdjunctionSection p i a v U hsm L t S
  change nativePhysicalHodgeEnergy LH S₀ _ = nativePhysicalHodgeEnergy LH S₀ _
  congr 1
  funext y
  simp only [ENNReal.ofReal_one,one_mul,multiplierWeight_coe]
  rfl

private theorem actualTailFinite :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ β : familyIncidence p i a v U → ℝ), Continuous φ → HasCompactSupport β → (∀ q, β q ≤ 1) →
      ∀ (ρ s ε : ℝ), 0 < ρ → 0 < s → 0 < ε →
      familyCutoffTailEnergy p i a v U hsm L S φ β ρ s ε < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ β hφ hβc hβ ρ s ε hρ hs hε
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  exact (familyCutoffTailEnergy_le p i a v U hsm L S φ β hβ ρ s ε hρ hs hε).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (familyPhysical_compact_weighted_energy_lt_top p i a v U hsm L _ hβc.isCompact S hS φ hφ))

private theorem actualTubeLimit :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ β : familyIncidence p i a v U → ℝ), Continuous φ → HasCompactSupport β → (∀ q, β q ≤ 1) →
      ∀ (ρ s : ℝ), 0 < ρ → 0 < s →
      (∀ q, q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) s → β q = 1) →
      ∀ C : ℝ≥0∞, Tendsto (fun ε : ℝ => familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε) (𝓝[>] 0) (𝓝 C) →
      Tendsto (fun ε : ℝ => familyTubeKernelEnergy p i a v U hsm L S φ ρ s ε) (𝓝[>] 0) (𝓝 C) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ β hφ hβc hβ ρ s hρ hs hβone C hlim
  have ht := familyCutoffTailEnergy_tendsto_zero p i a v U hsm L S φ β hφ hβc hβ ρ s hρ hs
  have h := ENNReal.Tendsto.sub hlim ht (Or.inr ENNReal.zero_ne_top)
  rw [tsub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hf := (actualTailFinite p i a v U hsm L S φ β hφ hβc hβ ρ s ε hρ hs hε).ne
  rw [← familyTubeKernelEnergy_add_tail p i a v U hsm L S φ β ρ s ε hβone]
  exact ENNReal.add_sub_cancel_right hf

theorem exists_family_tube_kernel_hodge_limit (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
        (u : X → ℝ), Continuous u →
        familyNativeMemberHodgeEnergy p i a v U hsm L (fun x => (u x : EReal)) ⟨0,h0⟩ S < ⊤ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 →
        (∀ ε : ℝ, 0 < ε → familyTubeKernelEnergy p i a v U hsm L S (fun q => u q.val.2) ρ ρ ε < ⊤) ∧
        Tendsto (fun ε : ℝ => familyTubeKernelEnergy p i a v U hsm L S (fun q => u q.val.2) ρ ρ ε) (𝓝[>] 0)
          (𝓝 (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyNativeMemberHodgeEnergy p i a v U hsm L
            (fun x => (u x : EReal)) ⟨0,h0⟩ S)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨r,β,hr,hrU,_hrK,_hβ,hβc,hβrange,hβone,hall⟩ := exists_family_compact_kernel_hodge_limit p i a v U hsm L h0
  refine ⟨r,hr,hrU,?_⟩
  intro S u hu
  have hφ : Continuous (fun q : familyIncidence p i a v U => u q.val.2) := hu.comp (continuous_snd.comp continuous_subtype_val)
  obtain ⟨hfinite,hlim⟩ := hall S (fun q => u q.val.2) hφ
  rw [familyCutoffMemberHodgeEnergy_one_originalWeight p i a v U hsm L] at hfinite
  refine ⟨hfinite,?_⟩
  intro ρ hρ hρr
  have hρhalf : ρ ≤ r / 2 := by linarith
  have hρfull : ρ ≤ r := by linarith
  have hρU : Metric.closedBall (0 : ComplexModel 1) ρ ⊆ U := (Metric.closedBall_subset_closedBall hρfull).trans hrU
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  refine ⟨?_,?_⟩
  · intro ε hε
    have h := familyPhysical_parameter_tube_kernel_energy_lt_top p i a v U hsm L ρ ρ ε hε hρU S hS u hu
    unfold familyTubeKernelEnergy
    apply lt_of_le_of_lt ?_ h
    apply lintegral_mono
    intro q
    let n : ℝ := ‖S q‖ ^ 2
    let k : ℝ := residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))
    let w : ℝ := Real.exp (-u q.val.2)
    have hn : 0 ≤ n := sq_nonneg _
    have hk : 0 ≤ k := residueKernel_nonneg hε.le _
    change ENNReal.ofReal n * (ENNReal.ofReal k * ENNReal.ofReal w) ≤ ENNReal.ofReal (k * n * w)
    apply le_of_eq
    rw [ENNReal.ofReal_mul (mul_nonneg hk hn),ENNReal.ofReal_mul hk]
    ac_rfl
  · have h := actualTubeLimit p i a v U hsm L S (fun q => u q.val.2) β hφ hβc (fun q => (hβrange q).2)
      ρ ρ hρ hρ (fun q hq => hβone q (Metric.closedBall_subset_closedBall hρhalf (Metric.ball_subset_closedBall hq))) _ (hlim ρ hρ)
    rw [familyCutoffMemberHodgeEnergy_one_originalWeight p i a v U hsm L] at h
    exact h

end SGPT.Trace.BertiniFamilyCanonical
