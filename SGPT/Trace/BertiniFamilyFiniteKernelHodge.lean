import SGPT.Trace.BertiniFamilyCutoffCentralHodge
import SGPT.Trace.BertiniHodgeWeightLinearity

/-! Produced ORIGINAL compact kernel limit has FULL intrinsic original member Hodge residue. -/
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
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalProductNormalResidue

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem familyCutoffKernelEnergy_sum {ι : Type} [Fintype ι] :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ : familyIncidence p i a v U → ℝ), Continuous φ →
      ∀ (β : ι → familyIncidence p i a v U → ℝ), (∀ j, Continuous (β j)) → (∀ j q, 0 ≤ β j q) →
      ∀ (ρ ε : ℝ), 0 < ε →
      familyCutoffKernelEnergy p i a v U hsm L S φ (fun q => ∑ j, β j q) ρ ε =
        ∑ j, familyCutoffKernelEnergy p i a v U hsm L S φ (β j) ρ ε := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ hφ β hβ hβ0 ρ ε hε
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hnorm := familyPhysical_normSq_measurable p i a v U hsm L S hS
  have hf : Continuous (fun q : familyIncidence p i a v U => scalarParameter p i a v U q / (ρ : ℂ)) :=
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm).continuous.div_const _
  have hker := (ENNReal.continuous_ofReal.comp ((continuous_residueKernel hε).comp hf)).measurable
  have hw := (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hφ.neg)).measurable
  unfold familyCutoffKernelEnergy
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hβ0 j _),Finset.mul_sum,Finset.sum_mul,Finset.mul_sum]
  apply lintegral_finsetSum'
  intro j _
  exact (hnorm.mul ((hker.mul (ENNReal.continuous_ofReal.comp (hβ j)).measurable).mul hw)).aemeasurable

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyCutoffMemberHodgeEnergy_partition {ι : Type} [Fintype ι] :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ : familyIncidence p i a v U → ℝ), Continuous φ →
      ∀ (β : ι → familyIncidence p i a v U → ℝ), (∀ j, Continuous (β j)) → (∀ j q, 0 ≤ β j q) →
      ∀ (t : U), (∀ y : member p (affinePoint i (a - t.val 0 • v)), ∑ j, β j (familyMemberLift p i a v U hsm t y) = 1) →
      familyCutoffMemberHodgeEnergy p i a v U hsm L t S φ (fun _ => 1) =
        ∑ j, familyCutoffMemberHodgeEnergy p i a v U hsm L t S φ (β j) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S φ hφ β hβ hβ0 t hsum
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))
  let S₀ := familyNativeMemberAdjunctionSection p i a v U hsm L t S
  let l := familyMemberLift p i a v U hsm t
  let w := fun y => ENNReal.ofReal (Real.exp (-φ (l y)))
  let α : ι → member p (affinePoint i (a - t.val 0 • v)) → ℝ≥0∞ := fun j y => ENNReal.ofReal (β j (l y))
  have hw : Measurable w := (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (hφ.comp l.contMDiff.continuous).neg)).measurable
  have hα (j : ι) : Measurable (α j) := (ENNReal.continuous_ofReal.comp ((hβ j).comp l.contMDiff.continuous)).measurable
  have hαsum (y : member p (affinePoint i (a - t.val 0 • v))) : ∑ j, α j y = 1 := by
    change (∑ j, ENNReal.ofReal (β j (l y))) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hβ0 j _),hsum y,ENNReal.ofReal_one]
  have h := nativePhysicalHodgeEnergy_weight_partition LH S₀ w hw α hα hαsum
  simpa only [familyCutoffMemberHodgeEnergy,ENNReal.ofReal_one,one_mul] using h

theorem exists_family_compact_kernel_hodge_limit (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (r : ℝ) (β : familyIncidence p i a v U → ℝ),
      0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      IsCompact (familyClosedParameterCollar p i a v U r) ∧ Continuous β ∧ HasCompactSupport β ∧
      (∀ q, 0 ≤ β q ∧ β q ≤ 1) ∧ (∀ q ∈ familyClosedParameterCollar p i a v U (r / 2), β q = 1) ∧
      ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
        (φ : familyIncidence p i a v U → ℝ), Continuous φ →
        familyCutoffMemberHodgeEnergy p i a v U hsm L ⟨0,h0⟩ S φ (fun _ => 1) < ⊤ ∧
        ∀ ρ : ℝ, 0 < ρ →
        Tendsto (fun ε : ℝ => familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε) (𝓝[>] 0)
          (𝓝 (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyCutoffMemberHodgeEnergy p i a v U hsm L ⟨0,h0⟩ S φ (fun _ => 1))) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨k,F,r,ψ,hr,hrU,hrK,hF,hψ,hψc,hψs,hsum,hone⟩ := exists_family_finite_real_normal_cutoffs p i a v U hsm h0
  let β : familyIncidence p i a v U → ℝ := fun q => ∑ j, ψ j q
  have hβ : Continuous β := continuous_finsetSum _ (fun j _ => (ψ j).contMDiff.continuous)
  have hβc : HasCompactSupport β := by
    have heq : (∑ j, (ψ j : familyIncidence p i a v U → ℝ)) = β := by
      funext q
      simp only [Finset.sum_apply]
      rfl
    rw [← heq]
    exact HasCompactSupport.finset_sum (fun j _ => hψc j)
  have hβ0 (q : familyIncidence p i a v U) : 0 ≤ β q := Finset.sum_nonneg (fun j _ => hψ j q)
  refine ⟨r,β,hr,hrU,hrK,hβ,hβc,fun q => ⟨hβ0 q,hsum q⟩,hone,?_⟩
  intro S φ hφ
  let t0 : U := ⟨0,h0⟩
  have ht0 : t0.val 0 = (0 : ℂ) := rfl
  have hcentral : ∀ y : member p (affinePoint i (a - t0.val 0 • v)), ∑ j, ψ j (familyMemberLift p i a v U hsm t0 y) = 1 := by
    intro y
    apply hone
    change (0 : ComplexModel 1) ∈ Metric.closedBall (0 : ComplexModel 1) (r / 2)
    exact Metric.mem_closedBall_self (by positivity)
  have hpart := familyCutoffMemberHodgeEnergy_partition p i a v U hsm L S φ hφ
    (fun j q => ψ j q) (fun j => (ψ j).contMDiff.continuous) hψ t0 hcentral
  have hfinite : familyCutoffMemberHodgeEnergy p i a v U hsm L t0 S φ (fun _ => 1) < ⊤ := by
    rw [hpart]
    apply ENNReal.sum_lt_top.mpr
    intro j _
    rw [← familyNormalTest_central_integral_eq_memberHodge p i a v U hsm L (F j) (hF j) S φ (ψ j)
      hφ (ψ j).contMDiff.continuous (hψc j) (hψs j) (hψ j) t0 ht0]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfinite,?_⟩
  intro ρ hρ
  have hlim := tendsto_finsetSum Finset.univ (fun j _ => familyCutoffKernelEnergy_limit_memberHodge p i a v U hsm L
    (F j) (hF j) S φ (ψ j) hφ (ψ j).contMDiff.continuous (hψc j) (hψs j) (hψ j) t0 ht0 ρ hρ)
  rw [← Finset.mul_sum,← hpart] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (familyCutoffKernelEnergy_sum p i a v U hsm L S φ hφ
    (fun j q => ψ j q) (fun j => (ψ j).contMDiff.continuous) hψ ρ ε hε).symm

end SGPT.Trace.BertiniFamilyCanonical
