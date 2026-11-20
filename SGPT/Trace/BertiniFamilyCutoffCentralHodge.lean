import SGPT.Trace.BertiniFamilyCutoffKernelIntegral
import SGPT.Trace.BertiniFamilyNormalResidueIntegral

/-! Actual global physical normal kernel residue is the SAME intrinsic original member Hodge energy. -/
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
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.BertiniNativeNormalKernel

private theorem actualNormalSlice_compactSupport {d : ℕ} {g : ComplexModel (d + 1) → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun u : ComplexModel d => g (normalProductEquiv d (u,0))) := by
  let P : ComplexModel (d + 1) → ComplexModel d := fun z => ((normalProductEquiv d).symm z).1
  have hK : IsCompact (P '' tsupport g) := hg.isCompact.image
    (continuous_fst.comp (normalProductEquiv d).symm.continuous)
  refine HasCompactSupport.intro hK fun u hu => ?_
  by_contra hne
  apply hu
  refine ⟨normalProductEquiv d (u,0),subset_tsupport g hne,?_⟩
  exact congrArg Prod.fst ((normalProductEquiv d).symm_apply_apply (u,0))

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

def familyCutoffMemberHodgeEnergy (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →
      (familyIncidence p i a v U → ℝ) → (familyIncidence p i a v U → ℝ) → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  letI : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  letI : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  exact fun S φ β => nativePhysicalHodgeEnergy
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))
    (familyNativeMemberAdjunctionSection p i a v U hsm L t S)
    (fun y => ENNReal.ofReal (β (familyMemberLift p i a v U hsm t y)) *
      ENNReal.ofReal (Real.exp (-φ (familyMemberLift p i a v U hsm t y))))

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyNormalTest_central_integral_eq_memberHodge :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ β : familyIncidence p i a v U → ℝ), Continuous φ → Continuous β →
      HasCompactSupport β → tsupport β ⊆ F.ambSource → (∀ q, 0 ≤ β q) →
      ∀ (t : U), t.val 0 = 0 →
      ENNReal.ofReal (∫ u : ComplexModel d, familyNormalTestDensity p i a v U hsm L F S φ
        (flatDataCoordinateCutoff F β) (normalProductEquiv d (u,0))) =
      familyCutoffMemberHodgeEnergy p i a v U hsm L t S φ β := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S φ β hφ hβ hβc hβs hβ0 t ht
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))
  let S₀ := familyNativeMemberAdjunctionSection p i a v U hsm L t S
  let w : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (β q) * ENNReal.ofReal (Real.exp (-φ q))
  let v₀ : member p (affinePoint i (a - t.val 0 • v)) → ℝ≥0∞ := fun y => w (familyMemberLift p i a v U hsm t y)
  let χ := flatDataCoordinateCutoff F β
  let T : ComplexModel (d + 1) → ℝ := familyNormalTestDensity p i a v U hsm L F S φ χ
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hsource : (familyNormalMemberSource p i a v U hsm F t : Set _).indicator v₀ = v₀ := by
    funext y
    by_cases hy : y ∈ familyNormalMemberSource p i a v U hsm F t
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy]
      have hy' : familyMemberLift p i a v U hsm t y ∉ F.ambSource := hy
      have hz : β (familyMemberLift p i a v U hsm t y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy' (hβs h))
      simp only [v₀,w,hz,ENNReal.ofReal_zero,zero_mul]
  have hbase := familyMemberPhysicalEnergy_normalResidue p i a v U hsm L F hF t S w
  change nativePhysicalHodgeEnergy LH S₀ ((familyNormalMemberSource p i a v U hsm F t : Set _).indicator v₀) = _ at hbase
  rw [hsource] at hbase
  have hD (u : ComplexModel d) : u ∈ familyNormalSliceDomain p i a v U hsm F t ↔ normalProductEquiv d (u,0) ∈ F.flat.target := by
    change normalProductEquiv d (u,t.val 0) ∈ F.flat.target ↔ _
    rw [ht]
  have hpoint (z : ComplexModel (d + 1)) (hz : z ∈ F.flat.target) : ENNReal.ofReal (T z) =
      familyNormalPhysicalDensity p i a v U hsm L F S w z := by
    have hreal := familyNormalRealDensity_ofReal p i a v U hsm L F S φ z hz
    rw [familyNormalPhysicalDensity_eq_value p i a v U hsm L F S _ z hz] at hreal
    dsimp only [T,χ]
    unfold familyNormalTestDensity flatDataCoordinateCutoff
    rw [if_pos hz,if_pos hz,ENNReal.ofReal_mul (hβ0 (finv F z)),hreal,
      familyNormalPhysicalDensity_eq_value p i a v U hsm L F S w z hz]
    dsimp only [w]
    ac_rfl
  have hsupp : Function.support (fun u : ComplexModel d => ENNReal.ofReal (T (normalProductEquiv d (u,0)))) ⊆
      familyNormalSliceDomain p i a v U hsm F t := by
    intro u hu
    by_contra hnot
    have hzt : normalProductEquiv d (u,0) ∉ F.flat.target := fun h => hnot ((hD u).mpr h)
    exact hu (by simp only [T,familyNormalTestDensity,if_neg hzt,ENNReal.ofReal_zero])
  have henergy : nativePhysicalHodgeEnergy LH S₀ v₀ =
      ∫⁻ u : ComplexModel d, ENNReal.ofReal (T (normalProductEquiv d (u,0))) ∂volume := by
    apply hbase.trans
    calc
      _ = ∫⁻ u in familyNormalSliceDomain p i a v U hsm F t,
          ENNReal.ofReal (T (normalProductEquiv d (u,0))) ∂volume := by
        apply setLIntegral_congr_fun (familyNormalSliceDomain p i a v U hsm F t).isOpen.measurableSet
        intro u hu
        have hz := (hD u).mp hu
        have heq := congrArg (fun τ : ℂ => familyNormalPhysicalDensity p i a v U hsm L F S w
          (normalProductEquiv d (u,τ))) ht
        exact heq.trans (hpoint _ hz).symm
      _ = _ := setLIntegral_eq_of_support_subset hsupp
  have hs := flatDataCoordinateCutoff_support F β hβc hβs
  have hTc : Continuous T := familyNormalTestDensity_continuous p i a v U hsm L F S hS φ hφ χ
    (flatDataCoordinateCutoff_continuous F β hβ hβc hβs) (hs.1.trans hs.2.2)
  have hTK : HasCompactSupport T := familyNormalTestDensity_compactSupport p i a v U hsm L F S φ χ
    (flatDataCoordinateCutoff_compactSupport F β hβc hβs)
  have hi : Integrable (fun u : ComplexModel d => T (normalProductEquiv d (u,0))) volume :=
    (hTc.comp ((normalProductEquiv d).continuous.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      (actualNormalSlice_compactSupport hTK)
  have hn : ∀ u : ComplexModel d, 0 ≤ T (normalProductEquiv d (u,0)) := fun u =>
    familyNormalTestDensity_nonneg p i a v U hsm L F S φ χ (flatDataCoordinateCutoff_nonneg F β hβ0) _
  have hr := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)
  exact hr.trans henergy.symm

theorem familyCutoffKernelEnergy_limit_memberHodge :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y)
      (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (φ β : familyIncidence p i a v U → ℝ), Continuous φ → Continuous β →
      HasCompactSupport β → tsupport β ⊆ F.ambSource → (∀ q, 0 ≤ β q) →
      ∀ (t : U), t.val 0 = 0 → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun ε : ℝ => familyCutoffKernelEnergy p i a v U hsm L S φ β ρ ε) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyCutoffMemberHodgeEnergy p i a v U hsm L t S φ β)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S φ β hφ hβ hβc hβs hβ0 t ht ρ hρ
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have h := familyCutoffKernelEnergy_limit p i a v U hsm L F hF S hS φ β hφ hβ hβc hβs hβ0 ρ hρ
  rw [ENNReal.ofReal_mul (by positivity),familyNormalTest_central_integral_eq_memberHodge p i a v U hsm L F hF S φ β hφ hβ hβc hβs hβ0 t ht] at h
  exact h

end SGPT.Trace.BertiniFamilyCanonical
