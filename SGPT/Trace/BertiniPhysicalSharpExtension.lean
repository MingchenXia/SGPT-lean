import SGPT.Trace.BertiniFamilyPreliminaryNormalization
import SGPT.Trace.BertiniPhysicalAuxiliaryMargin
import SGPT.Trace.BertiniOriginalWeightPencilLimit

/-! Actual singular physical sharp extension with produced kernel/Hodge
normalization; original auxiliary curvature chosen after manufactured loss. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalNativeNormalWeight
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNormalEpsilonLimit
open SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalExtensionODE
open SGPT.Trace.BertiniDiscExhaustion SGPT.Trace.TwistedL2
open SGPT.Trace.BertiniOriginalWeightPencilLimit

section Generic
variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

theorem nativePhysicalHodgeEnergy_weight_mono [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (L : HermitianHolomorphicLineBundle n Y)
    (S : ∀ y, (tensor (nativeCanonicalBundle (n := n) (X := Y)) L).Fiber y)
    (w w' : Y → ℝ≥0∞) (h : ∀ y, w y ≤ w' y) :
    nativePhysicalHodgeEnergy L S w ≤ nativePhysicalHodgeEnergy L S w' := by
  classical
  unfold nativePhysicalHodgeEnergy nativeCanonicalPartitionEnergy
  apply Finset.sum_le_sum
  intro j _
  apply lintegral_mono
  intro z
  unfold nativeCanonicalPhysicalCoordinateDensity
  split_ifs with hz
  · exact mul_le_mul' le_rfl (h _)
  · exact le_rfl

def nativeSectionOfHolomorphicOn (B : HermitianHolomorphicLineBundle.{0,0} n Y)
    (F : ∀ y, B.Fiber y)
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) B.Fiber F univ) :
    HolomorphicSections (n := n) B.Fiber := by
  refine {toFun := F,contMDiff_toFun := ?_}
  intro y
  let e : AtlasFrame B := ⟨trivializationAt ℂ B.Fiber y,inferInstance⟩
  let := e.property
  have he : y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  apply (e.val.contMDiffAt_section_iff he).mpr
  apply contMDiffAt_of_eventually_mdifferentiableAt
  filter_upwards [e.val.open_baseSet.mem_nhds he] with z hz
  exact (e.val.mdifferentiableAt_section_iff 𝓘(ℂ, ComplexModel n) F hz).mp
    ((mdifferentiableOn_univ.mp hF) z)
end Generic

section Family
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyNativeMemberHodgeEnergy_potential_antitone
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (φ ψ : X → EReal)
    (h : ∀ x, φ x ≤ ψ x) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
      familyNativeMemberHodgeEnergy p i a v U hsm L ψ t S ≤
        familyNativeMemberHodgeEnergy p i a v U hsm L φ t S := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  intro S
  unfold familyNativeMemberHodgeEnergy nativeBertiniMemberHodgeEnergy
  apply nativePhysicalHodgeEnergy_weight_mono
  intro y
  exact multiplierWeight_antitone (c := 1) zero_le_one (h y.val)
end Family

variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_original_physical_hodge_sharp_extension
    (omega : KahlerBackground (d + 1) X) (φ : X → EReal)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hL : IsSourceSmoothHermitianMetric L) (κ : ℝ), 0 < κ →
      (∀ (c : ComplexChart (d + 1) X) (z : ComplexModel (d + 1)), z ∈ c.val.target →
        ∀ w : ComplexModel (d + 1), (C + κ) * omega.form.val.coeff c z ![w,Complex.I • w] ≤
          (sourceNativeFirstChernForm L hL).val.coeff c z ![w,Complex.I • w]) →
      ∀ (N : ℕ)
        (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
        (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
        (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
        (h0 : (0 : ComplexModel 1) ∈ U),
      letI := familyChartedSpace p i a v U p.contMDiff hsm
      letI := isComplexManifold_family p i a v U p.contMDiff hsm
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∃ hVU : parameterDisc ρ ≤ U,
        letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        ∀ (σ δ : ℝ), 0 < σ → 0 < δ →
        ∀ F : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
          familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F < ⊤ →
        ∃ S : HolomorphicSections (n := d + 1)
          (familyNativePhysicalModel p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber,
          (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 →
            S q = familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L F q) ∧
          (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
            (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
            ‖S q‖ ^ 2) * multiplierWeight 1 (φ q.val.2)
            ∂familyMatchedVolume p i a v (parameterDisc ρ)
              (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)) ≤
            ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (Real.pi * ρ ^ 2) *
              familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F) := by
  obtain ⟨C,u,hC,hu,_hmono,hdom,_hlim,_hpsh,hpipe⟩ :=
    exists_original_qpsh_manufactured_pencil_pipeline omega φ hφ
  refine ⟨C,hC,?_⟩
  intro L hL κ hκ hchern N p i a v U hsm h0
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨r,hr,hrU,hkernel⟩ := exists_family_preliminary_kernel_hodge_limit p i a v U hsm L h0
  refine ⟨r,hr,hrU,?_⟩
  intro ρ hρ hρr
  obtain ⟨hVU,hsmall⟩ := hkernel ρ hρ hρr
  refine ⟨hVU,?_⟩
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro σ δ hσ hδ F hfinite
  let B := familyNativePhysicalModel p i a v (parameterDisc ρ) hsV L
  let μ := familyMatchedVolume p i a v (parameterDisc ρ) hsV
  let F₀ := familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L F
  have hF₀ : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1) B.Fiber F₀ univ :=
    (F₀.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεwithin : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε,Eventually.of_forall hεpos⟩
  have hm : 0 ≤ windowMass σ + δ := (windowMass_pos hσ).le.trans (le_add_of_nonneg_right hδ.le)
  let J : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (windowMass σ + δ) *
    (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyNativeMemberHodgeEnergy p i a v U hsm L
      (fun x => (u j x : EReal)) ⟨0,h0⟩ F)
  let I : ℝ≥0∞ := ENNReal.ofReal (windowMass σ + δ) *
    (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F)
  have hI : I < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)
  have hJlim (j : ℕ) : Tendsto (fun k => actualPreliminaryKernelEnergy B μ
      (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) (fun q => u j q.val.2) (ε k) σ δ F₀)
      atTop (𝓝 (J j)) :=
    ((hsmall F (u j) (continuous_of_chartSmooth' (hu j)) σ δ hm).2.2).comp hεwithin
  have hJbound (j : ℕ) : J j ≤ I := mul_le_mul' le_rfl
    (mul_le_mul' le_rfl (familyNativeMemberHodgeEnergy_potential_antitone p i a v U hsm L
      φ (fun x => (u j x : EReal)) (hdom j) ⟨0,h0⟩ F))
  obtain ⟨S,hS,htrace,henergy⟩ := hpipe N p i a v ρ σ δ hρ hσ hδ p.contMDiff hsV κ hκ B μ
    (familyMatchedVolume_smoothPositive p i a v (parameterDisc ρ) hsV)
    (familyNativePhysicalModel_smooth p i a v (parameterDisc ρ) hsV L hL)
    (familyPhysical_raw_curvature_of_original omega L hL (C + κ) hchern p i a v (parameterDisc ρ) hsV)
    F₀ hF₀ ε hεpos hε J hJlim I hI hJbound
  exact ⟨nativeSectionOfHolomorphicOn B S hS,htrace,henergy⟩

end SGPT.Trace.BertiniFamilyCanonical
