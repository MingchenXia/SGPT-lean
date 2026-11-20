import SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPolarCatalog
import SGPT.Foundations.Analysis.Pending.ActualOriginalPotentialOverlapSmoothDifference

/-! Actual preferred-chart original weak analytic readers of ANY signed current.
The mathematical statement and ENTIRE proof precede the import baseline. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
namespace SGPT.Foundations.Analysis.Pending.ActualPreferredOriginalCurrentAnalyticReader
open FirstPass FirstPass.HolomorphicMaps CanonicalCurrentFrame
  ActualQuasiPshPotentialSmoothCompatibility ActualWeakAnalyticCurrentPotentialAtlas
  ActualOriginalCurrentPolarCatalog
open _root_.SGPT.Foundations.Analysis.LocalCurrents
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem genuine_transition_pullback
    (e f : ComplexChart (m + 1) M) {U P : Opens (ComplexModel (m + 1))}
    {v : ComplexModel (m + 1) → EReal} (hv : LocalQuasiPshPotentialOn v P)
    (hs : (U : Set _) ⊆ (chartTransition e f).source)
    (hP : MapsTo (chartTransition e f) U P) :
    LocalQuasiPshPotentialOn (fun z => v (chartTransition e f z)) U := by
  let F := chartTransition e f
  have hF : ContDiffOn ℂ ∞ F U := fun x hx =>
    (chartTransition_contDiffAt e f (hs hx)).contDiffWithinAt
  refine ⟨U.isOpen, ?_, ?_⟩
  · intro x hx
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic U.isOpen hF hx
      (hv.2.1 (F x) (hP hx))
  · intro x hx A hA hxA
    let B := F.target ∩ F.symm ⁻¹' (A ∩ U)
    have hB : IsOpen B := F.symm.isOpen_inter_preimage (hA.inter U.isOpen)
    have hxB : F x ∈ B := by
      refine ⟨F.map_source (hs hx), ?_⟩
      change F.symm (F x) ∈ A ∩ U
      rw [F.left_inv (hs hx)]
      exact ⟨hxA, hx⟩
    obtain ⟨y, hy, hne⟩ := hv.2.2 (F x) (hP hx) B hB hxB
    refine ⟨F.symm y, ⟨hy.2.2.2, hy.2.2.1⟩, ?_⟩
    change v (F (F.symm y)) ≠ ⊥
    rwa [F.right_inv hy.2.1]

private theorem adjoint_transition_integral
    (e f : ComplexChart (m + 1) M)
    (η : TestForm (overlapSource e f)
      (Module.finrank ℝ (ComplexModel (m + 1)) - (degreeTwo (Nat.succ_pos m)).val))
    (ζ : TestForm (overlapTarget e f)
      (Module.finrank ℝ (ComplexModel (m + 1)) - (degreeTwo (Nat.succ_pos m)).val))
    (hrel : OverlapTestRelated e f η ζ) (v : ComplexModel (m + 1) → EReal) :
    ∫ x, DDCOverlap.ddcAdjoint
        (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η x *
        (v (chartTransition e f x)).toReal ∂volume =
      ∫ y, DDCOverlap.ddcAdjoint
        (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) ζ y *
        (v y).toReal ∂volume := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let B := currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
  have hderiv (x : ComplexModel (m + 1)) (hx : x ∈ F.source) :
      HasFDerivAt F (D x) x :=
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  have hae := DDCOverlap.ddcAdjoint_overlap_ae B volume e f η ζ hrel
  calc
    ∫ x, DDCOverlap.ddcAdjoint B η x * (v (F x)).toReal ∂volume =
        ∫ x in F.source, DDCOverlap.ddcAdjoint B η x * (v (F x)).toReal ∂volume := by
      rw [← integral_indicator F.open_source.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ F.source
      · simp [hx]
      · have hxt : x ∉ tsupport (DDCOverlap.ddcAdjoint B η) := fun h =>
          hx ((DDCOverlap.ddcAdjoint B η).tsupport_subset h)
        simp [hx, image_eq_zero_of_notMem_tsupport hxt]
    _ = ∫ x in F.source, |(D x).det| •
        (DDCOverlap.ddcAdjoint B ζ (F x) * (v (F x)).toReal) ∂volume := by
      refine setIntegral_congr_ae F.open_source.measurableSet ?_
      filter_upwards [hae] with x hx hxS
      rw [sub_eq_zero.mp (hx hxS), smul_eq_mul, mul_assoc]
    _ = ∫ y in F.target, DDCOverlap.ddcAdjoint B ζ y * (v y).toReal ∂volume :=
      (integral_target_eq_integral_abs_det_fderiv_smul volume hderiv
        (fun y => DDCOverlap.ddcAdjoint B ζ y * (v y).toReal)).symm
    _ = ∫ y, DDCOverlap.ddcAdjoint B ζ y * (v y).toReal ∂volume := by
      rw [← integral_indicator F.open_target.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ F.target
      · simp [hy]
      · have hyt : y ∉ tsupport (DDCOverlap.ddcAdjoint B ζ) := fun h =>
          hy ((DDCOverlap.ddcAdjoint B ζ).tsupport_subset h)
        simp [hy, image_eq_zero_of_notMem_tsupport hyt]

private theorem full_current_of_original_reading
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {Ω : Opens (ComplexModel (m + 1))}
    (hΩ : Ω ≤ chartTarget e) {u : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u Ω)
    (hread : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ) :
    T.restrictChart e hΩ = toLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (ddC (regularLocalQuasiPsh hu)) := by
  have hextract : fromLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (T.restrictChart e hΩ) =
        ddC (regularLocalQuasiPsh hu) := by
    ext w φ
    exact (GlobalCurrent.coefficients_restrictChart (canonicalBasis (m + 1))
      T e hΩ w φ).trans (hread w φ)
  rw [← hextract, CurrentPairing.toLocalCurrent_fromLocalCurrent]

private theorem reading_pullback
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e f : ComplexChart (m + 1) M) {P : Opens (ComplexModel (m + 1))}
    (hP : P ≤ chartTarget f) {u : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u P)
    (hread : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(P, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) f w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ) :
    let F := chartTransition e f
    let U : Opens (ComplexModel (m + 1)) :=
      ⟨chartTarget e ∩ (F.source ∩ F ⁻¹' P),
        (chartTarget e).isOpen.inter (F.isOpen_inter_preimage P.isOpen)⟩
    ∃ hv : LocalQuasiPshPotentialOn (fun x => u (F x)) U,
      ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
        T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
          ddC (regularLocalQuasiPsh hv) w φ := by
  intro F U
  have hUe : U ≤ chartTarget e := fun _ hx => hx.1
  have hUS : U ≤ overlapSource e f := fun _ hx => hx.2.1
  let hv := genuine_transition_pullback e f hu hUS (fun _ hx => hx.2.2)
  have hCu := full_current_of_original_reading T f hP hu hread
  refine ⟨hv, ?_⟩
  intro w φ
  let b := canonicalBasis (m + 1)
  let k := degreeTwo (Nat.succ_pos m)
  let B := currentPairingBasis b k
  let γ := contractVolume (basisVolume B) w
  let η := constantTestFormCLM γ φ
  obtain ⟨ζ, _hζsupp, _hζliteral, hζrel⟩ :=
    ActualChartOverlapTestTransport.exists_constant_form_counterpart e f (chartTarget e) P
      (Module.finrank ℝ (ComplexModel (m + 1)) - k.val) φ γ
  let ηS : TestForm (overlapSource e f) _ := TestFunction.monoCLM ℝ η
  let ζR : TestForm (overlapTarget e f) _ := TestFunction.monoCLM ℝ ζ
  have hrel : OverlapTestRelated e f ηS ζR := by
    intro x hx z
    rw [show ηS x = η x from testForm_inclusion_apply hUS η x,
      show ζR (F x) = ζ (F x) from testForm_inclusion_apply inf_le_right ζ (F x)]
    change φ x * γ z = _
    exact hζrel x hx z
  have hcurr : T.restrictChart e hUe η =
      T.restrictChart f hP (TestFunction.monoCLM ℝ ζ) := by
    have heq := T.overlap e f ηS ζR hrel
    have he : (TestFunction.monoCLM ℝ ηS : TestForm (chartTarget e) _) =
        TestFunction.monoCLM ℝ η := by
      ext x
      rw [testForm_inclusion_apply (overlapSource_le e f),
        testForm_inclusion_apply hUS, testForm_inclusion_apply hUe]
    have hf : (TestFunction.monoCLM ℝ ζR : TestForm (chartTarget f) _) =
        TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ ζ : TestForm P _) := by
      ext x
      rw [testForm_inclusion_apply (overlapTarget_le e f),
        testForm_inclusion_apply inf_le_right, testForm_inclusion_apply hP,
        testForm_inclusion_apply inf_le_left]
    change T.inChart e (TestFunction.monoCLM ℝ ηS) =
      T.inChart f (TestFunction.monoCLM ℝ ζR) at heq
    rw [he, hf] at heq
    exact heq
  have hpairu : T.restrictChart f hP (TestFunction.monoCLM ℝ ζ) =
      ∫ y, DDCOverlap.ddcAdjoint B ζR y * (u y).toReal ∂volume := by
    rw [hCu]
    change wedgePairing B (ddC (regularLocalQuasiPsh hu))
      (TestFunction.monoCLM ℝ ζ) = _
    rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [show DDCOverlap.ddcAdjoint B (TestFunction.monoCLM ℝ ζ : TestForm P _) y =
        DDCOverlap.ddcAdjoint B ζ y from DDCOverlap.ddcAdjoint_monoCLM_apply inf_le_left B ζ y,
        show DDCOverlap.ddcAdjoint B ζR y = DDCOverlap.ddcAdjoint B ζ y from
          DDCOverlap.ddcAdjoint_monoCLM_apply inf_le_right B ζ y]
  have hpairv : toLocalCurrent b k (ddC (regularLocalQuasiPsh hv)) η =
      ∫ x, DDCOverlap.ddcAdjoint B ηS x * (u (F x)).toReal ∂volume := by
    change wedgePairing B (ddC (regularLocalQuasiPsh hv)) η = _
    rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [show DDCOverlap.ddcAdjoint B ηS x = DDCOverlap.ddcAdjoint B η x from
        DDCOverlap.ddcAdjoint_monoCLM_apply hUS B η x]
  have hcov := adjoint_transition_integral e f ηS ζR hrel u
  have htest : T.restrictChart e hUe η =
      toLocalCurrent b k (ddC (regularLocalQuasiPsh hv)) η :=
    hcurr.trans (hpairu.trans (hcov.symm.trans hpairv.symm))
  change fromLocalCurrent b k (T.restrictChart e hUe) w φ =
    fromLocalCurrent b k (toLocalCurrent b k (ddC (regularLocalQuasiPsh hv))) w φ at htest
  rw [CurrentPairing.fromLocalCurrent_toLocalCurrent] at htest
  exact (GlobalCurrent.coefficients_restrictChart b T e hUe w φ).symm.trans htest

private theorem weak_analytic_pullback
    (e f : ComplexChart (m + 1) M) {u : ComplexModel (m + 1) → EReal}
    {x : ComplexModel (m + 1)} (hx : x ∈ (chartTransition e f).source)
    (han : HasAnalyticSingularitiesSmoothOffPoleAt u (chartTransition e f x)) :
    HasAnalyticSingularitiesSmoothOffPoleAt
      (fun z => u (chartTransition e f z)) x := by
  let F := chartTransition e f
  obtain ⟨c, N, g, hc, ⟨B, hBo, hxB, hg⟩, b, hb, hsm, hrep⟩ := han
  have hFt : Tendsto F (𝓝 x) (𝓝 (F x)) :=
    (chartTransition_contDiffAt_real e f hx).continuousAt.tendsto
  let R : Set (ComplexModel (m + 1)) := F.source ∩ F ⁻¹' B
  have hRo : IsOpen R := F.isOpen_inter_preimage hBo
  have hhol : HolomorphicGeneratorsAt (fun i z => g i (F z)) x := by
    refine ⟨R, hRo, ⟨hx, hxB⟩, ?_⟩
    intro i
    exact (hg i).comp
      (fun y hy => ((chartTransition_contDiffAt e f hy.1).differentiableAt
        (by simp)).differentiableWithinAt) (fun _ hy => hy.2)
  refine ⟨c, N, fun i z => g i (F z), hc, hhol, fun z => b (F z),
    hb.comp_continuousAt (chartTransition_contDiffAt_real e f hx).continuousAt, ?_, ?_⟩
  · filter_upwards [F.open_source.mem_nhds hx, hFt.eventually hsm] with y hy hby
    intro hnon
    have hnon' : generatorNormSq g (F y) ≠ 0 := hnon
    exact (hby hnon').comp y (chartTransition_contDiffAt_real e f hy)
  · filter_upwards [hFt.eventually hrep] with y hy
    exact hy

/-- The original natural local-potential condition itself supplies every
preferred-chart reader and its actual polar presentation, with full tests. -/
theorem exists_preferred_original_analytic_reader
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : HasWeakAnalyticLocalPotentials T) (p : M) :
    ∃ (U : Opens (ComplexModel (m + 1)))
      (_hU : U ≤ chartTarget (complexChartAt (n := m + 1) p))
      (v : ComplexModel (m + 1) → EReal) (hv : LocalQuasiPshPotentialOn v U),
      (complexChartAt (n := m + 1) p).val p ∈ U ∧
      HasAnalyticSingularitiesSmoothOffPoleAt v ((complexChartAt (n := m + 1) p).val p) ∧
      (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
        T.coefficients (canonicalBasis (m + 1)) (complexChartAt (n := m + 1) p) w
          (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hv) w φ) ∧
      ∀ A : Set M, OriginalPolar T A →
        ∃ (P : ComplexAnalyticPresentationAt (n := m + 1) A p) (c : ℝ),
          BoundedSmoothOffPoleLogarithmicTypeAt v c P.generator
            ((complexChartAt (n := m + 1) p).val p) := by
  obtain ⟨f, Ω, hΩ, u, hu, hps, hpΩ, han, hread⟩ := hT p
  let E := complexChartAt (n := m + 1) p
  let F := chartTransition E f
  let U : Opens (ComplexModel (m + 1)) :=
    ⟨chartTarget E ∩ (F.source ∩ F ⁻¹' Ω),
      (chartTarget E).isOpen.inter (F.isOpen_inter_preimage Ω.isOpen)⟩
  have hpE := mem_complexChartAt_source (n := m + 1) p
  have hpF : E.val p ∈ F.source := by
    change E.val p ∈ E.val.target ∩ E.val.symm ⁻¹' f.val.source
    refine ⟨E.val.map_source hpE, ?_⟩
    change E.val.symm (E.val p) ∈ f.val.source
    rwa [E.val.left_inv hpE]
  have hFp : F (E.val p) = f.val p := by
    change f.val (E.val.symm (E.val p)) = f.val p
    rw [E.val.left_inv hpE]
  have hpU : E.val p ∈ U := by
    refine ⟨E.val.map_source hpE, hpF, ?_⟩
    change F (E.val p) ∈ Ω
    rwa [hFp]
  have hU : U ≤ chartTarget E := fun _ hx => hx.1
  obtain ⟨hv, hreadv⟩ := reading_pullback T E f hΩ hu hread
  have hanv := weak_analytic_pullback E f hpF (hFp.symm ▸ han)
  refine ⟨U, hU, fun z => u (F z), hv, hpU, hanv, hreadv, ?_⟩
  intro A hpolar
  obtain ⟨c, N, g, hc, ⟨B, hBo, hpB, hg⟩, b, hb, hsm, heq⟩ := hanv
  obtain ⟨S, hSsub, hSo, hpS⟩ := _root_.eventually_nhds_iff.mp heq
  let R : Set (ComplexModel (m + 1)) := U ∩ (B ∩ S)
  have hRo : IsOpen R := U.isOpen.inter (hBo.inter hSo)
  let P : ComplexAnalyticPresentationAt (n := m + 1) A p := {
    generatorCount := N
    generator := g
    coordinateNeighborhood := R
    isOpen_coordinateNeighborhood := hRo
    center_mem_coordinateNeighborhood := ⟨hpU, hpB, hpS⟩
    coordinateNeighborhood_subset_target := fun _ hz => hU hz.1
    generator_holomorphic := fun i => (hg i).mono (fun _ hz => hz.2.1)
    zeroLocus := by
      intro y hys hyR
      rw [hpolar E U hU (fun z => u (F z)) hv hreadv y hys hyR.1]
      have hyrep := hSsub (E.val y) hyR.2.2
      change u (F (E.val y)) = (c : EReal) * generatorLog g (E.val y) +
        (b (E.val y) : EReal) at hyrep
      rw [hyrep]
      exact scaled_generatorLog_add_eq_bot_iff g (E.val y) hc (b (E.val y)) }
  exact ⟨P, c, hc, ⟨B, hBo, hpB, hg⟩, b, hb, hsm, heq⟩

end SGPT.Foundations.Analysis.Pending.ActualPreferredOriginalCurrentAnalyticReader
