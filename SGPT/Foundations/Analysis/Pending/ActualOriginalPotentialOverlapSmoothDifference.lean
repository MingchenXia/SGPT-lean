import SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-! Internally produced full native and smooth compatibility of the original
local potentials of the same signed current on genuine chart overlaps. -/

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualOriginalPotentialOverlapSmoothDifference
open FirstPass FirstPass.HolomorphicMaps CanonicalCurrentFrame
open ActualQuasiPshPotentialSmoothCompatibility
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

/-- The actual original coefficient readings of the same signed global current
internally produce complete native equality and original smooth potential
compatibility across its actual holomorphic charts. -/
theorem exists_original_chart_smooth_difference
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e f : ComplexChart (m + 1) M) {Ω P : Opens (ComplexModel (m + 1))}
    (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    {u v : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u Ω) (hv : LocalQuasiPshPotentialOn v P)
    (hreadu : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ)
    (hreadv : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(P, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) f w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hv) w φ) :
    let F := chartTransition e f
    let U : Opens (ComplexModel (m + 1)) :=
      ⟨Ω ∩ (F.source ∩ F ⁻¹' P), Ω.isOpen.inter (F.isOpen_inter_preimage P.isOpen)⟩
    ∃ (huU : LocalQuasiPshPotentialOn u U)
      (hvF : LocalQuasiPshPotentialOn (fun z => v (F z)) U),
      ddC (regularLocalQuasiPsh huU) = ddC (regularLocalQuasiPsh hvF) ∧
      ∀ x ∈ U, ∃ (W : Opens (ComplexModel (m + 1))) (hWU : W ≤ U)
        (h : ComplexModel (m + 1) → ℝ), x ∈ W ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
        ∃ hh : LocallyIntegrableOn h W volume,
          EqOn u (fun z => v (F z) + (h z : EReal)) W ∧
          restrictDistribution (regularLocalQuasiPsh huU - regularLocalQuasiPsh hvF) hWU =
            regularDistribution volume h hh ∧
          ∀ z ∈ W, ∀ w : ComplexModel (m + 1), leviForm h z w = 0 := by
  intro F U
  have hUΩ : U ≤ Ω := fun _ hz => hz.1
  have hUS : (U : Set _) ⊆ F.source := fun _ hz => hz.2.1
  have hUΩS : U ≤ Ω ⊓ overlapSource e f := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hUmaps : MapsTo F U P := fun _ hz => hz.2.2
  let huU := hu.mono U.isOpen hUΩ
  let hvF := genuine_transition_pullback e f hv hUS hUmaps
  have heq : ddC (regularLocalQuasiPsh huU) = ddC (regularLocalQuasiPsh hvF) := by
    let b := canonicalBasis (m + 1)
    let k := degreeTwo (Nat.succ_pos m)
    let B := currentPairingBasis b k
    have hover := (ActualOriginalLocalPotentialCurrentOverlap.original_local_potential_full_overlap
      T e f hΩ hP hu hv hreadu hreadv).2.2
    ext w φ
    let γ := contractVolume (basisVolume B) w
    let η := constantTestFormCLM γ φ
    obtain ⟨ζ, _hζsupp, _hζliteral, hζrel⟩ :=
      ActualChartOverlapTestTransport.exists_constant_form_counterpart e f Ω P
        (Module.finrank ℝ (ComplexModel (m + 1)) - k.val) φ γ
    let ηO : TestForm (Ω ⊓ overlapSource e f) _ := TestFunction.monoCLM ℝ η
    let ηS : TestForm (overlapSource e f) _ := TestFunction.monoCLM ℝ η
    let ζR : TestForm (overlapTarget e f) _ := TestFunction.monoCLM ℝ ζ
    have hrelO : ∀ x ∈ F.source, ∀ z : Fin (Module.finrank ℝ (ComplexModel (m + 1)) - k.val) →
        ComplexModel (m + 1), ηO x z = ζ (F x)
          (fun i => chartTransitionDerivative e f x (z i)) := by
      intro x hx z
      rw [show ηO x = η x from testForm_inclusion_apply hUΩS η x]
      change φ x * γ z = _
      exact hζrel x hx z
    have hrelS : OverlapTestRelated e f ηS ζR := by
      intro x hx z
      rw [show ηS x = η x from testForm_inclusion_apply hUS η x,
        show ζR (F x) = ζ (F x) from testForm_inclusion_apply inf_le_right ζ (F x)]
      change φ x * γ z = _
      exact hζrel x hx z
    have hbridge : ∫ x, DDCOverlap.ddcAdjoint B η x * (u x).toReal ∂volume =
        ∫ y, DDCOverlap.ddcAdjoint B ζ y * (v y).toReal ∂volume := by
      calc
        _ = ∫ x, DDCOverlap.ddcAdjoint B ηO x * (u x).toReal ∂volume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [show DDCOverlap.ddcAdjoint B ηO x = DDCOverlap.ddcAdjoint B η x from
              DDCOverlap.ddcAdjoint_monoCLM_apply hUΩS B η x]
        _ = _ := (hover ηO ζ hrelO).2
    have hcov : ∫ x, DDCOverlap.ddcAdjoint B η x * (v (F x)).toReal ∂volume =
        ∫ y, DDCOverlap.ddcAdjoint B ζ y * (v y).toReal ∂volume := by
      have hc := adjoint_transition_integral e f ηS ζR hrelS v
      calc
        _ = ∫ x, DDCOverlap.ddcAdjoint B ηS x * (v (F x)).toReal ∂volume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [show DDCOverlap.ddcAdjoint B ηS x = DDCOverlap.ddcAdjoint B η x from
              DDCOverlap.ddcAdjoint_monoCLM_apply hUS B η x]
        _ = ∫ y, DDCOverlap.ddcAdjoint B ζR y * (v y).toReal ∂volume := hc
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y => by
            dsimp only
            rw [show DDCOverlap.ddcAdjoint B ζR y = DDCOverlap.ddcAdjoint B ζ y from
              DDCOverlap.ddcAdjoint_monoCLM_apply inf_le_right B ζ y]
    have hpairu : toLocalCurrent b k (ddC (regularLocalQuasiPsh huU)) η =
        ∫ x, DDCOverlap.ddcAdjoint B η x * (u x).toReal ∂volume := by
      change wedgePairing B (ddC (regularLocalQuasiPsh huU)) η = _
      rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    have hpairv : toLocalCurrent b k (ddC (regularLocalQuasiPsh hvF)) η =
        ∫ x, DDCOverlap.ddcAdjoint B η x * (v (F x)).toReal ∂volume := by
      change wedgePairing B (ddC (regularLocalQuasiPsh hvF)) η = _
      rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    have htest : toLocalCurrent b k (ddC (regularLocalQuasiPsh huU)) η =
        toLocalCurrent b k (ddC (regularLocalQuasiPsh hvF)) η :=
      hpairu.trans (hbridge.trans (hcov.symm.trans hpairv.symm))
    change fromLocalCurrent b k (toLocalCurrent b k (ddC (regularLocalQuasiPsh huU))) w φ =
      fromLocalCurrent b k (toLocalCurrent b k (ddC (regularLocalQuasiPsh hvF))) w φ at htest
    simpa only [CurrentPairing.fromLocalCurrent_toLocalCurrent] using htest
  refine ⟨huU, hvF, heq, ?_⟩
  intro x hx
  exact exists_smooth_original_difference_of_equal_native_ddc huU hvF heq x hx

end SGPT.Foundations.Analysis.Pending.ActualOriginalPotentialOverlapSmoothDifference
