import SGPT.Bergman.SiuUniformGenerationMain
import SGPT.Trace.BertiniGlobalGeneration
import SGPT.Bergman.SiuKodairaGermSpan
import SGPT.Bergman.SiuKodairaNativeSection

/-! Actual uniform nonzero original native sections for flat twists, toward numerical invariance.
Blueprint: okounkov-flat-uniform-sections.tex. No whole source credit yet. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.FlatTwist
open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.NAPotential.GAGAMult
open SGPT.Trace.BertiniGlobalGeneration SGPT.NAPotential.SiuGen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Literal original unit germ lies in the actual zero-weight ideal, EVERY dimension. -/
theorem one_mem_zero_multiplierIdeal {c : ℝ} (hc : 0<c) (p : X) :
    (multiplierIdeal (n:=n) c (fun _ : X => (0:EReal))).mem p (fun _ => (1:ℂ)) := by
  refine ⟨Eventually.of_forall (fun _ => mdifferentiableAt_const),hc,?_⟩
  let z := (complexChartAt (n:=n) p).val p
  refine ⟨ball z 1,isOpen_ball,mem_ball_self zero_lt_one,differentiableOn_const _,?_⟩
  have hden : multiplierDensity (chartFunction (fun _ : X => (0:EReal)) (complexChartAt (n:=n) p))
      c (fun _ : ComplexModel n => (1:ℂ)) = fun _ => (1:ℝ≥0∞) := by
    funext w
    simp [multiplierDensity,multiplierWeight,chartFunction]
  change WeightedL2On _ c (fun _ : ComplexModel n => (1:ℂ)) (ball z 1) volume
  unfold WeightedL2On
  rw [hden]
  refine ⟨aemeasurable_const,?_⟩
  simpa using (lt_of_le_of_lt (measure_mono (ball_subset_closedBall : ball z 1 ⊆ closedBall z 1))
    ((isCompact_closedBall z 1).measure_lt_top (μ:=volume)))

/-- Evaluate TRUE unit-germ generation to obtain SAME actual native H0 section nonzero in original fiber. -/
theorem exists_native_section_nonzero_of_zero_generation
    (E : HermitianHolomorphicLineBundle.{0,0} n X) {c : ℝ} (hc : 0<c)
    (hgen : IsBaseGloballyGenerated E (multiplierIdeal (n:=n) c (fun _ : X => (0:EReal))))
    (p : X) : ∃ s : HolomorphicSections (n:=n) E.Fiber, s p ≠ 0 := by
  let e := prefFrame E p
  let := e.property
  have he : p ∈ e.val.baseSet := mem_prefFrame E p
  have hspan := hgen p e he (fun _ => (1:ℂ)) (one_mem_zero_multiplierIdeal hc p)
  obtain ⟨h,⟨s,hs,hcoef⟩,h0⟩ :=
    SGPT.Bergman.SiuKodaira.exists_generator_ne_zero_of_isInSpanAt hspan one_ne_zero
  refine ⟨SGPT.Bergman.SiuKodaira.nativeSectionOfHolomorphic E s hs.1,?_⟩
  intro hs0
  apply h0
  change s p = 0 at hs0
  have hz := congrArg (e.val.continuousLinearMapAt ℂ p) hs0
  have hz' : e.val.continuousLinearMapAt ℂ p (s p) = 0 := by simpa only [map_zero] using hz
  exact (congrFun hcoef p).trans hz'

/-- ONE threshold BEFORE ANY original flat bundle, power or point, producing actual SAME-fiber sections. -/
theorem exists_uniform_flat_twist_nonzero_sections [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0,0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ k₀ : ℕ, 0<k₀ ∧ ∀ k : ℕ, k₀≤k →
      ∀ N : HermitianHolomorphicLineBundle.{0,0} n X, IsSourceSmoothHermitianMetric N →
      IsOwnFirstChernForm N (0 : ClosedRealOneOneForm n X) →
      ∀ m : ℕ, 0<m → ∀ p : X,
        ∃ s : HolomorphicSections (n:=n) (twistedPower N (positivePower G (k-1)) m).Fiber,
          s p ≠ 0 := by
  obtain ⟨k₀,hk₀,huniform⟩ :=
    SGPT.Bergman.SiuUniformGeneration.siuGlobalUniformGeneration_prod_of_le G hG θG hθG hKah
  have hzero : IsThetaPshPotential (0 : ClosedRealOneOneForm n X).val (fun _ : X => (0:EReal)) := by
    apply (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    intro e z hz v
    simp
  refine ⟨k₀,hk₀,?_⟩
  intro k hk N hN hθN m hm p
  have hΦ := SGPT.Trace.ProductMultiplierRestriction.isThetaPshPotential_comp_fst
    (m:=1) (Y:=unitDisc) (0 : ClosedRealOneOneForm n X) hzero
  have hprod := huniform k hk N hN (0 : ClosedRealOneOneForm n X) hθN
    (fun _ : X × unitDisc => (0:EReal)) hΦ m hm
  have hbase := isBaseGloballyGenerated_of_prod _ hzero.1.quasiPlurisubharmonic
    (by exact_mod_cast hm : (0:ℝ)<(m:ℝ)) hprod
  exact exists_native_section_nonzero_of_zero_generation _ (by exact_mod_cast hm) hbase p

end SGPT.Okounkov.FlatTwist
