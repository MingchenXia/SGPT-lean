import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
import SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse
import SGPT.Foundations.Analysis.Pending.QuasiPshPositiveLeviRepresentative
import SGPT.Foundations.Analysis.Pending.ActualPreferredOriginalCurrentAnalyticReader
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
import SGPT.Foundations.Analysis.PlurisubharmonicAE
set_option autoImplicit false
/-! The complete original-domain statement and ENTIRE mathematical proof precede Lean. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPositiveLocalPsh
open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar
  GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  ActualQuasiPshPotentialSmoothCompatibility ActualDistributionTwoFormReading
  ActualAnalyticCurrentLocalDensity ActualCanonicalComplementaryCurrentCalibration
  GlobalPositiveCurrentACRestriction
  LelongPoincareDivisor ScalarLeviPositiveCurrent ActualDistributionTwoFormDdc
  _root_.SGPT.Foundations.Analysis.LocalCurrents
attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan
variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

private theorem local_ball_data (hu : LocalQuasiPshPotentialOn u Ω)
    {x : ComplexModel n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧
      LocallyIntegrableOn (fun z ↦ (u z).toReal) (ball x r) volume ∧
      ∀ᵐ z ∂volume.restrict (ball x r), u z ≠ ⊤ ∧ u z ≠ ⊥ := by
  obtain ⟨A, r, _hA, hr, hsub, hp, _hQ, hne⟩ :=
    ActualLocalQuasiPshQuadraticCorrection.exists_noncollapsed_positive_quadratic_correction hu hx
  let Q := ballPot A x 0
  have hfin := hp.ae_finite volume (convex_ball x r).isPreconnected hne
  have hufin : ∀ᵐ z ∂volume.restrict (ball x r), u z ≠ ⊤ ∧ u z ≠ ⊥ := by
    filter_upwards [hfin] with z hz
    exact ⟨(EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)).mp hz.1, (EReal.add_ne_bot_iff.mp hz.2).1⟩
  have hLP := hp.locallyIntegrableOn_toReal volume (convex_ball x r).isPreconnected hne
  have hLQ : LocallyIntegrableOn Q (ball x r) volume :=
    (contDiff_ballPot A x 0).continuous.continuousOn.locallyIntegrableOn isOpen_ball.measurableSet
  have hreal : (fun z ↦ (u z + (Q z : EReal)).toReal - Q z) =ᵐ[
      volume.restrict (ball x r)] (fun z ↦ (u z).toReal) := by
    filter_upwards [hufin] with z hz
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe, add_sub_cancel_right]
  exact ⟨r, hr, hsub, (hLP.sub hLQ).congr hreal, hufin⟩

private theorem local_real_data (hu : LocalQuasiPshPotentialOn u Ω) :
    LocallyIntegrableOn (fun z ↦ (u z).toReal) Ω volume ∧
      ∀ᵐ z ∂volume.restrict Ω, u z ≠ ⊤ ∧ u z ≠ ⊥ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, _hsub, hL, _hfin⟩ := local_ball_data hu hx
    simpa only [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds (mem_ball_self hr)),
      nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds hx)] using hL x (mem_ball_self hr)
  · apply ae_restrict_of_open_neighborhood_ae
    intro x hx
    obtain ⟨r, hr, _hsub, _hL, hfin⟩ := local_ball_data hu hx
    exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hfin⟩


variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}
private theorem reader_restrict (hVU : V ≤ U) (A : DistributionForm U 2) :
    complementaryRead (restrictForm A hVU) = restrict hVU (complementaryRead A) := by
  ext γ φ
  have hφ : (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) = extTest hVU φ := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hVU φ) y, extTest_apply]
  simp only [complementaryRead, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    restrictForm_apply, LocalBedfordTaylorLocality.restrict_apply, smul_eq_mul, hφ]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Full positivity of the original current makes every genuine original local reader PSH, retaining all its poles. -/
theorem plurisubharmonicOn_original_reader_of_full_positive
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M)
    {U : Opens (ComplexModel (m + 1))} (hU : U ≤ chartTarget e)
    {v : ComplexModel (m + 1) → EReal} (hv : LocalQuasiPshPotentialOn v U)
    (hread : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hv) w φ) :
    PlurisubharmonicOn v U := by
  have hcoeff : restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hU =
      ddC (regularLocalQuasiPsh hv) := by
    ext w φ
    exact hread w φ
  have hfull : ddc (scalarTopCurrent (regularLocalQuasiPsh hv)) =
      restrict hU (chartSpanCurrent T e) := by
    rw [← complementaryRead_ddC, ← hcoeff, reader_restrict,
      complementaryRead_coefficients_eq_chartSpanCurrent]
  have hpositive : IsPositive (ddc (scalarTopCurrent (regularLocalQuasiPsh hv))) := by
    rw [hfull]
    exact isPositive_restrict (isPositive_chartSpanCurrent T hT e) hU
  have hLevi := FullPositiveScalarCurrentLeviConverse.hasNonnegativeDistributionalLevi_of_isPositive_ddc
    (regularLocalQuasiPsh hv) hpositive
  obtain ⟨hL, hfin⟩ := local_real_data hv
  apply QuasiPshPositiveLeviRepresentative.plurisubharmonicOn_of_nonnegative_distributionalLevi
    hv.2.1 volume hfin hL
  exact hLevi

end SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPositiveLocalPsh
