import SGPT.Okounkov.TranscendentalPoleBlowup
import SGPT.Foundations.Analysis.Pending.AdmissiblePrincipalizationAnalyticModification
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.BlowupExistence
import SGPT.Foundations.Analysis.Pending.NormalCrossings
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison

/-!
# A quasi-psh pole along a closed submanifold (proof of `tok:ext-pole`)

Source: Demailly--Păun, *Numerical characterization of the Kähler cone*, Lemma 2.1, as quoted in
DRWNXZ (proofs of Proposition 3.4 and Theorem 6.1); Xia, *Foundations of pluripotential theory*,
`lem:global-normal-pole`. Blueprint node `tok:ext-pole`.

`exists_submanifold_pole : SubmanifoldPoleStatement` (the statement is in
`TranscendentalPoleStatement`). The pole is `F = log U`, `U = ∑_a θ_a² ∑_i |g_{a,i}|²` the weight
of a concentration partition of `V` (`SubmanifoldConcentrationPotential.exists_of_isCoherent`,
coherence of `𝓘_V` from `VanishingIdealCoherent`):

* quasi-plurisubharmonicity, the pole set, continuity, smoothness off `V`, smoothness of
  `e^F = U`, the analytic type `(1, 𝓘_V)` and the local form in flattening charts are proved in
  `TranscendentalPoleWeight`;
* the factorization `F ∘ π = log |h|² + smooth` on every blowup along `V` is
  `TranscendentalPoleBlowup.exists_blowup_factor`;
* the gentle analytic singularities of `c F` (`sourceGentle_concentrationPole`) use the blowup
  along `V` (which exists, `BlowupExistence.exists_isBlowupAlong`, is compact Kähler,
  `BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong`, and is a proper modification,
  `isAnalyticModification_of_isBlowupAlong`) with its exceptional divisor.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
open SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **A blowup along a closed submanifold is a proper analytic modification**: it is the
one-step admissible blowup sequence with centre `V = (𝓘_V).zeroLocus`, and the support of its
exceptional divisor is `π⁻¹ V`. -/
theorem isAnalyticModification_of_isBlowupAlong {V : Set X} {π : Z → X}
    (hπ : IsBlowupAlong n V π) :
    AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π := by
  have hcoh := VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1
  have hzero := zeroLocus_vanishingIdeal (n := n) hπ.1.1
  have hseq := HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.step (n := n) (X := X)
    (E₀ := []) (F := (vanishingIdeal (n := n) V).zeroLocus) id [] V π
    HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.refl hπ
    (NormalCrossings.hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
    (by rw [hzero]; exact fun y hy => hy)
  exact AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    hcoh hseq (exceptionalDivisor hπ) (by rw [support_exceptionalDivisor, hzero])

/-- The translation chart `w ↦ w - e(y)` of the chart `e` at `y`, centred at `y`. -/
def centeredChart (y : Z) :
    LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y) where
  source := (complexChartAt (n := n) y).val.target
  target := (fun w => w + (complexChartAt (n := n) y).val y) ⁻¹'
    (complexChartAt (n := n) y).val.target
  isOpen_source := (complexChartAt (n := n) y).val.open_target
  isOpen_target := (complexChartAt (n := n) y).val.open_target.preimage
    (continuous_id.add continuous_const)
  center_mem_source := (complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)
  toFun := fun w => w - (complexChartAt (n := n) y).val y
  invFun := fun w => w + (complexChartAt (n := n) y).val y
  toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
  mapsTo_toFun := fun w hw => by
    change w - (complexChartAt (n := n) y).val y + (complexChartAt (n := n) y).val y ∈
      (complexChartAt (n := n) y).val.target
    simpa using hw
  mapsTo_invFun := fun _ hw => hw
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

variable {V : Set X} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n V ι)

/-- **`c F` has gentle analytic singularities of type `(c, 𝓘_V)`** for every `c ∈ ℚ_{>0}`. -/
theorem sourceGentle_concentrationPole [CompactSpace X] (omega : KahlerBackground n X)
    (hV : IsClosedSubmanifold n V) (hVint : interior V = ∅) {c : ℚ} (hc : 0 < c) :
    SGPT.PSH.SourceGentleAnalyticSingularities (n := n)
      (fun x => ((c : ℝ) : EReal) * concentrationPole P x) c (vanishingIdeal (n := n) V) := by
  obtain ⟨A, -, hpsh⟩ := exists_isThetaPshPotential_concentrationPole P hV.1 hVint omega
  have hcR : (0 : ℝ) < c := Rat.cast_pos.mpr hc
  have hcpsh := PotentialMassComparison.isThetaPshPotential_smul hpsh hcR
  have hinv : ∀ x, (((c : ℝ)⁻¹ : ℝ) : EReal) * (((c : ℝ) : EReal) * concentrationPole P x) =
      concentrationPole P x := by
    intro x
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hcR.ne', EReal.coe_one, one_mul]
  obtain ⟨Zb, tZ, cZ, mZ, π, hπ⟩ := BlowupExistence.exists_isBlowupAlong V hV hVint
  obtain ⟨-, hK⟩ := BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong ⟨omega⟩ hπ
  refine ⟨⟨_, hcpsh⟩, hcpsh.quasiPshPotential, ?_, fun x => ?_, ?_,
    Zb, tZ, cZ, mZ, π, exceptionalDivisor hπ, isAnalyticModification_of_isBlowupAlong hπ, hK,
    fun y => ?_⟩
  · -- the analytic type `(c, 𝓘_V)`
    obtain ⟨-, hcoh, hloc⟩ := hasAnalyticSingularitiesOfType_concentrationPole P hV
    refine ⟨hc, hcoh, fun x => ?_⟩
    obtain ⟨U, hU, hxU, N, g, hg, hgen, R, C, hRC, hFeq⟩ := hloc x
    refine ⟨U, hU, hxU, N, g, hg, hgen, fun y => (c : ℝ) * R y, (c : ℝ) * C, fun y hy => ?_,
      fun y hy => ?_⟩
    · rw [abs_mul, abs_of_pos hcR]
      exact mul_le_mul_of_nonneg_left (hRC y hy) hcR.le
    · change ((c : ℝ) : EReal) * concentrationPole P y = _
      rw [hFeq y hy, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le)
        (EReal.coe_ne_top _)]
      norm_num
  · -- the exponential is finite
    show EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * (((c : ℝ) : EReal) * concentrationPole P x)) ≠ ⊤
    rw [hinv, exp_concentrationPole]
    exact ENNReal.ofReal_ne_top
  · -- the exponential is smooth
    have heq : (fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) *
        (((c : ℝ) : EReal) * concentrationPole P x))).toReal) =
        fun x => (EReal.exp (concentrationPole P x)).toReal := by
      funext x
      rw [hinv]
    exact heq ▸ chartSmooth_exp_concentrationPole P
  · -- the resolved local equation on the blowup
    obtain ⟨S, h, R, hS, hyS, hhol, hnon, hgen, hR, hid⟩ := exists_blowup_factor P hπ y
    set e := complexChartAt (n := n) y with he
    have hyt : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
    have hey : e.val.symm (e.val y) = y := e.val.left_inv (mem_complexChartAt_source y)
    have hT : Tendsto (fun w : ComplexModel n => e.val.symm (w + e.val y)) (𝓝 0) (𝓝 y) := by
      have h1 : Tendsto (fun w : ComplexModel n => w + e.val y) (𝓝 0) (𝓝 (e.val y)) := by
        have := (continuous_add_const (e.val y)).tendsto (0 : ComplexModel n)
        rwa [zero_add] at this
      have h2 := (e.val.continuousAt_symm hyt).tendsto.comp h1
      rwa [hey] at h2
    have hev : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + e.val y ∈ e.val.target ∧
        e.val.symm (w + e.val y) ∈ S := by
      have h1 : Tendsto (fun w : ComplexModel n => w + e.val y) (𝓝 0) (𝓝 (e.val y)) := by
        have := (continuous_add_const (e.val y)).tendsto (0 : ComplexModel n)
        rwa [zero_add] at this
      exact (h1.eventually (e.val.open_target.mem_nhds hyt)).and
        (hT.eventually (hS.mem_nhds hyS))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨S, hS, hyS, h, fun z hz => (hhol z hz).mdifferentiableWithinAt, hnon, hgen,
      centeredChart y, subset_rfl, sub_self _,
      fun w => (c : ℝ) * R (e.val.symm (w + e.val y)), r, hr,
      fun w hw => (hball w hw).1, ?_, fun w hw => ⟨(hball w hw).2, ?_⟩⟩
    · have hmaps : MapsTo (fun w : ComplexModel n => w + e.val y) (ball 0 r)
          (e.val.target ∩ e.val.symm ⁻¹' S) := fun w hw => hball w hw
      exact contDiffOn_const.mul ((hR e).comp
        ((contDiff_id.add contDiff_const).contDiffOn) hmaps)
    · change ((c : ℝ) : EReal) * concentrationPole P (π (e.val.symm (w + e.val y))) =
        ((c : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖h (e.val.symm (w + e.val y))‖ ^ 2)) +
          (((c : ℝ) * R (e.val.symm (w + e.val y)) : ℝ) : EReal)
      rw [hid _ (hball w hw).2, EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top _), ← EReal.coe_mul]

/-- **`tok:ext-pole`** (DP04 Lemma 2.1, FPT `lem:global-normal-pole`): every closed complex
submanifold `V` with empty interior of a compact Kähler manifold `(X, ω)` carries a pole
`F = log ∑_a θ_a² ∑_i |g_{a,i}|²` in the sense of `IsSubmanifoldPole`. -/
theorem exists_submanifold_pole : SubmanifoldPoleStatement.{u} := by
  intro n X _ _ _ _ omega V hV hVint
  obtain ⟨ι, _, ⟨P⟩⟩ :=
    exists_of_isCoherent (VanishingIdealCoherent.isCoherent_vanishingIdeal hV)
  obtain ⟨A, hA, hpsh⟩ := exists_isThetaPshPotential_concentrationPole P hV.1 hVint omega
  refine ⟨concentrationPole P,
    { exists_thetaPsh := ⟨A, hA.le, hpsh⟩
      eq_bot_iff := concentrationPole_eq_bot_iff P hV.1
      ne_top := concentrationPole_ne_top P
      continuous := continuous_concentrationPole P
      smoothOn_compl := smoothOn_compl_concentrationPole P hV.1
      chartSmooth_exp := chartSmooth_exp_concentrationPole P
      localForm := fun x _ k Φ hΦ => localForm_concentrationPole P hV.1 hΦ
      analyticType := hasAnalyticSingularitiesOfType_concentrationPole P hV
      blowup := ?_
      gentle := fun c hc => sourceGentle_concentrationPole P omega hV hVint hc }⟩
  intro Zb _ _ _ π hπ z
  obtain ⟨S, h, R, hS, hzS, hhol, -, hgen, hR, hid⟩ := exists_blowup_factor P hπ z
  exact ⟨S, h, R, hS, hzS, hhol, hgen, hR, hid⟩

end SGPT.Okounkov.TranscendentalPole
