import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Ring
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.OkaCoherence
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.Pending.OkaIdealOperations
import Mathlib.Tactic.FunProp
import SGPT.PSH.CanonicalGrowthManifold
import SGPT.Okounkov.TranscendentalSkodaAlgebra
import Mathlib.Tactic.Positivity
import SGPT.Okounkov.TranscendentalSkodaTheorem
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin
import SGPT.PSH.AtlasInfinityIdeal
import SGPT.Foundations.Analysis.FirstPass.ExtendedDifference
import SGPT.PSH.UniformRationalAnalyticCoefficient
import Mathlib.Topology.Connected.LocallyConnected

/-! # One global coherent type for compact rational analytic singularities

Source: SGPT69360cfd, chapter_pshfunctions1353–1366, def:neatanasing and
compact existence sentence1366 (E01). The proof produces one actual global
coherent holomorphic ideal with actual nearby generation, the same positive
rational coefficient everywhere, and exact bounded-remainder presentations
of the unchanged potential on connected original neighborhoods. Arbitrary
original varying chart dimensions, including0, are retained. There is no
output ideal, coherence, overlap or singularity-type certificate input.

Proof blueprint: blueprint.tex. Exact source, recursive-axiom and public-type
validation receipts are maintained alongside this module.
-/

/-! Consolidated checked atom: FiniteColonCancellation.lean. -/

/-!
The finite cancellation atom for actual Skoda-colon coherence.
Matrix equations arise from actual Skoda division and actual nearby Nadel
finite generators. Summing row norms avoids any division by an individual
possibly vanishing generator. Plan: blueprint.tex, colon-cancellation.
-/

set_option autoImplicit false

namespace SGPT.PSH.GlobalAnalyticType

open scoped BigOperators

/-- Actual finite row equations yield a growth estimate wherever the finite
multiplier-generator family is nonzero. No matrix inversion is assumed. -/
theorem norm_le_of_finite_colon_equations
    {r m : ℕ} (G : Fin r → ℂ) (H : Fin m → ℂ)
    (A : Fin m → Fin m → ℂ) (q : ℂ) (C : ℝ)
    (hrow : ∀ i, q * H i = ∑ j, A i j * H j)
    (hA : ∀ i j, ‖A i j‖ ≤ C * ∑ l, ‖G l‖)
    (hne : ∃ i, H i ≠ 0) :
    ‖q‖ ≤ (m : ℝ) * C * ∑ l, ‖G l‖ := by
  have hT : 0 < ∑ i, ‖H i‖ := by
    obtain ⟨i, hi⟩ := hne
    exact (norm_pos_iff.mpr hi).trans_le
      (Finset.single_le_sum (fun j _ => norm_nonneg (H j)) (Finset.mem_univ i))
  have hsum : ‖q‖ * ∑ i, ‖H i‖ ≤
      ((m : ℝ) * C * ∑ l, ‖G l‖) * ∑ i, ‖H i‖ := by
    calc
      ‖q‖ * ∑ i, ‖H i‖ = ∑ i, ‖q * H i‖ := by
        rw [Finset.mul_sum]
        simp only [norm_mul]
      _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖H j‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [hrow i]
        exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
      _ ≤ ∑ _i : Fin m, (C * ∑ l, ‖G l‖) * ∑ j, ‖H j‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg (H j))
      _ = ((m : ℝ) * C * ∑ l, ‖G l‖) * ∑ i, ‖H i‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact (mul_le_mul_iff_left₀ hT).mp (by simpa only [mul_comm (∑ i, ‖H i‖)] using hsum)

end SGPT.PSH.GlobalAnalyticType

/-! Consolidated checked atom: NadelColonNearby.lean. -/

/-! Actual nearby generators for local multiplier ideals and their finite
colons. Both integrability and holomorphic coefficient equations are literal.
This is uniform generation on one neighborhood, not pointwise Noetherianity.
Full source plan: blueprint.tex, local-coherence. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter MeasureTheory Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations

/-- Consolidating a literal finite germ sum gives one coefficient per actual
original generator; no new generated-ideal assumption is introduced. -/
theorem inSpanAt_of_inGermSpan_range
    {n N : ℕ} {G : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}
    {F : ComplexModel n → ℂ} (hF : HolAt F x)
    (hspan : MultiplierIdealBergmanNadelIdeal.InGermSpan (range G) x F) :
    InSpanAt G x F := by
  classical
  obtain ⟨L, s, a, hs, ha, heq⟩ := hspan
  choose σ hσ using hs
  refine ⟨hF, fun i z => ∑ j, if σ j = i then a j z else 0, fun i => ?_, ?_⟩
  · apply HolAt.fintype_sum
    intro j
    split_ifs
    · exact ha j
    · exact holAt_const 0 x
  · filter_upwards [heq] with z hz
    rw [hz]
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← hσ j]

/-- Actual weighted multiplier integrability has one finite generating family
which generates at every point of a genuine open neighborhood. -/
theorem idealFGAt_multiplierIntegrableAt
    {m : ℕ} {Ω : TopologicalSpace.Opens (ComplexModel (m + 1))}
    {ψ : ComplexModel (m + 1) → EReal} (hψ : PlurisubharmonicOn ψ Ω)
    {c : ℝ} (hc : 0 < c) {x : ComplexModel (m + 1)} (hx : x ∈ Ω) :
    IdealFGAt (fun y F => MultiplierIntegrableAt ψ c F y volume) x := by
  classical
  obtain ⟨r, hr, N, G, hball, hGhol, hGint, hgen⟩ :=
    MultiplierIdealBergmanNadelCoherence.exists_local_generators hψ hc hx
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr, Fin N, inferInstance, G,
    hGhol, fun y hy F => ⟨fun hF => ?_, fun hF => ?_⟩⟩
  · have hhol : HolAt F y := by
      obtain ⟨_, U, hU, hyU, hFU, _⟩ := hF
      exact eventually_of_mem (hU.mem_nhds hyU) fun z hz =>
        (hFU z hz).differentiableAt (hU.mem_nhds hz)
    exact inSpanAt_of_inGermSpan_range hhol (hgen y hy F hF)
  · obtain ⟨_, a, ha, heq⟩ := hF
    have hsum := MultiplierIdealBergmanNadelManifold.multiplierIntegrableAt_sum_mul
      hc (hψ y (hball hy)).quasiPlurisubharmonicAt ha (fun i => hGint i y hy)
    exact hsum.congr (EventuallyEq.refl _ _) heq.symm

/-- The finite colon of an actual weighted ideal is genuinely coherent near
the point, by proved Oka relations and the actual Nadel generators. -/
theorem idealFGAt_finite_multiplier_colon
    {m N : ℕ} {Ω : TopologicalSpace.Opens (ComplexModel (m + 1))}
    {ψ : ComplexModel (m + 1) → EReal} (hψ : PlurisubharmonicOn ψ Ω)
    {c : ℝ} (hc : 0 < c) {x : ComplexModel (m + 1)} (hx : x ∈ Ω)
    (H : Fin N → ComplexModel (m + 1) → ℂ) (hH : ∀ i, HolAt (H i) x) :
    IdealFGAt (fun y q => HolAt q y ∧ ∀ i,
      MultiplierIntegrableAt ψ c (fun z => q z * H i z) y volume) x := by
  let J := fun y F => MultiplierIntegrableAt ψ c F y volume
  have hJ : IdealFGAt J x := idealFGAt_multiplierIntegrableAt hψ hc hx
  have hoka := OkaCoherence.okaProperty_euclidean (m + 1)
  have hcolon := CoherentIdealColon.idealFGAt_iInter hoka N
    (fun i => colonIdeal J (H i)) (fun i => hJ.colon hoka (hH i))
  apply hcolon.congr
  exact Eventually.of_forall fun y q => by
    simp only [colonIdeal, J]
    constructor
    · rintro ⟨hq, h⟩
      exact ⟨hq, fun i => (h i).2⟩
    · rintro ⟨hq, h⟩
      exact ⟨hq, fun i => ⟨hq, h i⟩⟩

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: FiniteGermColonGrowth.lean. -/

/-! A genuine local Skoda-colon growth producer. Actual holomorphic finite
coefficient equations give their own finite bounds; nearby nonzero multiplier
stalks permit cancellation through their possible pointwise zero sets.
The final global source theorem must produce all these intermediate data.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An actual finite holomorphic germ-span equation gives a genuine norm
bound on a single neighborhood, with no bound certificate as an input. -/
theorem exists_norm_sum_bound_of_inSpanAt
    {r : ℕ} {G : Fin r → E → ℂ} {x : E} {F : E → ℂ}
    (hF : InSpanAt G x F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 x, ‖F z‖ ≤ C * ∑ i, ‖G i z‖ := by
  obtain ⟨_, a, ha, heq⟩ := hF
  let C : ℝ := ∑ i, (‖a i x‖ + 1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
  have hab : ∀ i, ∀ᶠ z in 𝓝 x, ‖a i z‖ ≤ C := by
    intro i
    filter_upwards [(ha i).differentiableAt.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one ‖a i x‖))] with z hz
    exact hz.le.trans (Finset.single_le_sum
      (fun j _ => by positivity : ∀ j ∈ (Finset.univ : Finset (Fin r)), 0 ≤ ‖a j x‖ + 1)
      (Finset.mem_univ i))
  refine ⟨C, hC, ?_⟩
  filter_upwards [heq, eventually_all.mpr hab] with z hz hzb
  rw [hz, Finset.mul_sum]
  calc ‖∑ i, a i z * G i z‖ ≤ ∑ i, ‖a i z * G i z‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖G i z‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hzb i) (norm_nonneg _)

/-- Actual finite germ equations produce the colon growth bound on one
neighborhood. Nonzero stalks are ordinary local analytic data, not a growth
or coherent-type conclusion; the source consumer produces them internally. -/
theorem exists_norm_sum_bound_of_finite_colon_germ_equations
    {r m : ℕ} {G : Fin r → E → ℂ} {H : Fin m → E → ℂ}
    {A : Fin m → Fin m → E → ℂ} {q : E → ℂ} {x : E}
    {U : Set E} (hU : IsOpen U) (hx : x ∈ U)
    (hG : ∀ i, ContinuousOn (G i) U) (hq : HolAt q x)
    (hH : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, ∃ i, H i z ≠ 0)
    (hrow : ∀ i, (fun z => q z * H i z) =ᶠ[𝓝 x]
      fun z => ∑ j, A i j z * H j z)
    (hA : ∀ i j, InSpanAt G x (A i j)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ z in 𝓝 x, ‖q z‖ ≤ D * ∑ l, ‖G l z‖ := by
  classical
  choose C hC hb using fun i j => exists_norm_sum_bound_of_inSpanAt (hA i j)
  let B : ℝ := ∑ i, ∑ j, C i j
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC i j
  have hCB : ∀ i j, C i j ≤ B := by
    intro i j
    exact (Finset.single_le_sum (fun k _ => hC i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hC k l)
        (Finset.mem_univ i))
  have hgeom : ∀ᶠ z in 𝓝 x, z ∈ U ∧ DifferentiableAt ℂ q z ∧
      (∀ i, q z * H i z = ∑ j, A i j z * H j z) ∧
      ∀ i j, ‖A i j z‖ ≤ C i j * ∑ l, ‖G l z‖ := by
    filter_upwards [hU.mem_nhds hx, hq, eventually_all.mpr hrow,
      eventually_all.mpr (fun i => eventually_all.mpr (hb i))] with z hzU hzq hzr hzb
    exact ⟨hzU, hzq, hzr, hzb⟩
  obtain ⟨W, hWsub, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hgeom
  refine ⟨(m : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB,
    eventually_of_mem (hWo.mem_nhds hxW) ?_⟩
  intro y hy
  have hyU : y ∈ U := (hWsub hy).1
  have hfreq : ∃ᶠ z in 𝓝 y, ‖q z‖ ≤ (m : ℝ) * B * ∑ l, ‖G l z‖ := by
    apply ((hH y hyU).and_eventually (hWo.mem_nhds hy)).mono
    rintro z ⟨hne, hzW⟩
    exact norm_le_of_finite_colon_equations (fun l => G l z) (fun i => H i z)
      (fun i j => A i j z) (q z) B (hWsub hzW).2.2.1 (fun i j =>
        ((hWsub hzW).2.2.2 i j).trans
          (mul_le_mul_of_nonneg_right (hCB i j)
            (Finset.sum_nonneg fun l _ => norm_nonneg (G l z)))) hne
  have hGc : ∀ i, ContinuousAt (G i) y :=
    fun i => (hG i).continuousAt (hU.mem_nhds hyU)
  have hSc : ContinuousAt (fun z => ∑ l, ‖G l z‖) y := by fun_prop
  exact le_of_tendsto_of_tendsto_of_frequently
    (hWsub hy).2.1.continuousAt.norm.tendsto
    ((continuousAt_const.mul continuousAt_const).mul hSc).tendsto hfreq

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: GrowthMultiplierProducts.lean. -/

/-! Actual growth germs act between the two genuine Skoda multiplier ideals.
Actual generator powers supply nonzero weighted members. No ideal or
coherence conclusion is assumed. Full source plan: blueprint.tex.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalSkoda

/-- Literal multiplication of the same weight retains both extended-real
endpoints; every exponent used in the colon construction is positive. -/
theorem multiplierWeight_add_one {c : ℝ} (hc : 0 < c) (P : EReal) :
    multiplierWeight (c + 1) P = multiplierWeight 1 P * multiplierWeight c P := by
  cases P with
  | bot => simp [multiplierWeight_bot hc, multiplierWeight_bot (by positivity : 0 < c + 1)]
  | top => simp [multiplierWeight_top hc, multiplierWeight_top (by positivity : 0 < c + 1)]
  | coe t =>
    simp only [multiplierWeight_coe, one_mul]
    rw [show -((c + 1) * t) = -t + -(c * t) by ring, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- The actual product density factorizes, including simultaneous zero/pole
cases under the original ENNReal multiplication convention. -/
theorem multiplierDensity_add_one_product {X : Type*} (ψ : X → EReal)
    {c : ℝ} (hc : 0 < c) (q H : X → ℂ) (x : X) :
    multiplierDensity ψ (c + 1) (fun y => q y * H y) x =
      multiplierDensity ψ 1 q x * multiplierDensity ψ c H x := by
  simp only [multiplierDensity, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), multiplierWeight_add_one hc]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- A literal logarithmic growth bound produces genuine higher weighted
integrability of the product with every actual lower multiplier germ. -/
theorem multiplierIntegrableAt_mul_of_growth_bound
    {n r : ℕ} {G : Fin r → ComplexModel n → ℂ} {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) {q H : ComplexModel n → ℂ}
    (hq : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ q z)
    (hbound : MoreSingularAt (fun z => logNormSq (q z)) (generatorLog G) x)
    {c : ℝ} (hH : MultiplierIntegrableAt (generatorLog G) c H x volume) :
    MultiplierIntegrableAt (generatorLog G) (c + 1) (fun z => q z * H z) x volume := by
  obtain ⟨V, hV, hxV, hGV⟩ := hG
  obtain ⟨hc, U, hU, hxU, hHU, hInt⟩ := hH
  obtain ⟨Q, hQsub, hQ, hxQ⟩ := _root_.mem_nhds_iff.mp hq
  obtain ⟨D, hD⟩ := hbound
  obtain ⟨B, hBsub, hB, hxB⟩ := _root_.mem_nhds_iff.mp hD
  let W : Set (ComplexModel n) := (U ∩ V) ∩ (Q ∩ B)
  have hW : IsOpen W := (hU.inter hV).inter (hQ.inter hB)
  have hWU : W ⊆ U := fun _ hy => hy.1.1
  have hWV : W ⊆ V := fun _ hy => hy.1.2
  have hqW : DifferentiableOn ℂ q W := fun y hy =>
    (hQsub hy.2.1).differentiableWithinAt
  have hHW : DifferentiableOn ℂ H W := hHU.mono hWU
  have hprod : DifferentiableOn ℂ (fun y => q y * H y) W := hqW.mul hHW
  refine ⟨by positivity, W, hW, ⟨⟨hxU, hxV⟩, hxQ, hxB⟩, hprod,
    aemeasurable_multiplierDensity_generatorLog hW
      (fun i => (hGV i).continuousOn.mono hWV) (by positivity) hprod.continuousOn, ?_⟩
  calc (∫⁻ y in W, multiplierDensity (generatorLog G) (c + 1) (fun z => q z * H z) y)
      ≤ ∫⁻ y in W, ENNReal.ofReal (Real.exp D) * multiplierDensity (generatorLog G) c H y := by
        apply setLIntegral_mono' hW.measurableSet
        intro y hy
        rw [multiplierDensity_add_one_product _ hc]
        exact mul_le_mul' (density_le_exp_of_original_log_bound (hBsub hy.2.2)) le_rfl
    _ = ENNReal.ofReal (Real.exp D) * ∫⁻ y in W, multiplierDensity (generatorLog G) c H y :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp D) * ∫⁻ y in U, multiplierDensity (generatorLog G) c H y :=
      mul_le_mul' le_rfl (lintegral_mono_set hWU)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInt.2

/-- Any actual holomorphic germ with a bounded original weighted density is
integrable on one finite-measure ball, not merely a formal stalk member. -/
theorem multiplierIntegrableAt_of_bounded_generator_density
    {n r : ℕ} {G : Fin r → ComplexModel n → ℂ} {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ F z) {c : ℝ} (hc : 0 < c)
    {K : ℝ≥0∞} (hK : K < ⊤)
    (hbound : ∀ᶠ z in 𝓝 x, multiplierDensity (generatorLog G) c F z ≤ K) :
    MultiplierIntegrableAt (generatorLog G) c F x volume := by
  obtain ⟨V, hV, hxV, hGV⟩ := hG
  have hev : ∀ᶠ z in 𝓝 x, z ∈ V ∧ DifferentiableAt ℂ F z ∧
      multiplierDensity (generatorLog G) c F z ≤ K :=
    by
      filter_upwards [hV.mem_nhds hxV, hF, hbound] with z hzV hzF hzb
      exact ⟨hzV, hzF, hzb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hFV : DifferentiableOn ℂ F (ball x ε) := fun y hy => (hball y hy).2.1.differentiableWithinAt
  refine ⟨hc, ball x ε, isOpen_ball, mem_ball_self hε, hFV,
    aemeasurable_multiplierDensity_generatorLog isOpen_ball
      (fun i => (hGV i).continuousOn.mono (fun y hy => (hball y hy).1)) hc.ne' hFV.continuousOn, ?_⟩
  calc (∫⁻ y in ball x ε, multiplierDensity (generatorLog G) c F y)
      ≤ ∫⁻ _y in ball x ε, K := setLIntegral_mono' measurableSet_ball (fun y hy => (hball y hy).2.2)
    _ = K * volume (ball x ε) := by rw [setLIntegral_const, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hK measure_ball_lt_top

/-- An actual power of every original generator belongs to the actual lower
Skoda multiplier ideal; no nonzero ideal witness is supplied as an input. -/
theorem multiplierIntegrableAt_generator_pow
    {n r : ℕ} {G : Fin r → ComplexModel n → ℂ} {x : ComplexModel n}
    (hG : HolomorphicGeneratorsAt G x) {k : ℕ} (hk : 0 < k) (i : Fin r) :
    MultiplierIntegrableAt (generatorLog G) (k : ℝ) (fun z => G i z ^ k) x volume := by
  have hF : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ (fun z => G i z ^ k) z := by
    obtain ⟨V, hV, hxV, hGV⟩ := hG
    exact eventually_of_mem (hV.mem_nhds hxV) fun z hz =>
      ((hGV i).differentiableAt (hV.mem_nhds hz)).pow k
  apply multiplierIntegrableAt_of_bounded_generator_density hG hF (by exact_mod_cast hk)
    (K := 1) (by simp)
  exact Eventually.of_forall fun z => by
    simpa only [Nat.cast_add, Nat.cast_zero, add_zero, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_mul, mul_one, multiplierDensity,
      multiplierWeight, EReal.coe_zero, zero_mul, neg_zero, EReal.exp_zero,
      one_pow, norm_one, ENNReal.ofReal_one] using
      multiplierDensity_prod_mul_le G (fun _ : Fin k => i) 0 (fun _ => 1) z

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: SkodaColonEquations.lean. -/

/-! Genuine Skoda division and actual Nadel germ generators manufacture the
finite colon equations and nonzero stalks needed for the local growth bound.
No matrix, nonzero multiplier ideal or desired growth bound is assumed in
the final colon-to-growth producer. Full source plan: blueprint.tex.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations
open SGPT.Okounkov.TranscendentalSkoda

/-- Actual lower multiplier generators and genuine Skoda division produce
one finite matrix whose entries belong to the original finite ideal. -/
theorem exists_finite_colon_equations_of_skoda
    {n r m : ℕ} (hn : 0 < n) (G : Fin r → ComplexModel n → ℂ)
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x)
    (H : Fin m → ComplexModel n → ℂ)
    (hgen : ∀ F, MultiplierIntegrableAt (generatorLog G) (n : ℝ) F x volume →
      InSpanAt H x F)
    {q : ComplexModel n → ℂ}
    (hcolon : ∀ i, MultiplierIntegrableAt (generatorLog G) ((n : ℝ) + 1)
      (fun z => q z * H i z) x volume) :
    ∃ A : Fin m → Fin m → ComplexModel n → ℂ,
      (∀ i j, InSpanAt G x (A i j)) ∧
      ∀ i, (fun z => q z * H i z) =ᶠ[𝓝 x] fun z => ∑ j, A i j z * H j z := by
  classical
  have hdiv : ∀ i, ∃ a : Fin r → ComplexModel n → ℂ,
      (∀ l, MultiplierIntegrableAt (generatorLog G) (n : ℝ) (a l) x volume) ∧
      (fun z => q z * H i z) =ᶠ[𝓝 x] fun z => ∑ l, G l z * a l z := by
    intro i
    apply skodaDivisionStatement n r hn G x hG n le_rfl (fun z => q z * H i z)
    simpa only [Nat.cast_add, Nat.cast_one] using hcolon i
  choose a ha hrow using hdiv
  have hcoeff : ∀ i l, ∃ b : Fin m → ComplexModel n → ℂ,
      (∀ j, HolAt (b j) x) ∧ a i l =ᶠ[𝓝 x] fun z => ∑ j, b j z * H j z := by
    intro i l
    exact (hgen (a i l) (ha i l)).2
  choose b hb hbeq using hcoeff
  have hGhol : ∀ l, HolAt (G l) x := by
    obtain ⟨U, hU, hxU, hGU⟩ := hG
    exact fun l => eventually_of_mem (hU.mem_nhds hxU) fun z hz =>
      (hGU l).differentiableAt (hU.mem_nhds hz)
  let A : Fin m → Fin m → ComplexModel n → ℂ := fun i j z => ∑ l, b i l j z * G l z
  refine ⟨A, fun i j => ⟨?_, fun l => b i l j, fun l => hb i l j,
    Eventually.of_forall fun _ => rfl⟩, fun i => ?_⟩
  · exact HolAt.fintype_sum fun l => (hb i l j).mul (hGhol l)
  · filter_upwards [hrow i, eventually_all.mpr (hbeq i)] with z hz hzb
    rw [hz]
    simp only [hzb, Finset.mul_sum, A, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- Actual generator powers inside the actual lower weighted ideal exclude
the zero multiplier stalk. No nonzero ideal or generator witness is assumed. -/
theorem frequently_exists_multiplier_generator_ne_zero
    {n r m : ℕ} (hn : 0 < n) (G : Fin r → ComplexModel n → ℂ)
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x)
    (H : Fin m → ComplexModel n → ℂ)
    (hgen : ∀ F, MultiplierIntegrableAt (generatorLog G) (n : ℝ) F x volume →
      InSpanAt H x F)
    (hne : ∃ i, ∃ᶠ z in 𝓝 x, G i z ≠ 0) :
    ∃ᶠ z in 𝓝 x, ∃ j, H j z ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hne
  have hpow := multiplierIntegrableAt_generator_pow hG hn i
  obtain ⟨_, a, _, heq⟩ := hgen (fun z => G i z ^ n) hpow
  by_contra hnot
  have hHzero : ∀ᶠ z in 𝓝 x, ∀ j, H j z = 0 := by
    simpa only [not_frequently, not_exists, not_ne_iff] using hnot
  have hzero : ∀ᶠ z in 𝓝 x, G i z ^ n = 0 := by
    filter_upwards [heq, hHzero] with z hz hzH
    simp only [hzH, mul_zero, Finset.sum_const_zero] at hz
    exact hz
  exact (hi.mono fun z hz => pow_ne_zero n hz)
    (hzero.mono fun _ hz hne => hne hz)

/-- The original proper finite family, actual nearby multiplier generators,
and actual higher weighted memberships produce the genuine colon growth.
Skoda equations and nonzero multiplier stalks are constructed internally. -/
theorem moreSingularAt_of_multiplier_colon
    {n r m : ℕ} (hn : 0 < n) (G : Fin r → ComplexModel n → ℂ)
    (Ω : TopologicalSpace.Opens (ComplexModel n))
    (hG : ∀ i, DifferentiableOn ℂ (G i) Ω)
    (H : Fin m → ComplexModel n → ℂ)
    (hgen : ∀ y ∈ (Ω : Set (ComplexModel n)), ∀ F,
      MultiplierIntegrableAt (generatorLog G) (n : ℝ) F y volume → InSpanAt H y F)
    (hne : ∀ y ∈ (Ω : Set (ComplexModel n)), ∃ i, ∃ᶠ z in 𝓝 y, G i z ≠ 0)
    {x : ComplexModel n} (hx : x ∈ Ω) {q : ComplexModel n → ℂ} (hq : HolAt q x)
    (hcolon : ∀ i, MultiplierIntegrableAt (generatorLog G) ((n : ℝ) + 1)
      (fun z => q z * H i z) x volume) :
    MoreSingularAt (fun z => logNormSq (q z)) (generatorLog G) x := by
  have hGat : ∀ y ∈ (Ω : Set (ComplexModel n)), HolomorphicGeneratorsAt G y :=
    fun y hy => ⟨Ω, Ω.isOpen, hy, hG⟩
  have hH : ∀ y ∈ (Ω : Set (ComplexModel n)), ∃ᶠ z in 𝓝 y, ∃ i, H i z ≠ 0 :=
    fun y hy => frequently_exists_multiplier_generator_ne_zero hn G (hGat y hy) H
      (hgen y hy) (hne y hy)
  obtain ⟨A, hA, hrow⟩ := exists_finite_colon_equations_of_skoda hn G (hGat x hx) H
    (hgen x hx) hcolon
  exact moreSingularAt_singleLog_iff_norm_sum_bound.mpr
    (exists_norm_sum_bound_of_finite_colon_germ_equations Ω.isOpen hx
      (fun i => (hG i).continuousOn) hq hH hrow hA)

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: ProperGrowthCoherence.lean. -/

/-! Nearby coherence of the actual bounded-growth ideal of an original
proper holomorphic family. Actual Nadel and Skoda supply every intermediate
ideal/generator/matrix/nonzero-stalk witness. Full source plan: blueprint.tex.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter MeasureTheory Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations

/-- The literal canonical holomorphic growth-germ predicate; this definition
alone asserts no nearby generation or coherence. -/
def growthGermPredicate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (G : Fin r → E → ℂ) (x : E) (q : E → ℂ) : Prop :=
  HolAt q x ∧ MoreSingularAt (fun z => logNormSq (q z)) (generatorLog G) x

/-- The full actual growth ideal is finitely generated on ONE neighborhood,
with exact membership at EVERY nearby point. Properness is ordinary
nonzero-family-germ data; no coherent growth ideal or matrix is an input. -/
theorem idealFGAt_growth_of_proper_holomorphic_family
    {n r : ℕ} (hn : 0 < n) (G : Fin r → ComplexModel n → ℂ)
    (Ω : TopologicalSpace.Opens (ComplexModel n))
    (hG : ∀ i, DifferentiableOn ℂ (G i) Ω)
    (hne : ∀ y ∈ (Ω : Set (ComplexModel n)), ∃ i, ∃ᶠ z in 𝓝 y, G i z ≠ 0)
    {x : ComplexModel n} (hx : x ∈ Ω) :
    IdealFGAt (growthGermPredicate G) x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hGat : ∀ y ∈ (Ω : Set (ComplexModel (d + 1))), HolomorphicGeneratorsAt G y :=
    fun y hy => ⟨Ω, Ω.isOpen, hy, hG⟩
  have hψ : PlurisubharmonicOn (generatorLog G) Ω := by
    intro y hy
    simpa only [EReal.coe_one, one_mul] using
      plurisubharmonicAt_scaled_generatorLog (hGat y hy) zero_lt_one
  have hnR : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  obtain ⟨ε, hε, m, H, hball, hHhol, hHint, hNadel⟩ :=
    MultiplierIdealBergmanNadelCoherence.exists_local_generators hψ hnR hx
  let U : TopologicalSpace.Opens (ComplexModel (d + 1)) := ⟨ball x ε, isOpen_ball⟩
  have hGatU : ∀ y ∈ (U : Set (ComplexModel (d + 1))), HolomorphicGeneratorsAt G y :=
    fun y hy => ⟨U, U.isOpen, hy, fun i => (hG i).mono hball⟩
  have hgen : ∀ y ∈ (U : Set (ComplexModel (d + 1))), ∀ F,
      MultiplierIntegrableAt (generatorLog G) ((d + 1 : ℕ) : ℝ) F y volume →
        InSpanAt H y F := by
    intro y hy F hF
    have hFhol : HolAt F y := by
      obtain ⟨_, W, hW, hyW, hFW, _⟩ := hF
      exact eventually_of_mem (hW.mem_nhds hyW) fun z hz =>
        (hFW z hz).differentiableAt (hW.mem_nhds hz)
    exact inSpanAt_of_inGermSpan_range hFhol (hNadel y hy F hF)
  have hHx : ∀ i, HolAt (H i) x := fun i =>
    eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) fun z hz =>
      (hHhol i).differentiableAt (isOpen_ball.mem_nhds hz)
  have hK := idealFGAt_finite_multiplier_colon hψ
    (c := ((d + 1 : ℕ) : ℝ) + 1) (by positivity) hx H hHx
  apply hK.congr
  refine eventually_of_mem (U.isOpen.mem_nhds (mem_ball_self hε)) fun y hy q => ?_
  constructor
  · rintro ⟨hq, hqH⟩
    exact ⟨hq, moreSingularAt_of_multiplier_colon (by omega) G U
      (fun i => (hG i).mono hball) H hgen
      (fun z hz => hne z (hball hz)) hy hq hqH⟩
  · rintro ⟨hq, hgrowth⟩
    exact ⟨hq, fun i => multiplierIntegrableAt_mul_of_growth_bound (hGatU y hy)
      hq hgrowth (hHint i y hy)⟩

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: LocalGrowthCoherence.lean. -/

/-! Full nearby coherence of the actual holomorphic growth ideal of every
finite original analytic family, including zero germs and dimension zero.
The only input is genuine holomorphic family data near the original point.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations

/-- An identically zero original family gives the actual zero germ ideal,
with an empty generating family on one whole neighborhood. -/
theorem idealFGAt_growth_of_eventually_zero_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (G : Fin r → E → ℂ) {x : E}
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, G i z = 0) :
    IdealFGAt (growthGermPredicate G) x := by
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hzero
  refine ⟨U, hU, hxU, Fin 0, inferInstance, Fin.elim0, (fun k => Fin.elim0 k), fun y hy q => ?_⟩
  constructor
  · rintro ⟨hq, hgrowth⟩
    refine ⟨hq, Fin.elim0, (fun k => Fin.elim0 k), ?_⟩
    obtain ⟨C, _, hb⟩ := moreSingularAt_singleLog_iff_norm_sum_bound.mp hgrowth
    have hqzero : ∀ᶠ z in 𝓝 y, q z = 0 := by
      filter_upwards [hb, hU.mem_nhds hy] with z hz hzU
      have hzG := hUsub hzU
      have hsum : (∑ i, ‖G i z‖) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hzG i, norm_zero]
      have hnorm : ‖q z‖ ≤ 0 := by
        simpa only [hsum, mul_zero] using hz
      exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
    change ∀ᶠ z in 𝓝 y, q z = ∑ i : Fin 0, (Fin.elim0 i : E → ℂ) z * (Fin.elim0 i : E → ℂ) z
    simpa only [Fin.sum_univ_zero] using hqzero
  · rintro ⟨hq, a, ha, heq⟩
    refine ⟨hq, moreSingularAt_singleLog_iff_norm_sum_bound.mpr ⟨0, le_rfl, ?_⟩⟩
    filter_upwards [heq] with z hz
    have hqzero : q z = 0 := by simpa using hz
    simp [hqzero]

/-- Actual dimension zero has either the unit or zero growth ideal; no
positive-dimensional Nadel, Skoda or measure assumption is used. -/
theorem idealFGAt_growth_dim_zero {r : ℕ}
    (G : Fin r → ComplexModel 0 → ℂ) (x : ComplexModel 0) :
    IdealFGAt (growthGermPredicate G) x := by
  classical
  by_cases hzero : ∀ i, G i x = 0
  · apply idealFGAt_growth_of_eventually_zero_family G
    exact Eventually.of_forall fun z i => by simpa only [Subsingleton.elim z x] using hzero i
  push Not at hzero
  obtain ⟨i, hi⟩ := hzero
  have hS : ∀ y : ComplexModel 0, 0 < ∑ l, ‖G l y‖ := by
    intro y
    have hix : G i y ≠ 0 := by simpa only [Subsingleton.elim y x] using hi
    exact (norm_pos_iff.mpr hix).trans_le
      (Finset.single_le_sum (fun j _ => norm_nonneg (G j y)) (Finset.mem_univ i))
  have hgrowth : ∀ y (q : ComplexModel 0 → ℂ),
      MoreSingularAt (fun z => logNormSq (q z)) (generatorLog G) y := by
    intro y q
    apply moreSingularAt_singleLog_iff_norm_sum_bound.mpr
    refine ⟨‖q y‖ / ∑ l, ‖G l y‖, div_nonneg (norm_nonneg _) (hS y).le,
      Eventually.of_forall fun z => ?_⟩
    rw [Subsingleton.elim z y, div_mul_cancel₀ _ (hS y).ne']
  have hunit := CoherentIdealColon.idealFGAt_unit x
  apply hunit.congr
  exact Eventually.of_forall fun y q => ⟨fun hq => ⟨hq, hgrowth y q⟩, fun hq => hq.1⟩

/-- Full nearby coherence of the true growth ideal, in every natural
coordinate dimension. Every Skoda/Nadel/colon/nonzero witness is produced
from the actual finite holomorphic family; no coherent ideal is an input. -/
theorem idealFGAt_growth_of_holomorphicGeneratorsAt
    {n r : ℕ} (G : Fin r → ComplexModel n → ℂ)
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x) :
    IdealFGAt (growthGermPredicate G) x := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact idealFGAt_growth_dim_zero G x
  by_cases hzero : ∀ i, ∀ᶠ z in 𝓝 x, G i z = 0
  · exact idealFGAt_growth_of_eventually_zero_family G (eventually_all.mpr hzero)
  have hne : ∃ i, ∃ᶠ z in 𝓝 x, G i z ≠ 0 := by
    by_contra hnot
    apply hzero
    intro i
    have hi : ¬ ∃ᶠ z in 𝓝 x, G i z ≠ 0 := fun h => hnot ⟨i, h⟩
    simpa only [not_frequently, not_ne_iff] using hi
  obtain ⟨i, hi⟩ := hne
  obtain ⟨V, hV, hxV, hGV⟩ := hG
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV x hxV
  let Ω : TopologicalSpace.Opens (ComplexModel n) := ⟨ball x ε, isOpen_ball⟩
  have hGΩ : ∀ j, DifferentiableOn ℂ (G j) Ω := fun j => (hGV j).mono hball
  have hproper : ∀ y ∈ (Ω : Set (ComplexModel n)), ∃ j, ∃ᶠ z in 𝓝 y, G j z ≠ 0 := by
    intro y hy
    refine ⟨i, ?_⟩
    by_contra hnot
    have hyzero : ∀ᶠ z in 𝓝 y, G i z = 0 := by
      simpa only [not_frequently, not_ne_iff] using hnot
    have hxzero := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero
      isOpen_ball (convex_ball x ε).isPreconnected (hGΩ i) hy hyzero x (mem_ball_self hε)
    exact hi (hxzero.mono fun _ hz hne => hne hz)
  exact idealFGAt_growth_of_proper_holomorphic_family hn G Ω hGΩ hproper (mem_ball_self hε)

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: AtlasChartGermGrowth.lean. -/

/-! Exact original varying-atlas holomorphic/growth/span germs in one actual
chart. These dictionaries keep every original function, coefficient and germ;
no fixed global dimension or chosen replacement potential is required.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations
open SGPT.PSH.VariableComplexAtlas

/-- Reindex actual nearby Oka generators by a literal finite natural count,
without changing any original function or nearby germ-span equation. -/
theorem idealFGAt_exists_fin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {J : E → (E → ℂ) → Prop} {x : E} (hJ : IdealFGAt J x) :
    ∃ (V : Set E), IsOpen V ∧ x ∈ V ∧ ∃ (N : ℕ) (F : Fin N → E → ℂ),
      (∀ j, DifferentiableOn ℂ (F j) V) ∧
      ∀ y ∈ V, ∀ q, J y q ↔ InSpanAt F y q := by
  obtain ⟨V, hV, hxV, μ, hμ, s, hs, hgen⟩ := hJ
  let e := (Fintype.equivFin μ).symm
  refine ⟨V, hV, hxV, Fintype.card μ, fun j => s (e j), fun j => hs (e j), ?_⟩
  intro y hy q
  exact (hgen y hy q).trans (CoherentIdealColon.inSpanAt_comp_equiv e s y q).symm

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The original inverse chart converges to the same original point. -/
theorem chartSymm_tendsto (i : A.Index) {x : X} (hx : x ∈ (A.chart i).source) :
    Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
  have h := (A.chart i).continuousAt_symm ((A.chart i).map_source hx)
  rw [ContinuousAt, (A.chart i).left_inv hx] at h
  exact h

/-- Actual original scalar holomorphy is exactly genuine coordinate germ
holomorphy, in any one original compatible chart and its own dimension. -/
theorem atlasHolomorphicAt_iff_chart_holAt (i : A.Index) {x : X}
    (hx : x ∈ (A.chart i).source) {h : X → ℂ} :
    A.AtlasHolomorphicAt h x ↔ HolAt (h ∘ (A.chart i).symm) (A.chart i x) := by
  constructor
  · rintro ⟨U, hU, hxU, hh⟩
    have hD : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
      (A.chart i).isOpen_inter_preimage_symm hU
    have hxD : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
      refine ⟨(A.chart i).map_source hx, ?_⟩
      simpa only [mem_preimage, (A.chart i).left_inv hx] using hxU
    exact holAt_of_differentiableOn hD (hh i) hxD
  · intro hh
    obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hh
    let U : Set X := (A.chart i).source ∩ (A.chart i) ⁻¹' V
    have hU : IsOpen U := (A.chart i).isOpen_inter_preimage hV
    have hlift : A.ChartHolomorphicOn ((h ∘ (A.chart i).symm) ∘ (A.chart i)) U :=
      coordinate_holomorphic_chartHolomorphicOn i
        (fun z hz => (hVsub hz).differentiableWithinAt)
    refine ⟨U, hU, ⟨hx, hxV⟩, fun j => (hlift j).congr ?_⟩
    intro z hz
    simp only [Function.comp_apply, (A.chart i).left_inv hz.2.1]

/-- An actual coordinate holomorphic germ lifts through its original chart. -/
theorem atlasHolomorphicAt_chartLift (i : A.Index) {x : X}
    (hx : x ∈ (A.chart i).source)
    {f : ComplexModel (A.dimension i) → ℂ} (hf : HolAt f (A.chart i x)) :
    A.AtlasHolomorphicAt (f ∘ (A.chart i)) x := by
  apply (atlasHolomorphicAt_iff_chart_holAt (A := A) i hx).mpr
  apply hf.congr
  filter_upwards [(A.chart i).open_target.mem_nhds ((A.chart i).map_source hx)] with z hz
  simp only [Function.comp_apply, (A.chart i).right_inv hz]

/-- The original logarithmic growth order has exactly the same finite bound
in a genuine inverse chart, in both directions. -/
theorem moreSingularAt_iff_chart (i : A.Index) {x : X}
    (hx : x ∈ (A.chart i).source) {u v : X → EReal} :
    MoreSingularAt u v x ↔ MoreSingularAt (u ∘ (A.chart i).symm)
      (v ∘ (A.chart i).symm) (A.chart i x) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (chartSymm_tendsto (A := A) i hx).eventually hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [((A.chart i).continuousAt hx).eventually hC,
      (A.chart i).open_source.mem_nhds hx] with y hy hyS
    simpa only [Function.comp_apply, (A.chart i).left_inv hyS] using hy

/-- Every actual original finite holomorphic combination is exactly its
coordinate combination, and conversely, including the same original germs. -/
theorem atlasIsInSpanAt_chartLift_iff (i : A.Index) {x : X}
    (hx : x ∈ (A.chart i).source) {N : ℕ}
    (F : Fin N → ComplexModel (A.dimension i) → ℂ) {q : X → ℂ} :
    A.AtlasIsInSpanAt (· ∈ range fun j => F j ∘ (A.chart i)) x q ↔
      InSpanAt F (A.chart i x) (q ∘ (A.chart i).symm) := by
  classical
  constructor
  · rintro ⟨hq, L, s, a, hs, ha, heq⟩
    choose σ hσ using hs
    apply inSpanAt_of_inGermSpan_range ((atlasHolomorphicAt_iff_chart_holAt (A := A) i hx).mp hq)
    refine ⟨L, fun j => F (σ j), fun j => a j ∘ (A.chart i).symm,
      fun j => ⟨σ j, rfl⟩, fun j => (atlasHolomorphicAt_iff_chart_holAt (A := A) i hx).mp (ha j), ?_⟩
    filter_upwards [(chartSymm_tendsto (A := A) i hx).eventually heq,
      (A.chart i).open_target.mem_nhds ((A.chart i).map_source hx)] with z hz hzT
    change q ((A.chart i).symm z) = _ at hz ⊢
    rw [hz]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hσ j]
    simp only [Function.comp_apply, (A.chart i).right_inv hzT]
  · rintro ⟨hq, a, ha, heq⟩
    refine ⟨(atlasHolomorphicAt_iff_chart_holAt (A := A) i hx).mpr hq, N,
      fun j => F j ∘ (A.chart i), fun j => a j ∘ (A.chart i),
      fun j => ⟨j, rfl⟩, fun j => atlasHolomorphicAt_chartLift (A := A) i hx (ha j), ?_⟩
    filter_upwards [((A.chart i).continuousAt hx).eventually heq,
      (A.chart i).open_source.mem_nhds hx] with y hy hyS
    simpa only [Function.comp_apply, (A.chart i).left_inv hyS] using hy

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: GermLogarithmicCalculus.lean. -/

/-! Pure finite logarithmic growth and bounded-remainder calculus. Every
inequality is about the original functions, including their common poles. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {X : Type*} [TopologicalSpace X]

/-- Finite original logarithmic growth bounds give the same bound for their
literal sum-of-squares logarithm. No holomorphic or measure premise is used. -/
theorem moreSingularAt_generatorLog_of_single_bounds
    {N : ℕ} {h : Fin N → X → ℂ} {P : X → EReal} {x : X}
    (hh : ∀ i, MoreSingularAt (fun y => logNormSq (h i y)) P x) :
    MoreSingularAt (generatorLog h) P x := by
  classical
  choose D hD using hh
  let K : Fin N → ℝ := fun i => Real.exp (D i)
  let C : ℝ := 1 + ∑ i : Fin N, K i
  have hK : ∀ i, 0 < K i := fun i => Real.exp_pos _
  have hsumK : 0 ≤ ∑ i : Fin N, K i := Finset.sum_nonneg fun i _ => (hK i).le
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨Real.log C, ?_⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ i,
      multiplierDensity P 1 (h i) y ≤ ENNReal.ofReal (K i) := by
    apply eventually_all.mpr
    intro i
    exact (hD i).mono fun _ hy => density_le_exp_of_original_log_bound hy
  filter_upwards [hall] with y hy
  cases hPy : P y with
  | bot =>
    have hz (i : Fin N) : h i y = 0 := by
      by_contra hi
      have htop := multiplierDensity_eq_top_at_pole zero_lt_one hPy hi
      have hle := hy i
      rw [htop] at hle
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
    rw [(generatorLog_eq_bot_iff h y).mpr hz]
    simp
  | top => simp
  | coe t =>
    have hreal (i : Fin N) : ‖h i y‖ ^ 2 * Real.exp (-t) ≤ K i := by
      apply (ENNReal.ofReal_le_ofReal_iff (hK i).le).mp
      simpa only [multiplierDensity, hPy, multiplierWeight_coe, one_mul,
        ← ENNReal.ofReal_mul (sq_nonneg (‖h i y‖))] using hy i
    have hsum : generatorNormSq h y * Real.exp (-t) ≤ ∑ i : Fin N, K i := by
      rw [generatorNormSq, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hreal i
    have hgen : generatorNormSq h y ≤ C * Real.exp t := by
      calc generatorNormSq h y
          = (generatorNormSq h y * Real.exp (-t)) * Real.exp t := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ (∑ i : Fin N, K i) * Real.exp t :=
          mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
        _ ≤ _ := by dsimp [C]; nlinarith [Real.exp_pos t]
    rw [generatorLog_eq_log_sum]
    calc ENNReal.log (ENNReal.ofReal (∑ i, ‖h i y‖ ^ 2))
        ≤ ENNReal.log (ENNReal.ofReal (C * Real.exp t)) :=
          ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hgen)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.log_mul_add,
          ENNReal.log_ofReal_of_pos hC, ENNReal.log_ofReal_of_pos (Real.exp_pos t),
          Real.log_exp, add_comm]

/-- Positive scaling preserves the actual additive growth order. -/
theorem moreSingularAt_pos_mul {f g : X → EReal} {x : X} {c : ℝ} (hc : 0 < c)
    (hfg : MoreSingularAt f g x) :
    MoreSingularAt (fun y => (c : EReal) * f y) (fun y => (c : EReal) * g y) x := by
  obtain ⟨D, hD⟩ := hfg
  refine ⟨c * D, ?_⟩
  filter_upwards [hD] with y hy
  have hl := mul_le_mul_of_nonneg_left hy (EReal.coe_nonneg.mpr hc.le)
  simpa only [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le)
    (EReal.coe_ne_top c), ← EReal.coe_mul] using hl

/-- A literal bounded real remainder produces both genuine growth orders. -/
theorem moreSingularAt_pair_of_bounded_remainder
    {u v : X → EReal} {b : X → ℝ} {x : X}
    (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => v y + (b y : EReal)) :
    MoreSingularAt u v x ∧ MoreSingularAt v u x := by
  obtain ⟨B, _, hB⟩ := hb
  constructor
  · refine ⟨B, ?_⟩
    filter_upwards [heq, hB] with y hy hby
    rw [hy]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp hby).2)
  · refine ⟨B, ?_⟩
    filter_upwards [heq, hB] with y hy hby
    rw [hy, add_assoc, ← EReal.coe_add]
    have h0 : (0 : EReal) ≤ ((b y + B : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by linarith [(abs_le.mp hby).1])
    simpa only [add_zero] using add_le_add (le_refl (v y)) h0

/-- The normalized original potential has exactly the original finite-family
logarithmic type; the positive coefficient is actually inverted here. -/
theorem normalized_moreSingularAt_pair
    {u v : X → EReal} {b : X → ℝ} {x : X} {c : ℝ} (hc : 0 < c)
    (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => (c : EReal) * v y + (b y : EReal)) :
    MoreSingularAt (fun y => ((c⁻¹ : ℝ) : EReal) * u y) v x ∧
      MoreSingularAt v (fun y => ((c⁻¹ : ℝ) : EReal) * u y) x := by
  obtain ⟨huv, hvu⟩ := moreSingularAt_pair_of_bounded_remainder hb heq
  have h1 := moreSingularAt_pos_mul (inv_pos.mpr hc) huv
  have h2 := moreSingularAt_pos_mul (inv_pos.mpr hc) hvu
  simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one,
    one_mul] using And.intro h1 h2

/-- Two actual germ bounds supply one real bounded remainder on a whole
neighborhood, with the same literal values and common poles retained. -/
theorem exists_bounded_remainder_of_moreSingularAt_pair
    {u v : X → EReal} {x : X}
    (hu : ∀ᶠ y in 𝓝 x, u y ≠ ⊤) (hv : ∀ᶠ y in 𝓝 x, v y ≠ ⊤)
    (huv : MoreSingularAt u v x) (hvu : MoreSingularAt v u x) :
    ∃ b : X → ℝ, BoundedRealGermAt b x ∧
      u =ᶠ[𝓝 x] fun y => v y + (b y : EReal) := by
  obtain ⟨C, hC⟩ := huv
  obtain ⟨D, hD⟩ := hvu
  let b : X → ℝ := fun y => canonicalERealDiffToReal (u y) (v y)
  refine ⟨b, ⟨|C| + |D|, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hu, hv, hC, hD] with y huy hvy hCy hDy
    have htype : SameSingularityTypeOn u v {y} :=
      ⟨⟨C, fun z hz => by simpa only [mem_singleton_iff.mp hz] using hCy⟩,
        ⟨D, fun z hz => by simpa only [mem_singleton_iff.mp hz] using hDy⟩⟩
    by_cases hp : u y = ⊥
    · have hvp := htype.2.eq_bot_of_eq_bot (mem_singleton y) hp
      simp only [b, hp, hvp, canonicalERealDiffToReal_bot_bot, abs_zero]
      positivity
    · have hvp : v y ≠ ⊥ := fun hvp => hp (htype.1.eq_bot_of_eq_bot (mem_singleton y) hvp)
      have huc := EReal.coe_toReal huy hp
      have hvc := EReal.coe_toReal hvy hvp
      rw [← huc, ← hvc, ← EReal.coe_add] at hCy hDy
      have hCr := EReal.coe_le_coe_iff.mp hCy
      have hDr := EReal.coe_le_coe_iff.mp hDy
      change |canonicalERealDiffToReal (u y) (v y)| ≤ _
      rw [← huc, ← hvc, canonicalERealDiffToReal_coe_coe]
      exact abs_le.mpr ⟨by linarith [le_abs_self D, abs_nonneg C],
        by linarith [le_abs_self C, abs_nonneg D]⟩
  · filter_upwards [hu, hv, hC, hD] with y huy hvy hCy hDy
    have hpole : u y = ⊥ ↔ v y = ⊥ := by
      constructor <;> intro hp
      · exact le_bot_iff.mp (by simpa [hp] using hDy)
      · exact le_bot_iff.mp (by simpa [hp] using hCy)
    by_cases hp : u y = ⊥
    · simp only [b, hp, hpole.mp hp, canonicalERealDiffToReal_bot_bot, EReal.coe_zero,
        add_zero]
    · have hvp : v y ≠ ⊥ := fun hvp => hp (hpole.mpr hvp)
      change u y = v y + (canonicalERealDiffToReal (u y) (v y) : EReal)
      have huc := EReal.coe_toReal huy hp
      have hvc := EReal.coe_toReal hvy hvp
      rw [← huc, ← hvc, canonicalERealDiffToReal_coe_coe, ← EReal.coe_add]
      congr 1
      ring

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: CoordinateGrowthType.lean. -/

/-! Nearby generators of the actual growth ideal retain the same literal
logarithmic type, including common zero germs. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- The original member of a finite family has its actual norm growth. -/
theorem moreSingularAt_single_generator {r : ℕ} (G : Fin r → E → ℂ)
    (x : E) (i : Fin r) :
    MoreSingularAt (fun z => logNormSq (G i z)) (generatorLog G) x := by
  apply moreSingularAt_singleLog_iff_norm_sum_bound.mpr
  refine ⟨1, zero_le_one, Eventually.of_forall fun z => ?_⟩
  simpa only [one_mul] using Finset.single_le_sum
    (fun j _ => norm_nonneg (G j z)) (Finset.mem_univ i)

/-- Both genuine logarithmic type bounds are produced from the actual
finite nearby generating equations. No type equivalence is supplied. -/
theorem moreSingularAt_generatorLog_pair_of_growth_generators
    {r N : ℕ} {G : Fin r → E → ℂ} {F : Fin N → E → ℂ} {x : E}
    (hG : ∀ i, HolAt (G i) x) (hF : ∀ j, HolAt (F j) x)
    (hgen : ∀ q, growthGermPredicate G x q ↔ InSpanAt F x q) :
    MoreSingularAt (generatorLog G) (generatorLog F) x ∧
      MoreSingularAt (generatorLog F) (generatorLog G) x := by
  classical
  constructor
  · apply moreSingularAt_generatorLog_of_single_bounds
    intro i
    have hGi : growthGermPredicate G x (G i) :=
      ⟨hG i, moreSingularAt_single_generator G x i⟩
    exact moreSingularAt_singleLog_iff_norm_sum_bound.mpr
      (exists_norm_sum_bound_of_inSpanAt ((hgen _).mp hGi))
  · apply moreSingularAt_generatorLog_of_single_bounds
    intro j
    exact ((hgen _).mpr (inSpanAt_self hF j)).2

/-- A finite original family logarithm is never plus infinity. -/
theorem generatorLog_ne_top {T : Type*} {N : ℕ} (F : Fin N → T → ℂ) (y : T) :
    generatorLog F y ≠ ⊤ := by
  rw [generatorLog_eq_log_sum]
  exact fun h => ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)

/-- Positive scalar multiplication preserves absence of plus infinity. -/
theorem positive_mul_ne_top {a : EReal} (ha : a ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * a ≠ ⊤ := by
  cases a with
  | bot => simp only [EReal.coe_mul_bot_of_pos hc, ne_eq, bot_ne_top, not_false_eq_true]
  | top => exact False.elim (ha rfl)
  | coe a =>
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _

/-- The original source potential with coefficient c acquires an actual
bounded real remainder for the PRODUCED coherent generators. -/
theorem exists_bounded_remainder_of_growth_generators
    {r N : ℕ} {G : Fin r → E → ℂ} {F : Fin N → E → ℂ} {x : E}
    {u : E → EReal} {b : E → ℝ} {c : ℝ} (hc : 0 < c)
    (hG : ∀ i, HolAt (G i) x) (hF : ∀ j, HolAt (F j) x)
    (hgen : ∀ q, growthGermPredicate G x q ↔ InSpanAt F x q)
    (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog G y + (b y : EReal)) :
    ∃ d : E → ℝ, BoundedRealGermAt d x ∧
      u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog F y + (d y : EReal) := by
  obtain ⟨hGF, hFG⟩ := moreSingularAt_generatorLog_pair_of_growth_generators hG hF hgen
  obtain ⟨huG, hGu⟩ := moreSingularAt_pair_of_bounded_remainder hb heq
  have hGFc := moreSingularAt_pos_mul hc hGF
  have hFGc := moreSingularAt_pos_mul hc hFG
  apply exists_bounded_remainder_of_moreSingularAt_pair
  · filter_upwards [heq] with y hy
    rw [hy]
    exact EReal.add_ne_top (positive_mul_ne_top (generatorLog_ne_top G y) hc)
      (EReal.coe_ne_top _)
  · exact Eventually.of_forall fun y => positive_mul_ne_top (generatorLog_ne_top F y) hc
  · exact huG.trans hGFc
  · exact hFGc.trans hGu

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: AtlasCanonicalGrowth.lean. -/

/-! ONE intrinsic growth ideal on all original points. Actual local
presentations identify it with coordinate growth germs; no overlap or coherent
ideal is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations
open SGPT.PSH.VariableComplexAtlas

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The single original global ideal to be proved coherent. Its membership
only uses actual original holomorphic germs and the unchanged potential. -/
def atlasCanonicalGrowthIdeal (A : VariableComplexAtlas X) (c : ℚ) (u : X → EReal) :
    AtlasGermIdeal A :=
  atlasInftyIdeal A (fun y => (((c : ℝ)⁻¹ : ℝ) : EReal) * u y)

/-- Every actual common-c presentation identifies the same global ideal
membership with the original finite family's genuine growth condition. -/
theorem mem_atlasCanonicalGrowthIdeal_iff_growth
    {u : X → EReal} {c : ℚ} (hc : 0 < c) {r : ℕ} {G : Fin r → X → ℂ}
    {b : X → ℝ} {x : X} (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal))
    {q : X → ℂ} :
    (atlasCanonicalGrowthIdeal A c u).mem x q ↔
      A.AtlasHolomorphicAt q x ∧
        MoreSingularAt (fun y => logNormSq (q y)) (generatorLog G) x := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨hPG, hGP⟩ := normalized_moreSingularAt_pair hcR hb heq
  change (A.AtlasHolomorphicAt q x ∧ MoreSingularAt _ _ x) ↔ _
  exact and_congr_right fun _ => ⟨fun hq => hq.trans hPG, fun hq => hq.trans hGP⟩

/-- The same actual original membership is exactly the coordinate growth
germ, without changing the original test function or its holomorphic germ. -/
theorem mem_atlasCanonicalGrowthIdeal_iff_chart_growth
    {u : X → EReal} {c : ℚ} (hc : 0 < c) {r : ℕ} {G : Fin r → X → ℂ}
    {b : X → ℝ} {x : X} (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal))
    (i : A.Index) (hx : x ∈ (A.chart i).source) {q : X → ℂ} :
    (atlasCanonicalGrowthIdeal A c u).mem x q ↔
      growthGermPredicate (fun j => G j ∘ (A.chart i).symm)
        (A.chart i x) (q ∘ (A.chart i).symm) := by
  rw [mem_atlasCanonicalGrowthIdeal_iff_growth hc hb heq]
  change _ ↔ HolAt _ _ ∧ MoreSingularAt _ _ _
  rw [atlasHolomorphicAt_iff_chart_holAt (A := A) i hx,
    moreSingularAt_iff_chart (A := A) i hx]
  rfl

end SGPT.PSH.GlobalAnalyticType

end

/-! Consolidated checked atom: AtlasCoherentGrowthType.lean. -/

/-! Actual original connected presentations for ONE intrinsic global
coherent holomorphic ideal. The ideal and its nearby generators are produced
from the original local analytic data. No output ideal/certificate is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalAnalyticType

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open OkaRelationSheaf OkaIdealOperations
open SGPT.PSH.VariableComplexAtlas

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- A common-c original analytic presentation supplies actual finite
coherent generators of the SAME global ideal and a literal bounded remainder
for the SAME original potential, on one connected original neighborhood. -/
theorem exists_local_atlasCanonicalGrowth_type
    {u : X → EReal} {c : ℚ} (hc : 0 < c)
    {r : ℕ} {G : Fin r → X → ℂ} {b : X → ℝ} {C : ℝ} {U : Set X}
    (hC : 0 ≤ C) (hU : IsOpen U)
    (hG : ∀ j, A.ChartHolomorphicOn (G j) U)
    (hb : ∀ y ∈ U, |b y| ≤ C)
    (heq : EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal)) U)
    {x : X} (hxU : x ∈ U) :
    ∃ (N : ℕ) (F : Fin N → X → ℂ) (d : X → ℝ) (B : ℝ) (W : Set X),
      0 ≤ B ∧ IsOpen W ∧ IsConnected W ∧ x ∈ W ∧
        (∀ j, A.ChartHolomorphicOn (F j) W) ∧
        (∀ y ∈ W, ∀ q, (atlasCanonicalGrowthIdeal A c u).mem y q ↔
          A.AtlasIsInSpanAt (· ∈ range F) y q) ∧
        (∀ y ∈ W, |d y| ≤ B) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog F y + (d y : EReal)) W := by
  classical
  obtain ⟨i, hxS⟩ := A.cover x
  let e := A.chart i
  let D : Set (ComplexModel (A.dimension i)) := e.target ∩ e.symm ⁻¹' U
  have hD : IsOpen D := e.isOpen_inter_preimage_symm hU
  have hxD : e x ∈ D := by
    refine ⟨e.map_source hxS, ?_⟩
    simpa only [mem_preimage, e, (A.chart i).left_inv hxS] using hxU
  let G' : Fin r → ComplexModel (A.dimension i) → ℂ := fun j => G j ∘ e.symm
  have hG' : HolomorphicGeneratorsAt G' (e x) := ⟨D, hD, hxD, fun j => hG j i⟩
  obtain ⟨V, hV, hxV, N, F, hF, hgen⟩ := idealFGAt_exists_fin
    (idealFGAt_growth_of_holomorphicGeneratorsAt G' hG')
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hGx : ∀ j, HolAt (G' j) (e x) :=
    fun j => holAt_of_differentiableOn hD (hG j i) hxD
  have hFx : ∀ j, HolAt (F j) (e x) :=
    fun j => holAt_of_differentiableOn hV (hF j) hxV
  have hb' : BoundedRealGermAt (b ∘ e.symm) (e x) :=
    ⟨C, hC, eventually_of_mem (hD.mem_nhds hxD) fun z hz => hb _ hz.2⟩
  have heq' : (u ∘ e.symm) =ᶠ[𝓝 (e x)]
      fun z => ((c : ℝ) : EReal) * generatorLog G' z + ((b ∘ e.symm) z : EReal) :=
    eventually_of_mem (hD.mem_nhds hxD) fun z hz => heq hz.2
  obtain ⟨d, ⟨B, hB, hd⟩, hdeq⟩ := exists_bounded_remainder_of_growth_generators
    hcR hGx hFx (hgen _ hxV) hb' heq'
  have hall : ∀ᶠ z in 𝓝 (e x),
      z ∈ V ∧ z ∈ D ∧ |d z| ≤ B ∧
        u (e.symm z) = ((c : ℝ) : EReal) * generatorLog F z + (d z : EReal) := by
    filter_upwards [hV.mem_nhds hxV, hD.mem_nhds hxD, hd, hdeq] with z hzV hzD hdz hez
    exact ⟨hzV, hzD, hdz, hez⟩
  obtain ⟨W, ⟨hW, hxW, hWconn⟩, hWsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (e x)).mem_iff.mp hall
  let P : Set X := e.source ∩ e ⁻¹' W
  have hP : IsOpen P := e.isOpen_inter_preimage hW
  have hWtarget : W ⊆ e.target := fun z hz => (hWsub hz).2.1.1
  have himage : e.symm '' W = P := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (hWtarget hz), ?_⟩
      change e (e.symm z) ∈ W
      simpa only [e.right_inv (hWtarget hz)] using hz
    · rintro ⟨hyS, hyW⟩
      exact ⟨e y, hyW, e.left_inv hyS⟩
  have hPconn : IsConnected P := by
    rw [← himage]
    exact hWconn.image _ (e.continuousOn_symm.mono hWtarget)
  refine ⟨N, fun j => F j ∘ e, d ∘ e, B, P,
    hB, hP, hPconn, ⟨hxS, hxW⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    exact coordinate_holomorphic_chartHolomorphicOn (A := A) i
      ((hF j).mono fun z hz => (hWsub hz).1)
  · intro y hy q
    have hyU : y ∈ U := by
      have h := (hWsub hy.2).2.1.2
      simpa only [mem_preimage, e.left_inv hy.1] using h
    have hby : BoundedRealGermAt b y :=
      ⟨C, hC, eventually_of_mem (hU.mem_nhds hyU) fun z hz => hb z hz⟩
    have hey : u =ᶠ[𝓝 y]
        fun z => ((c : ℝ) : EReal) * generatorLog G z + (b z : EReal) :=
      eventually_of_mem (hU.mem_nhds hyU) fun z hz => heq hz
    exact (mem_atlasCanonicalGrowthIdeal_iff_chart_growth hc hby hey i hy.1).trans
      ((hgen (e y) (hWsub hy.2).1 (q ∘ e.symm)).trans
        (atlasIsInSpanAt_chartLift_iff (A := A) i hy.1 F).symm)
  · intro y hy
    exact (hWsub hy.2).2.2.1
  · intro y hy
    have h := (hWsub hy.2).2.2.2
    simpa only [generatorLog, generatorVector, Function.comp_apply, e.left_inv hy.1] using h

/-- Whole compact local-to-global existence: ONE positive rational scalar,
ONE actual coherent original holomorphic ideal, and SAME original analytic
potential on connected neighborhoods. No ideal/coherence/type certificate is
an input, and every original varying chart dimension including0 is retained. -/
theorem exists_atlasCoherentRationalAnalyticType_of_compact
    [CompactSpace X] {u : X → EReal} (ha : A.HasRationalAnalyticType u) :
    ∃ (c : ℚ) (I : AtlasGermIdeal A), A.HasAtlasCoherentRationalAnalyticType u c I := by
  classical
  obtain ⟨c, m, N, G, b, C, U, hc, hcover, hdata⟩ :=
    exists_uniform_rational_analytic_coefficient ha
  have hlocal (x : X) :
      ∃ (N : ℕ) (F : Fin N → X → ℂ) (d : X → ℝ) (B : ℝ) (W : Set X),
        0 ≤ B ∧ IsOpen W ∧ IsConnected W ∧ x ∈ W ∧
          (∀ j, A.ChartHolomorphicOn (F j) W) ∧
          (∀ y ∈ W, ∀ q, (atlasCanonicalGrowthIdeal A c u).mem y q ↔
            A.AtlasIsInSpanAt (· ∈ range F) y q) ∧
          (∀ y ∈ W, |d y| ≤ B) ∧
          EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog F y + (d y : EReal)) W := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨hC, hU, _, hG, hb, heq⟩ := hdata i
    exact exists_local_atlasCanonicalGrowth_type hc hC hU hG hb heq hi
  refine ⟨c, atlasCanonicalGrowthIdeal A c u, hc, ?_, hlocal⟩
  intro x
  obtain ⟨N, F, d, B, W, _, hW, _, hxW, hF, hgen, _, _⟩ := hlocal x
  exact ⟨W, hW, hxW, N, F, hF, hgen⟩

end SGPT.PSH.GlobalAnalyticType

end

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The complete compact source assertion: every original QPSH potential
with rational analytic singularities admits ONE global coherent type.
The construction actually uses only the original local analytic data. -/
theorem IsQPSH.exists_coherentRationalAnalyticType_of_compact
    [CompactSpace X] {u : X → EReal} (_hu : A.IsQPSH u)
    (ha : A.HasRationalAnalyticType u) :
    ∃ (c : ℚ) (I : AtlasGermIdeal A), A.HasAtlasCoherentRationalAnalyticType u c I :=
  SGPT.PSH.GlobalAnalyticType.exists_atlasCoherentRationalAnalyticType_of_compact ha

end SGPT.PSH.VariableComplexAtlas
