import SGPT.NPP.CapacityModulus
import SGPT.PSH.SourceCapacityConvergence
import SGPT.Toric.ProjectiveToricNonPluripolarMass
import SGPT.Toric.ProjectiveToricReverse
import SGPT.Toric.ProjectiveToricBottomExample
import SGPT.Toric.ProjectiveToricNewtonBody
import SGPT.Toric.ProjectiveToricModelEnvelope
import SGPT.Toric.LogLogModelEnvelope
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-!
# Decreasing sequences need not converge in capacity on an open set

Source erratum for `prop:mono_psh_cap` (chapter `chapter_npp.tex`), clause (1):
with the book's `def:conv_cap`, which measures the whole gap sets
`{φ_i > φ + δ} ⊆ U` with the global capacity `Cap_θ`, a decreasing sequence of
`θ`-psh functions on an open set `U` need not converge in capacity.

Counterexample: `X = ℙ¹` with `θ = ω_FS` (a Kähler form, so its class is big
and `V_θ = 0`), `U` the punctured unit disc `{0 < |z| < 1}` of the finite chart,
`u_j = |z|^{2j}` (decreasing to `0` on `U`). For `δ = 1/2` and `t ∈ [3/4, 1)`
with `t^j > 1/2`, the gap contains the circle `{|z|² = t}`, and the global
`θ`-psh function `ψ = max(log t - log(1+|z|²), log(|z|²/(1+|z|²)))` is a
capacity competitor (`-1 ≤ ψ ≤ 0`) whose non-pluripolar measure has mass `1` and
lives on that circle (by plurifine locality, the two logarithmic pieces have
zero non-pluripolar mass). Hence `Cap_θ(gap_j) ≥ 1` for every `j`.

The statement is correct for convergence in capacity on compact subsets of `U`
(the form of `[GZ17, Prop. 4.25]`); that corrected version is not proved here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.MonotoneCapacityCounterexample

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Toric SGPT.Convex

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The Fubini--Study form as a source closed real `(1,1)`-form. -/
def fsForm : AtlasClosedRealOneOneForm (ofFixedModel 1 P1) :=
  nativeClosedFormToAtlas projectiveNativeFSBackground.form

/-- The finite affine coordinate of a point. -/
def fc (p : P1) : ℂ := projectiveModelChart false p 0

/-- The punctured unit disc `{0 < |z| < 1}` of the finite chart. -/
def puncturedDisc : Opens P1 where
  carrier := projectiveToricBoundaryᶜ ∩ ((projectiveModelChart false).source ∩
    projectiveModelChart false ⁻¹' {z : ComplexModel 1 | ‖z 0‖ < 1})
  is_open' := isClosed_projectiveToricBoundary.isOpen_compl.inter
    ((projectiveModelChart false).isOpen_inter_preimage
      (isOpen_lt (continuous_norm.comp (PiLp.continuous_apply 2 _ 0)) continuous_const))

/-- The decreasing sequence `|z|^{2j}`. -/
def seq (j : ℕ) (p : P1) : EReal := (((‖fc p‖ ^ 2) ^ j : ℝ) : EReal)

theorem profile_convex (j : ℕ) :
    ConvexOn ℝ univ (fun m : EuclideanSpace ℝ (Fin 1) =>
      Real.exp (j * m 0) + projectiveLineLogPartition (m 0)) := by
  have hexp : ConvexOn ℝ univ (fun x : ℝ => Real.exp (j * x)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h := convexOn_exp.2 (mem_univ (j * x)) (mem_univ (j * y)) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    calc Real.exp (j * (a * x + b * y)) = Real.exp (a * (j * x) + b * (j * y)) := by ring_nf
      _ ≤ _ := h
  have hsum : ConvexOn ℝ univ (fun x : ℝ => Real.exp (j * x) + projectiveLineLogPartition x) :=
    hexp.add convexOn_projectiveLineLogPartition
  have h := hsum.comp_linearMap
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).toLinearMap
  simpa [Function.comp_def] using h

/-- Each `|z|^{2j}` is `ω_FS`-psh on the punctured disc, in the source sense. -/
theorem isThetaPSHOn_seq (j : ℕ) :
    (ofFixedModel 1 P1).IsThetaPSHOn fsForm (seq j) puncturedDisc := by
  apply isThetaPSHOn_of_finite_single_chart (A := ofFixedModel 1 P1)
    (i := projectiveNativeChart false) (fun p hp => hp.2.1) projectiveFSPotential
    contDiff_projectiveFSPotential.contDiffOn (fun _ _ => rfl)
  · intro z hz
    have hzT : z ∈ complexTorus 1 := (projectiveToricBoundary_chart_off_iff false z).mp hz.2.1
    apply (plurisubharmonicOn_tropicalPullback_of_convexOn (profile_convex j) z hzT).congr
    filter_upwards [(isOpen_complexTorus 1).mem_nhds hzT,
      (projectiveModelChart false).open_target.mem_nhds hz.1] with y hy hyT
    have hy0 : y 0 ≠ 0 := hy 0
    change ((Real.exp (j * tropicalization y 0) +
        projectiveLineLogPartition (tropicalization y 0) : ℝ) : EReal) =
      (((‖projectiveModelChart false ((projectiveModelChart false).symm y) 0‖ ^ 2) ^ j : ℝ) :
        EReal) + (projectiveFSPotential y : EReal)
    rw [(projectiveModelChart false).right_inv hyT, ← EReal.coe_add,
      projectiveLineLogPartition_tropicalization hy0, projectiveFSPotential_eq,
      tropicalization_apply_eq_log_norm_sq, Real.exp_nat_mul,
      Real.exp_log (pow_pos (norm_pos_iff.mpr hy0) 2)]
  · intro p _
    exact ⟨_, rfl⟩

theorem isThetaPSH_zero_fsForm :
    (ofFixedModel 1 P1).IsThetaPSH fsForm (fun _ => (0 : EReal)) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [fsForm, sourceNativeAtlasForm_roundTrip]
  exact PluripolarCapacityDichotomy.isThetaPshPotential_zero _

theorem seq_antitone {p : P1} (hp : p ∈ puncturedDisc) : Antitone fun j => seq j p := by
  have h1 : ‖fc p‖ ^ 2 < 1 := by
    have : ‖fc p‖ < 1 := hp.2.2
    nlinarith [norm_nonneg (fc p)]
  intro i j hij
  exact EReal.coe_le_coe_iff.mpr (pow_le_pow_of_le_one (by positivity) h1.le hij)

theorem seq_tendsto {p : P1} (hp : p ∈ puncturedDisc) :
    Tendsto (fun j => seq j p) atTop (𝓝 0) := by
  have h1 : ‖fc p‖ ^ 2 < 1 := by
    have : ‖fc p‖ < 1 := hp.2.2
    nlinarith [norm_nonneg (fc p)]
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h1
  have h' := (continuous_coe_real_ereal.tendsto 0).comp h
  simpa [seq, Function.comp_def] using h'

/-! ### The capacity competitor -/

/-- The `log(|z|²/(1+|z|²))` piece (pole at the origin). -/
def outer : P1 → EReal := projectiveLogSingularity

/-- The `log t - log(1+|z|²)` piece (pole at infinity). -/
def inner (t : ℝ) : P1 → EReal :=
  fun p => projectiveOppositeLogSingularity p - ((-Real.log t : ℝ) : EReal)

/-- The competitor `max(inner, outer) = log max(t, |z|²) - log(1 + |z|²)`. -/
def comp (t : ℝ) : P1 → EReal := fun p => max (inner t p) (outer p)

theorem psh_outer : IsThetaPshPotential projectiveNativeFSBackground.form.val outer :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveLogSingularity

theorem psh_opposite :
    IsThetaPshPotential projectiveNativeFSBackground.form.val projectiveOppositeLogSingularity :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveOppositeLogSingularity

theorem psh_inner (t : ℝ) :
    IsThetaPshPotential projectiveNativeFSBackground.form.val (inner t) :=
  psh_opposite.sub_const (-Real.log t)

theorem psh_comp (t : ℝ) :
    IsThetaPshPotential projectiveNativeFSBackground.form.val (comp t) :=
  IsThetaPshPotential.max (psh_inner t) psh_outer

theorem newtonBody_opposite :
    projectiveToricNewtonBody projectiveOppositeLogSingularity = {0} := by
  rw [projectiveToricNewtonBody, convexNewtonBody,
    projectiveToricLegendre_oppositeLogSingularity, effectiveDomain_indicator]
  exact isClosed_singleton.closure_eq

theorem mass_outer :
    DiagonalMass.diagonalPotentialMeasure projectiveNativeFSBackground.form outer psh_outer univ
      = 0 := by
  have h := projectiveToricNonPluripolarMeasure_univ_eq_newtonLength
    isThetaPSH_projectiveLogSingularity projectiveLogSingularity_circleInvariant
  rw [projectiveToricNewtonBody_logSingularity, measure_singleton] at h
  exact h

theorem mass_inner (t : ℝ) :
    DiagonalMass.diagonalPotentialMeasure projectiveNativeFSBackground.form (inner t)
      (psh_inner t) univ = 0 := by
  have h := projectiveToricNonPluripolarMeasure_univ_eq_newtonLength
    isThetaPSH_projectiveOppositeLogSingularity projectiveOppositeLogSingularity_circleInvariant
  rw [newtonBody_opposite, measure_singleton] at h
  have he := GlobalMeasureInvariance.globalMixedMeasure_sub_const
    (fun _ : Fin 1 => psh_opposite.1) (fun _ => -Real.log t)
  have he' := congrArg (fun μ : Measure P1 => μ univ) he
  exact he'.trans h

/-- A point of `ℙ¹` is the origin, the point at infinity, or a torus point
of the finite chart. -/
theorem trichotomy (p : P1) :
    p = projectiveOrigin ∨ p = projectiveInfinity ∨
      (p ∉ projectiveToricBoundary ∧ p ∈ (projectiveModelChart false).source ∧
        fc p ≠ 0) := by
  by_cases hb : p ∈ projectiveToricBoundary
  · rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨hb, projectiveToricBoundary_compl_subset_finite_source hb, ?_⟩)
    exact projectiveFiniteCoordinate_mem_torus_of_off_boundary hb 0

/-- Values at torus points of the finite chart. -/
theorem values_torus {t : ℝ} (_ht : 0 < t) {p : P1}
    (hs : p ∈ (projectiveModelChart false).source) (h0 : fc p ≠ 0) :
    inner t p = ((Real.log t - Real.log (1 + ‖fc p‖ ^ 2) : ℝ) : EReal) ∧
      outer p = ((Real.log (‖fc p‖ ^ 2 / (1 + ‖fc p‖ ^ 2)) : ℝ) : EReal) := by
  have hp : (projectiveModelChart false).symm (projectiveModelChart false p) = p :=
    (projectiveModelChart false).left_inv hs
  have hn : Complex.normSq (projectiveModelChart false p 0) = ‖fc p‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  have hpos : 0 < ‖fc p‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
  constructor
  · have hopp := projectiveOppositeLogSingularity_finite (projectiveModelChart false p)
    rw [hp, projectiveFSPotential_eq, hn] at hopp
    change projectiveOppositeLogSingularity p - ((-Real.log t : ℝ) : EReal) = _
    rw [hopp, ← EReal.coe_sub]
    congr 1
    ring
  · have hlog := projectiveLogSingularity_finite (projectiveModelChart false p)
    rw [hp, hn] at hlog
    change projectiveLogSingularity p = _
    rw [hlog, ENNReal.log_ofReal_of_pos (div_pos hpos (by positivity))]

theorem values_origin (t : ℝ) :
    inner t projectiveOrigin = (Real.log t : EReal) ∧ outer projectiveOrigin = ⊥ := by
  refine ⟨?_, projectiveLogSingularity_origin⟩
  change projectiveOppositeLogSingularity projectiveOrigin - ((-Real.log t : ℝ) : EReal) = _
  rw [projectiveOppositeLogSingularity_origin, zero_sub, ← EReal.coe_neg, neg_neg]

theorem values_infinity (t : ℝ) :
    inner t projectiveInfinity = ⊥ ∧ outer projectiveInfinity = 0 := by
  refine ⟨?_, projectiveLogSingularity_infinity⟩
  change projectiveOppositeLogSingularity projectiveInfinity - ((-Real.log t : ℝ) : EReal) = _
  rw [projectiveOppositeLogSingularity_infinity]
  exact EReal.bot_sub _

theorem log_three_sevenths : -1 ≤ Real.log (3 / 7) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

theorem ratio_ge {t s : ℝ} (ht : 3 / 4 ≤ t) (hts : t ≤ s) : 3 / 7 ≤ s / (1 + s) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem comp_le_zero {t : ℝ} (ht : 3 / 4 ≤ t) (ht1 : t < 1) (p : P1) : comp t p ≤ 0 := by
  have htpos : 0 < t := by linarith
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht1.le
  rcases trichotomy p with rfl | rfl | ⟨_, hs, h0⟩
  · obtain ⟨hi, ho⟩ := values_origin t
    change max _ _ ≤ _
    rw [hi, ho, max_bot_right]
    exact_mod_cast hlogt
  · obtain ⟨hi, ho⟩ := values_infinity t
    change max _ _ ≤ _
    rw [hi, ho, max_bot_left]
  · obtain ⟨hi, ho⟩ := values_torus htpos hs h0
    change max _ _ ≤ _
    rw [hi, ho]
    have hpos : 0 < ‖fc p‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
    apply max_le
    · have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + ‖fc p‖ ^ 2 by linarith)
      exact_mod_cast (by linarith : Real.log t - Real.log (1 + ‖fc p‖ ^ 2) ≤ 0)
    · have h : ‖fc p‖ ^ 2 / (1 + ‖fc p‖ ^ 2) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      exact_mod_cast Real.log_nonpos (by positivity) h

theorem neg_one_le_comp {t : ℝ} (ht : 3 / 4 ≤ t) (ht1 : t < 1) (p : P1) :
    (0 : EReal) ≤ comp t p + 1 := by
  have htpos : 0 < t := by linarith
  have hkey : -1 ≤ Real.log (t / (1 + t)) :=
    log_three_sevenths.trans (Real.log_le_log (by norm_num) (ratio_ge ht le_rfl))
  suffices h : ((-1 : ℝ) : EReal) ≤ comp t p by
    have h0 : (0 : EReal) = ((-1 : ℝ) : EReal) + 1 := by
      rw [← EReal.coe_one, ← EReal.coe_add]
      norm_num
    rw [h0]
    exact add_le_add h le_rfl
  rcases trichotomy p with rfl | rfl | ⟨_, hs, h0⟩
  · obtain ⟨hi, ho⟩ := values_origin t
    change _ ≤ max _ _
    rw [hi, ho, max_bot_right]
    have : Real.log (t / (1 + t)) ≤ Real.log t :=
      Real.log_le_log (div_pos htpos (by linarith)) (div_le_self htpos.le (by linarith))
    exact_mod_cast (by linarith : (-1 : ℝ) ≤ Real.log t)
  · obtain ⟨hi, ho⟩ := values_infinity t
    change _ ≤ max _ _
    rw [hi, ho, max_bot_left]
    exact_mod_cast (by norm_num : (-1 : ℝ) ≤ 0)
  · obtain ⟨hi, ho⟩ := values_torus htpos hs h0
    change _ ≤ max _ _
    rw [hi, ho]
    have hpos : 0 < ‖fc p‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
    rcases le_total (‖fc p‖ ^ 2) t with hst | hts
    · apply le_max_of_le_left
      have h1 : Real.log (1 + ‖fc p‖ ^ 2) ≤ Real.log (1 + t) :=
        Real.log_le_log (by positivity) (by linarith)
      have h2 : Real.log (t / (1 + t)) = Real.log t - Real.log (1 + t) :=
        Real.log_div htpos.ne' (by linarith)
      exact_mod_cast (by linarith : (-1 : ℝ) ≤ Real.log t - Real.log (1 + ‖fc p‖ ^ 2))
    · apply le_max_of_le_right
      have h1 : t / (1 + t) ≤ ‖fc p‖ ^ 2 / (1 + ‖fc p‖ ^ 2) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      have h2 := Real.log_le_log (div_pos htpos (by linarith)) h1
      exact_mod_cast (by linarith : (-1 : ℝ) ≤ Real.log (‖fc p‖ ^ 2 / (1 + ‖fc p‖ ^ 2)))

/-- The gap set of `seq j` at `δ = 1/2` on the punctured disc. -/
def gap (j : ℕ) : Set P1 :=
  sourceCapacityUpperGap puncturedDisc (fun x => seq j x) (fun _ => 0) (1 / 2)

/-- Where the two pieces agree, we are on the circle `|z|² = t`, inside the gap. -/
theorem mem_gap_of_eq {t : ℝ} {j : ℕ} (ht : 3 / 4 ≤ t) (ht1 : t < 1) (hj : 1 / 2 < t ^ j)
    {p : P1} (hp : inner t p = outer p) : p ∈ gap j := by
  have htpos : 0 < t := by linarith
  rcases trichotomy p with rfl | rfl | ⟨hb, hs, h0⟩
  · obtain ⟨hi, ho⟩ := values_origin t
    rw [hi, ho] at hp
    exact absurd hp (EReal.coe_ne_bot _)
  · obtain ⟨hi, ho⟩ := values_infinity t
    rw [hi, ho] at hp
    exact absurd hp.symm (by simp)
  · obtain ⟨hi, ho⟩ := values_torus htpos hs h0
    rw [hi, ho, EReal.coe_eq_coe_iff] at hp
    have hpos : 0 < ‖fc p‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
    rw [Real.log_div hpos.ne' (by positivity)] at hp
    have hlog : Real.log t = Real.log (‖fc p‖ ^ 2) := by linarith
    have hts : t = ‖fc p‖ ^ 2 :=
      Real.log_injOn_pos (mem_Ioi.mpr htpos) (mem_Ioi.mpr hpos) hlog
    have hn1 : ‖fc p‖ < 1 := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    have hU : p ∈ puncturedDisc := ⟨hb, hs, hn1⟩
    have hmem := (mem_sourceCapacityUpperGap puncturedDisc (fun x => seq j x) (fun _ => 0)
      (1 / 2) ⟨p, hU⟩).mpr
    apply hmem
    change (0 : EReal) + ((1 / 2 : ℝ) : EReal) < (((‖fc p‖ ^ 2) ^ j : ℝ) : EReal)
    rw [zero_add, ← hts]
    exact_mod_cast hj

/-- The capacity of every gap set is at least one. -/
theorem one_le_capacity_gap (j : ℕ) : 1 ≤ sourceThetaCapacity fsForm (gap j) := by
  obtain ⟨t, hj, ht, ht1⟩ : ∃ t : ℝ, 1 / 2 < t ^ j ∧ 3 / 4 ≤ t ∧ t < 1 := by
    have hc : Tendsto (fun t : ℝ => t ^ j) (𝓝 1) (𝓝 1) := by
      simpa using ((continuous_pow j).tendsto (1 : ℝ))
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 1 / 2 < t ^ j ∧ 3 / 4 ≤ t ∧ t < 1 := by
      filter_upwards [nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))),
        nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (3 : ℝ) / 4 < 1)), self_mem_nhdsWithin]
        with t h1 h2 h3
      exact ⟨h1, h2.le, h3⟩
    exact hev.exists
  let ω := projectiveNativeFSBackground
  let μ := DiagonalMass.diagonalPotentialMeasure ω.form (comp t) (psh_comp t)
  -- total mass one
  have hmass : μ univ = 1 := by
    have hzero := PluripolarCapacityDichotomy.isThetaPshPotential_zero ω
    have hle : μ univ ≤ DiagonalMass.diagonalPotentialMeasure ω.form (fun _ => 0) hzero univ :=
      GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω
        (fun _ : Fin 1 => psh_comp t) (fun _ => hzero)
        (fun _ => MoreSingularOn.of_le fun x _ => by
          simpa using comp_le_zero ht ht1 x)
    have hge : DiagonalMass.diagonalPotentialMeasure ω.form (fun _ => 0) hzero univ ≤ μ univ :=
      GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω
        (fun _ : Fin 1 => hzero) (fun _ => psh_comp t)
        (fun _ => ⟨1, fun x _ => by simpa using neg_one_le_comp ht ht1 x⟩)
    have h1 : DiagonalMass.diagonalPotentialMeasure ω.form (fun _ => 0) hzero univ = 1 :=
      projectiveToricNonPluripolarMeasure_zero_univ
    rw [h1] at hle hge
    exact le_antisymm hle hge
  -- the complement of the gap is null
  have hcompl : μ (gap j)ᶜ = 0 := by
    let S₁ : Set P1 := {x | ∀ _i : Fin 1, outer x < inner t x}
    let S₂ : Set P1 := {x | ∀ _i : Fin 1, inner t x < outer x}
    have hsub : (gap j)ᶜ ⊆ S₁ ∪ S₂ := by
      intro x hx
      rcases lt_trichotomy (outer x) (inner t x) with h | h | h
      · exact Or.inl fun _ => h
      · exact absurd (mem_gap_of_eq ht ht1 hj h.symm) hx
      · exact Or.inr fun _ => h
    have h₁ : μ S₁ = 0 := by
      have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
        (fun _ : Fin 1 => (psh_inner t).1) (fun _ : Fin 1 => psh_outer.1)
        (fun _ : Fin 1 => (psh_comp t).1)
      have h := congrArg (fun ν : Measure P1 => ν univ) hloc
      simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
      change μ S₁ = _ at h
      rw [h]
      exact measure_mono_null (subset_univ _) (mass_inner t)
    have h₂ : μ S₂ = 0 := by
      have hmax : ∀ _i : Fin 1, ThetaPlurisubharmonic projectiveNativeFSBackground.form.val
          (fun x => max (outer x) (inner t x)) := fun _ =>
        (IsThetaPshPotential.max psh_outer (psh_inner t)).1
      have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
        (fun _ : Fin 1 => psh_outer.1) (fun _ : Fin 1 => (psh_inner t).1) hmax
      have hcongr : GlobalNonPluripolar.globalMixedMeasure
          (fun _ : Fin 1 => projectiveNativeFSBackground.form)
          (fun _ x => max (outer x) (inner t x)) hmax = μ :=
        GlobalDiagonalScaling.globalMixedMeasure_congr rfl
          (funext fun _ => funext fun x => max_comm _ _) hmax (fun _ => (psh_comp t).1)
      have h := congrArg (fun ν : Measure P1 => ν univ) hloc
      simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
      rw [hcongr] at h
      change μ S₂ = _ at h
      rw [h]
      exact measure_mono_null (subset_univ _) mass_outer
    exact measure_mono_null hsub (measure_union_null h₁ h₂)
  have hμgap : 1 ≤ μ (gap j) := by
    have h := measure_univ_le_add_compl (μ := μ) (gap j)
    rw [hmass, hcompl, add_zero] at h
    exact h
  have hcap : μ (gap j) ≤ thetaCapacity ω.form (fun _ => 0) (gap j) :=
    diagonalPotentialMeasure_le_thetaCapacity (psh_comp t) (comp_le_zero ht ht1)
      (neg_one_le_comp ht ht1) (gap j)
  rw [fsForm, sourceThetaCapacity_kahler]
  exact hμgap.trans hcap

/-- Source erratum for `prop:mono_psh_cap`, clause (1): on `ℙ¹` with the
Fubini--Study form (a Kähler, hence big, class), the decreasing sequence
`|z|^{2j}` of `θ`-psh functions on the punctured unit disc converges pointwise
to the `θ`-psh function `0`, but does not converge to it in capacity in the sense
of `def:conv_cap`. -/
theorem not_tendstoInCapacity_of_decreasing :
    ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 P1)) (U : Opens P1)
      (u : ℕ → P1 → EReal) (v : P1 → EReal),
      IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) ∧
      (∀ j, (ofFixedModel 1 P1).IsThetaPSHOn θ (u j) U) ∧
      (ofFixedModel 1 P1).IsThetaPSHOn θ v U ∧
      (∀ x ∈ U, Antitone fun j => u j x) ∧
      (∀ x ∈ U, Tendsto (fun j => u j x) atTop (𝓝 (v x))) ∧
      ¬ SourceTendstoInCapacity θ U (fun j (x : U) => u j x) atTop (fun x => v x) := by
  refine ⟨fsForm, puncturedDisc, seq, fun _ => 0, ?_, isThetaPSHOn_seq,
    isThetaPSH_zero_fsForm.isThetaPSHOn _, fun x hx => seq_antitone hx,
    fun x hx => seq_tendsto hx, ?_⟩
  · rw [fsForm, sourceNativeAtlasForm_roundTrip]
    exact PluripolarCapacityDichotomy.isBigClass_kahler _
  · rintro ⟨_, _, hcap⟩
    have h := ((hcap (1 / 2) (by norm_num)).1.eventually
      (Iio_mem_nhds zero_lt_one)).exists
    obtain ⟨j, hj⟩ := h
    exact absurd (one_le_capacity_gap j) (not_le.mpr hj)

end SGPT.NPP.MonotoneCapacityCounterexample
