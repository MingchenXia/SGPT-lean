import SGPT.Okounkov.TranscendentalL2Hormander
import SGPT.Foundations.Analysis.Pending.OTChenExtension
import SGPT.Foundations.Analysis.Pending.LeviWirtinger
import SGPT.Foundations.Analysis.Pending.HiepSliceLemma
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
import SGPT.Foundations.Analysis.DistributionRegularization

/-!
# Solving `∂̄` with `L²` estimates on open sets with a strictly psh exhaustion

Plan `tok/RELGEN2/PLAN.md`, steps P2–P3 (blueprint `l2:exhaustion-solution`,
`l2:complement-exhaustion`, chapter `claude-tok-l2`).

`HasStrictPshExhaustion Ω`: every compact `K ⊆ Ω` admits a smooth function `s` on `ℂⁿ`, strictly
plurisubharmonic on `{s < 1}`, with `{s ≤ 1}` compact inside `Ω` and `s ≤ 1/2` on `K` (the data of
`hormanderL2_of_exhaustion`). This is the case for the complement `B(p, r) \ {h = 0}` of the zero
set of a holomorphic function in a ball (`hasStrictPshExhaustion_ball_inter_ne_zero`), with
`s = e^{κ (‖x - p‖² - R²)} + δ ‖1/h‖²` capped to a constant near the boundary.

`exists_holomorphic_of_strictPshExhaustion` (Hörmander, *An introduction to complex analysis in
several variables*, Theorem 4.4.2, with the curvature norm of Demailly, *Complex analytic and
differential geometry*, VIII.6.5): let `Φ` be smooth and plurisubharmonic on `Ω`, `h₀` smooth on
`Ω`, and `g ≥ 0` with `|∂̄_ξ h₀|² ≤ g · Levi Φ (ξ)` on `Ω` and `∫_Ω g e^{-Φ} < ∞`. Then there is a
holomorphic `G` on `Ω` with `∫_Ω |h₀ - G|² e^{-Φ} ≤ 2 ∫_Ω g e^{-Φ}`. Proof: on each compact set
`K_j` of an exhaustion of `Ω`, Hörmander's estimate (`hormanderL2_of_exhaustion` with `t = 1`) and
Weyl's lemma give `G_j` holomorphic near `K_j` with `∫_{K_j} |h₀ - G_j|² e^{-Φ} ≤ 2 ∫_Ω g e^{-Φ}`;
the `G_j` are locally uniformly bounded (sub-mean value inequality), Montel's theorem gives a
locally uniform limit and Fatou's lemma the estimate.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric Complex
open scoped Topology ContDiff ComplexConjugate ENNReal

noncomputable section

namespace SGPT.Okounkov.TranscendentalL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ}

/-- `Ω` has a strictly plurisubharmonic exhaustion in the sense needed by Hörmander's method:
for every compact `K ⊆ Ω` there is a smooth `s` with `ε ‖v‖² ≤ Levi s (v)` on `{s < 1}`,
`{s ≤ 1}` compact and contained in `Ω`, and `s ≤ 1/2` on `K`. -/
def HasStrictPshExhaustion (Ω : Set (ComplexModel n)) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
    ∃ (s : ComplexModel n → ℝ) (ε : ℝ), 0 < ε ∧ ContDiff ℝ ∞ s ∧ IsCompact {x | s x ≤ 1} ∧
      {x | s x ≤ 1} ⊆ Ω ∧ (∀ x ∈ K, s x ≤ 1 / 2) ∧
      ∀ x, s x < 1 → ∀ v, ε * ‖v‖ ^ 2 ≤ leviForm s x v

/-! ### One compact set -/

/-- **One application of Hörmander's estimate, corrected by Weyl's lemma.** Given the estimate
on `D'` (compact closure in `Ω`) for the weights `Φ + lam₁`, `Φ + lam₂`, there is `G` holomorphic
on `D'` with `∫_{D'} |h₀ - G|² e^{-Φ-lam₁} ≤ (1 + t) ∫_Ω g e^{-Φ}`. -/
theorem exists_holomorphic_of_hormanderClause {Ω D' : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hD'o : IsOpen D') (hD'Ω : closure D' ⊆ Ω) (hD'c : IsCompact (closure D'))
    {lam₁ lam₂ : ComplexModel n → ℝ} (hl₁ : ContinuousOn lam₁ D') (hl₂ : ContinuousOn lam₂ D')
    (hl : ∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) {t : ℝ} (ht : 0 < t)
    (hest : HormanderClause Ω D' lam₁ lam₂ t)
    {Φ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ Ω) (hpsh : ∀ x ∈ Ω, ∀ ξ, 0 ≤ leviForm Φ x ξ)
    {h₀ : ComplexModel n → ℂ} (hh₀ : ContDiffOn ℝ ∞ h₀ Ω)
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ Ω, 0 ≤ g x)
    (hfg : ∀ x ∈ Ω, ∀ ξ : ComplexModel n, ‖dbarDir ξ h₀ x‖ ^ 2 ≤ g x * leviForm Φ x ξ)
    (hgi : Integrable (fun x ↦ g x * Real.exp (-Φ x)) (volume.restrict Ω)) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G D' ∧
      ∫⁻ x in D', ENNReal.ofReal (‖h₀ x - G x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x))) ≤
        ENNReal.ofReal ((1 + t) * ∫ x in Ω, g x * Real.exp (-Φ x)) := by
  set a := h₀ with ha
  set v : Fin n → ComplexModel n → ℂ := fun j ↦ dbarDir (coordVec j) a with hv
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hD'sub : D' ⊆ Ω := subset_closure.trans hD'Ω
  have hD'b : Bornology.IsBounded D' := hD'c.isBounded.subset subset_closure
  have haΩ1 : ContDiffOn ℝ 1 a Ω := hh₀.of_le (WithTop.coe_le_coe.mpr le_top)
  have haD' : ContDiffOn ℝ 1 a D' := haΩ1.mono hD'sub
  have hΦc : ContinuousOn Φ Ω := hΦ.continuousOn
  -- bounds on the compact closure
  obtain ⟨BΦ, hBΦ'⟩ := hD'c.exists_bound_of_continuousOn (hΦc.mono hD'Ω)
  have hBΦ : ∀ x ∈ closure D', -BΦ ≤ Φ x := fun x hx ↦
    neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using hBΦ' x hx)
  have hvcontΩ : ∀ j, ContinuousOn (v j) Ω := fun j ↦
    continuousOn_dbarDir_of_contDiffOn hΩ haΩ1 _
  have hvbd : ∀ j, ∃ M : ℝ, ∀ x ∈ closure D', ‖v j x‖ ^ 2 ≤ M := fun j ↦ by
    obtain ⟨M, hM⟩ := hD'c.exists_bound_of_continuousOn ((hvcontΩ j).mono hD'Ω)
    exact ⟨M ^ 2, fun x hx ↦ pow_le_pow_left₀ (norm_nonneg _) (hM x hx) 2⟩
  have hwt : ∀ x ∈ D', ∀ l, 0 ≤ l → Real.exp (-(Φ x + l)) ≤ Real.exp BΦ := fun x hx l hl ↦
    Real.exp_le_exp.mpr (by linarith [hBΦ x (subset_closure hx)])
  have hvmem : ∀ j, MemLp (v j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x) := by
    intro j
    obtain ⟨M, hM⟩ := hvbd j
    rw [memLp_weightedVolume_iff (w := fun x ↦ Φ x + lam₂ x)
      (((hΦc.mono hD'sub).add hl₂).aemeasurable hD'm)
      (((hvcontΩ j).mono hD'sub).aestronglyMeasurable hD'm)]
    refine integrable_restrict_of_continuousOn_bound hD'o hD'b
      ((((hvcontΩ j).mono hD'sub).norm.pow 2).mul ((hΦc.mono hD'sub).add hl₂).neg.rexp)
      (M := max M 0 * Real.exp BΦ) fun z hz ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul ((hM z (subset_closure hz)).trans (le_max_left _ _))
      (hwt z hz _ ((hl z hz).1.trans (hl z hz).2)) (by positivity) (le_max_right _ _)
  have hvclosed : WeakDbarClosed D' v := weakDbarClosed_of_contDiffOn hD'o haD'
  have hglevi : ∀ x ∈ D', ∀ ξ : Fin n → ℂ, ‖∑ j, conj (ξ j) * v j x‖ ^ 2 ≤
      g x * leviForm Φ x (∑ j, ξ j • coordVec j) := by
    intro x hx ξ
    rw [show ∑ j, conj (ξ j) * v j x = dbarDir (∑ j, ξ j • coordVec j) a x from
      (dbarDir_sum_dir Finset.univ ξ coordVec a x).symm]
    exact hfg x (hD'sub hx) _
  have hl₁c : ContinuousOn (fun x ↦ Real.exp (-lam₁ x)) D' := hl₁.neg.rexp
  have hgint : Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') := by
    have h1 : Integrable (fun x ↦ g x * Real.exp (-Φ x)) (volume.restrict D') :=
      hgi.mono_measure (Measure.restrict_mono hD'sub le_rfl)
    refine h1.mono' ?_ ?_
    · have hm : AEStronglyMeasurable (fun x ↦ (g x * Real.exp (-Φ x)) * Real.exp (-lam₁ x))
          (volume.restrict D') :=
        h1.aestronglyMeasurable.mul (hl₁c.aestronglyMeasurable hD'm)
      refine hm.congr (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [neg_add, Real.exp_add]
      ring
    · refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun x hx ↦ ?_)
      have hg := hg0 x (hD'sub hx)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hg
      linarith [(hl x hx).1]
  obtain ⟨⟨u₀, hu₀mem, hu₀eq, hu₀orth⟩, hbd⟩ := hest Φ hΦ hpsh v hvmem hvclosed g
    (fun x hx ↦ hg0 x (hD'sub hx)) hglevi hgint
  have hu₀bd := hbd u₀ hu₀mem hu₀eq hu₀orth
  -- Weyl's lemma
  have hwc : ContinuousOn (fun x ↦ Φ x + lam₁ x) D' := (hΦc.mono hD'sub).add hl₁
  have hu₀loc : LocallyIntegrableOn u₀ D' :=
    locallyIntegrableOn_of_memLp_weightedVolume hD'o hwc hu₀mem
  have haloc : LocallyIntegrableOn a D' := haD'.continuousOn.locallyIntegrableOn hD'm
  have hFloc : LocallyIntegrableOn (fun z ↦ a z - u₀ z) D' := haloc.sub hu₀loc
  have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
      ∫ x, (a x - u₀ x) * dbarDir (coordVec j) h x = 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn hu₀loc hdc hdcs hdts
    simp only [sub_mul]
    rw [integral_sub i1 i2, weakDbarEq_of_contDiffOn hD'o haD' h hh j, hu₀eq h hh j]
    ring
  obtain ⟨G, hG, hGae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
    (integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  have hae : (fun z ↦ a z - G z) =ᵐ[volume.restrict D'] u₀ := by
    filter_upwards [hGae] with x hx
    rw [← hx]; ring
  refine ⟨G, hG, ?_⟩
  have hint : Integrable (fun x ↦ ‖u₀ x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') :=
    (memLp_weightedVolume_iff (w := fun x ↦ Φ x + lam₁ x) (hwc.aemeasurable hD'm)
      (aestronglyMeasurable_of_memLp_weightedVolume (hwc.aemeasurable hD'm) hu₀mem)).mp hu₀mem
  calc ∫⁻ x in D', ENNReal.ofReal (‖a x - G x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x)))
      = ∫⁻ x in D', ENNReal.ofReal (‖u₀ x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x))) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
    _ = ENNReal.ofReal (∫ x in D', ‖u₀ x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x))) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + t) * ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x))) :=
        ENNReal.ofReal_le_ofReal hu₀bd
    _ ≤ ENNReal.ofReal ((1 + t) * ∫ x in Ω, g x * Real.exp (-Φ x)) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by linarith))
        calc ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x))
            ≤ ∫ x in D', g x * Real.exp (-Φ x) := by
              refine setIntegral_mono_on hgint
                (hgi.mono_measure (Measure.restrict_mono hD'sub le_rfl)) hD'm fun x hx ↦ ?_
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg0 x (hD'sub hx))
              linarith [(hl x hx).1]
          _ ≤ ∫ x in Ω, g x * Real.exp (-Φ x) :=
              setIntegral_mono_set hgi
                ((ae_restrict_iff' hΩ.measurableSet).mpr (Eventually.of_forall fun x hx ↦
                  mul_nonneg (hg0 x hx) (Real.exp_pos _).le))
                (Eventually.of_forall hD'sub)

/-! ### A compact exhaustion -/

/-- The compact sets `K j = {x : ‖x‖ ≤ j, dist (x, ℂⁿ \ Ω) ≥ 1/(j+1)}` exhausting an open `Ω`. -/
def exhaustionSet (Ω : Set (ComplexModel n)) (j : ℕ) : Set (ComplexModel n) :=
  {x | ‖x‖ ≤ j ∧ ∀ y ∉ Ω, 1 / ((j : ℝ) + 1) ≤ dist x y}

theorem isCompact_exhaustionSet (Ω : Set (ComplexModel n)) (j : ℕ) :
    IsCompact (exhaustionSet Ω j) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {x : ComplexModel n | ‖x‖ ≤ j} := isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {x : ComplexModel n | ∀ y ∉ Ω, 1 / ((j : ℝ) + 1) ≤ dist x y} := by
      simp only [Set.ofPred_forall]
      exact isClosed_biInter fun y _ ↦ isClosed_le continuous_const
        (continuous_id.dist continuous_const)
    exact h1.inter h2
  · exact (Metric.isBounded_closedBall (x := (0 : ComplexModel n)) (r := j)).subset
      fun x hx ↦ by simpa [mem_closedBall, dist_zero_right] using hx.1

theorem exhaustionSet_subset (Ω : Set (ComplexModel n)) (j : ℕ) : exhaustionSet Ω j ⊆ Ω := by
  intro x hx
  by_contra hxΩ
  have h := hx.2 x hxΩ
  rw [dist_self] at h
  have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith

/-- Every point of `Ω` has a closed ball inside `K j` for all large `j`. -/
theorem exists_closedBall_subset_exhaustionSet {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {x : ComplexModel n} (hx : x ∈ Ω) :
    ∃ ρ > 0, ∀ᶠ j in atTop, closedBall x ρ ⊆ exhaustionSet Ω j := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  refine ⟨ε / 2, half_pos hε, ?_⟩
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (‖x‖ + ε + 2 / ε)
  filter_upwards [eventually_ge_atTop j₀] with j hj y hy
  have hjR : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
  rw [mem_closedBall] at hy
  refine ⟨?_, fun w hw ↦ ?_⟩
  · have : ‖y‖ ≤ ‖x‖ + dist y x := by
      have := norm_le_norm_add_norm_sub' y x
      rwa [dist_eq_norm]
    have h2 : 0 < 2 / ε := by positivity
    linarith
  · have hxw : ε ≤ dist x w := by
      by_contra h
      exact hw (hεΩ (mem_ball.mpr (by rw [dist_comm]; linarith)))
    have hyw : ε / 2 ≤ dist y w := by
      have := dist_triangle x y w
      rw [dist_comm] at hy
      linarith
    have hj1 : 2 / ε < (j : ℝ) + 1 := by
      have : 0 ≤ ‖x‖ := norm_nonneg _
      linarith
    calc 1 / ((j : ℝ) + 1) ≤ ε / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          rw [div_lt_iff₀ hε] at hj1
          linarith
      _ ≤ dist y w := hyw

/-! ### The global solution -/

/-- **`∂̄` with `L²` estimates on an open set with a strictly psh exhaustion** (plan P3,
blueprint `l2:exhaustion-solution`). Let `Φ` be smooth and plurisubharmonic on `Ω`, `h₀` smooth
on `Ω`, and `g ≥ 0` with `|∂̄_ξ h₀|² ≤ g · Levi Φ (ξ)` on `Ω` and `∫_Ω g e^{-Φ} < ∞`. Then some
`G` holomorphic on `Ω` satisfies `∫_Ω |h₀ - G|² e^{-Φ} ≤ 2 ∫_Ω g e^{-Φ}`. -/
theorem exists_holomorphic_of_strictPshExhaustion {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hex : HasStrictPshExhaustion Ω)
    {Φ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ Ω) (hpsh : ∀ x ∈ Ω, ∀ ξ, 0 ≤ leviForm Φ x ξ)
    {h₀ : ComplexModel n → ℂ} (hh₀ : ContDiffOn ℝ ∞ h₀ Ω)
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ Ω, 0 ≤ g x)
    (hfg : ∀ x ∈ Ω, ∀ ξ : ComplexModel n, ‖dbarDir ξ h₀ x‖ ^ 2 ≤ g x * leviForm Φ x ξ)
    (hgi : Integrable (fun x ↦ g x * Real.exp (-Φ x)) (volume.restrict Ω)) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G Ω ∧
      ∫⁻ x in Ω, ENNReal.ofReal (‖h₀ x - G x‖ ^ 2 * Real.exp (-Φ x)) ≤
        ENNReal.ofReal (2 * ∫ x in Ω, g x * Real.exp (-Φ x)) := by
  set A : ℝ := ∫ x in Ω, g x * Real.exp (-Φ x) with hA
  set K : ℕ → Set (ComplexModel n) := exhaustionSet Ω with hK
  have hKc : ∀ j, IsCompact (K j) := isCompact_exhaustionSet Ω
  have hKΩ : ∀ j, K j ⊆ Ω := exhaustionSet_subset Ω
  have hΦc : ContinuousOn Φ Ω := hΦ.continuousOn
  have hh₀c : ContinuousOn h₀ Ω := hh₀.continuousOn
  -- one compact set at a time
  have key : ∀ j, ∃ (O : Set (ComplexModel n)) (G : ComplexModel n → ℂ), IsOpen O ∧ K j ⊆ O ∧
      DifferentiableOn ℂ G O ∧
      ∫⁻ x in K j, ENNReal.ofReal (‖h₀ x - G x‖ ^ 2 * Real.exp (-Φ x)) ≤
        ENNReal.ofReal (2 * A) := by
    intro j
    obtain ⟨s, ε, hε, hscd, hScpt, hsΩ, hsK, hslevi⟩ := hex (K j) (hKc j) (hKΩ j)
    obtain ⟨D', U, lam₁, lam₂, hD'o, hD'Ω, hD'c, hUo, hKU, hUD', hl₁, hl₂, hl, hlU, hclause⟩ :=
      hormanderL2_of_exhaustion (D := Ω) (K := K j) hε hscd hScpt hsΩ hsK hslevi one_pos
    obtain ⟨G, hG, hGbd⟩ := exists_holomorphic_of_hormanderClause hΩ hD'o hD'Ω hD'c hl₁ hl₂ hl
      one_pos hclause hΦ hpsh hh₀ hg0 hfg hgi
    refine ⟨U, G, hUo, hKU, hG.mono hUD', ?_⟩
    rw [one_add_one_eq_two] at hGbd
    refine le_trans ?_ hGbd
    refine (lintegral_mono_set (hKU.trans hUD')).trans' ?_
    refine setLIntegral_mono' (hKc j).isClosed.measurableSet fun x hx ↦ ?_
    rw [(hlU x (hKU hx)).1, add_zero]
  choose O G hOo hKO hGO hGbd using key
  -- local uniform bounds
  have hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (G i) (ball x r) ∧ ∀ y ∈ ball x r, ‖G i y‖ ≤ M := by
    intro x hx
    obtain ⟨ρ', hρ', hev⟩ := exists_closedBall_subset_exhaustionSet hΩ hx
    set ρ := ρ' / 2 with hρ
    have hρ0 : 0 < ρ := half_pos hρ'
    have hcb : IsCompact (closedBall x ρ') := isCompact_closedBall x ρ'
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
    have hcbΩ : closedBall x ρ' ⊆ Ω := (hj₀ j₀ le_rfl).trans (hKΩ j₀)
    obtain ⟨MΦ, hMΦ⟩ := hcb.exists_bound_of_continuousOn (hΦc.mono hcbΩ)
    obtain ⟨Mh, hMh⟩ := hcb.exists_bound_of_continuousOn (hh₀c.mono hcbΩ)
    set V : ℝ≥0∞ := volume (ball (0 : ComplexModel n) ρ) with hV
    have hV0 : V ≠ 0 := (measure_ball_pos volume _ hρ0).ne'
    have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
    set B : ℝ≥0∞ := (2 * ENNReal.ofReal (Real.exp MΦ) * ENNReal.ofReal (2 * A) +
      2 * ENNReal.ofReal (Mh ^ 2) * V) / V with hB
    have hBtop : B ≠ ⊤ := ENNReal.div_ne_top (by finiteness) hV0
    refine ⟨ρ, hρ0, Real.sqrt B.toReal, eventually_atTop.mpr ⟨j₀, fun i hi ↦ ?_⟩⟩
    have hsub : ∀ y ∈ ball x ρ, closedBall y ρ ⊆ closedBall x ρ' := fun y hy z hz ↦ by
      rw [mem_ball] at hy
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z y x]
    have hxK : closedBall x ρ' ⊆ K i := hj₀ i hi
    have hxr : ball x ρ ⊆ O i := fun y hy ↦
      hKO i (hxK (hsub y hy (mem_closedBall_self hρ0.le)))
    refine ⟨(hGO i).mono hxr, fun y hy ↦ ?_⟩
    have hyO : closedBall y ρ ⊆ O i := (hsub y hy).trans (hxK.trans (hKO i))
    have hmv := lintegral_ball_normSq_ge (hOo i) (hGO i) hρ0 hyO
    rw [Measure.addHaar_ball_center] at hmv
    have hballK : ball y ρ ⊆ K i := ball_subset_closedBall.trans ((hsub y hy).trans hxK)
    have hpt : ∀ z ∈ ball y ρ, ENNReal.ofReal (‖G i z‖ ^ 2) ≤
        2 * ENNReal.ofReal (Real.exp MΦ) *
          ENNReal.ofReal (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z)) +
        2 * ENNReal.ofReal (Mh ^ 2) := by
      intro z hz
      have hzc : z ∈ closedBall x ρ' := hsub y hy (ball_subset_closedBall hz)
      have hΦz : Φ z ≤ MΦ := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMΦ z hzc)
      have hhz : ‖h₀ z‖ ≤ Mh := hMh z hzc
      have hsq : ‖G i z‖ ^ 2 ≤ 2 * (Real.exp MΦ * (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z))) +
          2 * Mh ^ 2 := by
        have e1 : Real.exp MΦ * Real.exp (-Φ z) ≥ 1 := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have e2 : ‖G i z‖ ≤ ‖h₀ z - G i z‖ + ‖h₀ z‖ := by
          have := norm_sub_le (h₀ z) (h₀ z - G i z)
          rw [sub_sub_cancel] at this
          linarith
        have e3 : ‖G i z‖ ^ 2 ≤ 2 * ‖h₀ z - G i z‖ ^ 2 + 2 * ‖h₀ z‖ ^ 2 := by
          nlinarith [norm_nonneg (G i z), norm_nonneg (h₀ z - G i z), norm_nonneg (h₀ z),
            sq_nonneg (‖h₀ z - G i z‖ - ‖h₀ z‖)]
        have e4 : ‖h₀ z‖ ^ 2 ≤ Mh ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hhz 2
        have e5 : ‖h₀ z - G i z‖ ^ 2 ≤ Real.exp MΦ * (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z)) := by
          have h0 : 0 ≤ ‖h₀ z - G i z‖ ^ 2 := sq_nonneg _
          nlinarith
        linarith
      calc ENNReal.ofReal (‖G i z‖ ^ 2)
          ≤ ENNReal.ofReal (2 * (Real.exp MΦ * (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z))) +
              2 * Mh ^ 2) := ENNReal.ofReal_le_ofReal hsq
        _ = 2 * ENNReal.ofReal (Real.exp MΦ) *
              ENNReal.ofReal (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z)) +
            2 * ENNReal.ofReal (Mh ^ 2) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_ofNat]
              ring
    have hchain : V * ENNReal.ofReal (‖G i y‖ ^ 2) ≤
        2 * ENNReal.ofReal (Real.exp MΦ) * ENNReal.ofReal (2 * A) +
          2 * ENNReal.ofReal (Mh ^ 2) * V := by
      calc V * ENNReal.ofReal (‖G i y‖ ^ 2)
          ≤ ∫⁻ z in ball y ρ, ENNReal.ofReal (‖G i z‖ ^ 2) := hmv
        _ ≤ ∫⁻ z in ball y ρ, (2 * ENNReal.ofReal (Real.exp MΦ) *
              ENNReal.ofReal (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z)) +
            2 * ENNReal.ofReal (Mh ^ 2)) := setLIntegral_mono' measurableSet_ball hpt
        _ ≤ 2 * ENNReal.ofReal (Real.exp MΦ) *
              (∫⁻ z in ball y ρ, ENNReal.ofReal (‖h₀ z - G i z‖ ^ 2 * Real.exp (-Φ z))) +
            2 * ENNReal.ofReal (Mh ^ 2) * V := by
              rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by finiteness),
                setLIntegral_const, Measure.addHaar_ball_center]
        _ ≤ 2 * ENNReal.ofReal (Real.exp MΦ) * ENNReal.ofReal (2 * A) +
            2 * ENNReal.ofReal (Mh ^ 2) * V := by
              gcongr
              exact (lintegral_mono_set hballK).trans (hGbd i)
    have hle : ENNReal.ofReal (‖G i y‖ ^ 2) ≤ B := by
      rw [hB, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop), mul_comm]
      exact hchain
    have hsq : ‖G i y‖ ^ 2 ≤ B.toReal := (ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle
    exact Real.le_sqrt_of_sq_le hsq
  obtain ⟨ψ, Glim, hψ, hGlim, hconv⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded
    hΩ G hloc
  refine ⟨Glim, hGlim, ?_⟩
  -- Fatou's lemma
  set f : ℕ → ComplexModel n → ℝ≥0∞ := fun k ↦ (K (ψ k)).indicator
    fun x ↦ ENNReal.ofReal (‖h₀ x - G (ψ k) x‖ ^ 2 * Real.exp (-Φ x)) with hf
  have hfint : ∀ k, ∫⁻ x in Ω, f k x ≤ ENNReal.ofReal (2 * A) := by
    intro k
    rw [hf, lintegral_indicator (hKc _).isClosed.measurableSet,
      Measure.restrict_restrict (hKc _).isClosed.measurableSet,
      inter_eq_left.mpr (hKΩ _)]
    exact hGbd _
  have hfmeas : ∀ k, AEMeasurable (f k) (volume.restrict Ω) := by
    intro k
    have hKm := (hKc (ψ k)).isClosed.measurableSet
    refine (aemeasurable_indicator_iff hKm).mpr ?_
    rw [Measure.restrict_restrict hKm]
    have hc : ContinuousOn (fun x ↦ ENNReal.ofReal (‖h₀ x - G (ψ k) x‖ ^ 2 * Real.exp (-Φ x)))
        (K (ψ k) ∩ Ω) := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((hh₀c.mono inter_subset_right).sub
        ((hGO (ψ k)).continuousOn.mono (inter_subset_left.trans (hKO _)))).norm.pow 2).mul ?_
      exact (hΦc.mono inter_subset_right).neg.rexp
    exact hc.aemeasurable (hKm.inter hΩ.measurableSet)
  have hpoint : ∀ x ∈ Ω, ENNReal.ofReal (‖h₀ x - Glim x‖ ^ 2 * Real.exp (-Φ x)) ≤
      liminf (fun k ↦ f k x) atTop := by
    intro x hx
    obtain ⟨ρ, hρ, hev⟩ := exists_closedBall_subset_exhaustionSet hΩ hx
    have hevK : ∀ᶠ k in atTop, x ∈ K (ψ k) :=
      (hψ.tendsto_atTop.eventually hev).mono fun k hk ↦ hk (mem_closedBall_self hρ.le)
    have ht : Tendsto (fun k ↦ ENNReal.ofReal (‖h₀ x - G (ψ k) x‖ ^ 2 * Real.exp (-Φ x)))
        atTop (𝓝 (ENNReal.ofReal (‖h₀ x - Glim x‖ ^ 2 * Real.exp (-Φ x)))) := by
      refine ENNReal.tendsto_ofReal ?_
      exact ((((hconv.tendsto_at hx).const_sub (h₀ x)).norm).pow 2).mul_const _
    have ht' : Tendsto (fun k ↦ f k x) atTop
        (𝓝 (ENNReal.ofReal (‖h₀ x - Glim x‖ ^ 2 * Real.exp (-Φ x)))) := by
      refine ht.congr' ?_
      filter_upwards [hevK] with k hk
      simp only [hf, indicator_of_mem hk]
    exact ht'.liminf_eq.ge
  calc ∫⁻ x in Ω, ENNReal.ofReal (‖h₀ x - Glim x‖ ^ 2 * Real.exp (-Φ x))
      ≤ ∫⁻ x in Ω, liminf (fun k ↦ f k x) atTop := setLIntegral_mono' hΩ.measurableSet hpoint
    _ ≤ liminf (fun k ↦ ∫⁻ x in Ω, f k x) atTop := lintegral_liminf_le' hfmeas
    _ ≤ ENNReal.ofReal (2 * A) :=
        liminf_le_of_frequently_le' (Frequently.of_forall hfint)

/-! ### The complement of a hypersurface in a ball -/

/-- The cap `T(t) = 2 - (2 - t)(1 - θ(2t - 3))`: `T(t) = t` for `t ≤ 3/2`, `T(t) = 2` for `t ≥ 2`,
and `T(t) > 1` for `t > 1`. -/
def capProfile (t : ℝ) : ℝ := 2 - (2 - t) * (1 - Real.smoothTransition (2 * t - 3))

theorem contDiff_capProfile : ContDiff ℝ ∞ capProfile := by
  unfold capProfile
  exact contDiff_const.sub ((contDiff_const.sub contDiff_id).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))))

theorem capProfile_of_le {t : ℝ} (ht : t ≤ 3 / 2) : capProfile t = t := by
  rw [capProfile, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem capProfile_of_ge {t : ℝ} (ht : 2 ≤ t) : capProfile t = 2 := by
  rw [capProfile, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem one_lt_capProfile {t : ℝ} (ht : 1 < t) : 1 < capProfile t := by
  have h0 := Real.smoothTransition.nonneg (2 * t - 3)
  have h1 := Real.smoothTransition.le_one (2 * t - 3)
  unfold capProfile
  rcases le_or_gt 2 t with h2 | h2
  · nlinarith
  · nlinarith

theorem le_one_of_capProfile_le_one {t : ℝ} (ht : capProfile t ≤ 1) : t ≤ 1 := by
  by_contra h
  exact absurd ht (not_le.mpr (one_lt_capProfile (not_le.mp h)))

/-- The Levi form of `|G|²` for a holomorphic `G` is nonnegative. -/
theorem leviForm_normSq_nonneg {G : ComplexModel n → ℂ} {z : ComplexModel n}
    (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) (v : ComplexModel n) :
    0 ≤ leviForm (fun y ↦ Complex.normSq (G y)) z v := by
  have h := ConcentrationPotentialLevi.leviForm_sq_mul_normSq (c := fun _ ↦ (1 : ℝ))
    contDiffAt_const hG v
  have hfun : (fun y ↦ (fun _ ↦ (1 : ℝ)) y ^ 2 * Complex.normSq (G y)) =
      fun y ↦ Complex.normSq (G y) := by
    funext y; simp
  rw [hfun] at h
  rw [h]
  have hd : ConcentrationPotentialLevi.delC (fun _ : ComplexModel n ↦ (1 : ℝ)) z v = 0 := by
    simp [ConcentrationPotentialLevi.delC]
  rw [hd, leviForm_const]
  simp only [mul_zero, map_zero, sub_zero, add_zero]
  exact Complex.normSq_nonneg _

/-- The core of the exhaustion of `B(p, r) \ {h = 0}`: `e^{κ (‖x - p‖² - R²)} + δ ‖1/h‖²`. -/
def exhaustionCore (p : ComplexModel n) (R2 κ δ : ℝ) (h : ComplexModel n → ℂ)
    (x : ComplexModel n) : ℝ :=
  Real.exp (κ * (‖x - p‖ ^ 2 - R2)) + δ * ‖(h x)⁻¹‖ ^ 2

theorem contDiffAt_exhaustionCore {p : ComplexModel n} {r R2 κ δ : ℝ} {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h (ball p r)) {x : ComplexModel n} (hx : x ∈ ball p r)
    (hx0 : h x ≠ 0) : ContDiffAt ℝ ∞ (exhaustionCore p R2 κ δ h) x := by
  have h1 : ContDiffAt ℝ ∞ (fun y : ComplexModel n ↦ Real.exp (κ * (‖y - p‖ ^ 2 - R2))) x := by
    refine Real.contDiff_exp.contDiffAt.comp x ?_
    refine contDiffAt_const.mul (ContDiffAt.sub ?_ contDiffAt_const)
    exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hhx : ContDiffAt ℂ ∞ h x := contDiffAt_of_differentiableOn_complex hh isOpen_ball hx
  have h2 : ContDiffAt ℝ ∞ (fun y ↦ (h y)⁻¹) x := (hhx.inv hx0).restrict_scalars ℝ
  have h3 : ContDiffAt ℝ ∞ (fun y ↦ δ * ‖(h y)⁻¹‖ ^ 2) x :=
    contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp x h2)
  exact h1.add h3

/-- The Levi form of the core: `κ e^{-κR²} ‖v‖² ≤ Levi (core) (v)` off the zeros of `h`. -/
theorem le_leviForm_exhaustionCore {p : ComplexModel n} {r R2 κ δ : ℝ} (hκ : 0 ≤ κ)
    (hδ : 0 ≤ δ) {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h (ball p r)) {x : ComplexModel n} (hx : x ∈ ball p r)
    (hx0 : h x ≠ 0) (v : ComplexModel n) :
    κ * Real.exp (-(κ * R2)) * ‖v‖ ^ 2 ≤ leviForm (exhaustionCore p R2 κ δ h) x v := by
  set G : ℝ → ℝ := fun t ↦ Real.exp (κ * (t - R2)) with hG
  have hGd : ∀ t, HasDerivAt G (κ * Real.exp (κ * (t - R2))) t := fun t ↦ by
    have := (((hasDerivAt_id t).sub_const R2).const_mul κ).exp
    simpa [G, mul_comm] using this
  have hGdd : ∀ t, HasDerivAt (fun t ↦ κ * Real.exp (κ * (t - R2)))
      (κ * (κ * Real.exp (κ * (t - R2)))) t := fun t ↦ (hGd t).const_mul κ
  have hdG : deriv G = fun t ↦ κ * Real.exp (κ * (t - R2)) := funext fun t ↦ (hGd t).deriv
  have hddG : deriv (deriv G) = fun t ↦ κ * (κ * Real.exp (κ * (t - R2))) := by
    rw [hdG]; exact funext fun t ↦ (hGdd t).deriv
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul
    (contDiff_id.sub contDiff_const))
  -- the exponential term
  have hE : leviForm (fun y : ComplexModel n ↦ Real.exp (κ * (‖y - p‖ ^ 2 - R2))) x v =
      κ * Real.exp (κ * (‖x - p‖ ^ 2 - R2)) * ‖v‖ ^ 2 +
        κ * (κ * Real.exp (κ * (‖x - p‖ ^ 2 - R2))) * ‖inner ℂ (x - p) v‖ ^ 2 := by
    have h1 := leviForm_comp_sub (fun y : ComplexModel n ↦ G (‖y‖ ^ 2)) p x v
    have h2 := RadialLeviPreimage.leviForm_comp_norm_sq hGc (x - p) v
    rw [hddG, hdG] at h2
    simp only [G] at h1 h2
    rw [h1, h2]
  have hE' : κ * Real.exp (-(κ * R2)) * ‖v‖ ^ 2 ≤
      leviForm (fun y : ComplexModel n ↦ Real.exp (κ * (‖y - p‖ ^ 2 - R2))) x v := by
    rw [hE]
    have hexp : Real.exp (-(κ * R2)) ≤ Real.exp (κ * (‖x - p‖ ^ 2 - R2)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖x - p‖])
    have h3 : 0 ≤ κ * (κ * Real.exp (κ * (‖x - p‖ ^ 2 - R2))) * ‖inner ℂ (x - p) v‖ ^ 2 := by
      positivity
    have h4 : κ * Real.exp (-(κ * R2)) * ‖v‖ ^ 2 ≤
        κ * Real.exp (κ * (‖x - p‖ ^ 2 - R2)) * ‖v‖ ^ 2 := by
      gcongr
    linarith
  -- the term `δ ‖1/h‖²`
  have hhx : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (fun y ↦ (h y)⁻¹) y := by
    have hc : ContinuousAt h x := (hh.differentiableAt (isOpen_ball.mem_nhds hx)).continuousAt
    filter_upwards [isOpen_ball.mem_nhds hx, hc.eventually_ne hx0] with y hy hy0
    exact (hh.differentiableAt (isOpen_ball.mem_nhds hy)).inv hy0
  have hN : 0 ≤ leviForm (fun y ↦ δ * ‖(h y)⁻¹‖ ^ 2) x v := by
    have hfun : (fun y ↦ δ * ‖(h y)⁻¹‖ ^ 2) = δ • fun y ↦ Complex.normSq ((h y)⁻¹) := by
      funext y; simp [Complex.normSq_eq_norm_sq]
    rw [hfun, leviForm_smul (ConcentrationPotentialLevi.contDiffAt_normSq hhx)]
    exact mul_nonneg hδ (leviForm_normSq_nonneg hhx v)
  have hc1 : ContDiffAt ℝ 2 (fun y : ComplexModel n ↦ Real.exp (κ * (‖y - p‖ ^ 2 - R2))) x := by
    refine (Real.contDiff_exp.contDiffAt.comp x ?_)
    refine contDiffAt_const.mul (ContDiffAt.sub ?_ contDiffAt_const)
    exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun y ↦ δ * ‖(h y)⁻¹‖ ^ 2) x := by
    have hhx' : ContDiffAt ℂ 2 h x :=
      (contDiffAt_of_differentiableOn_complex hh isOpen_ball hx).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp x
      ((hhx'.inv hx0).restrict_scalars ℝ))
  have hsplit : exhaustionCore p R2 κ δ h =
      (fun y : ComplexModel n ↦ Real.exp (κ * (‖y - p‖ ^ 2 - R2))) +
        fun y ↦ δ * ‖(h y)⁻¹‖ ^ 2 := rfl
  rw [hsplit, leviForm_add hc1 hc2]
  linarith

/-- **The complement of a hypersurface in a ball has a strictly psh exhaustion** (plan P2,
blueprint `l2:complement-exhaustion`): for `h` holomorphic on `B(p, r)`, the open set
`B(p, r) \ {h = 0}` satisfies `HasStrictPshExhaustion`, with
`s = T(e^{κ (‖x - p‖² - R²)} + δ ‖1/h‖²)` on the set and `s = 2` off it (`T = capProfile`). -/
theorem hasStrictPshExhaustion_ball_inter_ne_zero {p : ComplexModel n} {r : ℝ}
    {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h (ball p r)) :
    HasStrictPshExhaustion (ball p r ∩ {x | h x ≠ 0}) := by
  classical
  intro K hKc hKΩ
  set Ω := ball p r ∩ {x | h x ≠ 0} with hΩ
  have hΩo : IsOpen Ω := hh.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ ↦ 2, 1, one_pos, contDiff_const, ?_, ?_, fun x hx ↦ hx.elim, ?_⟩
    · have : {x : ComplexModel n | (2 : ℝ) ≤ 1} = ∅ := by
        ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]; norm_num
      rw [this]; exact isCompact_empty
    · intro x hx; exact absurd hx (by norm_num)
    · intro x hx; exact absurd hx (by norm_num)
  obtain ⟨rK, hrKr, hKrK⟩ := exists_lt_subset_ball hKc.isClosed (hKΩ.trans inter_subset_left)
  have hrK0 : 0 < rK := by
    obtain ⟨x, hx⟩ := hKne
    exact (dist_nonneg).trans_lt (mem_ball.mp (hKrK hx))
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (f := fun x ↦ (h x)⁻¹)
    ((hh.continuousOn.mono (hKΩ.trans inter_subset_left)).inv₀ fun x hx ↦ (hKΩ hx).2)
  set d : ℝ := (r ^ 2 - rK ^ 2) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; nlinarith
  set R2 : ℝ := rK ^ 2 + d with hR2
  set κ : ℝ := 4 / d with hκ
  have hκ0 : 0 < κ := by positivity
  set δ : ℝ := 1 / (4 * (M ^ 2 + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set s₀ := exhaustionCore p R2 κ δ h with hs₀
  set s : ComplexModel n → ℝ := fun x ↦ if x ∈ Ω then capProfile (s₀ x) else 2 with hs
  have hsΩ : ∀ x ∈ Ω, s x = capProfile (s₀ x) := fun x hx ↦ if_pos hx
  have hsnΩ : ∀ x ∉ Ω, s x = 2 := fun x hx ↦ if_neg hx
  have hs₀nn : ∀ x, Real.exp (κ * (‖x - p‖ ^ 2 - R2)) ≤ s₀ x := fun x ↦ by
    simp only [hs₀, exhaustionCore]
    have : 0 ≤ δ * ‖(h x)⁻¹‖ ^ 2 := by positivity
    linarith
  have hs₀c : ∀ x ∈ Ω, ContDiffAt ℝ ∞ s₀ x := fun x hx ↦ contDiffAt_exhaustionCore hh hx.1 hx.2
  -- `s = 2` near every point off `Ω`
  have hfar : ∀ x ∉ Ω, s =ᶠ[𝓝 x] fun _ ↦ 2 := by
    intro x hx
    by_cases hxb : x ∈ ball p r
    · have hx0 : h x = 0 := by
        by_contra h0; exact hx ⟨hxb, h0⟩
      have hNo : IsOpen (ball p r ∩ (fun y ↦ ‖h y‖ ^ 2) ⁻¹' Iio (δ / 2)) :=
        (hh.continuousOn.norm.pow 2).isOpen_inter_preimage isOpen_ball isOpen_Iio
      filter_upwards [hNo.mem_nhds ⟨hxb, by simp [hx0, hδ0]⟩] with y hy
      by_cases hyΩ : y ∈ Ω
      · rw [hsΩ y hyΩ]
        refine capProfile_of_ge ?_
        have hy0 : h y ≠ 0 := hyΩ.2
        have hpos : 0 < ‖h y‖ ^ 2 := by positivity
        have hlt : ‖h y‖ ^ 2 < δ / 2 := hy.2
        have h2 : 2 ≤ δ * ‖(h y)⁻¹‖ ^ 2 := by
          rw [norm_inv, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
          linarith
        have : 0 ≤ Real.exp (κ * (‖y - p‖ ^ 2 - R2)) := (Real.exp_pos _).le
        simp only [hs₀, exhaustionCore]
        linarith
      · exact hsnΩ y hyΩ
    · have hxr : r ≤ ‖x - p‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hxb; exact hxb
      have hr0 : 0 < r := hrK0.trans hrKr
      have hNo : IsOpen {y : ComplexModel n | R2 + d / 2 < ‖y - p‖ ^ 2} :=
        isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm.pow 2)
      have hxN : R2 + d / 2 < ‖x - p‖ ^ 2 := by
        have : r ^ 2 ≤ ‖x - p‖ ^ 2 := pow_le_pow_left₀ hr0.le hxr 2
        rw [hR2, hd] at *
        nlinarith
      filter_upwards [hNo.mem_nhds hxN] with y hy
      by_cases hyΩ : y ∈ Ω
      · rw [hsΩ y hyΩ]
        refine capProfile_of_ge ((?_ : (2 : ℝ) ≤ Real.exp (κ * (‖y - p‖ ^ 2 - R2))).trans
          (hs₀nn y))
        have h1 : 2 ≤ κ * (‖y - p‖ ^ 2 - R2) := by
          have hy' : d / 2 < ‖y - p‖ ^ 2 - R2 := by
            have hy2 : R2 + d / 2 < ‖y - p‖ ^ 2 := hy
            linarith
          rw [hκ, div_mul_eq_mul_div, le_div_iff₀ hd0]
          linarith
        linarith [Real.add_one_le_exp (κ * (‖y - p‖ ^ 2 - R2))]
      · exact hsnΩ y hyΩ
  have hscd : ContDiff ℝ ∞ s := by
    refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
    by_cases hx : x ∈ Ω
    · have hev : s =ᶠ[𝓝 x] fun y ↦ capProfile (s₀ y) := by
        filter_upwards [hΩo.mem_nhds hx] with y hy using hsΩ y hy
      exact ((contDiff_capProfile.contDiffAt.comp x (hs₀c x hx))).congr_of_eventuallyEq hev
    · exact contDiffAt_const.congr_of_eventuallyEq (hfar x hx)
  have hsc : Continuous s := hscd.continuous
  have hsub : {x | s x ≤ 1} ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    simp only [mem_ofPred_eq, hsnΩ x hxΩ] at hx
    norm_num at hx
  have hScpt : IsCompact {x | s x ≤ 1} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hsc continuous_const)
      ((Metric.isBounded_ball (x := p) (r := r)).subset (hsub.trans inter_subset_left))
  refine ⟨s, κ * Real.exp (-(κ * R2)), by positivity, hscd, hScpt, hsub, ?_, ?_⟩
  · -- `s ≤ 1/2` on `K`
    intro x hxK
    have hxΩ := hKΩ hxK
    have hxp : ‖x - p‖ ^ 2 ≤ rK ^ 2 := by
      have := mem_ball.mp (hKrK hxK)
      rw [dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
    have h1 : Real.exp (κ * (‖x - p‖ ^ 2 - R2)) ≤ 1 / 4 := by
      have hle : κ * (‖x - p‖ ^ 2 - R2) ≤ -4 := by
        have : ‖x - p‖ ^ 2 - R2 ≤ -d := by rw [hR2]; linarith
        calc κ * (‖x - p‖ ^ 2 - R2) ≤ κ * (-d) := mul_le_mul_of_nonneg_left this hκ0.le
          _ = -4 := by rw [hκ]; field_simp
      have h5 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
      calc Real.exp (κ * (‖x - p‖ ^ 2 - R2)) ≤ Real.exp (-4) := Real.exp_le_exp.mpr hle
        _ = 1 / Real.exp 4 := by rw [Real.exp_neg, one_div]
        _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (Real.exp_pos 4) (by norm_num)]; linarith
    have h2 : δ * ‖(h x)⁻¹‖ ^ 2 ≤ 1 / 4 := by
      have hb : ‖(h x)⁻¹‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM x hxK) 2
      rw [hδ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : s₀ x ≤ 1 / 2 := by
      simp only [hs₀, exhaustionCore]; linarith
    rw [hsΩ x hxΩ, capProfile_of_le (by linarith)]
    exact h3
  · -- strict plurisubharmonicity on `{s < 1}`
    intro x hx v
    have hxΩ : x ∈ Ω := hsub (le_of_lt hx)
    have hs₀x : s₀ x < 1 := by
      rw [hsΩ x hxΩ] at hx
      by_contra hge
      exact absurd hx (not_lt.mpr (one_lt_capProfile (lt_of_le_of_ne (not_lt.mp hge)
        (fun h1 ↦ by rw [← h1, capProfile_of_le (by norm_num)] at hx; linarith))).le)
    have hs₀cont : ContinuousOn s₀ Ω := fun y hy ↦ (hs₀c y hy).continuousAt.continuousWithinAt
    have hOo : IsOpen (Ω ∩ s₀ ⁻¹' Iio (3 / 2)) := hs₀cont.isOpen_inter_preimage hΩo isOpen_Iio
    have hEq : EqOn s s₀ (Ω ∩ s₀ ⁻¹' Iio (3 / 2)) := fun y hy ↦ by
      rw [hsΩ y hy.1, capProfile_of_le (le_of_lt hy.2)]
    rw [leviForm_congr_of_eqOn hOo hEq ⟨hxΩ, show s₀ x < 3 / 2 by linarith⟩]
    exact le_leviForm_exhaustionCore hκ0.le hδ0.le hh hxΩ.1 hxΩ.2 v

/-- **`∂̄` with `L²` estimates on the complement of a hypersurface in a ball** (plan P3 for
`Ω = B(p, r) \ {h = 0}`, blueprint `l2:complement-solution`). -/
theorem exists_holomorphic_ball_inter_ne_zero {p : ComplexModel n} {r : ℝ}
    {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h (ball p r))
    {Φ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (ball p r ∩ {x | h x ≠ 0}))
    (hpsh : ∀ x ∈ ball p r ∩ {x | h x ≠ 0}, ∀ ξ, 0 ≤ leviForm Φ x ξ)
    {h₀ : ComplexModel n → ℂ} (hh₀ : ContDiffOn ℝ ∞ h₀ (ball p r ∩ {x | h x ≠ 0}))
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ ball p r ∩ {x | h x ≠ 0}, 0 ≤ g x)
    (hfg : ∀ x ∈ ball p r ∩ {x | h x ≠ 0}, ∀ ξ : ComplexModel n,
      ‖dbarDir ξ h₀ x‖ ^ 2 ≤ g x * leviForm Φ x ξ)
    (hgi : Integrable (fun x ↦ g x * Real.exp (-Φ x)) (volume.restrict (ball p r ∩ {x | h x ≠ 0}))) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball p r ∩ {x | h x ≠ 0}) ∧
      ∫⁻ x in ball p r ∩ {x | h x ≠ 0}, ENNReal.ofReal (‖h₀ x - G x‖ ^ 2 * Real.exp (-Φ x)) ≤
        ENNReal.ofReal (2 * ∫ x in ball p r ∩ {x | h x ≠ 0}, g x * Real.exp (-Φ x)) :=
  exists_holomorphic_of_strictPshExhaustion
    (hh.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton)
    (hasStrictPshExhaustion_ball_inter_ne_zero hh) hΦ hpsh hh₀ hg0 hfg hgi

end SGPT.Okounkov.TranscendentalL2
