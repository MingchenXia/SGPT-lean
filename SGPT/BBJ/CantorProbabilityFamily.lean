import SGPT.BBJ.CantorLogPotential

/-! The same moving-section kernels averaged against an arbitrary probability.
The literal extended deficit integral retains poles, including atoms. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual nonnegative kernel integral for any parameter measure. -/
def cantorProbabilityLogIntegral (σ : Measure (ℕ → Bool)) (p : P1) : ℝ≥0∞ :=
  ∫⁻ b, cantorLogDeficit b p ∂σ

/-- The negative extended integral, not an integral of totalized real values. -/
def cantorProbabilityLogPotential (σ : Measure (ℕ → Bool)) (p : P1) : EReal :=
  -(cantorProbabilityLogIntegral σ p : EReal)

/-- The family recovers the original literal Cantor average. -/
theorem cantorProbabilityLogPotential_cantorBitProbability :
    cantorProbabilityLogPotential cantorBitProbability = cantorLogPotential := rfl

theorem cantorProbabilityLogPotential_nonpos (σ : Measure (ℕ → Bool)) (p : P1) :
    cantorProbabilityLogPotential σ p ≤ 0 := by
  change -(cantorProbabilityLogIntegral σ p : EReal) ≤ 0
  simpa only [neg_zero] using
    EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_nonneg (cantorProbabilityLogIntegral σ p))

theorem cantorProbabilityLogPotential_ne_top (σ : Measure (ℕ → Bool)) (p : P1) :
    cantorProbabilityLogPotential σ p ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (cantorProbabilityLogPotential_nonpos σ p) EReal.zero_lt_top)

private lemma family_corrected_deficit (C r : ℝ) (hr : r ≤ C) (h : EReal) (hh : h ≤ 0) :
    ((C : EReal) - (h+(r : EReal))).toENNReal =
      ENNReal.ofReal (C-r) + (-h).toENNReal := by
  have ht : h ≠ ⊤ := ne_of_lt (hh.trans_lt EReal.zero_lt_top)
  by_cases hb : h = ⊥
  · simp [hb]
  have he := EReal.coe_toReal ht hb
  rw [← he]
  have hn : h.toReal ≤ 0 :=
    EReal.coe_le_coe_iff.mp (by simpa only [he, EReal.coe_zero] using hh)
  simp only [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg,
    EReal.real_coe_toENNReal]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hr) (neg_nonneg.mpr hn)]
  congr 1
  ring

private lemma family_corrected_integral (C r : ℝ) (hr : r ≤ C) (G : ℝ≥0∞) :
    (C : EReal) - ((ENNReal.ofReal (C-r)+G : ℝ≥0∞) : EReal) =
      -(G : EReal)+(r : EReal) := by
  by_cases hG : G = ⊤
  · simp [hG]
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal,
    max_eq_left (sub_nonneg.mpr hr), ← EReal.coe_ennreal_toReal hG]
  simp only [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg]
  congr 1
  ring

private lemma family_continuous_corrected_kernel (j : Bool) :
    Continuous (fun q : (ℕ → Bool) × ComplexModel 1 =>
      movingProjectiveSectionPotential (cantorCode q.1) ((projectiveModelChart j).symm q.2)
        +(projectiveFSPotential q.2 : EReal)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hp : ContinuousAt (fun q : (ℕ → Bool) × ComplexModel 1 =>
      (movingProjectiveSectionPotential (cantorCode q.1) ((projectiveModelChart j).symm q.2),
        (projectiveFSPotential q.2 : EReal))) q :=
    (continuous_cantorLogKernel j).continuousAt.prodMk
      ((continuous_coe_real_ereal.comp
        (contDiff_projectiveFSPotential.continuous.comp continuous_snd)).continuousAt)
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).comp hp

/-- Full chart PSH of the literal average for every probability, retaining poles. -/
theorem cantorProbabilityLogPotential_corrected_psh
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] (j : Bool) :
    PlurisubharmonicOn (fun z : ComplexModel 1 =>
      cantorProbabilityLogPotential σ ((projectiveModelChart j).symm z)
        +(projectiveFSPotential z : EReal)) univ := by
  intro z₀ _
  let R : ℝ := ‖z₀‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let W : Set (ComplexModel 1) := ball 0 R
  have hz : z₀ ∈ W := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith
  let C : ℝ := Real.log (1+R^2)
  let u : (ℕ → Bool) → ComplexModel 1 → EReal := fun b z =>
    movingProjectiveSectionPotential (cantorCode b) ((projectiveModelChart j).symm z)
      +(projectiveFSPotential z : EReal)
  have hρ (z : ComplexModel 1) (hz : z ∈ W) : projectiveFSPotential z ≤ C :=
    (projectiveFSPotential_closedBall_bounds R hR z (ball_subset_closedBall hz)).2
  have hC : ∀ b, ∀ z ∈ W, u b z ≤ (C : EReal) := by
    intro b z hz
    exact (add_le_add (movingProjectiveSectionPotential_nonpos _ _)
      (EReal.coe_le_coe_iff.mpr (hρ z hz))).trans_eq (zero_add _)
  have hm : Measurable (fun q : (ℕ → Bool) × ComplexModel 1 =>
      ((C : EReal)-u q.1 q.2).toENNReal) :=
    (continuous_finiteDeficit C).measurable.comp
      (family_continuous_corrected_kernel j).measurable
  have hu : ∀ b, DiscPshOn (u b) W := by
    intro b
    exact (movingProjectiveSectionPotential_corrected_psh (cantorCode b) j).discPshOn.mono
      (subset_univ _)
  have havg := plurisubharmonicOn_probabilityPshAverage σ C u W
    isOpen_ball hm hC hu
  apply (havg z₀ hz).congr
  filter_upwards [isOpen_ball.mem_nhds hz] with z hzW
  have heq (b : ℕ → Bool) : ((C : EReal)-u b z).toENNReal =
      ENNReal.ofReal (C-projectiveFSPotential z)+
        cantorLogDeficit b ((projectiveModelChart j).symm z) :=
    family_corrected_deficit C _ (hρ z hzW) _ (movingProjectiveSectionPotential_nonpos _ _)
  unfold probabilityPshAverage
  simp_rw [heq]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact family_corrected_integral C _ (hρ z hzW) _

/-- Noncollapse is independent of whether the probability has atoms. -/
theorem cantorProbabilityLogIntegral_lt_top_off
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ]
    (p : P1) (hp : p ∉ projectiveCantorSet) :
    cantorProbabilityLogIntegral σ p < ⊤ := by
  obtain ⟨L, _, hL⟩ := movingProjectiveSectionPotential_code_uniform_lower p hp
  have hg (b : ℕ → Bool) : cantorLogDeficit b p ≤ ENNReal.ofReal (-L) := by
    have h := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hL b))
    simpa only [cantorLogDeficit, ← EReal.coe_neg,EReal.real_coe_toENNReal] using h
  have hI := lintegral_mono (μ := σ) hg
  simp only [lintegral_const,measure_univ,mul_one] at hI
  exact hI.trans_lt ENNReal.ofReal_lt_top

theorem cantorProbabilityLogPotential_ne_bot_off
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ]
    (p : P1) (hp : p ∉ projectiveCantorSet) :
    cantorProbabilityLogPotential σ p ≠ ⊥ := by
  intro h
  have ht : (cantorProbabilityLogIntegral σ p : EReal) = ⊤ := EReal.neg_eq_bot_iff.mp h
  exact (cantorProbabilityLogIntegral_lt_top_off σ p hp).ne (EReal.coe_ennreal_eq_top_iff.mp ht)

theorem cantorProbabilityLogPotential_locallyNondegenerate
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] :
    SGPT.PSH.LocallyNondegenerateOn (cantorProbabilityLogPotential σ) univ := by
  intro p _ O hO hp
  obtain ⟨q,hqO,hqK⟩ := dense_compl_projectiveCantorSet.inter_open_nonempty O hO ⟨p,hp⟩
  exact ⟨q,⟨mem_univ _,hqO⟩,cantorProbabilityLogPotential_ne_bot_off σ q hqK⟩

/-- The original source FS-PSH predicate for every actual probability. -/
theorem isThetaPSH_cantorProbabilityLogPotential
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (cantorProbabilityLogPotential σ) := by
  apply SGPT.PSH.VariableComplexAtlas.isThetaPSH_of_chart_corrected
    (fun _ => projectiveFSPotential)
    (fun _ => contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ => rfl) ?_
    (cantorProbabilityLogPotential_ne_top σ) (cantorProbabilityLogPotential_locallyNondegenerate σ)
  intro j z _
  exact cantorProbabilityLogPotential_corrected_psh σ j z (mem_univ _)

/-- Genuine native FS-PSH for the same extended integral. -/
theorem isThetaPshPotential_cantorProbabilityLogPotential
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] :
    IsThetaPshPotential projectiveNativeFSBackground.form.val (cantorProbabilityLogPotential σ) :=
  isThetaPshPotential_projectiveNativeFS_of_source (isThetaPSH_cantorProbabilityLogPotential σ)

theorem locallyIntegrableOn_cantorProbabilityLogPotential_chart
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] (e : ComplexChart 1 P1) :
    LocallyIntegrableOn (fun z => (chartFunction (cantorProbabilityLogPotential σ) e z).toReal)
      e.val.target volume :=
  (isThetaPshPotential_cantorProbabilityLogPotential σ).quasiPshPotential.locallyIntegrableOn_chart_toReal e

theorem integrableOn_cantorProbabilityLogPotential_chart
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] (e : ComplexChart 1 P1)
    {K : Set (ComplexModel 1)} (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    IntegrableOn (fun z => (chartFunction (cantorProbabilityLogPotential σ) e z).toReal) K volume :=
  (isThetaPshPotential_cantorProbabilityLogPotential σ).quasiPshPotential.integrableOn_chart_toReal e hK hKe

end SGPT.BBJ
