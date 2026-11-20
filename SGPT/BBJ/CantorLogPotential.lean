import SGPT.BBJ.UniformMovingSectionL1
import SGPT.BBJ.CantorProbability
import SGPT.BBJ.CantorSectionBounds
import SGPT.BBJ.ProbabilityPshAverage

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- Nonnegative extended deficit of the actual moving kernel. -/
def cantorLogDeficit (b : ℕ → Bool) (p : P1) : ℝ≥0∞ :=
  (-movingProjectiveSectionPotential (cantorCode b) p).toENNReal

/-- Literal nonnegative integral, retaining infinite values. -/
def cantorLogIntegral (p : P1) : ℝ≥0∞ :=
  ∫⁻ b, cantorLogDeficit b p ∂cantorBitProbability

/-- The actual logarithmic average; infinite integral gives bottom. -/
def cantorLogPotential (p : P1) : EReal := -(cantorLogIntegral p : EReal)

theorem continuous_cantorLogKernel (j : Bool) :
    Continuous (fun q : (ℕ → Bool) × ComplexModel 1 =>
      movingProjectiveSectionPotential (cantorCode q.1)
        ((projectiveModelChart j).symm q.2)) :=
by
  have hc : Continuous (fun q : (ℕ → Bool) × ComplexModel 1 => cantorCode q.1) :=
    continuous_cantorCode.comp continuous_fst
  have hm : Continuous (fun q : (ℕ → Bool) × ComplexModel 1 =>
      (cantorCode q.1, q.2)) := hc.prodMk continuous_snd
  simpa only [Function.comp_def] using (continuous_movingSectionKernel j).comp hm

theorem measurable_cantorLogDeficit_chart (j : Bool) :
    Measurable (fun q : (ℕ → Bool) × ComplexModel 1 =>
      cantorLogDeficit q.1 ((projectiveModelChart j).symm q.2)) :=
  (continuous_cantorLogKernel j).neg.measurable.ereal_toENNReal

theorem measurable_cantorLogDeficit (p : P1) :
    Measurable (fun b => cantorLogDeficit b p) := by
  obtain ⟨j, hj⟩ := projectiveLineAtlas.cover p
  change Bool at j
  have hm := (measurable_cantorLogDeficit_chart j).comp
    (measurable_id.prodMk (measurable_const (a := (projectiveModelChart j) p)))
  change Measurable (fun b : ℕ → Bool => cantorLogDeficit b
    ((projectiveModelChart j).symm ((projectiveModelChart j) p))) at hm
  rw [(projectiveModelChart j).left_inv hj] at hm
  exact hm

theorem cantorLogPotential_nonpos (p : P1) : cantorLogPotential p ≤ 0 := by
  change -(cantorLogIntegral p : EReal) ≤ 0
  simpa only [neg_zero] using EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_nonneg (cantorLogIntegral p))

theorem cantorLogPotential_ne_top (p : P1) : cantorLogPotential p ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (cantorLogPotential_nonpos p) EReal.zero_lt_top)

/-- Finite correction of a nonpositive extended kernel, including its pole. -/
private lemma corrected_deficit (C r : ℝ) (hr : r ≤ C) (h : EReal) (hh : h ≤ 0) :
    ((C : EReal) - (h+(r : EReal))).toENNReal =
      ENNReal.ofReal (C-r) + (-h).toENNReal := by
  have ht : h ≠ ⊤ := ne_of_lt (hh.trans_lt EReal.zero_lt_top)
  by_cases hb : h = ⊥
  · simp [hb]
  have he := EReal.coe_toReal ht hb
  rw [← he]
  have hn : h.toReal ≤ 0 := by
    exact EReal.coe_le_coe_iff.mp (by simpa only [he, EReal.coe_zero] using hh)
  simp only [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg,
    EReal.real_coe_toENNReal]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hr) (neg_nonneg.mpr hn)]
  congr 1
  ring

private lemma corrected_integral (C r : ℝ) (hr : r ≤ C) (G : ℝ≥0∞) :
    (C : EReal) - ((ENNReal.ofReal (C-r)+G : ℝ≥0∞) : EReal) =
      -(G : EReal)+(r : EReal) := by
  by_cases hG : G = ⊤
  · simp [hG]
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal,
    max_eq_left (sub_nonneg.mpr hr), ← EReal.coe_ennreal_toReal hG]
  simp only [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg]
  congr 1
  ring

private lemma continuous_cantorCorrectedKernel (j : Bool) :
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

/-- The literal average, corrected by the same FS potential, is genuinely PSH. -/
theorem cantorLogPotential_corrected_psh (j : Bool) :
    PlurisubharmonicOn (fun z : ComplexModel 1 =>
      cantorLogPotential ((projectiveModelChart j).symm z)
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
      ((C : EReal)-u q.1 q.2).toENNReal) := by
    exact (continuous_finiteDeficit C).measurable.comp
      (continuous_cantorCorrectedKernel j).measurable
  have hu : ∀ b, DiscPshOn (u b) W := by
    intro b
    exact (movingProjectiveSectionPotential_corrected_psh (cantorCode b) j).discPshOn.mono
      (subset_univ _)
  have havg := plurisubharmonicOn_probabilityPshAverage cantorBitProbability C u W
    isOpen_ball hm hC hu
  apply (havg z₀ hz).congr
  filter_upwards [isOpen_ball.mem_nhds hz] with z hzW
  have heq (b : ℕ → Bool) : ((C : EReal)-u b z).toENNReal =
      ENNReal.ofReal (C-projectiveFSPotential z)+
        cantorLogDeficit b ((projectiveModelChart j).symm z) :=
    corrected_deficit C _ (hρ z hzW) _ (movingProjectiveSectionPotential_nonpos _ _)
  unfold probabilityPshAverage
  simp_rw [heq]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact corrected_integral C _ (hρ z hzW) _

private theorem finite_off_cantor_code_lower (z : ℂ)
    (hz : projectiveLineHomeomorph (z : OnePoint ℂ) ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ b : ℕ → Bool,
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorCode b)
        (projectiveLineHomeomorph (z : OnePoint ℂ)) := by
  let C : Set ℂ := range (fun b : ℕ → Bool => (cantorCode b : ℂ))
  have hcompact : IsCompact C := isCompact_range
    (Complex.continuous_ofReal.comp continuous_cantorCode)
  have hnonempty : C.Nonempty := ⟨(cantorCode (fun _ => false) : ℂ),fun _ => false,rfl⟩
  have hzC : z ∉ C := by
    rintro ⟨b,rfl⟩
    exact hz ⟨b,rfl⟩
  let d := Metric.infDist z C
  have hd : 0 < d := (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hzC
  let B := Real.log (d^2)-Real.log (1+Complex.normSq z)-Real.log 2
  refine ⟨min 0 B,min_le_left _ _,fun b => ?_⟩
  let c := cantorCode b
  have hcC : (c : ℂ) ∈ C := ⟨b,rfl⟩
  have hgap : d ≤ dist z (c : ℂ) := Metric.infDist_le_dist_of_mem hcC
  rw [dist_eq_norm] at hgap
  have hzc : z-(c : ℂ) ≠ 0 := norm_pos_iff.mp (hd.trans_le hgap)
  have hlog := Real.log_le_log (sq_pos_of_pos hd)
    (pow_le_pow_left₀ hd.le hgap 2)
  have hc0 : 0 ≤ c := cantorCode_nonneg b
  have hc1 : c < 1/2 := cantorCode_lt_half b
  have hCLog : Real.log (1+c^2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith)
  apply le_trans (EReal.coe_le_coe_iff.mpr (min_le_right 0 B))
  rw [movingProjectiveSectionPotential_finite,logNormSq_of_ne_zero hzc,
    ← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff]
  dsimp only [B]
  linarith


/-- A finite lower bound for every actual code center, not just finite prefixes. -/
theorem movingProjectiveSectionPotential_code_uniform_lower (p : P1)
    (hp : p ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ b : ℕ → Bool,
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorCode b) p := by
  obtain ⟨q,rfl⟩ := projectiveLineHomeomorph.surjective p
  induction q using OnePoint.rec with
  | infty =>
    refine ⟨-Real.log 2,?_,fun b => ?_⟩
    · exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
    · exact movingProjectiveSectionPotential_infinity_lower (cantorCode b)
        (cantorCode_nonneg b) (cantorCode_lt_half b).le
  | coe z => exact finite_off_cantor_code_lower z hp

/-- Every point outside the actual Cantor set has a finite deficit integral. -/
theorem cantorLogIntegral_lt_top_off (p : P1) (hp : p ∉ projectiveCantorSet) :
    cantorLogIntegral p < ⊤ := by
  obtain ⟨L, _, hL⟩ := movingProjectiveSectionPotential_code_uniform_lower p hp
  have hg (b : ℕ → Bool) : cantorLogDeficit b p ≤ ENNReal.ofReal (-L) := by
    have h := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hL b))
    simpa only [cantorLogDeficit, ← EReal.coe_neg,EReal.real_coe_toENNReal] using h
  have hI := lintegral_mono (μ := cantorBitProbability) hg
  simp only [lintegral_const,measure_univ,mul_one] at hI
  exact hI.trans_lt ENNReal.ofReal_lt_top

theorem cantorLogPotential_ne_bot_off (p : P1) (hp : p ∉ projectiveCantorSet) :
    cantorLogPotential p ≠ ⊥ := by
  intro h
  have ht : (cantorLogIntegral p : EReal) = ⊤ := EReal.neg_eq_bot_iff.mp h
  exact (cantorLogIntegral_lt_top_off p hp).ne (EReal.coe_ennreal_eq_top_iff.mp ht)

theorem cantorLogPotential_locallyNondegenerate :
    SGPT.PSH.LocallyNondegenerateOn cantorLogPotential univ := by
  intro p _ O hO hp
  obtain ⟨q,hqO,hqK⟩ := dense_compl_projectiveCantorSet.inter_open_nonempty O hO ⟨p,hp⟩
  exact ⟨q,⟨mem_univ _,hqO⟩,cantorLogPotential_ne_bot_off q hqK⟩

/-- Entire original source FS-PSH condition for the literal average. -/
theorem isThetaPSH_cantorLogPotential :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm cantorLogPotential := by
  apply SGPT.PSH.VariableComplexAtlas.isThetaPSH_of_chart_corrected
    (fun _ => projectiveFSPotential)
    (fun _ => contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ => rfl) ?_
    cantorLogPotential_ne_top cantorLogPotential_locallyNondegenerate
  intro j z _
  exact cantorLogPotential_corrected_psh j z (mem_univ _)

/-- Genuine native FS-PSH for the same literal integral. -/
theorem isThetaPshPotential_cantorLogPotential :
    IsThetaPshPotential projectiveNativeFSBackground.form.val cantorLogPotential :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_cantorLogPotential

/-- Local integrability in every genuine native chart of the original manifold. -/
theorem locallyIntegrableOn_cantorLogPotential_chart
    (e : ComplexChart 1 P1) :
    LocallyIntegrableOn (fun z => (chartFunction cantorLogPotential e z).toReal)
      e.val.target volume :=
  isThetaPshPotential_cantorLogPotential.quasiPshPotential.locallyIntegrableOn_chart_toReal e

/-- Actual integrability on any compact subset of any genuine native chart. -/
theorem integrableOn_cantorLogPotential_chart (e : ComplexChart 1 P1)
    {K : Set (ComplexModel 1)} (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    IntegrableOn (fun z => (chartFunction cantorLogPotential e z).toReal) K volume :=
  isThetaPshPotential_cantorLogPotential.quasiPshPotential.integrableOn_chart_toReal e hK hKe

/-- Two actual code centers in the same cylinder have a single-tail difference bound. -/
lemma cantorCode_cylinder_abs_lt (a b : ℕ → Bool) (n : ℕ)
    (ha : a ∈ cantorCylinder (Finset.range n) b) :
    |cantorCode b-cantorCode a| < 2*cantorCoefficient n := by
  have hp : (∑ k ∈ Finset.range n, (if a k then cantorCoefficient k else 0)) =
      ∑ k ∈ Finset.range n, (if b k then cantorCoefficient k else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    have he : a k = b k := ha k hk
    rw [he]
  have ha' := cantorCode_prefix_error a n
  have hb' := cantorCode_prefix_error b n
  rw [hp] at ha'
  apply lt_of_le_of_lt ?_ (by nlinarith [cantorCoefficient_pos n] :
    (4/3 : ℝ)*cantorCoefficient n < 2*cantorCoefficient n)
  exact abs_le.mpr ⟨by linarith [ha'.2,hb'.1],by linarith [hb'.2,ha'.1]⟩

/-- Each actual matching cylinder gives the quantitative extended kernel bound. -/
lemma movingProjectiveSectionPotential_matching_cylinder (a b : ℕ → Bool) (n : ℕ)
    (ha : a ∈ cantorCylinder (Finset.range n) b) :
    movingProjectiveSectionPotential (cantorCode a) (projectiveCantorCode b) ≤
      ((-(16 : ℝ)^(n+1)*Real.log 2 : ℝ) : EReal) := by
  let c := cantorCode a
  have htail : |cantorCode b-c| < 2*cantorCoefficient n := cantorCode_cylinder_abs_lt a b n ha
  change movingProjectiveSectionPotential c
    (projectiveLineHomeomorph ((cantorCode b : ℂ) : OnePoint ℂ)) ≤ _
  rw [movingProjectiveSectionPotential_finite]
  by_cases he : cantorCode b=c
  · simp [he]
  · have hz : (cantorCode b : ℂ)-(c : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr he)
    have hn : ‖(cantorCode b : ℂ)-(c : ℂ)‖ < 2*cantorCoefficient n := by
      simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using htail
    have hlog := Real.log_le_log (sq_pos_of_pos (norm_pos_iff.mpr hz))
      (pow_le_pow_left₀ (norm_nonneg _) hn.le 2)
    simp only [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (cantorCoefficient_pos n).ne',cantorCoefficient_log] at hlog
    have hF : 0 ≤ Real.log (1+Complex.normSq (cantorCode b : ℂ)) :=
      Real.log_nonneg (by have := Complex.normSq_nonneg (cantorCode b : ℂ); linarith)
    have hC : 0 ≤ Real.log (1+c^2) := Real.log_nonneg (by nlinarith [sq_nonneg c])
    have hm : (2 : ℝ) ≤ (16 : ℝ)^(n+1) := by
      have h := (Nat.le_pow (Nat.succ_pos n) : 16 ≤ 16^(n+1))
      exact le_trans (by norm_num : (2 : ℝ) ≤ 16) (by exact_mod_cast h)
    have hnum := mul_nonneg (sub_nonneg.mpr hm) (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
    rw [logNormSq_of_ne_zero hz,Real.log_pow,← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff]
    norm_num at hlog hF hC ⊢
    nlinarith

lemma measurableSet_cantorCylinder (I : Finset ℕ) (b : ℕ → Bool) :
    MeasurableSet (cantorCylinder I b) :=
  MeasurableSet.pi I.countable_toSet (fun _ _ => measurableSet_singleton _)

/-- Cylinder mass supplies an exponentially divergent lower bound for the actual integral. -/
lemma cantorLogIntegral_code_lower (b : ℕ → Bool) (n : ℕ) :
    ENNReal.ofReal (16*(8 : ℝ)^n*Real.log 2) ≤ cantorLogIntegral (projectiveCantorCode b) := by
  let T := cantorCylinder (Finset.range n) b
  let A : ℝ := (16 : ℝ)^(n+1)*Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (a : ℕ → Bool) :
      T.indicator (fun _ => ENNReal.ofReal A) a ≤ cantorLogDeficit a (projectiveCantorCode b) := by
    by_cases ha : a ∈ T
    · rw [Set.indicator_of_mem ha]
      have h := EReal.toENNReal_le_toENNReal
        (EReal.neg_le_neg_iff.mpr (movingProjectiveSectionPotential_matching_cylinder a b n ha))
      have he : -(-(16 : ℝ)^(n+1)*Real.log 2) = A := by dsimp [A]; ring
      simpa only [cantorLogDeficit, ← EReal.coe_neg, he, EReal.real_coe_toENNReal] using h
    · rw [Set.indicator_of_notMem ha]
      exact zero_le
  have hI := lintegral_mono (μ := cantorBitProbability) hpoint
  rw [lintegral_indicator_const (measurableSet_cantorCylinder _ _),
    cantorBitProbability_cylinder, Finset.card_range] at hI
  have hcoeff : ENNReal.ofReal A*(1/2 : ℝ≥0∞)^n =
      ENNReal.ofReal (16*(8 : ℝ)^n*Real.log 2) := by
    have he : A*(1/2 : ℝ)^n = 16*(8 : ℝ)^n*Real.log 2 := by
      dsimp [A]
      rw [pow_succ]
      calc
        _ = 16*((16 : ℝ)^n*(1/2 : ℝ)^n)*Real.log 2 := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
      symm
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
      norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2), ← ENNReal.ofReal_mul hA, he]
  rw [hcoeff] at hI
  exact hI

/-- The literal average has an infinite deficit at every actual Cantor point. -/
lemma cantorLogIntegral_code_eq_top (b : ℕ → Bool) :
    cantorLogIntegral (projectiveCantorCode b) = ⊤ := by
  by_contra h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt
    ((cantorLogIntegral (projectiveCantorCode b)).toReal/(16*Real.log 2))
    (by norm_num : (1 : ℝ)<8)
  have hreal : (cantorLogIntegral (projectiveCantorCode b)).toReal < 16*(8 : ℝ)^n*Real.log 2 := by
    have := (div_lt_iff₀ (by positivity : 0 < 16*Real.log 2)).mp hn
    nlinarith
  have hle := cantorLogIntegral_code_lower b n
  rw [← ENNReal.ofReal_toReal h] at hle
  have hle' := (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).mp hle
  exact (not_lt_of_ge hle') hreal

/-- Exact pole locus of the actual averaged potential, distinct from the earlier witness. -/
theorem cantorLogPotential_eq_bot_iff (p : P1) :
    cantorLogPotential p = ⊥ ↔ p ∈ projectiveCantorSet := by
  constructor
  · intro hp
    by_contra hK
    exact cantorLogPotential_ne_bot_off p hK hp
  · rintro ⟨b,rfl⟩
    simp only [cantorLogPotential,cantorLogIntegral_code_eq_top,EReal.coe_ennreal_top,EReal.neg_top]

end SGPT.BBJ
