import SGPT.BBJ.CantorLogPotential
import SGPT.PSH.PlurifineBasis
import Mathlib.MeasureTheory.MeasurableSpace.Card

/-! Genuine PSH averages separating the existing actual fast Cantor code. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceNonBorelDraft
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.BBJ SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "Bits" => ℕ → Bool

def domain : Opens (ComplexModel 1) :=
  ⟨{z | Complex.normSq (z 0) < 1},
    isOpen_lt (Complex.continuous_normSq.comp
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous) continuous_const⟩

def code (b : Bits) : ComplexModel 1 := projectiveModelEquiv (cantorCode b : ℂ)

lemma code_mem (b : Bits) : code b ∈ domain := by
  change Complex.normSq (projectiveModelEquiv (cantorCode b : ℂ) 0) < 1
  rw [projectiveModelEquiv_apply_zero, Complex.normSq_ofReal]
  have h0 := cantorCode_nonneg b
  have h1 := cantorCode_lt_half b
  nlinarith

lemma code_chart (b : Bits) :
    (projectiveModelChart false).symm (code b) = projectiveCantorCode b := by
  change projectiveLineHomeomorph
    (projectiveFiniteChart.symm (projectiveModelEquiv.symm (projectiveModelEquiv _))) = _
  rw [projectiveModelEquiv.symm_apply_apply, projectiveFiniteChart_symm]
  rfl

def weight (a b : Bits) : ℝ := (cantorCode a-cantorCode b)^2

lemma weight_bounds (a b : Bits) : 0 ≤ weight a b ∧ weight a b ≤ 1 := by
  have ha0 := cantorCode_nonneg a
  have hb0 := cantorCode_nonneg b
  have ha1 := cantorCode_lt_half a
  have hb1 := cantorCode_lt_half b
  constructor
  · exact sq_nonneg _
  · dsimp [weight]
    nlinarith [sq_nonneg (cantorCode a+cantorCode b)]

lemma weight_pos {a b : Bits} (hne : a ≠ b) : 0 < weight a b := by
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h => hne (cantorCode_injective h)))

def kernel (a b : Bits) (z : ComplexModel 1) : EReal :=
  (weight a b : EReal) *
    (movingProjectiveSectionPotential (cantorCode b) ((projectiveModelChart false).symm z)
      +(projectiveFSPotential z : EReal))

lemma kernel_psh (a b : Bits) : PlurisubharmonicOn (kernel a b) univ := by
  by_cases h : weight a b = 0
  · have heq : kernel a b = fun _ => (0 : EReal) := by
      funext z
      simp only [kernel, h, EReal.coe_zero, zero_mul]
    rw [heq]
    exact fun z _ => plurisubharmonicAt_const (0 : EReal) (by simp) z
  · exact (movingProjectiveSectionPotential_corrected_psh (cantorCode b) false).const_mul
      (lt_of_le_of_ne (weight_bounds a b).1 (Ne.symm h))

lemma kernel_upper (a b : Bits) (z : ComplexModel 1) (hz : z ∈ domain) :
    kernel a b z ≤ (Real.log 2 : EReal) := by
  have hρ : projectiveFSPotential z ≤ Real.log 2 := by
    rw [projectiveFSPotential_eq]
    exact Real.log_le_log (by have := Complex.normSq_nonneg (z 0); linarith)
      (by change Complex.normSq (z 0) < 1 at hz; linarith)
  have hc : movingProjectiveSectionPotential (cantorCode b)
      ((projectiveModelChart false).symm z)+(projectiveFSPotential z : EReal) ≤
        (projectiveFSPotential z : EReal) := by
    simpa only [zero_add] using add_le_add
      (movingProjectiveSectionPotential_nonpos (cantorCode b)
        ((projectiveModelChart false).symm z)) (le_refl (projectiveFSPotential z : EReal))
  have h := mul_le_mul_of_nonneg_left (hc.trans (EReal.coe_le_coe_iff.mpr hρ))
    (EReal.coe_nonneg.mpr (weight_bounds a b).1)
  apply h.trans
  rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
  exact mul_le_of_le_one_left (Real.log_nonneg (by norm_num)) (weight_bounds a b).2

lemma kernel_deficit_measurable (a : Bits) :
    Measurable (fun q : Bits × ComplexModel 1 =>
      ((Real.log 2 : EReal)-kernel a q.1 q.2).toENNReal) := by
  have hw : Measurable (fun q : Bits × ComplexModel 1 => weight a q.1) := by
    exact (continuous_const.sub (continuous_cantorCode.comp continuous_fst)).pow 2 |>.measurable
  have hρ : Measurable (fun q : Bits × ComplexModel 1 =>
      (projectiveFSPotential q.2 : EReal)) :=
    (continuous_coe_real_ereal.comp
      (contDiff_projectiveFSPotential.continuous.comp continuous_snd)).measurable
  exact (measurable_const.sub (hw.coe_real_ereal.mul
    ((continuous_cantorLogKernel false).measurable.add hρ))).ereal_toENNReal

def separator (a : Bits) : ComplexModel 1 → EReal :=
  probabilityPshAverage cantorBitProbability (Real.log 2) (kernel a)

lemma separator_psh (a : Bits) : PlurisubharmonicOn (separator a) domain := by
  exact plurisubharmonicOn_probabilityPshAverage cantorBitProbability (Real.log 2)
    (kernel a) domain domain.isOpen (kernel_deficit_measurable a) (kernel_upper a)
      (fun b => (kernel_psh a b).discPshOn.mono (subset_univ _))

end SGPT.PSH.SourceNonBorelDraft
