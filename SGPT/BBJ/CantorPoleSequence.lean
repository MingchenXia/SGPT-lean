import SGPT.BBJ.CantorSectionBounds
import SGPT.BBJ.CantorPrefixes
import SGPT.BBJ.MovingProjectiveSection
import SGPT.BBJ.CantorProbability
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

/-! The literal finite averages and decreasing pole sequence in the fourth
complete proof of source-bbj-polar-cantor.tex. The witness constructed here
serves polarity; no current representation of the independent measure is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open GlobalMultilinearExpansion
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual finite level average over all `2^n` zero-extended prefix centers. -/
def cantorLevelPotential (n : ℕ) : P1 → EReal :=
  sumPot Finset.univ (fun _ : Fin n → Bool => cantorAverageWeight n)
    (fun s => movingProjectiveSectionPotential (cantorPrefixReal s))

lemma cantorLevelPotential_nonpos (n : ℕ) (p : P1) : cantorLevelPotential n p ≤ 0 := by
  apply Finset.sum_nonpos
  intro s _
  have h := mul_le_mul_of_nonneg_left
    (movingProjectiveSectionPotential_nonpos (cantorPrefixReal s) p)
    (EReal.coe_nonneg.mpr (cantorAverageWeight_pos n).le)
  simpa only [mul_zero] using h

lemma isThetaPshPotential_cantorLevelPotential (n : ℕ) :
    IsThetaPshPotential SGPT.Toric.projectiveNativeFSBackground.form.val
      (cantorLevelPotential n) := by
  have hform : sumForm Finset.univ (fun _ : Fin n → Bool => cantorAverageWeight n)
      (fun _ => SGPT.Toric.projectiveNativeFSBackground.form) =
      SGPT.Toric.projectiveNativeFSBackground.form := by
    rw [sumForm, ← Finset.sum_smul, sum_cantorAverageWeight, one_smul]
  have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot
    (T := Finset.univ) (alpha := fun _ : Fin n → Bool =>
      SGPT.Toric.projectiveNativeFSBackground.form) Finset.univ_nonempty
    (fun _ => cantorAverageWeight_pos n)
    (fun s => isThetaPshPotential_movingProjectiveSectionPotential (cantorPrefixReal s))
  simpa only [hform, cantorLevelPotential] using h

/-- The exact finite partial pole sum; no regularization or different potential is substituted. -/
def cantorPolePartial (N : ℕ) (p : P1) : EReal :=
  ∑ n ∈ Finset.range N, ((cantorLevelWeight n : ℝ) : EReal) * cantorLevelPotential n p

lemma cantorPolePartial_zero (p : P1) : cantorPolePartial 0 p = 0 := by
  simp [cantorPolePartial]

private def partialWeight (N : ℕ) : Option (Fin N) → ℝ
  | none => (1 / 2 : ℝ) ^ N
  | some n => cantorLevelWeight n

private def partialFunction (N : ℕ) : Option (Fin N) → P1 → EReal
  | none => fun _ => 0
  | some n => cantorLevelPotential n

private lemma partialWeight_pos (N : ℕ) (i : Option (Fin N)) : 0 < partialWeight N i := by
  cases i with
  | none => exact pow_pos (by norm_num) _
  | some n => exact cantorLevelWeight_pos n

private lemma sum_partialWeight (N : ℕ) : (∑ i : Option (Fin N), partialWeight N i) = 1 := by
  rw [Fintype.sum_option]
  change (1 / 2 : ℝ) ^ N + (∑ n : Fin N, cantorLevelWeight n) = 1
  rw [Fin.sum_univ_eq_sum_range, sum_cantorLevelWeight]
  ring

private lemma cantorPolePartial_eq_sumPot (N : ℕ) :
    cantorPolePartial N = sumPot Finset.univ (partialWeight N) (partialFunction N) := by
  funext p
  simp only [sumPot, Fintype.sum_option, partialWeight, partialFunction, mul_zero, zero_add]
  exact (Fin.sum_univ_eq_sum_range
    (fun n => (cantorLevelWeight n : EReal) * cantorLevelPotential n p) N).symm

/-- The residual positive coefficient multiplies the genuine zero FS potential,
so EVERY partial sum, including the empty one, is genuine FS-PSH. -/
lemma isThetaPshPotential_cantorPolePartial (N : ℕ) :
    IsThetaPshPotential SGPT.Toric.projectiveNativeFSBackground.form.val (cantorPolePartial N) := by
  have hform : sumForm Finset.univ (partialWeight N)
      (fun _ => SGPT.Toric.projectiveNativeFSBackground.form) =
      SGPT.Toric.projectiveNativeFSBackground.form := by
    rw [sumForm, ← Finset.sum_smul, sum_partialWeight, one_smul]
  have hf (i : Option (Fin N)) : IsThetaPshPotential
      SGPT.Toric.projectiveNativeFSBackground.form.val (partialFunction N i) := by
    cases i with
    | none =>
      exact (LocalPotentials.isThetaPshPotential_zero_iff
        SGPT.Toric.projectiveNativeFSBackground.form).mpr
        SGPT.Toric.projectiveNativeFSBackground.isSemipositive
    | some n => exact isThetaPshPotential_cantorLevelPotential n
  have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot
    (T := Finset.univ) (alpha := fun _ : Option (Fin N) =>
      SGPT.Toric.projectiveNativeFSBackground.form) Finset.univ_nonempty
    (partialWeight_pos N) hf
  rw [cantorPolePartial_eq_sumPot]
  simpa only [hform] using h

lemma cantorPolePartial_antitone (p : P1) : Antitone (fun N => cantorPolePartial N p) := by
  apply antitone_nat_of_succ_le
  intro N
  change (∑ n ∈ Finset.range (N + 1),
    ((cantorLevelWeight n : ℝ) : EReal) * cantorLevelPotential n p) ≤ _
  rw [Finset.sum_range_succ]
  have h := mul_le_mul_of_nonneg_left (cantorLevelPotential_nonpos N p)
    (EReal.coe_nonneg.mpr (cantorLevelWeight_pos N).le)
  simpa only [mul_zero, zero_add, add_comm, cantorPolePartial] using
    add_le_add_left h (cantorPolePartial N p)

/-- The actual decreasing infimum used to witness the Cantor pole set. -/
def projectiveCantorPolePotential (p : P1) : EReal := ⨅ N, cantorPolePartial N p

lemma thetaPlurisubharmonic_projectiveCantorPolePotential :
    ThetaPlurisubharmonic SGPT.Toric.projectiveNativeFSBackground.form.val
      projectiveCantorPolePotential :=
  ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
    (fun N => (isThetaPshPotential_cantorPolePartial N).1) cantorPolePartial_antitone

lemma projectiveCantorPolePotential_nonpos (p : P1) : projectiveCantorPolePotential p ≤ 0 := by
  have h := iInf_le (fun N => cantorPolePartial N p) 0
  simpa only [projectiveCantorPolePotential, cantorPolePartial_zero] using h

lemma projectiveCantorPolePotential_ne_top (p : P1) : projectiveCantorPolePotential p ≠ ⊤ :=
  ne_of_lt ((projectiveCantorPolePotential_nonpos p).trans_lt (by simp))


private lemma coe_finset_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ I, f i : ℝ) : EReal) = ∑ i ∈ I, (f i : EReal) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp only [Finset.sum_insert hi, EReal.coe_add, ih]

lemma cantorLevelPotential_lower (p : P1) (L : ℝ)
    (hL : ∀ (n : ℕ) (s : Fin n → Bool),
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorPrefixReal s) p) (n : ℕ) :
    (L : EReal) ≤ cantorLevelPotential n p := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun s _ => mul_le_mul_of_nonneg_left (hL n s)
      (EReal.coe_nonneg.mpr (cantorAverageWeight_pos n).le))
  have heq : (∑ s : Fin n → Bool, (cantorAverageWeight n : EReal) * (L : EReal)) =
      (L : EReal) := by
    simp only [← EReal.coe_mul, ← coe_finset_sum, ← Finset.sum_mul,
      sum_cantorAverageWeight, one_mul]
  rw [heq] at h
  exact h

lemma cantorPolePartial_lower (p : P1) (L : ℝ) (hL0 : L ≤ 0)
    (hL : ∀ (n : ℕ) (s : Fin n → Bool),
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorPrefixReal s) p) (N : ℕ) :
    (L : EReal) ≤ cantorPolePartial N p := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => mul_le_mul_of_nonneg_left (cantorLevelPotential_lower p L hL n)
      (EReal.coe_nonneg.mpr (cantorLevelWeight_pos n).le))
  have heq : (∑ n ∈ Finset.range N, (cantorLevelWeight n : EReal) * (L : EReal)) =
      (((∑ n ∈ Finset.range N, cantorLevelWeight n) * L : ℝ) : EReal) := by
    simp only [← EReal.coe_mul, ← coe_finset_sum, Finset.sum_mul]
  rw [heq] at h
  exact (EReal.coe_le_coe_iff.mpr (by
    nlinarith [(cantorLevelWeight_partial_bounds N).2])).trans h

/-- A genuine finite lower bound is produced at every point outside the Cantor set. -/
lemma projectiveCantorPolePotential_finite_off (p : P1) (hp : p ∉ projectiveCantorSet) :
    ⊥ < projectiveCantorPolePotential p := by
  obtain ⟨L, hL0, hL⟩ := movingProjectiveSectionPotential_prefix_uniform_lower p hp
  exact (EReal.bot_lt_coe L).trans_le
    (le_iInf (fun N => cantorPolePartial_lower p L hL0 hL N))


lemma isThetaPshPotential_projectiveCantorPolePotential :
    IsThetaPshPotential SGPT.Toric.projectiveNativeFSBackground.form.val
      projectiveCantorPolePotential := by
  refine ⟨thetaPlurisubharmonic_projectiveCantorPolePotential, ?_⟩
  intro p O hO hp
  obtain ⟨q, hqO, hqK⟩ := dense_compl_projectiveCantorSet.inter_open_nonempty O hO ⟨p, hp⟩
  exact ⟨q, hqO, ne_of_gt (projectiveCantorPolePotential_finite_off q hqK)⟩

private lemma nonpos_sum_le_term {ι : Type*} (I : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ I, f i ≤ 0) (i : ι) (hi : i ∈ I) :
    ∑ j ∈ I, f j ≤ f i := by
  classical
  rw [← Finset.sum_erase_add I f hi]
  have h : ∑ j ∈ I.erase i, f j ≤ 0 := Finset.sum_nonpos
    (fun j hj => hf j (Finset.mem_of_mem_erase hj))
  simpa only [zero_add, add_zero, add_comm] using add_le_add_right h (f i)

lemma cantorLevelPotential_matching_upper (b : ℕ → Bool) (n : ℕ) :
    cantorLevelPotential n (projectiveCantorCode b) ≤
      ((cantorAverageWeight n * (-(16 : ℝ)^(n+1)*Real.log 2) : ℝ) : EReal) := by
  apply le_trans (nonpos_sum_le_term Finset.univ _
    (fun s _ => by
      have h := mul_le_mul_of_nonneg_left
        (movingProjectiveSectionPotential_nonpos (cantorPrefixReal s) (projectiveCantorCode b))
        (EReal.coe_nonneg.mpr (cantorAverageWeight_pos n).le)
      simpa only [mul_zero] using h)
    (fun i : Fin n => b i) (Finset.mem_univ _))
  simpa only [EReal.coe_mul] using mul_le_mul_of_nonneg_left
    (movingProjectiveSectionPotential_matching_prefix b n)
    (EReal.coe_nonneg.mpr (cantorAverageWeight_pos n).le)


lemma projectiveCantorPolePotential_matching_upper (b : ℕ → Bool) (n : ℕ) :
    projectiveCantorPolePotential (projectiveCantorCode b) ≤
      ((-8 * (4 : ℝ)^n * Real.log 2 : ℝ) : EReal) := by
  have hpartial : cantorPolePartial (n+1) (projectiveCantorCode b) ≤
      (cantorLevelWeight n : EReal) * cantorLevelPotential n (projectiveCantorCode b) := by
    exact nonpos_sum_le_term (Finset.range (n+1)) _
      (fun j _ => by
        have h := mul_le_mul_of_nonneg_left
          (cantorLevelPotential_nonpos j (projectiveCantorCode b))
          (EReal.coe_nonneg.mpr (cantorLevelWeight_pos j).le)
        simpa only [mul_zero] using h)
      n (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hlevel := mul_le_mul_of_nonneg_left (cantorLevelPotential_matching_upper b n)
    (EReal.coe_nonneg.mpr (cantorLevelWeight_pos n).le)
  have hcoeff : cantorLevelWeight n *
      (cantorAverageWeight n * (-(16 : ℝ)^(n+1)*Real.log 2)) =
      -8*(4 : ℝ)^n*Real.log 2 := by
    calc
      _ = -(cantorLevelWeight n * cantorAverageWeight n * (16 : ℝ)^(n+1)) *
          Real.log 2 := by ring
      _ = _ := by rw [cantor_matching_coefficient]; ring
  rw [← EReal.coe_mul, hcoeff] at hlevel
  exact (iInf_le (fun N => cantorPolePartial N (projectiveCantorCode b)) (n+1)).trans
    (hpartial.trans hlevel)

lemma projectiveCantorPolePotential_code_eq_bot (b : ℕ → Bool) :
    projectiveCantorPolePotential (projectiveCantorCode b) = ⊥ := by
  apply le_antisymm ?_ bot_le
  by_contra h
  have hpos : ⊥ < projectiveCantorPolePotential (projectiveCantorCode b) :=
    lt_of_not_ge h
  obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hpos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    ((-r)/(8*Real.log 2)) (by norm_num : (1 : ℝ) < 4)
  have hreal : -8*(4 : ℝ)^n*Real.log 2 < r := by
    have := (div_lt_iff₀ (by positivity : 0 < 8*Real.log 2)).mp hn
    nlinarith
  exact (not_lt_of_ge (projectiveCantorPolePotential_matching_upper b n))
    ((EReal.coe_lt_coe_iff.mpr hreal).trans hr)


/-- The exact pole locus, in both directions, of the constructed potential. -/
lemma projectiveCantorPolePotential_eq_bot_iff (p : P1) :
    projectiveCantorPolePotential p = ⊥ ↔ p ∈ projectiveCantorSet := by
  constructor
  · intro hp
    by_contra hK
    exact (ne_of_gt (projectiveCantorPolePotential_finite_off p hK)) hp
  · rintro ⟨b, rfl⟩
    exact projectiveCantorPolePotential_code_eq_bot b

/-- Polarity is proved from the actual nondegenerate global quasi-PSH witness. -/
lemma manifoldLocallyPluripolar_projectiveCantorSet :
    ManifoldLocallyPluripolar (n := 1) projectiveCantorSet := by
  have h := quasiPsh_poles_manifoldLocallyPluripolar
    isThetaPshPotential_projectiveCantorPolePotential.quasiPshPotential
  have heq : {p : P1 | projectiveCantorPolePotential p = ⊥} = projectiveCantorSet := by
    ext p
    exact projectiveCantorPolePotential_eq_bot_iff p
  rwa [heq] at h

end SGPT.BBJ
