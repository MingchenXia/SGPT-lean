import SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
import SGPT.Foundations.Analysis.Pending.DiagonalMassComparison
import SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false

/-!
# Actual weak convergence of increasing diagonal products

A pointwise increasing sequence with a bounded gap from its genuine limit
has actual open-set semicontinuity and constant finite total mass. Normalize
by that mass and apply portmanteau to produce native finite-measure weak
convergence. The final consumers are the actual max approximations in
Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingDiagonalWeakConvergence

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open IncreasingLimitOpenMeasure DiagonalMassComparison NonPluripolarPoleCoalescing

noncomputable section

/-- Equal finite total masses and open-set semicontinuity produce native weak
convergence, including a zero common mass and an empty space. -/
theorem finiteMeasure_tendsto_of_mass_eq_of_isOpen_le_liminf
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {mu : ℕ → FiniteMeasure X} {nu : FiniteMeasure X}
    (hmass : ∀ j, (mu j).mass = nu.mass)
    (hopen : ∀ G : Set X, IsOpen G →
      (nu : Measure X) G ≤ liminf (fun j => (mu j : Measure X) G) atTop) :
    Tendsto mu atTop (𝓝 nu) := by
  by_cases hnu : nu = 0
  · subst nu
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa only [hmass, FiniteMeasure.zero_mass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0)) atTop (𝓝 0))
  rcases isEmpty_or_nonempty X with hX | hX
  · exact (hnu (Subtype.ext (Subsingleton.elim _ _))).elim
  have hmu : ∀ j, mu j ≠ 0 := fun j =>
    (FiniteMeasure.mass_nonzero_iff _).mp (hmass j ▸ (FiniteMeasure.mass_nonzero_iff _).mpr hnu)
  have hnorm : Tendsto (fun j => (mu j).normalize) atTop (𝓝 nu.normalize) := by
    apply tendsto_of_forall_isOpen_le_liminf_nat'
    intro G hG
    rw [nu.toMeasure_normalize_eq_of_nonzero hnu, Measure.coe_nnreal_smul_apply]
    have hscaled := mul_le_mul_of_nonneg_left (hopen G hG)
      (show (0 : ℝ≥0∞) ≤ (nu.mass⁻¹ : ℝ≥0) from zero_le)
    have hproduct := ENNReal.le_liminf_mul
      (u := fun _ : ℕ => ((nu.mass⁻¹ : ℝ≥0) : ℝ≥0∞))
      (v := fun j => (mu j : Measure X) G) (f := atTop)
    simp only [liminf_const] at hproduct
    refine (hscaled.trans hproduct).trans_eq ?_
    apply congrArg (fun a : ℕ → ℝ≥0∞ => liminf a atTop)
    funext j
    rw [(mu j).toMeasure_normalize_eq_of_nonzero (hmu j),
      Measure.coe_nnreal_smul_apply, hmass j]
    rfl
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hnorm
    (by simpa only [hmass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => nu.mass) atTop (𝓝 nu.mass)))

/-- The regularized supremum is the given genuine pointwise limit. -/
theorem uscRegularization_iSup_eq_of_monotone_tendsto
    {X : Type*} [TopologicalSpace X] {u : ℕ → X → EReal} {v : X → EReal}
    (hmono : Monotone u) (hv : UpperSemicontinuous v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x))) :
    uscRegularization (⨆ j, u j) = v := by
  have hsup : (⨆ j, u j) = v := by
    funext x
    simp only [iSup_apply]
    exact iSup_eq_of_tendsto (fun _ _ hij => hmono hij x) (hlim x)
  rw [hsup, uscRegularization_eq hv]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual diagonal product, with its Kähler finite-mass proof. -/
def finiteDiagonalMeasure (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential theta.val u) : FiniteMeasure M :=
  ⟨diagonalPotentialMeasure theta u hu,
    globalMixedMeasure_isFiniteMeasure omega (fun _ => hu.1)⟩

/-- Actual increasing open-set semicontinuity and actual equal masses yield
weak convergence of the actual diagonal products. -/
theorem weakTendsto_diagonal_of_monotone_of_mass_eq
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hmono : Monotone u) {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (hmass : ∀ j, diagonalPotentialMeasure theta (u j) (hu j) univ =
      diagonalPotentialMeasure theta v hv univ) :
    Tendsto (fun j => finiteDiagonalMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteDiagonalMeasure omega theta v hv)) := by
  have heq := uscRegularization_iSup_eq_of_monotone_tendsto hmono
    hv.1.quasiPlurisubharmonic.upperSemicontinuous hlim
  apply finiteMeasure_tendsto_of_mass_eq_of_isOpen_le_liminf
  · intro j
    exact congrArg ENNReal.toNNReal (hmass j)
  · intro G hG
    have hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j)) := heq ▸ hv
    have h := diagonalPotentialMeasure_isOpen_le_liminf u hu hmono hU hG
    change diagonalPotentialMeasure theta v hv G ≤
      liminf (fun j => diagonalPotentialMeasure theta (u j) (hu j) G) atTop
    simpa only [heq] using h

/-- Bounded-difference mass invariance produces the equal masses; no weak
convergence or total-mass conclusion is assumed. -/
theorem weakTendsto_diagonal_of_monotone_of_boundedGap
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : 0 ≤ B) (hgap : ∀ j x, v x ≤ u j x + (B : EReal)) :
    Tendsto (fun j => finiteDiagonalMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteDiagonalMeasure omega theta v hv)) := by
  apply weakTendsto_diagonal_of_monotone_of_mass_eq omega hu hmono hv hlim
  intro j
  apply diagonal_univ_eq_of_le_add omega hsemi (hu j).1 hv.1 hB
  · intro x
    have hsup := iSup_eq_of_tendsto (fun _ _ hij => hmono hij x) (hlim x)
    exact hsup ▸ le_iSup (fun k => u k x) j
  · exact hgap j

/-- Ordinary continuous-test convergence follows for every continuous test. -/
theorem tendsto_integral_diagonal_of_monotone_of_boundedGap
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {u : ℕ → M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : 0 ≤ B) (hgap : ∀ j x, v x ≤ u j x + (B : EReal))
    (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂(diagonalPotentialMeasure theta (u j) (hu j))) atTop
      (𝓝 (∫ x, chi x ∂(diagonalPotentialMeasure theta v hv))) :=
  (FiniteMeasure.continuous_integral_continuousMap chi).tendsto
    (finiteDiagonalMeasure omega theta v hv) |>.comp
      (weakTendsto_diagonal_of_monotone_of_boundedGap omega hsemi hu hmono hv hlim hB hgap)

/-- The actual positive-parameter maxima converge weakly; their natural
regularity is the sole approximation regularity input. -/
theorem weakTendsto_poleCoalescingApprox
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hsemi : theta.val.IsSemipositive) {a b : M → EReal}
    (hb : IsThetaPshPotential theta.val b) {eps : ℕ → ℝ}
    (hpos : ∀ j, 0 < eps j) (hanti : Antitone eps)
    (hlim : Tendsto eps atTop (𝓝 0))
    (happrox : ∀ j, IsThetaPshPotential theta.val (poleCoalescingApprox (eps j) a b))
    (hab : a ≤ b) (hb0 : b ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) :
    Tendsto (fun j => finiteDiagonalMeasure omega theta
      (poleCoalescingApprox (eps j) a b) (happrox j)) atTop
      (𝓝 (finiteDiagonalMeasure omega theta b hb)) := by
  apply weakTendsto_diagonal_of_monotone_of_boundedGap omega hsemi happrox
    (fun i j hij => poleCoalescingApprox_antitone hb0 (hpos j) (hpos i) (hanti hij)) hb
    (tendsto_poleCoalescingApprox hpos hlim hab hb0) hB
  intro j x
  exact (hba x).trans (add_le_add (le_max_left _ _) le_rfl)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual strict sequence is genuine for the original Kähler form. -/
theorem isThetaPshPotential_poleCoalescingSequence_kahler
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b) (j : ℕ) :
    IsThetaPshPotential omega.form.val
      (poleCoalescingApprox (strictKahlerParameter lam j) a b) := by
  simpa only [one_smul] using isThetaPshPotential_smul_kahler_mono omega
    (show (1 + lam) / 2 ≤ 1 by linarith)
    (isThetaPshPotential_poleCoalescingSequence omega hlam hlam1 ha hb j)

/-- The explicit strict Kähler schedule produces actual ordinary diagonal
weak convergence, with all approximation regularity produced. -/
theorem weakTendsto_poleCoalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hab : a ≤ b) (hb0 : b ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) :
    Tendsto (fun j => finiteDiagonalMeasure omega omega.form
      (poleCoalescingApprox (strictKahlerParameter lam j) a b)
      (isThetaPshPotential_poleCoalescingSequence_kahler omega hlam hlam1 ha hb j))
      atTop (𝓝 (finiteDiagonalMeasure omega omega.form b
        (by
          simpa only [one_smul] using
            isThetaPshPotential_smul_kahler_mono omega hlam1.le hb))) := by
  obtain ⟨hpos, hanti, hlim, hscaled⟩ := strictKahlerParameter_spec hlam hlam1
  exact weakTendsto_poleCoalescingApprox omega omega.isSemipositive
    (by simpa only [one_smul] using isThetaPshPotential_smul_kahler_mono omega hlam1.le hb)
    hpos hanti hlim (isThetaPshPotential_poleCoalescingSequence_kahler omega hlam hlam1 ha hb)
    hab hb0 hB hba

/-- Continuous test integrals along the actual strict schedule converge. -/
theorem tendsto_integral_poleCoalescingSequence
    (omega : KahlerBackground n M) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    {a b : M → EReal}
    (ha : IsThetaPshPotential (lam • omega.form).val a)
    (hb : IsThetaPshPotential (lam • omega.form).val b)
    (hab : a ≤ b) (hb0 : b ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂(diagonalPotentialMeasure omega.form
      (poleCoalescingApprox (strictKahlerParameter lam j) a b)
      (isThetaPshPotential_poleCoalescingSequence_kahler omega hlam hlam1 ha hb j)))
      atTop (𝓝 (∫ x, chi x ∂(diagonalPotentialMeasure omega.form b
        (by
          simpa only [one_smul] using
            isThetaPshPotential_smul_kahler_mono omega hlam1.le hb)))) :=
  (FiniteMeasure.continuous_integral_continuousMap chi).tendsto _ |>.comp
    (weakTendsto_poleCoalescingSequence omega hlam hlam1 ha hb hab hb0 hB hba)

end

end SGPT.Foundations.Analysis.Pending.IncreasingDiagonalWeakConvergence
