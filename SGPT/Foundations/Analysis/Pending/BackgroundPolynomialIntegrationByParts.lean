import SGPT.Foundations.Analysis.Pending.CanonicalBackgroundPolynomial
import SGPT.Foundations.Analysis.Pending.SameTypeStrictIntegrationByParts

set_option autoImplicit false

/-!
# Arbitrary-background diagonal integration by parts

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 2. Actual Kähler domination
produces strict half-curvature inputs in all sufficiently large natural
backgrounds. Actual weighted mixed-product polynomials then recover the
original background by their constant coefficients.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.BackgroundPolynomialIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open KahlerDomination CanonicalBackgroundPolynomial MixedMassBoundedDifference
open NonPluripolarMixedCutoffs SameTypeStrictIntegrationByParts PolarizationAlgebra
open DeepCoincidenceIntegrationByParts

noncomputable section

/-- Infinitely many actual background evaluations determine the original
coefficient on the two-choice slot support. -/
theorem original_coefficient_eq_zero {n : ℕ}
    (d : (Fin n → Option (Fin n)) → ℝ) (N0 : ℕ)
    (h : ∀ N : ℕ, N0 ≤ N →
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
        (N : ℝ) ^ backgroundDegree g * d g = 0) :
    d (fun i => some i) = 0 := by
  classical
  let D : (Fin n → Option (Fin n)) → ℝ :=
    fun g => if ∀ i, g i ∈ backgroundChoices i then d g else 0
  have hpi : Fintype.piFinset (backgroundChoices (n := n)) =
      Finset.univ.filter (fun g => ∀ i, g i ∈ backgroundChoices i) := by
    ext g
    simp [Fintype.mem_piFinset]
  have hk (N : ℕ) (hN : N0 ≤ N) :
      ∑ g, (N : ℝ) ^ backgroundDegree g * D g = 0 := by
    have h' := h N hN
    rw [hpi, Finset.sum_filter] at h'
    refine (Finset.sum_congr rfl fun g _ => ?_).trans h'
    simp only [D]
    split_ifs <;> simp
  have h0 := sum_eq_zero_of_forall_nat_ge backgroundDegree D N0 hk
  exact (sum_zero_background_degree d).symm.trans h0

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual domination gives one positive natural threshold for both Kähler
positivity and a strict half-background PSH margin. -/
theorem exists_strict_background_threshold (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (theta + (N : ℝ) • omega.form).val.IsKahler ∧
      ((1 / 2 : ℝ) • (theta + (N : ℝ) • omega.form) - theta).val.IsSemipositive := by
  obtain ⟨A, -, hA⟩ := exists_pos_isSemipositive_add_smul omega theta
  obtain ⟨B, -, hB⟩ := exists_pos_isSemipositive_add_smul omega (-theta)
  let N0 : ℕ := ⌈max (A + 1) B⌉₊ + 1
  refine ⟨N0, by omega, fun N hN => ?_⟩
  have hlarge : max (A + 1) B ≤ (N : ℝ) := by
    have hceil : (⌈max (A + 1) B⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [Nat.le_ceil (max (A + 1) B)]
  have hAN : A ≤ (N : ℝ) - 1 := by linarith [le_max_left (A + 1) B]
  have hBN : B ≤ (N : ℝ) := (le_max_right (A + 1) B).trans hlarge
  have hsemi := isSemipositive_add_smul_mono omega.isSemipositive hAN hA
  have hkahler := isKahler_add_smul_succ omega hsemi
  have hhalf := isSemipositive_smul
    (isSemipositive_add_smul_mono omega.isSemipositive hBN hB)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have heq : (1 / 2 : ℝ) • (-theta + (N : ℝ) • omega.form) =
      (1 / 2 : ℝ) • (theta + (N : ℝ) • omega.form) - theta := by module
  rw [heq] at hhalf
  exact ⟨by simpa only [sub_add_cancel] using hkahler, hhalf⟩

omit [CompactSpace M] in
/-- The produced semipositive margin preserves the original genuine potential
in the strict half-background. -/
theorem isThetaPshPotential_half_background {theta eta : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hmargin : ((1 / 2 : ℝ) • eta - theta).val.IsSemipositive) :
    IsThetaPshPotential ((1 / 2 : ℝ) • eta).val u := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu hmargin
  simpa only [add_sub_cancel] using h

variable [MeasurableSpace M] [BorelSpace M]

/-- Same-type genuine pairs satisfy the actual diagonal integration by parts
identity for an arbitrary closed background. All large-background and
polynomial inputs are produced; no target identity is assumed. -/
theorem diagonal_integral_sub_eq_sum_of_sameType
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {a b p q : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => a) (fun _ => ha.1)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => theta) (fun _ => b) (fun _ => hb.1)) =
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha.1 hb.1 hp.1 (stepSelector k) k) -
       (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂binaryMixedMeasure theta ha.1 hb.1 hq.1 (stepSelector k) k)) := by
  classical
  let eta : Fin n → ClosedRealOneOneForm n M := fun _ => theta
  let sa : Fin n → M → EReal := fun _ => a
  let sb : Fin n → M → EReal := fun _ => b
  let sp (k : Fin n) := Function.update (binaryPotentialTuple (stepSelector k) a b) k p
  let sq (k : Fin n) := Function.update (binaryPotentialTuple (stepSelector k) a b) k q
  have hsa : ∀ i, IsThetaPshPotential (eta i).val (sa i) := fun _ => ha
  have hsb : ∀ i, IsThetaPshPotential (eta i).val (sb i) := fun _ => hb
  have hsp (k : Fin n) : ∀ i, IsThetaPshPotential (eta i).val (sp k i) :=
    isThetaPshPotential_binaryUpdatedTuple theta ha hb hp (stepSelector k) k
  have hsq (k : Fin n) : ∀ i, IsThetaPshPotential (eta i).val (sq k i) :=
    isThetaPshPotential_binaryUpdatedTuple theta ha hb hq (stepSelector k) k
  let I (u v : M → EReal) (s : Fin n → M → EReal)
      (hs : ∀ i, IsThetaPshPotential (eta i).val (s i))
      (g : Fin n → Option (Fin n)) : ℝ :=
    ∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun j => optForm omega eta (g j))
        (fun j => optPot s (g j)) (fun j => optPot_psh omega hs (g j))
  let d (g : Fin n → Option (Fin n)) : ℝ :=
    (I p q sa hsa g - I p q sb hsb g) -
      ∑ k : Fin n, (I a b (sp k) (hsp k) g - I a b (sq k) (hsq k) g)
  obtain ⟨N0, hN0, hthreshold⟩ := exists_strict_background_threshold omega theta
  have hpoly (N : ℕ) (hN : N0 ≤ N) :
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
        (N : ℝ) ^ backgroundDegree g * d g = 0 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hN0 hN
    obtain ⟨hkahler, hmargin⟩ := hthreshold N hN
    let omegaN : KahlerBackground n M := ⟨theta + (N : ℝ) • omega.form, hkahler⟩
    have hhalfA := isThetaPshPotential_half_background ha hmargin
    have hhalfB := isThetaPshPotential_half_background hb hmargin
    have hhalfP := isThetaPshPotential_half_background hp hmargin
    have hhalfQ := isThetaPshPotential_half_background hq hmargin
    have hactual := diagonal_integral_sub_eq_sum_of_sameType_strictCurvature omegaN
      (lam := 1 / 2) (by norm_num) (by norm_num) hhalfA hhalfB hhalfP hhalfQ hab hpq
    change
      (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure (fun i => eta i + (N : ℝ) • omega.form) sa
          (fun i => (isThetaPshPotential_add_background omega hsa hNpos.le i).1)) -
      (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure (fun i => eta i + (N : ℝ) • omega.form) sb
          (fun i => (isThetaPshPotential_add_background omega hsb hNpos.le i).1)) =
      ∑ k : Fin n,
        ((∫ x, canonicalERealDiffToReal (a x) (b x)
          ∂globalMixedMeasure (fun i => eta i + (N : ℝ) • omega.form) (sp k)
            (fun i => (isThetaPshPotential_add_background omega (hsp k) hNpos.le i).1)) -
         (∫ x, canonicalERealDiffToReal (a x) (b x)
          ∂globalMixedMeasure (fun i => eta i + (N : ℝ) • omega.form) (sq k)
            (fun i => (isThetaPshPotential_add_background omega (hsq k) hNpos.le i).1)))
      at hactual
    have hexpA := integral_canonicalDiff_add_background omega hp hq hpq hsa hNpos
    have hexpB := integral_canonicalDiff_add_background omega hp hq hpq hsb hNpos
    have hexpP (k : Fin n) :=
      integral_canonicalDiff_add_background omega ha hb hab (hsp k) hNpos
    have hexpQ (k : Fin n) :=
      integral_canonicalDiff_add_background omega ha hb hab (hsq k) hNpos
    have hright := Finset.sum_congr (s₁ := Finset.univ) rfl fun k _ =>
      congrArg₂ (fun x y : ℝ => x - y) (hexpP k) (hexpQ k)
    have hpolys := (congrArg₂ (fun x y : ℝ => x - y) hexpA hexpB).symm.trans
      (hactual.trans hright)
    change
      (∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
        (N : ℝ) ^ backgroundDegree g * I p q sa hsa g) -
      (∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
        (N : ℝ) ^ backgroundDegree g * I p q sb hsb g) =
      ∑ k : Fin n,
        ((∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
          (N : ℝ) ^ backgroundDegree g * I a b (sp k) (hsp k) g) -
         (∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
          (N : ℝ) ^ backgroundDegree g * I a b (sq k) (hsq k) g)) at hpolys
    simp only [d, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    conv_lhs => rhs; rhs; rw [Finset.sum_comm]
    exact sub_eq_zero.mpr (by simpa only [Finset.sum_sub_distrib] using hpolys)
  have h0 := original_coefficient_eq_zero d N0 hpoly
  change
    ((∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure eta sa (fun i => (hsa i).1)) -
     (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂globalMixedMeasure eta sb (fun i => (hsb i).1))) -
    ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂globalMixedMeasure eta (sp k) (fun i => (hsp k i).1)) -
       (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂globalMixedMeasure eta (sq k) (fun i => (hsq k i).1))) = 0 at h0
  exact sub_eq_zero.mp h0

end

end SGPT.Foundations.Analysis.Pending.BackgroundPolynomialIntegrationByParts
