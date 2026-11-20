import SGPT.Foundations.Analysis.Pending.FullMixedSingularIntegrationByParts
import SGPT.Foundations.Analysis.Pending.DeepCoincidenceIntegrationByParts
import SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
import SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy

set_option autoImplicit false

/-! # Actual compact weighted singular Stokes for smooth real test functions

The actual non-pluripolar telescope in Xia SGPT (4.30), PDF0171, follows
from full mixed IBP and genuine smooth-test background production. Strip
compactification and actual singular fibre slicing remain separate producers.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularSmoothTestStokes

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar GlobalDiagonalScaling
  FullMixedSingularIntegrationByParts RelativeEnergyIntegrability
  DeepCoincidenceIntegrationByParts ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- A positive actual Kähler multiple produces the genuine same-type test pair. -/
theorem exists_smooth_test_background (omega : KahlerBackground n M)
    (g : M → ℝ) (hg : ChartSmooth (n := n) g) :
    ∃ A : ℝ, 0 < A ∧ IsThetaPshPotential (A • omega.form).val (fun x => (g x : EReal)) ∧
      IsThetaPshPotential (A • omega.form).val (fun _ => 0) ∧
      SameSingularityTypeOn (fun x => (g x : EReal)) (fun _ => 0) univ := by
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (ddcClosedForm g hg)
  have hgp : ThetaPlurisubharmonic (A • omega.form).val (fun x => (g x : EReal)) := by
    apply (LocalPotentials.thetaPlurisubharmonic_smooth_iff _ g hg).mpr
    intro e z hz v
    have hh := hdom e z hz v
    simp only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply,
      ddcClosedForm_coeff] at hh
    linarith
  have hgn : IsThetaPshPotential (A • omega.form).val (fun x => (g x : EReal)) := by
    refine ⟨hgp, ?_⟩
    intro x U _ hx
    exact ⟨x, hx, EReal.coe_ne_bot _⟩
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff (A • omega.form)).mpr
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le)
  have hb := GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
    (ProductTestForms.ChartSmooth.continuous hg)
  have hz : IsBoundedPotential (fun _ : M => (0 : EReal)) := ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩
  exact ⟨A, hA, hgn, hzero, BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb hz⟩

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual hybrid product with a genuine distinguished test current. -/
def hybridUpdatedMixedMeasure {α β : ClosedRealOneOneForm n M} {a b r : M → EReal}
    (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential α.val b)
    (k : Fin n) (hr : IsThetaPshPotential β.val r) : Measure M :=
  updatedMixedMeasure (eta := fun _ => α) (psi := prefixPotentialTuple k.val a b) k
    (fun i _ => by
      dsimp only [prefixPotentialTuple]
      split_ifs
      · exact ha
      · exact hb) hr

/-- Genuine mixed one-slot IBP telescopes across every actual singular prefix. -/
theorem integral_sub_diagonal_eq_sum_hybrid (omega : KahlerBackground n M)
    {α β : ClosedRealOneOneForm n M} {a b p q : M → EReal}
    (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential α.val b)
    (hp : IsThetaPshPotential β.val p) (hq : IsThetaPshPotential β.val q)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => α) (fun _ => b) (fun _ => hb.1)) =
    ∑ k : Fin n, ((∫ x, canonicalERealDiffToReal (a x) (b x)
      ∂hybridUpdatedMixedMeasure ha hb k hp) -
      (∫ x, canonicalERealDiffToReal (a x) (b x) ∂hybridUpdatedMixedMeasure ha hb k hq)) := by
  classical
  let f : Fin (n + 1) → ℝ := fun j => ∫ x, canonicalERealDiffToReal (p x) (q x)
    ∂prefixMixedMeasure α ha.1 hb.1 j.val
  have h0 : prefixMixedMeasure α ha.1 hb.1 0 =
      globalMixedMeasure (fun _ => α) (fun _ => b) (fun _ => hb.1) := by
    apply globalMixedMeasure_congr rfl
    funext i
    simp [prefixPotentialTuple]
  have hn : prefixMixedMeasure α ha.1 hb.1 n =
      globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) := by
    apply globalMixedMeasure_congr rfl
    funext i
    simp [prefixPotentialTuple, i.isLt]
  have hstep (k : Fin n) : f k.succ - f k.castSucc =
      (∫ x, canonicalERealDiffToReal (a x) (b x) ∂hybridUpdatedMixedMeasure ha hb k hp) -
      (∫ x, canonicalERealDiffToReal (a x) (b x) ∂hybridUpdatedMixedMeasure ha hb k hq) := by
    let hother : ∀ i : Fin n, i ≠ k → IsThetaPshPotential α.val (prefixPotentialTuple k.val a b i) := by
      intro i _
      dsimp only [prefixPotentialTuple]
      split_ifs
      · exact ha
      · exact hb
    have hs := integral_sub_mixed_update_symm omega k hother ha hb hp hq hab hpq
    have hforms : Function.update (fun _ : Fin n => α) k α = fun _ => α :=
      Function.update_eq_self k _
    have hpa : Function.update (prefixPotentialTuple k.val a b) k a =
        prefixPotentialTuple (k.val + 1) a b := by
      funext i
      by_cases hi : i = k
      · subst hi
        simp [prefixPotentialTuple]
      · rw [Function.update_of_ne hi]
        have hne : i.val ≠ k.val := fun h => hi (Fin.ext h)
        have heq : i.val < k.val + 1 ↔ i.val < k.val := by omega
        simp only [prefixPotentialTuple, heq]
    have hpb : Function.update (prefixPotentialTuple k.val a b) k b =
        prefixPotentialTuple k.val a b := by
      funext i
      by_cases hi : i = k
      · subst hi
        simp [prefixPotentialTuple]
      · exact Function.update_of_ne hi _ _
    have hA : updatedMixedMeasure k hother ha = prefixMixedMeasure α ha.1 hb.1 (k.val + 1) :=
      globalMixedMeasure_congr hforms hpa _ _
    have hB : updatedMixedMeasure k hother hb = prefixMixedMeasure α ha.1 hb.1 k.val :=
      globalMixedMeasure_congr hforms hpb _ _
    rw [hA, hB] at hs
    exact hs
  calc
    _ = f (Fin.last n) - f 0 := by
      change _ = (∫ x, canonicalERealDiffToReal (p x) (q x) ∂prefixMixedMeasure α ha.1 hb.1 n) -
        (∫ x, canonicalERealDiffToReal (p x) (q x) ∂prefixMixedMeasure α ha.1 hb.1 0)
      rw [hn, h0]
    _ = ∑ k : Fin n, (f k.succ - f k.castSucc) := (sum_fin_successive_sub f).symm
    _ = _ := Finset.sum_congr rfl fun k _ => hstep k

/-- Each smooth real test has a genuinely produced regularizer giving the
actual compact NP-Stokes pairing, with no strip/fibre identity premise. -/
theorem exists_integral_smooth_test_stokes (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {W Φ : M → EReal}
    (hW : IsThetaPshPotential α.val W) (hΦ : IsThetaPshPotential α.val Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ) (g : M → ℝ) (hg : ChartSmooth (n := n) g) :
    ∃ A : ℝ, 0 < A ∧ ∃ hp : IsThetaPshPotential (A • omega.form).val (fun x => (g x : EReal)),
      ∃ hq : IsThetaPshPotential (A • omega.form).val (fun _ => 0),
      (∑ k : Fin n, ((∫ x, canonicalERealDiffToReal (W x) (Φ x)
        ∂hybridUpdatedMixedMeasure hW hΦ k hp) -
        (∫ x, canonicalERealDiffToReal (W x) (Φ x) ∂hybridUpdatedMixedMeasure hW hΦ k hq))) =
      (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => W) (fun _ => hW.1)) -
      (∫ x, g x ∂globalMixedMeasure (fun _ => α) (fun _ => Φ) (fun _ => hΦ.1)) := by
  obtain ⟨A, hA, hp, hq, htype⟩ := exists_smooth_test_background omega g hg
  refine ⟨A, hA, hp, hq, ?_⟩
  have hs := (integral_sub_diagonal_eq_sum_hybrid omega hW hΦ hp hq hWΦ htype).symm
  have hdiff (x : M) : canonicalERealDiffToReal (g x : EReal) 0 = g x := by
    simpa only [EReal.coe_zero, sub_zero] using canonicalERealDiffToReal_coe_coe (g x) 0
  simpa only [hdiff] using hs

end

end SGPT.Foundations.Analysis.Pending.SingularSmoothTestStokes
