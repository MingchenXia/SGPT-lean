import SGPT.Foundations.Analysis.Pending.GermOrderProduct
import SGPT.Foundations.Analysis.Pending.RegularDirection

set_option autoImplicit false

/-! # Actual Taylor order and growth of an entire finite holomorphic family

These are local growth producers for the logarithmic coefficient dictionary.
Every bound, least jet and regular line is produced from actual holomorphic
germs. No global generic-divisor or Siu conclusion is asserted here.
-/

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualHolomorphicFiniteJetGrowth

open FirstPass HolomorphicTaylorTail

noncomputable section

/-- An actual convergent normal-coordinate Taylor ideal expansion internally
produces the positive norm-growth bound, including the empty coordinate sum. -/
theorem exists_pos_norm_pow_bound_of_inNormalPow {n a : ℕ}
    {f : ComplexModel n → ℂ} (hf : InNormalPow 0 0 a f) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 (0 : ComplexModel n), ‖f x‖ ≤ C * ‖x‖ ^ a := by
  classical
  induction a generalizing f with
  | zero =>
    have hc := hf.self_of_nhds.continuousAt.norm
    refine ⟨‖f 0‖ + 1, by positivity, ?_⟩
    exact (hc.eventually (gt_mem_nhds (lt_add_one ‖f 0‖))).mono fun x hx => by
      simpa only [pow_zero, mul_one] using hx.le
  | succ a ih =>
    obtain ⟨H, _, hH, heq⟩ := hf
    choose C hC hbound using fun i => ih (hH i)
    have hsum : (0 : ℝ) ≤ ∑ i, C i :=
      Finset.sum_nonneg fun i _ => (hC i).le
    refine ⟨1 + ∑ i, C i, by linarith, ?_⟩
    filter_upwards [heq, Filter.eventually_all.mpr hbound] with x hx hxb
    rw [hx]
    calc
      ‖∑ i, x i * H i x‖ ≤ ∑ i, ‖x i * H i x‖ := norm_sum_le _ _
      _ ≤ ∑ i, C i * ‖x‖ ^ (a + 1) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        calc
          ‖x i‖ * ‖H i x‖ ≤ ‖x‖ * (C i * ‖x‖ ^ a) :=
            mul_le_mul (PiLp.norm_apply_le x i) (hxb i) (norm_nonneg _) (norm_nonneg _)
          _ = C i * ‖x‖ ^ (a + 1) := by rw [pow_succ]; ring
      _ = (∑ i, C i) * ‖x‖ ^ (a + 1) := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + ∑ i, C i) * ‖x‖ ^ (a + 1) := by gcongr; linarith

private theorem inNormalPow_of_low_jets {n a : ℕ} {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ x in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f x)
    (hlow : ∀ k < a, iteratedFDeriv ℂ k f 0 = 0) : InNormalPow 0 0 a f := by
  obtain ⟨U, hUf, hU, h0⟩ := _root_.eventually_nhds_iff.mp hf
  have hdiff : DifferentiableOn ℂ f U := fun x hx => (hUf x hx).differentiableWithinAt
  apply inNormalPow_of_iterDeriv_eq_zero a (by simp [complexCoordinatePlane]) hf
  apply Eventually.of_forall
  intro y hy L hL
  have hy0 : y = 0 := by
    ext i
    exact hy i (Nat.zero_le _)
  subst y
  rw [OrderMultiplicativity.iterDeriv_eq_iteratedFDeriv hU hdiff L h0, hlow _ hL]
  rfl

private theorem exists_nonzero_jet {m : ℕ} {f : ComplexModel (m + 1) → ℂ}
    (hf : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ f x)
    (hne : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), f x = 0) :
    ∃ a : ℕ, iteratedFDeriv ℂ a f 0 ≠ 0 := by
  let e : ComplexModel (m + 1) := EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℂ)
  have he : e ≠ 0 := by simp [e]
  obtain ⟨A, d, u, hu, hu0, hunit⟩ :=
    exists_regular_continuousLinearEquiv hf hne he
  let w : ComplexModel (m + 1) := A e
  have hunit' : ∀ᶠ t in 𝓝 (0 : ℂ), f (t • w) = t ^ d * u t := by
    filter_upwards [hunit] with t ht
    simpa only [map_smul, w] using ht
  obtain ⟨U, hUf, hU, h0⟩ := _root_.eventually_nhds_iff.mp hf
  have hdiff : DifferentiableOn ℂ f U := fun x hx => (hUf x hx).differentiableWithinAt
  have han : AnalyticOnNhd ℂ f U :=
    HolomorphicAnalytic.analyticOnNhd_of_differentiableOn hU hdiff
  have hφ : AnalyticAt ℂ (fun t : ℂ => f (t • w)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => t • w) 0 :=
      analyticAt_id.smul analyticAt_const
    have houter : AnalyticAt ℂ f ((0 : ℂ) • w) := by simpa using han 0 h0
    exact AnalyticAt.comp (g := f) (f := fun t : ℂ => t • w) houter hlin
  have hord : analyticOrderAt (fun t : ℂ => f (t • w)) 0 = d :=
    hφ.analyticOrderAt_eq_natCast.mpr ⟨u, hu, hu0, by
      simpa only [sub_zero, smul_eq_mul] using hunit'⟩
  have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hφ).mp hord).2
  have hline := HolomorphicAnalytic.iteratedDeriv_comp_line hU
    (han.contDiffOn hU.uniqueDiffOn) h0 w d
  simp only [zero_add] at hline
  rw [hline] at hd
  refine ⟨d, fun h => hd ?_⟩
  rw [h]
  rfl

/-- The original finite holomorphic family internally supplies its least
nonzero Taylor jet, a common positive norm-growth bound and a genuine regular
line with the matching unit factor. No order or growth certificate is an input. -/
theorem exists_finite_family_jet_growth {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) x)
    (hne : ∃ i, ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), f i x = 0) :
    ∃ (a : ℕ) (i : Fin N),
      (∀ j k, k < a → iteratedFDeriv ℂ k (f j) 0 = 0) ∧
      iteratedFDeriv ℂ a (f i) 0 ≠ 0 ∧
      ∃ C : ℝ, 0 < C ∧
        (∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), ∀ j, ‖f j x‖ ≤ C * ‖x‖ ^ a) ∧
        ∃ (w : ComplexModel (m + 1)) (h : ℂ → ℂ),
          w ≠ 0 ∧ AnalyticAt ℂ h 0 ∧ h 0 ≠ 0 ∧
          ∀ᶠ t in 𝓝 (0 : ℂ), f i (t • w) = t ^ a * h t := by
  classical
  have hex : ∃ a : ℕ, ∃ i, iteratedFDeriv ℂ a (f i) 0 ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    obtain ⟨a, ha⟩ := exists_nonzero_jet (hf i) hi
    exact ⟨a, i, ha⟩
  let a := Nat.find hex
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  change iteratedFDeriv ℂ a (f i) 0 ≠ 0 at hi
  have hlow : ∀ j k, k < a → iteratedFDeriv ℂ k (f j) 0 = 0 := by
    intro j k hk
    by_contra h
    exact Nat.find_min hex hk ⟨j, h⟩
  have hnormal : ∀ j, InNormalPow 0 0 a (f j) :=
    fun j => inNormalPow_of_low_jets (hf j) (hlow j)
  choose C hC hbound using fun j => exists_pos_norm_pow_bound_of_inNormalPow (hnormal j)
  let Csum : ℝ := 1 + ∑ j, C j
  have hCsum : 0 < Csum := by
    dsimp only [Csum]
    have : (0 : ℝ) ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
    linarith
  have hCj : ∀ j, C j ≤ Csum := by
    intro j
    have h := Finset.single_le_sum (f := C) (fun k _ => (hC k).le) (Finset.mem_univ j)
    dsimp only [Csum]
    linarith
  have hcommon : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), ∀ j, ‖f j x‖ ≤ Csum * ‖x‖ ^ a := by
    filter_upwards [Filter.eventually_all.mpr hbound] with x hx j
    exact (hx j).trans (mul_le_mul_of_nonneg_right (hCj j) (pow_nonneg (norm_nonneg _) _))
  obtain ⟨U, hUf, hU, h0⟩ := _root_.eventually_nhds_iff.mp (hf i)
  have hdiff : DifferentiableOn ℂ (f i) U := fun x hx => (hUf x hx).differentiableWithinAt
  have han : AnalyticOnNhd ℂ (f i) U :=
    HolomorphicAnalytic.analyticOnNhd_of_differentiableOn hU hdiff
  have hdiag : ∃ w : ComplexModel (m + 1), w ≠ 0 ∧
      iteratedFDeriv ℂ a (f i) 0 (fun _ => w) ≠ 0 := by
    obtain ⟨v, hv⟩ := GermOrderProduct.exists_apply_diag_ne_zero
      (fun σ q => ((han 0 h0).contDiffAt).iteratedFDeriv_comp_perm q σ) hi
    by_cases ha : a = 0
    · let w : ComplexModel (m + 1) := EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℂ)
      refine ⟨w, by simp [w], ?_⟩
      have hempty : IsEmpty (Fin a) := by
        exact ⟨fun k => by have := k.isLt; omega⟩
      have heq : (fun _ : Fin a => w) = (fun _ : Fin a => v) := by
        funext k
        exact hempty.false k |>.elim
      rw [heq]
      exact hv
    · have : Nonempty (Fin a) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero ha)
      refine ⟨v, fun h => hv ?_, hv⟩
      subst v
      exact (iteratedFDeriv ℂ a (f i) 0).map_zero
  obtain ⟨w, hw, hwd⟩ := hdiag
  have hord := GermOrderProduct.analyticOrderAt_line_eq hU han h0 (hlow i) hwd
  simp only [zero_add] at hord
  have hφ : AnalyticAt ℂ (fun t : ℂ => f i (t • w)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => t • w) 0 :=
      analyticAt_id.smul analyticAt_const
    have houter : AnalyticAt ℂ (f i) ((0 : ℂ) • w) := by simpa using han 0 h0
    exact AnalyticAt.comp (g := f i) (f := fun t : ℂ => t • w) houter hlin
  obtain ⟨h, hh, hh0, heq⟩ := hφ.analyticOrderAt_eq_natCast.mp hord
  refine ⟨a, i, hlow, hi, Csum, hCsum, hcommon, w, h, hw, hh, hh0, ?_⟩
  simpa only [sub_zero, smul_eq_mul] using heq

end

end SGPT.Foundations.Analysis.Pending.ActualHolomorphicFiniteJetGrowth
