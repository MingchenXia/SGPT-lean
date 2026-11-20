import SGPT.Foundations.Analysis.Pending.ActualDivisorialLogarithmicResidual
import SGPT.Foundations.Analysis.Pending.PshLelongUpperSemicontinuity
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.SNCHolomorphicLogNormalForm
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.Pending.PshConvexCone

set_option autoImplicit false

/-! # Actual simultaneous SNC logarithmic removal

The exact original plane thresholds internally produce all intermediate
PSH residuals and intersection bounds. True PSH AE uniqueness restores every
pole. No mass, residual, compatibility or limiting certificate is assumed.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.ActualSNCLogarithmicResidual

open FirstPass FirstPass.NonKahlerLocus LelongNumberComparison

noncomputable section

private theorem lelong_linear_equiv {n : ℕ}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) (u : ComplexModel n → EReal)
    (z : ComplexModel n) :
    lelongNumber (n := n) (fun w => u (L w)) z = lelongNumber (n := n) u (L z) := by
  let Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := L.symm
    invFun := L
    toFun_holomorphic := L.symm.differentiable.differentiableOn
    invFun_holomorphic := L.differentiable.differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun w _ => L.apply_symm_apply w
    right_inv := fun w _ => L.symm_apply_apply w }
  have h := LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq
    Φ (x := L z) (mem_univ _) (u := u)
  simpa only [Φ, L.symm_apply_apply] using h

private theorem remove_coordinate {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    {Ω : Set (ComplexModel (m + 1))} (hu : PlurisubharmonicOn u Ω)
    (j : Fin (m + 1)) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall 0 (2 * r) ⊆ Ω) {K : ℝ}
    (hK : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (2 * r), u z ≤ (K : EReal))
    {a : ℝ≥0} (hν : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z j = 0 →
      (a : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u z) :
    ∃ q : ComplexModel (m + 1) → EReal,
      PlurisubharmonicOn q (ball 0 r) ∧
      (∀ z ∈ ball 0 r, q z ≤ ((K - (a : ℝ) * Real.log r : ℝ) : EReal)) ∧
      ∀ z ∈ ball 0 r, z j ≠ 0 →
        q z = u z + ((-(a : ℝ) * Real.log ‖z j‖ : ℝ) : EReal) := by
  classical
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let T : ComplexModel (m + 1) ≃ₗᵢ[ℂ] ComplexModel (m + 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let L := T.toContinuousLinearEquiv
  have hj (z : ComplexModel (m + 1)) : (L z) j = z (Fin.last m) := by
    change z (e.symm j) = z (Fin.last m)
    simp [e]
  have hl (z : ComplexModel (m + 1)) : (L.symm z) (Fin.last m) = z j := by
    have h := hj (L.symm z)
    rw [L.apply_symm_apply] at h
    exact h.symm
  have hball (z : ComplexModel (m + 1)) (s : ℝ) :
      L z ∈ ball (0 : ComplexModel (m + 1)) s ↔ z ∈ ball 0 s := by
    simp only [mem_ball_zero_iff]
    change ‖T z‖ < s ↔ ‖z‖ < s
    rw [T.norm_map]
  have hclosed (z : ComplexModel (m + 1)) (s : ℝ) :
      L z ∈ closedBall (0 : ComplexModel (m + 1)) s ↔ z ∈ closedBall 0 s := by
    simp only [mem_closedBall_zero_iff]
    change ‖T z‖ ≤ s ↔ ‖z‖ ≤ s
    rw [T.norm_map]
  have hback (z : ComplexModel (m + 1)) (s : ℝ) :
      L.symm z ∈ ball (0 : ComplexModel (m + 1)) s ↔ z ∈ ball 0 s := by
    simpa only [L.apply_symm_apply] using (hball (L.symm z) s).symm
  have hup := hu.comp_continuousLinearMap L.toContinuousLinearMap
  have hν' : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z (Fin.last m) = 0 →
      (a : ℝ≥0∞) ≤ lelongNumber (n := m + 1) (fun w => u (L w)) z := by
    intro z hz hz0
    rw [lelong_linear_equiv L u z]
    exact hν (L z) ((hball z r).mpr hz) (by rw [hj, hz0])
  obtain ⟨hq, hqb, hqe⟩ :=
    ActualDivisorialLogarithmicResidual.coordinate_residual_psh_of_le_lelongNumber
      hup (by simp : (0 : ComplexModel (m + 1)) (Fin.last m) = 0) hr
      (fun z hz => hΩ ((hclosed z (2 * r)).mpr hz))
      (fun z hz => hK (L z) ((hclosed z (2 * r)).mpr hz)) hν'
  let Q := PshCodimTwoExtension.extension {z : ComplexModel (m + 1) | z (Fin.last m) = 0}
    (fun z => u (L z) + ((-(a : ℝ) / 2 *
      Real.log (Complex.normSq (z (Fin.last m))) : ℝ) : EReal))
  change PlurisubharmonicOn Q (ball 0 r) at hq
  refine ⟨fun z => Q (L.symm z),
    (hq.comp_continuousLinearMap L.symm.toContinuousLinearMap).mono
      (fun z hz => (hback z r).mpr hz), ?_, ?_⟩
  · intro z hz
    exact hqb (L.symm z) ((hback z r).mpr hz)
  · intro z hz hz0
    have hzlast : (L.symm z) (Fin.last m) ≠ 0 := by rwa [hl]
    have he := hqe ⟨(hback z r).mpr hz, hzlast⟩
    change Q (L.symm z) = u (L (L.symm z)) +
      ((-(a : ℝ) / 2 * Real.log (Complex.normSq ((L.symm z) (Fin.last m))) : ℝ) : EReal) at he
    rw [L.apply_symm_apply, hl] at he
    change Q (L.symm z) = u z + ((-(a : ℝ) * Real.log ‖z j‖ : ℝ) : EReal)
    rw [he]
    congr 2
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring

private theorem correction_continuous {n : ℕ} (s : Finset (Fin n)) (a : Fin n → ℝ≥0)
    {x : ComplexModel n} (hx : ∀ i ∈ s, x i ≠ 0) :
    ContinuousAt (fun z : ComplexModel n => -(∑ i ∈ s, (a i : ℝ) * Real.log ‖z i‖)) x := by
  apply ContinuousAt.neg
  exact tendsto_finsetSum s fun i hi =>
    continuousAt_const.mul
      (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt).norm.log
        (norm_ne_zero_iff.mpr (hx i hi)))

private theorem remaining_threshold {n : ℕ} {u q : ComplexModel n → EReal}
    {R r : ℝ} (hrR : r ≤ R) (s : Finset (Fin n)) (a : Fin n → ℝ≥0)
    (hq : PlurisubharmonicOn q (ball 0 r))
    (heq : ∀ z ∈ ball (0 : ComplexModel n) r, (∀ i ∈ s, z i ≠ 0) →
      q z = u z + ((-(∑ i ∈ s, (a i : ℝ) * Real.log ‖z i‖) : ℝ) : EReal))
    (hν : ∀ j z, z ∈ ball (0 : ComplexModel n) R → z j = 0 →
      (a j : ℝ≥0∞) ≤ lelongNumber (n := n) u z)
    {j : Fin n} (hj : j ∉ s) {x : ComplexModel n}
    (hx : x ∈ ball (0 : ComplexModel n) r) (hxj : x j = 0) :
    (a j : ℝ≥0∞) ≤ lelongNumber (n := n) q x := by
  classical
  have hoff (y : ComplexModel n) (hy : y ∈ ball (0 : ComplexModel n) r)
      (hyj : y j = 0) (hys : ∀ i ∈ s, y i ≠ 0) :
      (a j : ℝ≥0∞) ≤ lelongNumber (n := n) q y := by
    have hcoords : ∀ᶠ z in 𝓝 y, ∀ i ∈ s, z i ≠ 0 := by
      apply (eventually_all_finset s).mpr
      intro i hi
      exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.eventually_ne (hys i hi)
    have hgerm : q =ᶠ[𝓝 y] fun z => u z +
        ((-(∑ i ∈ s, (a i : ℝ) * Real.log ‖z i‖) : ℝ) : EReal) := by
      filter_upwards [isOpen_ball.mem_nhds hy, hcoords] with z hz hzs
      exact heq z hz hzs
    rw [lelongNumber_congr hgerm,
      LelongChartReaderInvariance.lelongNumber_add_continuous_eq (correction_continuous s a hys)]
    exact hν j y (ball_subset_ball hrR hy) hyj
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have hnear : ∀ᶠ y in 𝓝 x, lelongNumber (n := n) q y < (a j : ℝ≥0∞) := by
    have h := PshLelongUpperSemicontinuity.eventually_lelongNumber_lt_of_lt hq isOpen_ball hx
      (a := (a j : ℝ)) (by simpa only [ENNReal.ofReal_coe_nnreal] using hlt)
    simpa only [ENNReal.ofReal_coe_nnreal] using h
  let v : ComplexModel n := WithLp.toLp 2 (fun i => if i = j then 0 else (1 : ℂ))
  let f : ℂ → ComplexModel n := fun t => x + t • v
  have hfj (t : ℂ) : f t j = 0 := by simp [f, v, hxj]
  have hfi (t : ℂ) (i : Fin n) (hi : i ∈ s) : f t i = x i + t := by
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [f, v, hij]
  have hf : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 x) := by
    have hc : ContinuousAt f 0 := by fun_prop
    simpa only [f, zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ i ∈ s, f t i ≠ 0 := by
    apply (eventually_all_finset s).mpr
    intro i hi
    by_cases hxi : x i = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [hfi t i hi, hxi, zero_add, mem_compl_iff, mem_singleton_iff] using ht
    · have hcont : ContinuousAt (fun t : ℂ => x i + t) 0 := by fun_prop
      have he := hcont.eventually_ne (by simpa using hxi)
      exact (he.filter_mono nhdsWithin_le_nhds).mono fun t ht => by
        simpa only [hfi t i hi] using ht
  obtain ⟨t, ht, htball, htcoords⟩ :=
    ((hf.eventually hnear).and ((hf.eventually (isOpen_ball.mem_nhds hx)).and hevent)).exists
  exact not_lt_of_ge (hoff (f t) htball (hfj t) htcoords) ht

private theorem exists_partial_residual {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    {Ω : Set (ComplexModel (m + 1))} (hu : PlurisubharmonicOn u Ω)
    {R : ℝ} (hR : 0 < R) (hΩ : closedBall 0 (2 * R) ⊆ Ω)
    {K : ℝ} (hK : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (2 * R), u z ≤ (K : EReal))
    (a : Fin (m + 1) → ℝ≥0)
    (hν : ∀ j z, z ∈ ball (0 : ComplexModel (m + 1)) R → z j = 0 →
      (a j : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u z)
    (s : Finset (Fin (m + 1))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ C : ℝ, ∃ q : ComplexModel (m + 1) → EReal,
      PlurisubharmonicOn q (ball 0 r) ∧ (∀ z ∈ ball 0 r, q z ≤ (C : EReal)) ∧
      ∀ z ∈ ball 0 r, (∀ i ∈ s, z i ≠ 0) →
        q z = u z + ((-(∑ i ∈ s, (a i : ℝ) * Real.log ‖z i‖) : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨R, hR, le_rfl, K, u, hu.mono ?_, ?_, ?_⟩
      · exact ((ball_subset_ball (by linarith : R ≤ 2 * R)).trans ball_subset_closedBall).trans hΩ
      · intro z hz
        exact hK z (ball_subset_closedBall (ball_subset_ball (by linarith : R ≤ 2 * R) hz))
      · intro z _ _
        simp
  | @insert j s hj ih =>
      obtain ⟨r, hr, hrR, C, q, hq, hqb, hqe⟩ := ih
      let t : ℝ := r / 4
      have ht : 0 < t := by dsimp [t]; positivity
      have htr : t ≤ r := by dsimp [t]; linarith
      have hsub : closedBall (0 : ComplexModel (m + 1)) (2 * t) ⊆ ball 0 r := by
        exact closedBall_subset_ball (by dsimp [t]; linarith)
      obtain ⟨q', hq', hq'b, hq'e⟩ := remove_coordinate hq j ht hsub
        (fun z hz => hqb z (hsub hz))
        (fun z hz hzj => remaining_threshold hrR s a hq hqe hν hj
          (ball_subset_ball htr hz) hzj)
      refine ⟨t, ht, htr.trans hrR, C - (a j : ℝ) * Real.log t, q', hq', hq'b, ?_⟩
      intro z hz hzs
      have hzj : z j ≠ 0 := hzs j (Finset.mem_insert_self j s)
      have hzS : ∀ i ∈ s, z i ≠ 0 := fun i hi => hzs i (Finset.mem_insert_of_mem hi)
      rw [hq'e z hz hzj, hqe z (ball_subset_ball htr hz) hzS, add_assoc, ← EReal.coe_add]
      congr 2
      rw [Finset.sum_insert hj]
      ring

private theorem logarithmic_sum_psh {n : ℕ} (a : Fin n → ℝ≥0) (s : Finset (Fin n)) :
    PlurisubharmonicOn (fun z : ComplexModel n =>
      ∑ i ∈ s, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) univ := by
  classical
  have hterm (i : Fin n) : PlurisubharmonicOn (fun z : ComplexModel n =>
      (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) univ := by
    by_cases hi : a i = 0
    · simp only [hi, NNReal.coe_zero, zero_div, EReal.coe_zero, zero_mul]
      exact fun z _ => plurisubharmonicAt_const 0 (by simp) z
    have hpos : 0 < (a i : ℝ) / 2 := by
      have : 0 < (a i : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hi)
      positivity
    have hlog : PlurisubharmonicOn (fun z : ComplexModel n => logNormSq (z i)) univ := by
      exact (show PlurisubharmonicOn (logNormSq (E := ℂ)) univ from
        fun z _ => plurisubharmonicAt_logNormSq z).comp_continuousLinearMap
          (EuclideanSpace.proj (𝕜 := ℂ) i)
    exact hlog.const_mul hpos
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact fun z _ => plurisubharmonicAt_const 0 (by simp) z
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hterm i).add ih

private theorem coe_sum {n : ℕ} (f : Fin n → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) :=
  map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ

/-- All SNC factors are removed internally at their exact original plane
thresholds. AE uniqueness restores the complete identity at every pole. -/
theorem exists_simultaneous_residual {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    {Ω : Set (ComplexModel (m + 1))} (hu : PlurisubharmonicOn u Ω)
    {R : ℝ} (hR : 0 < R) (hΩ : closedBall 0 (2 * R) ⊆ Ω)
    {K : ℝ} (hK : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (2 * R), u z ≤ (K : EReal))
    (a : Fin (m + 1) → ℝ≥0)
    (hν : ∀ j z, z ∈ ball (0 : ComplexModel (m + 1)) R → z j = 0 →
      (a j : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u z) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ C : ℝ, ∃ q : ComplexModel (m + 1) → EReal,
      PlurisubharmonicOn q (ball 0 r) ∧ (∀ z ∈ ball 0 r, q z ≤ (C : EReal)) ∧
      (∀ z ∈ ball 0 r, u z =
        (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) + q z) ∧
      ∀ z ∈ ball 0 r, u z ≤
        (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) + (C : EReal) := by
  classical
  obtain ⟨r, hr, hrR, C, q, hq, hqb, hqe⟩ :=
    exists_partial_residual hu hR hΩ hK a hν Finset.univ
  have hus : PlurisubharmonicOn u (ball 0 r) := hu.mono
    (((ball_subset_ball (by linarith : r ≤ 2 * R)).trans ball_subset_closedBall).trans hΩ)
  have hsum := logarithmic_sum_psh a Finset.univ
  have hfull := (hsum.mono (subset_univ (ball (0 : ComplexModel (m + 1)) r))).add hq
  have hae : u =ᵐ[volume.restrict (ball (0 : ComplexModel (m + 1)) r)]
      (fun z => (∑ i, (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i)) + q z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (SNCHolomorphicLogNormalForm.ae_coordinates_ne_zero (m + 1))]
      with z hz hzc
    have he := hqe z hz (fun i _ => hzc i)
    have hlog (i : Fin (m + 1)) :
        (((a i : ℝ) / 2 : ℝ) : EReal) * logNormSq (z i) =
          (((a i : ℝ) * Real.log ‖z i‖ : ℝ) : EReal) := by
      rw [logNormSq_of_ne_zero (hzc i), Real.log_pow, ← EReal.coe_mul]
      congr 1
      ring
    simp_rw [hlog]
    rw [← coe_sum, he, add_comm (u z), ← add_assoc, ← EReal.coe_add,
      add_neg_cancel, EReal.coe_zero, zero_add]
  have hevery := hus.eqOn_of_ae_eq hfull isOpen_ball volume hae
  refine ⟨r, hr, hrR, C, q, hq, hqb, hevery, ?_⟩
  intro z hz
  rw [hevery hz]
  exact add_le_add le_rfl (hqb z hz)

end
end SGPT.Foundations.Analysis.Pending.ActualSNCLogarithmicResidual
