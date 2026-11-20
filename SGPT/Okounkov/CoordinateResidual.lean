import SGPT.Foundations.Analysis.Pending.ActualSNCLogarithmicResidual
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Okounkov.LocalLelongAdditivity

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Metric
open scoped Topology ENNReal NNReal Manifold
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

/-- The source divisorial coefficient uses the squared coordinate logarithm.
The genuine native threshold is twice that coefficient. -/
theorem exists_coordinate_divisorial_residual {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} {Ω : Set (ComplexModel (m + 1))}
    (hu : PlurisubharmonicOn u Ω) {R : ℝ} (hR : 0 < R)
    (hΩ : closedBall 0 (2 * R) ⊆ Ω) {K : ℝ}
    (hK : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (2 * R), u z ≤ (K : EReal))
    (j : Fin (m + 1)) (c : ℝ≥0)
    (hν : ∀ z ∈ ball (0 : ComplexModel (m + 1)) R, z j = 0 →
      (2 * (c : ℝ≥0∞)) ≤ lelongNumber (n := m + 1) u z) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ C : ℝ, ∃ q : ComplexModel (m + 1) → EReal,
      PlurisubharmonicOn q (ball 0 r) ∧ (∀ z ∈ ball 0 r, q z ≤ (C : EReal)) ∧
      ∀ z ∈ ball 0 r, u z = ((c : ℝ) : EReal) * logNormSq (z j) + q z := by
  classical
  let a : Fin (m + 1) → ℝ≥0 := Pi.single j (2 * c)
  have ha : ∀ l z, z ∈ ball (0 : ComplexModel (m + 1)) R → z l = 0 →
      (a l : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u z := by
    intro l z hz hzl
    by_cases hl : l = j
    · subst l
      simpa [a] using hν z hz hzl
    · simp [a, hl]
  obtain ⟨r, hr, hrR, C, q, hq, hqb, hqe, _⟩ :=
    ActualSNCLogarithmicResidual.exists_simultaneous_residual hu hR hΩ hK a ha
  refine ⟨r, hr, hrR, C, q, hq, hqb, ?_⟩
  intro z hz
  rw [hqe z hz]
  congr 1
  rw [Finset.sum_eq_single j]
  · congr 1
    simp [a]
  · intro l _ hl
    simp [a, hl]
  · simp

/-- The genuine source logarithmic factor has the actual native point reader.
This transports main's coordinate logarithm normalization and positive scaling. -/
theorem lelongNumber_scaled_logNormSq_eq {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) {c : ℝ≥0} (hc : 0 < c) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => ((c : ℝ) : EReal) * logNormSq (z j)) x =
      2 * (c : ℝ≥0∞) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hfun : (fun z : ComplexModel n => ((c : ℝ) : EReal) * logNormSq (z j)) =
      (fun z => ((2 * (c : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) := by
    funext z
    rw [logNormSq, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.log_pow,
      ← mul_assoc]
    change (((c : ℝ) : EReal) * ((2 : ℝ) : EReal)) * _ = _
    rw [← EReal.coe_mul, mul_comm (c : ℝ) 2]
  rw [hfun, ActualLelongPositiveScaling.lelongNumber_smul_eq (by positivity),
    LocalHolomorphicLelongReaderCovariance.lelongNumber_coordinate_log_eq_one_of_eq_zero j hx,
    mul_one, ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- At an actual attained original divisor coefficient, the genuinely produced
local residual has zero native point reader.  No residual-zero certificate is
an input; the original finite coefficient cancels in actual local additivity. -/
theorem lelongNumber_coordinate_residual_eq_zero {n : ℕ}
    {Ω : TopologicalSpace.Opens (ComplexModel n)} {u q : ComplexModel n → EReal}
    (hq : PlurisubharmonicOn q Ω) (j : Fin n) (c : ℝ≥0)
    (heq : EqOn u (fun z => ((c : ℝ) : EReal) * logNormSq (z j) + q z) Ω)
    (x : Ω) (hx : (x : ComplexModel n) j = 0)
    (hν : lelongNumber (n := n) u x = 2 * (c : ℝ≥0∞)) :
    lelongNumber (n := n) q x = 0 := by
  have hgerm : u =ᶠ[𝓝 (x : ComplexModel n)]
      (fun z => ((c : ℝ) : EReal) * logNormSq (z j) + q z) := by
    filter_upwards [Ω.isOpen.mem_nhds x.property] with z hz
    exact heq hz
  by_cases hc : c = 0
  · subst c
    simpa using (LelongNumberComparison.lelongNumber_congr hgerm).symm.trans hν
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hcpos
  have hlog : PlurisubharmonicOn
      (fun z : ComplexModel n => ((c : ℝ) : EReal) * logNormSq (z j)) Ω := by
    have hp : PlurisubharmonicOn (fun z : ComplexModel n => logNormSq (z j)) Set.univ :=
      (show PlurisubharmonicOn (logNormSq (E := ℂ)) Set.univ from
        fun z _ => plurisubharmonicAt_logNormSq z).comp_continuousLinearMap
          (EuclideanSpace.proj (𝕜 := ℂ) j)
    exact (hp.const_mul hcR).mono (subset_univ (Ω : Set (ComplexModel n)))
  have hsum : 2 * (c : ℝ≥0∞) =
      2 * (c : ℝ≥0∞) + lelongNumber (n := n) q x := by
    calc
      _ = lelongNumber (n := n) u x := hν.symm
      _ = lelongNumber (n := n)
          (fun z => ((c : ℝ) : EReal) * logNormSq (z j) + q z) x :=
        LelongNumberComparison.lelongNumber_congr hgerm
      _ = lelongNumber (n := n)
          (fun z : ComplexModel n => ((c : ℝ) : EReal) * logNormSq (z j))
            (x : ComplexModel n) +
          lelongNumber (n := n) q x :=
        lelongNumber_add_eq_on_opens (fun z hz => (hlog z hz).quasiPlurisubharmonicAt)
          (fun z hz => (hq z hz).quasiPlurisubharmonicAt) x
      _ = _ := by rw [lelongNumber_scaled_logNormSq_eq j hx hcpos]
  apply (ENNReal.add_right_inj (a := 2 * (c : ℝ≥0∞))
    (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)).mp
  simpa using hsum.symm

end SGPT.Okounkov
