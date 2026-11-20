import SGPT.PSH.HermitianExtremalRadialRegularization
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacitySublevel

/-!
# Uniform ordinary capacity of the actual smooth compact sublevels

The original PSH function lies below its radial convolutions, so the
compact sublevel at level `N+2` is contained in an original strict sublevel
at level `N+1`. The proved weighted CLN theorem for that original function
therefore supplies one `C/(N+1)` bound, independent of the regularization.
No uniform-L1 assertion about a chosen smooth approximation is assumed.

This is the ordinary local-capacity side of FPT Step 3; comparison with
the actual nonclosed Hermitian product is a separate geometric step.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology

variable {n : ℕ}

/-- A one-unit threshold shift turns the closed sublevel of a majorant
into an original strict sublevel, retaining original poles. -/
theorem compactSublevel_subset_original_strict_sublevel
    {K : Set (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {ψ : ComplexModel n → EReal} (hlower : ∀ j z, z ∈ K → ψ z ≤ (f j z : EReal))
    (j N : ℕ) :
    compactSublevel K f j (N + 1) ⊆ {z | ψ z < (-(N + 1 : ℕ) : ℝ)} := by
  intro z hz
  have hfz : f j z ≤ -(((N + 1 : ℕ) : ℝ) + 1) := hz.2
  exact (hlower j z hz.1).trans_lt (EReal.coe_lt_coe_iff.mpr (by
    have h := hfz
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    linarith))

/-- The actual ordinary relative capacities of all compact smooth
sublevels have one finite inverse-linear bound. -/
theorem exists_relCapacity_compactSublevel_le (a : ComplexModel n)
    {R : ℝ} (hR : 0 < R) {Ω : TopologicalSpace.Opens (ComplexModel n)}
    (hΩ : closedBall a (5 * R) ⊆ Ω)
    {V : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hV : IsPreconnected V) (hψ : PlurisubharmonicOn ψ V)
    (hne : ∃ z ∈ V, ψ z ≠ ⊥) (hball : closedBall a (3 * R) ⊆ V)
    {K : Set (ComplexModel n)} (hK : K ⊆ ball a (R / 2))
    {f : ℕ → ComplexModel n → ℝ}
    (hlower : ∀ j z, z ∈ K → ψ z ≤ (f j z : EReal)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j N,
      relCapacity Ω (compactSublevel K f j (N + 1)) ≤
        ENNReal.ofReal (C / ((N : ℝ) + 1)) := by
  obtain ⟨A, S, hS, hbound⟩ := exists_relCapacity_sublevel_le a hR hΩ hV hψ hne hball
  refine ⟨max A 0, le_max_right _ _, fun j N => ?_⟩
  have hsub : compactSublevel K f j (N + 1) ⊆
      ball a (R / 2) ∩ {z | ψ z < (-(N + 1 : ℕ) : ℝ)} :=
    fun z hz => ⟨hK hz.1, compactSublevel_subset_original_strict_sublevel hlower j N hz⟩
  refine (relCapacity_mono hsub).trans ((hbound (N + 1)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < S + ((N + 1 : ℕ) : ℝ) := by positivity
  calc A / (S + ((N + 1 : ℕ) : ℝ)) ≤ max A 0 / (S + ((N + 1 : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right (le_max_left _ _) hden.le
    _ ≤ max A 0 / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

/-- The hypotheses above are manufactured for the literal radial
convolution sequence on every smaller closed ball. -/
theorem radialApproximation_lower_bound_on_closedBall (a : ComplexModel n)
    {r R : ℝ} (hrR : r < R) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ z ∈ ball a R, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a R, u z ≤ 0) :
    ∀ j z, z ∈ closedBall a r →
      u z ≤ (radialApproximation ((R - r) / 2) u j z : EReal) :=
  fun j z hz => ((radialApproximation_on_ball a hrR hu hne hnonpos).2.2.2.2 j z hz).1

/-- The uniform bound specialized to the actual radial convolutions of
the original local PSH function; every analytic input is produced. -/
theorem exists_relCapacity_radial_compactSublevel_le (a : ComplexModel n)
    {r R T : ℝ} (hR : 0 < R) (hr : r < R / 2) (hRT : 3 * R < T)
    {Ω : TopologicalSpace.Opens (ComplexModel n)} (hΩ : closedBall a (5 * R) ⊆ Ω)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u (ball a T))
    (hne : ∃ z ∈ ball a T, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a T, u z ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j N,
      relCapacity Ω (compactSublevel (closedBall a r)
        (radialApproximation ((T - r) / 2) u) j (N + 1)) ≤
        ENNReal.ofReal (C / ((N : ℝ) + 1)) := by
  have hrT : r < T := by linarith
  exact exists_relCapacity_compactSublevel_le a hR hΩ (convex_ball a T).isPreconnected
    hu hne (closedBall_subset_ball hRT) (closedBall_subset_ball hr)
    (radialApproximation_lower_bound_on_closedBall a hrT hu hne hnonpos)

end SGPT.PSH.HermitianExtremal
