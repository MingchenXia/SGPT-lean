import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

set_option autoImplicit false

/-!
# The non-nef locus of a big class is the positive Lelong locus of `V_θ`

Let `(X, ω)` be a compact Kähler manifold and `α = {θ}` a class with smooth representative `θ`.
Its non-nef locus is `E_nn(α) = ⋃_{ε > 0} E_nK(α + ε{ω})`, where `E_nK(β)` is the set of points
at which every Kähler current in `β` has positive Lelong number (`FirstPass.NonKahlerLocus`).

* `kahlerCurrentAddSmul` — **a `θ`-PSH potential is a Kähler current in `α + ε{ω}`**: if
  `θ + ddᶜu ≥ 0` then `θ + εω + ddᶜu ≥ εω`, so `u` is the potential of a Kähler current in
  `α + ε{ω}` dominating the Kähler form `εω`.
* `nonNefLocus_subset_lelongNumber_pos` — consequently `E_nn(α) ⊆ {x : ν(u, x) > 0}` for
  *every* `θ`-PSH potential `u` (no bigness, no positivity of the dimension).
* `nonNefLocus_eq_setOf_lelongNumber_pos` — **for `α` big, `E_nn(α) = {x : ν(V_θ, x) > 0}`**
  (blueprint `ana:nonnef-lelong-locus`).  The inclusion `⊇` is
  `MinimalSingularityLelongVanishing.lelongNumber_thetaPshSupremum_eq_zero` in positive
  dimension; in dimension `0` every point is isolated, every Lelong number is `⊤` and both
  sets are the whole manifold.  The inclusion `⊆` is the previous item with `u = V_θ`, which is
  a `θ`-PSH potential when `α` is big
  (`MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum`).

Sorry-free; no existing statement is changed.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonNefLocusLelong

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **A `θ`-PSH potential is the potential of a Kähler current in `{θ} + ε{ω}`**: the current
`θ + εω + ddᶜu` dominates the Kähler form `εω`. -/
def kahlerCurrentAddSmul (omega : KahlerBackground n Y) (θ : ClosedRealOneOneForm n Y)
    {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) {ε : ℝ} (hε : 0 < ε) :
    KahlerCurrent (RealBottChern.ofRepresentative θ +
      ε • RealBottChern.ofRepresentative omega.form) where
  representative := θ + ε • omega.form
  represents := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  potential := u
  lowerBound := KahlerBackground.smul hε omega
  strictlyPsh := by
    have hform : θ + ε • omega.form - (KahlerBackground.smul hε omega).form = θ := by
      rw [KahlerBackground.smul_form]
      abel
    rw [hform]
    exact hu

@[simp] theorem kahlerCurrentAddSmul_potential (omega : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) {ε : ℝ}
    (hε : 0 < ε) : (kahlerCurrentAddSmul omega θ hu hε).potential = u := rfl

/-- **`E_nn({θ}) ⊆ {ν(u, ·) > 0}` for every `θ`-PSH potential `u`.**  At a point of
`E_nK({θ} + ε{ω})` every Kähler current of that class has positive Lelong number, in particular
the current `θ + εω + ddᶜu`. -/
theorem nonNefLocus_subset_lelongNumber_pos (omega : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) :
    nonNefLocus omega (RealBottChern.ofRepresentative θ) ⊆
      {x | 0 < lelongNumber (n := n) u x} := by
  intro x hx
  obtain ⟨ε, hxε⟩ := mem_nonNefLocus.mp hx
  have h := (mem_nonKahlerLocus.mp hxε) (kahlerCurrentAddSmul omega θ hu ε.2)
  simpa using h

/-- In dimension `0` every Lelong number is `⊤`: every point is isolated, so the punctured
neighbourhood filter is `⊥`. -/
theorem lelongNumber_eq_top_of_dim_zero (hn : n = 0) (u : Y → EReal) (x : Y) :
    lelongNumber (n := n) u x = ⊤ := by
  apply LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
  have hbot : 𝓝[≠] x = ⊥ :=
    (isOpen_singleton_iff_punctured_nhds x).mp
      (RooftopDimZero.isOpen_singleton_of_dim_zero (M := Y) hn x)
  rw [hbot]
  exact Filter.eventually_bot

/-- In dimension `0` the non-nef locus is the whole manifold. -/
theorem nonNefLocus_eq_univ_of_dim_zero (hn : n = 0) (omega : KahlerBackground n Y)
    (alpha : RealBottChern n Y) : nonNefLocus omega alpha = univ := by
  refine eq_univ_of_forall fun x => mem_nonNefLocus.mpr ⟨⟨1, one_pos⟩, ?_⟩
  intro T
  rw [lelongNumber_eq_top_of_dim_zero hn]
  exact ENNReal.zero_lt_top

/-- **The non-nef locus of a big class through `V_θ`** (blueprint `ana:nonnef-lelong-locus`;
Copy-4 `sec:nK`, Boucksom 2004 §3).  On a compact Kähler manifold of any dimension, if
`α = {θ}` is big then `E_nn(α) = {x : ν(V_θ, x) > 0}`. -/
theorem nonNefLocus_eq_setOf_lelongNumber_pos [CompactSpace Y]
    (omega : KahlerBackground n Y) (θ : ClosedRealOneOneForm n Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    nonNefLocus omega (RealBottChern.ofRepresentative θ) =
      {x | 0 < lelongNumber (n := n) (thetaPshSupremum θ.val) x} := by
  cases isEmpty_or_nonempty Y with
  | inl hY => exact Subsingleton.elim _ _
  | inr hY =>
  refine (nonNefLocus_subset_lelongNumber_pos omega θ
    (MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig)).antisymm ?_
  intro x hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [nonNefLocus_eq_univ_of_dim_zero hn]
    exact mem_univ x
  · by_contra hxn
    have h0 := MinimalSingularityLelongVanishing.lelongNumber_thetaPshSupremum_eq_zero hn omega θ
      hbig hxn
    exact (ne_of_gt hx) h0

end

end SGPT.Foundations.Analysis.Pending.NonNefLocusLelong
