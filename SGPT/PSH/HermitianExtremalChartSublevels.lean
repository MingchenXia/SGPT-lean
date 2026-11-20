import SGPT.PSH.HermitianExtremalRadialRegularization

/-!
# The source sublevel construction in genuine native charts

These are the actual chart images of the smaller ball and its compact
closure, and the literal pullbacks of the proved radial convolutions.
The analytic inputs are only the original local PSH function, its
nondegeneracy, its upper bound, and an actual pole in the smaller ball.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

def chartBall (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) (r : ℝ) : Set M :=
  e.val.source ∩ e.val ⁻¹' ball a r

def chartClosedBall (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) (r : ℝ) : Set M :=
  e.val.symm '' closedBall a r

def chartRadialApproximation (e : ComplexChart (m + 1) M) (s : ℝ)
    (u : ComplexModel (m + 1) → EReal) (j : ℕ) (x : M) : ℝ :=
  radialApproximation s u j (e.val x)

omit [IsComplexManifold (m + 1) M] in
theorem chartBall_isOpen (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) (r : ℝ) :
    IsOpen (chartBall e a r) := e.val.isOpen_inter_preimage isOpen_ball

omit [IsComplexManifold (m + 1) M] in
theorem chartClosedBall_isCompact (e : ComplexChart (m + 1) M)
    (a : ComplexModel (m + 1)) (r : ℝ) (htarget : closedBall a r ⊆ e.val.target) :
    IsCompact (chartClosedBall e a r) :=
  (isCompact_closedBall a r).image_of_continuousOn (e.val.continuousOn_symm.mono htarget)

omit [IsComplexManifold (m + 1) M] in
theorem chartBall_subset_chartClosedBall (e : ComplexChart (m + 1) M)
    (a : ComplexModel (m + 1)) (r : ℝ) : chartBall e a r ⊆ chartClosedBall e a r := by
  intro x hx
  exact ⟨e.val x, ball_subset_closedBall hx.2, e.val.left_inv hx.1⟩

omit [IsComplexManifold (m + 1) M] in
/-- The exact chart pullbacks inherit continuity, monotonicity, pole
convergence and the uniform original convolution bounds. -/
theorem chartRadialApproximation_properties (e : ComplexChart (m + 1) M)
    (a : ComplexModel (m + 1)) {r R : ℝ} (hrR : r < R)
    (htarget : closedBall a r ⊆ e.val.target) {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ z ∈ ball a R, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a R, u z ≤ 0) :
    (∀ j, ContinuousOn (chartRadialApproximation e ((R - r) / 2) u j) (chartClosedBall e a r)) ∧
    (∀ j, ContinuousOn (chartRadialApproximation e ((R - r) / 2) u j) (chartBall e a r)) ∧
    (∀ x ∈ chartClosedBall e a r,
      Antitone fun j => chartRadialApproximation e ((R - r) / 2) u j x) ∧
    (∀ x ∈ chartBall e a r, Tendsto
      (fun j => (chartRadialApproximation e ((R - r) / 2) u j x : EReal))
      atTop (𝓝 (u (e.val x)))) ∧
    ∀ j x, x ∈ chartClosedBall e a r →
      u (e.val x) ≤ (chartRadialApproximation e ((R - r) / 2) u j x : EReal) ∧
      chartRadialApproximation e ((R - r) / 2) u j x ≤ 0 := by
  obtain ⟨hsmooth, _, hanti, hlim, hbound⟩ := radialApproximation_on_ball a hrR hu hne hnonpos
  have hsource : chartClosedBall e a r ⊆ e.val.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.val.map_target (htarget hz)
  have hmaps : MapsTo e.val (chartClosedBall e a r) (closedBall a r) := by
    rintro x ⟨z, hz, rfl⟩
    rwa [e.val.right_inv (htarget hz)]
  have hcont (j : ℕ) : ContinuousOn
      (chartRadialApproximation e ((R - r) / 2) u j) (chartClosedBall e a r) :=
    (hsmooth j).continuousOn.comp (e.val.continuousOn.mono hsource) hmaps
  exact ⟨hcont, fun j => (hcont j).mono (chartBall_subset_chartClosedBall e a r),
    fun x hx => hanti (e.val x) (hmaps hx),
    fun x hx => hlim (e.val x) (ball_subset_closedBall hx.2),
    fun j x hx => hbound j (e.val x) (hmaps hx)⟩

variable [CompactSpace M] [ConnectedSpace M]

/-- Source Step 1 with actual radial regularizations: every inner
sublevel extremal is manufactured in the nonclosed Hermitian class. -/
theorem chartRadial_sublevelLimit_isHermitianPSH (ω : Background (m + 1) M)
    (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) {r R : ℝ} (hrR : r < R)
    (htarget : closedBall a r ⊆ e.val.target) {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ z ∈ ball a R, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a R, u z ≤ 0)
    (hpole : ∃ z ∈ ball a r, u z = ⊥) (N : ℕ) :
    IsHermitianPSH ω (sublevelLimit ω (chartClosedBall e a r)
      (chartRadialApproximation e ((R - r) / 2) u) N) := by
  obtain ⟨_, hcont, hanti, hlim, _⟩ :=
    chartRadialApproximation_properties e a hrR htarget hu hne hnonpos
  obtain ⟨z, hz, hpolez⟩ := hpole
  have hztarget := htarget (ball_subset_closedBall hz)
  have hx : e.val.symm z ∈ chartBall e a r :=
    ⟨e.val.map_target hztarget, by simpa only [mem_preimage, e.val.right_inv hztarget] using hz⟩
  apply sublevelLimit_isHermitianPSH_of_pole ω (chartBall_isOpen e a r)
    (chartBall_subset_chartClosedBall e a r) hcont hanti hx
  simpa only [e.val.right_inv hztarget, hpolez] using hlim _ hx

/-- Under the actual bounded branch for the original local pole set,
the complete outer extremal is produced in the same original class. -/
theorem chartRadial_sublevel_outer_of_not_pole (ω : Background (m + 1) M)
    (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) {r R : ℝ} (hrR : r < R)
    (htarget : closedBall a r ⊆ e.val.target) {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ z ∈ ball a R, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a R, u z ≤ 0)
    (hpole : ∃ z ∈ ball a r, u z = ⊥)
    (hnot : ¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧
      ∀ x ∈ chartBall e a r ∩ {x | u (e.val x) = ⊥}, q x = ⊥) :
    ∃ C : ℝ,
      (∀ N x, sublevelLimit ω (chartClosedBall e a r)
        (chartRadialApproximation e ((R - r) / 2) u) N x ≤ (C : EReal)) ∧
      IsHermitianPSH ω (uscRegularization (fun x => ⨆ N,
        sublevelLimit ω (chartClosedBall e a r)
          (chartRadialApproximation e ((R - r) / 2) u) N x)) ∧
      (∀ x, 0 ≤ uscRegularization (fun x => ⨆ N,
        sublevelLimit ω (chartClosedBall e a r)
          (chartRadialApproximation e ((R - r) / 2) u) N x) x) ∧
      ∀ x, uscRegularization (fun x => ⨆ N,
        sublevelLimit ω (chartClosedBall e a r)
          (chartRadialApproximation e ((R - r) / 2) u) N x) x ≤ (C : EReal) := by
  obtain ⟨_, hcont, _, hlim, _⟩ :=
    chartRadialApproximation_properties e a hrR htarget hu hne hnonpos
  obtain ⟨C, _, _, hC⟩ := bounded_regularizedExtremal_of_not_pole ω _ hnot
  have hclass := chartRadial_sublevelLimit_isHermitianPSH ω e a hrR htarget hu hne hnonpos hpole
  refine ⟨C, fun N x => ?_, sublevel_outer_isHermitianPSH ω (chartBall_isOpen e a r)
    (chartBall_subset_chartClosedBall e a r) hcont hlim hclass C hC⟩
  exact (sublevelLimit_le_regularized_pole_extremal ω (chartBall_isOpen e a r)
    (chartBall_subset_chartClosedBall e a r) hcont hlim N (hclass N) x).trans (hC x)

end SGPT.PSH.HermitianExtremal
