import SGPT.PSH.HermitianExtremalChartSublevels

/-!
# Manufactured bounded tails of the actual compact-sublevel extremals

The initial index and common bound are produced from eventual nonempty
interior. Every term is in the actual Hermitian class, and antitonicity
transfers the first finite bound to the whole tail. The literal inner
limit and its real supremum convergence are also proved. The final
theorem obtains all these inputs from the original local PSH witness
and the actual radial convolutions, including an original pole.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalMassLimit
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [ConnectedSpace M]

/-- A genuine bounded decreasing tail and its actual inner supremum
convergence, with the initial index and finite bound selected internally. -/
theorem exists_bounded_sublevel_tail (ω : Background (m + 1) M)
    {K : Set M} {f : ℕ → M → ℝ}
    (hf : ∀ x ∈ K, Antitone fun j => f j x) (N : ℕ)
    (hinterior : ∀ᶠ j in atTop, (interior (compactSublevel K f j N)).Nonempty) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j, IsHermitianPSH ω (regularizedExtremal ω (compactSublevel K f (j + J) N))) ∧
      (∀ j x, 0 ≤ regularizedExtremal ω (compactSublevel K f (j + J) N) x ∧
        regularizedExtremal ω (compactSublevel K f (j + J) N) x ≤ (C : EReal)) ∧
      (∀ x, Antitone fun j => regularizedExtremal ω (compactSublevel K f (j + J) N) x) ∧
      (fun x => ⨅ j, regularizedExtremal ω (compactSublevel K f (j + J) N) x) =
        sublevelLimit ω K f N ∧
      Tendsto (fun j => (⨆ x, regularizedExtremal ω (compactSublevel K f (j + J) N) x).toReal)
        atTop (𝓝 (⨆ x, sublevelLimit ω K f N x).toReal) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hinterior
  obtain ⟨C₀, _, _, hC₀⟩ := bounded_regularizedExtremal_of_nonempty_interior ω _ (hJ J le_rfl)
  let C : ℝ := max C₀ 0
  have hclass (j : ℕ) :
      IsHermitianPSH ω (regularizedExtremal ω (compactSublevel K f (j + J) N)) :=
    (bounded_regularizedExtremal_of_nonempty_interior ω _
      (hJ (j + J) (Nat.le_add_left J j))).choose_spec.1
  have hnonneg (j : ℕ) (x : M) :
      0 ≤ regularizedExtremal ω (compactSublevel K f (j + J) N) x :=
    regularizedExtremal_nonneg ω _ x
  have hupper (j : ℕ) (x : M) :
      regularizedExtremal ω (compactSublevel K f (j + J) N) x ≤ (C : EReal) :=
    ((sublevelExtremal_antitone_j ω hf N x (Nat.le_add_left J j)).trans (hC₀ x)).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hanti (x : M) : Antitone fun j =>
      regularizedExtremal ω (compactSublevel K f (j + J) N) x :=
    fun _ _ hjk => sublevelExtremal_antitone_j ω hf N x (Nat.add_le_add_right hjk J)
  have heq : (fun x => ⨅ j, regularizedExtremal ω (compactSublevel K f (j + J) N) x) =
      sublevelLimit ω K f N :=
    funext fun x => (sublevelExtremal_antitone_j ω hf N x).iInf_nat_add J
  have hlimclass := (isHermitianPSH_iInf_of_nonneg ω hclass hanti hnonneg).1
  have hsup := tendsto_real_iSup_iInf ω hclass hanti hlimclass
  have hsupvalue : (⨆ x, ⨅ j, regularizedExtremal ω (compactSublevel K f (j + J) N) x) =
      ⨆ x, sublevelLimit ω K f N x := iSup_congr fun x => congrFun heq x
  exact ⟨J, C, le_max_right _ _, hclass, fun j x => ⟨hnonneg j x, hupper j x⟩,
    hanti, heq, by simpa only [hsupvalue] using hsup⟩

/-- No sequence, class, boundedness, tail index or convergence certificate
is supplied: the original local PSH function and a genuine pole produce
the actual bounded extremal tails needed for the inner mass limit. -/
theorem exists_chartRadial_bounded_sublevel_tail (ω : Background (m + 1) M)
    (e : ComplexChart (m + 1) M) (a : ComplexModel (m + 1)) {r R : ℝ} (hrR : r < R)
    (htarget : closedBall a r ⊆ e.val.target) {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u (ball a R))
    (hne : ∃ z ∈ ball a R, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a R, u z ≤ 0)
    (hpole : ∃ z ∈ ball a r, u z = ⊥) (N : ℕ) :
    let K := chartClosedBall e a r
    let f := chartRadialApproximation e ((R - r) / 2) u
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j, IsHermitianPSH ω (regularizedExtremal ω (compactSublevel K f (j + J) N))) ∧
      (∀ j x, 0 ≤ regularizedExtremal ω (compactSublevel K f (j + J) N) x ∧
        regularizedExtremal ω (compactSublevel K f (j + J) N) x ≤ (C : EReal)) ∧
      (∀ x, Antitone fun j => regularizedExtremal ω (compactSublevel K f (j + J) N) x) ∧
      (fun x => ⨅ j, regularizedExtremal ω (compactSublevel K f (j + J) N) x) =
        sublevelLimit ω K f N ∧
      Tendsto (fun j => (⨆ x, regularizedExtremal ω (compactSublevel K f (j + J) N) x).toReal)
        atTop (𝓝 (⨆ x, sublevelLimit ω K f N x).toReal) := by
  obtain ⟨_, hcont, hanti, hlim, _⟩ :=
    chartRadialApproximation_properties e a hrR htarget hu hne hnonpos
  obtain ⟨z, hz, hpolez⟩ := hpole
  have hztarget := htarget (ball_subset_closedBall hz)
  have hx : e.val.symm z ∈ chartBall e a r :=
    ⟨e.val.map_target hztarget, by simpa only [mem_preimage, e.val.right_inv hztarget] using hz⟩
  apply exists_bounded_sublevel_tail ω hanti N
  apply eventually_nonempty_interior_compactSublevel (chartBall_isOpen e a r)
    (chartBall_subset_chartClosedBall e a r) hcont hx
  simpa only [e.val.right_inv hztarget, hpolez] using hlim _ hx

end SGPT.PSH.HermitianExtremal
