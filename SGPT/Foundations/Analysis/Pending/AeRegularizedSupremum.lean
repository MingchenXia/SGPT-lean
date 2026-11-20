import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.IncreasingPshBallSubmean

set_option autoImplicit false

/-!
# The regularized supremum of a PSH family agrees with the raw supremum a.e.

Xia, Proposition 1.2.5 (`xia-sgpt:page-0025`): for a family of
plurisubharmonic functions which is locally uniformly bounded above, the
upper-semicontinuous regularization of the supremum differs from the raw
pointwise supremum only on a Lebesgue null set.

No new analytic input is needed here.  Choquet's lemma
(`Pending.ChoquetRegularization`) replaces the family by a sequence with the
same regularized supremum; the running finite maxima of that sequence are an
*increasing* sequence of plurisubharmonic functions with the same pointwise
supremum; and the increasing case is already proved in this workspace by the
sharp moving-centre submean plus Lebesgue differentiation
(`ae_uscRegularization_iSup_eq_on_ball`).
-/

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.AeRegularizedSupremum

open SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

-- The running maxima themselves are `Pending.runningMax` (`ChoquetRegularization`);
-- only their plurisubharmonicity is local to this file.
omit [MeasurableSpace E] [BorelSpace E] in
theorem plurisubharmonicOn_runningMax {s : ℕ → E → EReal} {U : Set E}
    (hs : ∀ k, PlurisubharmonicOn (s k) U) (k : ℕ) :
    PlurisubharmonicOn (runningMax s k) U := by
  induction k with
  | zero => exact hs 0
  | succ m ih => exact ih.max (hs (m + 1))

section UscCentre

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- **Xia, Proposition 1.2.5** (`xia-sgpt:page-0025`), in the local form
supplied by the workspace.  On a ball on which a nonempty plurisubharmonic
family is uniformly bounded above, the regularized supremum of the family
agrees with the raw supremum Lebesgue-almost everywhere. -/
theorem ae_uscRegularization_sSup_eq_on_ball
    {F : Set (E → EReal)} {U : Set E} (hF : F.Nonempty)
    (hpsh : ∀ f ∈ F, PlurisubharmonicOn f U)
    (μ : Measure E) [μ.IsAddHaarMeasure] (a : E) {S C : ℝ} (hS : 0 < S)
    (hBU : ball a S ⊆ U)
    (hC : ∀ f ∈ F, ∀ y ∈ ball a S, f y ≤ (C : EReal)) :
    ∀ᵐ x ∂μ, x ∈ ball a (S / 2) →
      uscRegularization (sSup F) x = sSup F x := by
  obtain ⟨s, hsF, hs⟩ := exists_seq_uscRegularization_iSup_eq hF
  have hgpsh : ∀ k, DiscPshOn (runningMax s k) U := fun k =>
    FirstPass.PlurisubharmonicOn.discPshOn
      (plurisubharmonicOn_runningMax (fun j => hpsh (s j) (hsF j)) k)
  have hgmono : ∀ y ∈ U, Monotone fun k => runningMax s k y :=
    fun y _ j k hjk => runningMax_monotone s hjk y
  have hgC : ∀ k, ∀ y ∈ ball a S, runningMax s k y ≤ (C : EReal) := by
    intro k
    induction k with
    | zero => exact fun y hy => hC (s 0) (hsF 0) y hy
    | succ m ih =>
      intro y hy
      exact max_le (ih y hy) (hC (s (m + 1)) (hsF (m + 1)) y hy)
  have hae := ae_uscRegularization_iSup_eq_on_ball hgpsh hgmono μ a hS hBU hgC
  filter_upwards [hae] with x hx
  intro hxmem
  have h1 : uscRegularization (fun y => ⨆ k, runningMax s k y) x =
      ⨆ k, runningMax s k x := hx hxmem
  have h2 : (fun y => ⨆ k, runningMax s k y) = ⨆ k, s k := by
    funext y
    simp only [iSup_apply]
    exact iSup_runningMax s y
  rw [h2, hs, iSup_runningMax s x] at h1
  have h4 : (⨆ k, s k x) ≤ sSup F x := iSup_le fun k => le_sSup (hsF k) x
  have h5 : sSup F x ≤ uscRegularization (sSup F) x := le_uscRegularization _ x
  exact le_antisymm (by rw [h1]; exact h4) h5

end UscCentre

end

end SGPT.Foundations.Analysis.Pending.AeRegularizedSupremum
