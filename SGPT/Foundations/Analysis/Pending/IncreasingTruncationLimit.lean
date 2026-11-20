import SGPT.Foundations.Analysis.FirstPass.Envelopes
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasing

set_option autoImplicit false

/-!
# Lower semicontinuity of non-pluripolar products along increasing sequences

Let `v_j` be an increasing sequence of plurisubharmonic functions on an open set
`Ω ⊆ ℂⁿ` with regularized limit `V = (sup_j v_j)^*`.  On every open `O ⊆ Ω` the
non-pluripolar Monge–Ampère measure of `V` is at most the lower limit of those of
the `v_j`:

  `⟨(ddᶜ V)ⁿ⟩(O) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`.

This is the local content of the semicontinuity theorem for non-pluripolar products
(Darvas–Di Nezza–Lu, *The metric geometry of singularity types*, Theorem 2.6 / the
survey [DDNL25, Theorem 2.6]; Xia, SGPT, Theorem 2.4.2, `xia-sgpt:page-0074`, and
Corollary 2.4.1, `xia-sgpt:page-0075`).  It is proved from the Bedford–Taylor convergence theorem for
*increasing* sequences of locally bounded plurisubharmonic functions
(`BedfordTaylor.incWClaim_all`, Cegrell's proof via quasi-continuity, without the
Dirichlet problem; Błocki, lecture notes, Theorem 2.2.5), applied to the truncations
`max(v_j, -K)`, by the reduction `truncationLimitMeasure_le_liminf_of_increasingConvergence`.

The diagonal mixed form used by the global measures is derived from it; in
dimension zero it holds outright, because the empty mixed measure does not depend on
the tuple.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere MongeAmpere MixedNonPluripolar

variable {n : ℕ}

/-- **DDNL, Theorem 2.6, local form.** The non-pluripolar Monge–Ampère measure of the
regularized limit of an increasing sequence of plurisubharmonic functions (any function
agreeing with it on `Ω`) is, on open sets, at most the lower limit of the measures of the
sequence. -/
theorem truncationLimitMeasure_le_liminf_of_monotone (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {v : ℕ → ComplexModel n → EReal}
    (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) :
    truncationLimitMeasure Ω V hV O ≤
      liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop :=
  truncationLimitMeasure_le_liminf_of_increasingConvergence hn
    (boundedIncreasingConvergence Ω) hv hmono hVeq hV hO hOΩ

/-- The diagonal mixed form, in every dimension. -/
theorem mixedTruncationLimitMeasure_le_liminf_of_monotone
    {Ω : Opens (ComplexModel n)} {v : ℕ → ComplexModel n → EReal}
    (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hmono : ∀ z ∈ Ω, Monotone fun j => v j z)
    {V : ComplexModel n → EReal} (hVeq : EqOn V (uscRegularization (⨆ j, v j)) Ω)
    (hV : PlurisubharmonicOn V Ω)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) :
    mixedTruncationLimitMeasure Ω (fun _ => V) (fun _ => hV) O ≤
      liminf (fun j => mixedTruncationLimitMeasure Ω (fun _ => v j) (fun _ => hv j) O)
        atTop := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb : IsLocallyBoundedMixedPshOn Ω (fun i : Fin 0 => fun _ => (0 : ℝ)) :=
      fun i => Fin.elim0 i
    simp_rw [mixedTruncationLimitMeasure_zero_dim Ω _ _ _ hb]
    exact le_of_eq (liminf_const _).symm
  · simp_rw [mixedTruncationLimitMeasure_diagonal hn]
    exact truncationLimitMeasure_le_liminf_of_monotone hn hv hmono hVeq hV hO hOΩ

end SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit
