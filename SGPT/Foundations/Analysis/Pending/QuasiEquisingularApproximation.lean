import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationInterface
import SGPT.Foundations.Analysis.Pending.UniformLocalBergmanFiniteAtlas
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanOverlapAnalyticType
import SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanGlobalAnalyticType

set_option autoImplicit false

open scoped Topology

/-!
# Existence of quasi-equisingular approximations

Source: SGPT, Theorem 1.6.2 on `xia-sgpt:page-0049`, citing Demailly's
regularization theorem. The defining predicate is fully explicit in the
verified core; the existence theorem is imported from
`Pending.QuasiEquisingularApproximationInterface`, where it is proved from
Demailly's approximation theorem (`Pending.QuasiEquisingularApproximationDemailly`).
The case of a potential with analytic singularity type (constant sequence)
is proved in `Pending.QuasiEquisingularBasics`.
-/

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximation

open Filter
open FirstPass FirstPass.PositiveClasses
open FirstPass.NumericalRestrictedVolumeScaffold
open FirstPass.QuasiEquisingularApproximation
open QuasiEquisingularBergmanAtlas
open FiniteShiftedBergmanCollarGluing
open FiniteShiftedBergmanOverlapAnalyticType
open FiniteShiftedBergmanCoordinateIdealGluing
open FiniteShiftedBergmanGlobalAnalyticType

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Adding a nonnegative multiple of the fixed Kähler background preserves a
theta-PSH potential.  Consequently the finite local Bergman atlas needed at
each positive-error stage of Demailly regularization is already available
from compactness.  This does not choose compatible collar data or construct
the global regularized term. -/
theorem nonempty_finiteUniformLocalBergmanAtlas_of_nonnegative_error
  (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) (hm : 0 < m) :
    Nonempty (QuasiEquisingularBergmanAtlas.FiniteUniformLocalBergmanAtlas
      (θ + ε • omega.form).val u m) := by
  apply QuasiEquisingularBergmanAtlas.nonempty_finiteUniformLocalBergmanAtlas
    (m := m) ?_ hm
  apply LocalPotentials.isThetaPshPotential_add_of_semipositive hu
  intro e z hz
  exact coefficientSemipositive_smul hε (omega.isSemipositive e z hz)

/-- The final term of the finite shifted collar construction at each index.
The definition retains all finite collar data explicitly; it makes no claim
that the terms decrease or converge as the Bergman degree varies. -/
noncomputable def finiteShiftedBergmanStages
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (ε : ℕ → ℝ) (m : ℕ → ℕ)
    (A : ∀ k, FiniteUniformLocalBergmanAtlas (θ + ε k • omega.form).val u (m k))
    (offset : ∀ k, Fin (A k).count → ℝ) (g : ℕ → M → EReal) : ℕ → M → EReal :=
  fun k => finiteShiftedBergmanGlued (A k) (offset k) (g k) (A k).count

omit [CompactSpace M] in
/-- At every finite Bergman stage whose cores are separated from later cores,
the final collar potential has the strong smooth-remainder analytic
singularities required for admissible restricted-volume currents.  This is a
stagewise conclusion only; it neither supplies the separated collars nor the
cross-stage approximation estimates. -/
theorem finiteShiftedBergmanStages_hasManifoldSmoothAnalyticSingularities
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (ε : ℕ → ℝ) (m : ℕ → ℕ)
    (A : ∀ k, FiniteUniformLocalBergmanAtlas (θ + ε k • omega.form).val u (m k))
    (offset : ∀ k, Fin (A k).count → ℝ) (g : ℕ → M → EReal)
    (H : ∀ k, FiniteShiftedBergmanCollarData (A k) (offset k) (g k))
    (hm : ∀ k, 0 < m k)
    (hsep : ∀ k, ShiftedLaterCoreSeparation (H k))
    (hcover : ∀ k x, ∃ i : Fin (A k).count, x ∈ (H k).inner i) :
    ∀ k, HasManifoldSmoothAnalyticSingularities (n := n)
      (finiteShiftedBergmanStages omega θ ε m A offset g k) := by
  intro k
  simpa only [finiteShiftedBergmanStages] using
    finiteShiftedBergmanGlued_hasManifoldSmoothAnalyticSingularities
      (A k) (offset k) (g k) (H k) (hm k) (hsep k) (hcover k)

omit [CompactSpace M] in
/-- **Finite-stage endpoint for Demailly regularization.**  If every Bergman
degree admits its genuine finite shifted collar data, and the remaining
sequence-level decrease, convergence, and multiplier-ideal estimates have
been established, then the resulting final collar terms satisfy the exact
quasi-equisingular approximation predicate.  The proof discharges the
theta-PSH and bounded rational analytic-singularity clauses from the verified
finite construction.  It does not manufacture any of the three explicit
sequence-level estimates. -/
theorem isQuasiEquisingularApproximation_of_finiteShiftedBergmanStages
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (ε : ℕ → ℝ) (m : ℕ → ℕ)
    (A : ∀ k, FiniteUniformLocalBergmanAtlas (θ + ε k • omega.form).val u (m k))
    (offset : ∀ k, Fin (A k).count → ℝ) (g : ℕ → M → EReal)
    (H : ∀ k, FiniteShiftedBergmanCollarData (A k) (offset k) (g k))
    (hu : IsThetaPshPotential θ.val u) (hε : NonnegativeDecreasesToZero ε)
    (hm : ∀ k, 0 < m k)
    (hg : ∀ k, IsThetaPshPotential (θ + ε k • omega.form).val (g k))
    (hcover : ∀ k x, ∃ i : Fin (A k).count, x ∈ (H k).inner i)
    (hstep : ∀ k x,
      finiteShiftedBergmanStages omega θ ε m A offset g (k + 1) x ≤
        finiteShiftedBergmanStages omega θ ε m A offset g k x)
    (hlimit : ∀ x,
      Tendsto (fun k => finiteShiftedBergmanStages omega θ ε m A offset g k x)
        atTop (𝓝 (u x)))
    (hmult : ∀ c d : ℝ, 0 < c → c < d → ∀ᶠ k in atTop,
      MultiplierIdealIncluded (n := n)
        (finiteShiftedBergmanStages omega θ ε m A offset g k) d u c) :
    IsQuasiEquisingularApproximation omega θ u ε
      (finiteShiftedBergmanStages omega θ ε m A offset g) := by
  refine ⟨hu, hε, ?_, ?_, ?_, hmult⟩
  · intro k
    simpa only [finiteShiftedBergmanStages] using
      (finiteShiftedBergmanGlued_effectiveTerm_of_coreCover (A k) (offset k) (g k)
        (H k) (hm k) (hg k) (hcover k)).1
  · intro k
    simpa only [finiteShiftedBergmanStages] using
      (finiteShiftedBergmanGlued_effectiveTerm_of_coreCover (A k) (offset k) (g k)
        (H k) (hm k) (hg k) (hcover k)).2
  · refine ⟨?_, hlimit⟩
    intro x
    exact antitone_nat_of_succ_le fun k => hstep k x

/-- Demailly's global regularization theorem in the exact quasi-equisingular
form used by the revised manuscript (Xia, Theorem 1.6.2; proved, see
`QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation`). -/
theorem exists_quasiEquisingularApproximation
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ ε : ℕ → ℝ, ∃ uSeq : ℕ → M → EReal,
      IsQuasiEquisingularApproximation omega θ u ε uSeq :=
  xiaTheorem162_exists_quasiEquisingularApproximation omega θ hu

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximation
