import SGPT.Foundations.Analysis.Pending.ThetaPshL1Order
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof

/-!
# Quasi-everywhere lower recovery of an L1 limit

For a uniformly bounded-above sequence of theta-PSH potentials converging
chart-locally in L1, its pointwise limsup dominates the limit quasi-everywhere.
Regularize each countable tail supremum, compare with the L1 limit, and remove
the countable union of the genuine negligible sets. This is the lower recovery
step used in Xia, SGPT Corollary 4.1.1, PDF page 0150.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaPshL1Limsup

open FirstPass FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A canonical chart-local L1 limit lies below the pointwise limsup outside
a pluripolar set, for a sequence with one finite uniform upper bound. -/
theorem le_limsup_quasiEverywhere_of_manifoldL1LocallyTendsto
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hv : IsThetaPshPotential theta.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    {C : ℝ} (hC : ∀ j x, u j x ≤ (C : EReal)) :
    QuasiEverywhere (n := n) (fun x => v x ≤ limsup (fun j => u j x) atTop) := by
  let tail : ℕ → M → EReal := fun N => uscRegularization (⨆ j, u (j + N))
  have htail : ∀ N, IsThetaPshPotential theta.val (tail N) := fun N =>
    NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
      (fun j => hu (j + N)) (fun j x => hC (j + N) x)
  have hvle : ∀ N, v ≤ tail N := by
    intro N
    apply ThetaPshL1Order.le_of_manifoldL1LocallyTendsto
      (fun j => hu (j + N)) hv (htail N)
    · intro e K hK hKe
      exact (tendsto_add_atTop_iff_nat N).mpr (hlim e K hK hKe)
    · intro j x
      apply (le_uscRegularization (⨆ j, u (j + N)) x).trans'
      simpa only [iSup_apply] using le_iSup (fun j => u (j + N) x) j
  have hQ : QuasiEverywhere (n := n)
      (fun x => ∀ N, tail N x ≤ (⨆ j, u (j + N)) x) :=
    RooftopObstacleQuasiEverywhere.quasiEverywhere_forall
      (PluripolarOuterCapacity.countablyStablePluripolar omega)
      (fun N => NegligibleSetsPluripolarProof.negligibleSetsPluripolar omega theta
        (fun j => u (j + N)) C (fun j => hu (j + N)) (fun j x => hC (j + N) x))
  refine hQ.mono fun x hx => ?_
  rw [limsup_eq_iInf_iSup_of_nat']
  exact le_iInf fun N => by simpa only [iSup_apply] using (hvle N x).trans (hx N)

end SGPT.Foundations.Analysis.Pending.ThetaPshL1Limsup
