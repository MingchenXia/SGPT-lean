import SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointLimits
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Limsup

/-!
# Quasi-everywhere recovery of subgeodesic endpoints

Xia, SGPT Corollary 4.1.1, PDF page 0150. Pointwise endpoint limits exist
by vertical convexity. The genuine L1 endpoint condition, the chord's compact
upper bound, and negligible-set pluripolarity identify them quasi-everywhere
with their prescribed endpoints. Neither bounded endpoints nor bigness is
required; every dimension, including zero, is covered.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointQuasiEverywhere

open FirstPass FirstPass.PositiveClasses SubgeodesicEndpointLimits

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The left pointwise limit of a subgeodesic is its prescribed left
endpoint quasi-everywhere on a compact connected Kähler manifold. -/
theorem leftLimit_quasiEverywhereEq
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta.val curve u₀ u₁) :
    QuasiEverywhereEq (n := n) (leftLimit curve) u₀ := by
  obtain ⟨a, _b, ha, _hb, htime, _htimeb⟩ :=
    exists_paired_endpoint_sequences (t := (1 / 2 : ℝ)) (by norm_num)
  have haI : ∀ j, a j ∈ Ioo (0 : ℝ) 1 := fun j =>
    ⟨(ha j).1, (ha j).2.trans (by norm_num)⟩
  obtain ⟨C, hC⟩ := exists_uniform_upper_bound h
  have hQ := ThetaPshL1Limsup.le_limsup_quasiEverywhere_of_manifoldL1LocallyTendsto
    omega theta (fun j => h.interior.thetaPshPotential (haI j)) h.left_endpoint
    (h.tendsto_left.comp htime) (fun j x => hC (a j) (haI j) x)
  refine hQ.mono fun x hx => le_antisymm (leftLimit_le h x) ?_
  have hp : Tendsto (fun j => curve (a j) x) atTop (𝓝 (leftLimit curve x)) :=
    (tendsto_leftLimit h.interior x).comp htime
  simpa only [hp.limsup_eq] using hx

/-- The right endpoint recovery is the left recovery of the reversed path. -/
theorem rightLimit_quasiEverywhereEq
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta.val curve u₀ u₁) :
    QuasiEverywhereEq (n := n) (rightLimit curve) u₁ :=
  leftLimit_quasiEverywhereEq omega theta h.timeReversed

end SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointQuasiEverywhere
