import SGPT.Hodge.ConeWeak
import SGPT.Hodge.BDivCone

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual finite Hodge basis internally produces smooth C0-convergent
representatives of EVERY original class net, not just natural sequences. -/
theorem exists_formNet_representatives_tendsto_C0 (ω : KahlerBackground n M)
    {ι : Type*} {l : Filter ι} (β : ι → RealBottChern n M) (α : RealBottChern n M)
    (hβ : Tendsto β l (@nhds _ (SGPT.BDivisor.euclideanTopology _) α)) :
    ∃ (θ : ClosedRealOneOneForm n M) (η : ι → ClosedRealOneOneForm n M),
      RealBottChern.ofRepresentative θ = α ∧
      (∀ j, RealBottChern.ofRepresentative (η j) = β j) ∧
      Tendsto (fun j => formC0Seminorm ω (η j - θ)) l (𝓝 0) := by
  classical
  let _ := SGPT.Hodge.finiteDimensional_realBottChern ω
  let b := Module.finBasis ℝ (RealBottChern n M)
  obtain ⟨s,hread,-,C,-,hbound⟩ := SGPT.Hodge.exists_linear_representatives ω b
  have hcoord := (SGPT.Hodge.tendsto_euclideanTopology_iff_equivFun b).mp hβ
  have hzero : Tendsto (fun j => C * ∑ k, |b.coord k (β j - α)|) l (𝓝 0) := by
    have hk (k) : Tendsto (fun j => |b.coord k (β j - α)|) l (𝓝 0) := by
      have h := ((tendsto_pi_nhds.mp hcoord k).sub_const (b.equivFun α k)).abs
      simpa only [map_sub,Module.Basis.coord_apply,Module.Basis.equivFun_apply,sub_self,abs_zero] using h
    simpa only [Finset.sum_const_zero,mul_zero] using
      (tendsto_finsetSum Finset.univ (fun k _ => hk k)).const_mul C
  have hnorm (j) : formC0Seminorm ω (s (β j) - s α) ≤
      C * ∑ k, |b.coord k (β j - α)| := by
    rw [←map_sub]
    exact hbound (β j - α)
  exact ⟨s α,fun j => s (β j),hread α,(fun j => hread (β j)),
    squeeze_zero' (Eventually.of_forall fun j => apply_nonneg (formC0Seminorm ω) _)
      (Eventually.of_forall hnorm) hzero⟩

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
