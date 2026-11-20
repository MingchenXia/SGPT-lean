import SGPT.Hodge.ConeTopology
import SGPT.Hodge.BDivCone

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
open Set Filter
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

/-- Original compact class sets INTERNALLY produce actual uniform semipositive
smooth representatives of R{omega}-alpha, without a supplied class bound. -/
theorem exists_uniform_semipositive_upper_of_isCompact (ω : KahlerBackground n X)
    (K : Set (RealBottChern n X))
    (hK : @IsCompact _ (SGPT.BDivisor.euclideanTopology _) K) :
    ∃ R : ℝ, 1≤R ∧ ∀ α∈K,∃ θ : ClosedRealOneOneForm n X,
      RealBottChern.ofRepresentative θ=R • RealBottChern.ofRepresentative ω.form-α ∧
      θ.val.IsSemipositive := by
  classical
  let := SGPT.Hodge.finiteDimensional_realBottChern ω
  let b := Module.finBasis ℝ (RealBottChern n X)
  obtain ⟨s,hread,-,C,hC,hbound⟩ := SGPT.Hodge.exists_linear_representatives ω b
  let := SGPT.BDivisor.euclideanTopology (RealBottChern n X)
  let f : RealBottChern n X → ℝ := fun α => C * ∑ j,|b.coord j α|
  have hf : Continuous f := by
    apply continuous_const.mul
    exact continuous_finsetSum _ fun j _ => (SGPT.BDivisor.continuous_euclideanTopology (b.coord j)).abs
  obtain ⟨B,hB⟩ := (hK.image hf).bddAbove
  let R := max B 1
  have hR : 1≤R := le_max_right _ _
  refine ⟨R,hR,?_⟩
  intro α hα
  have hsemiBound : formC0Seminorm ω (s α)≤R :=
    (hbound α).trans ((hB (mem_image_of_mem f hα)).trans (le_max_left _ _))
  refine ⟨R • ω.form-s α,?_,?_⟩
  · change RealBottChern.ofRepresentativeLinearMap (R • ω.form-s α)=_
    rw [map_sub,map_smul]
    change R • RealBottChern.ofRepresentative ω.form-RealBottChern.ofRepresentative (s α)=_
    rw [hread]
  · exact ((formC0Seminorm_le_iff ω (s α) (zero_le_one.trans hR)).mp hsemiBound).2

end SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
