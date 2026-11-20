import SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
import SGPT.Foundations.Analysis.Pending.RegularizedMaxOffPoleAppend
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials

set_option autoImplicit false

/-! # An actual finite atlas of weak analytic local potentials

The input is the original natural pointwise local-potential condition on an
actual current. Neither a chosen atlas nor a global background/potential nor
any current-parts identity is supplied. Compactness is explicit.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualWeakAnalyticCurrentPotentialAtlas
open FirstPass CanonicalCurrentFrame ChartPartition RegularizedMaxOffPoleAppend
  ActualQuasiPshPotentialSmoothCompatibility
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The natural original weak analytic local-potential condition. Every full
native coefficient is read by the genuine original quasi-PSH potential;
analyticity is requested only at the original point. -/
def HasWeakAnalyticLocalPotentials
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∀ p : M, ∃ (e : ComplexChart (m + 1) M) (Ω : Opens (ComplexModel (m + 1)))
    (_hΩ : Ω ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
    (hu : LocalQuasiPshPotentialOn u Ω),
    p ∈ e.val.source ∧ e.val p ∈ Ω ∧
    HasAnalyticSingularitiesSmoothOffPoleAt u (e.val p) ∧
    ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ

private theorem exists_precompact_data_at
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : HasWeakAnalyticLocalPotentials T) (p : M) :
    ∃ (e : ComplexChart (m + 1) M) (Ω : Opens (ComplexModel (m + 1)))
      (_hΩ : Ω ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
      (hu : LocalQuasiPshPotentialOn u Ω) (D : Opens (ComplexModel (m + 1))),
      p ∈ e.val.source ∧ e.val p ∈ D ∧
      IsCompact (closure (D : Set (ComplexModel (m + 1)))) ∧
      closure (D : Set (ComplexModel (m + 1))) ⊆ Ω ∧
      (∀ z ∈ closure (D : Set (ComplexModel (m + 1))),
        HasAnalyticSingularitiesSmoothOffPoleAt u z) ∧
      ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
        T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
          ddC (regularLocalQuasiPsh hu) w φ := by
  obtain ⟨e, Ω, hΩ, u, hu, hps, hpΩ, han, hread⟩ := hT p
  obtain ⟨c, N, f, htype⟩ := han
  obtain ⟨S, hSsub, hS, hpS⟩ := _root_.mem_nhds_iff.mp
    (RegularizedMaxOffPoleAppend.BoundedSmoothOffPoleLogarithmicTypeAt.eventually htype)
  obtain ⟨r, hr, hball⟩ := isOpen_iff.mp (Ω.isOpen.inter hS) (e.val p) ⟨hpΩ, hpS⟩
  let D : Opens (ComplexModel (m + 1)) := ⟨ball (e.val p) (r / 2), isOpen_ball⟩
  have hcl : closure (D : Set (ComplexModel (m + 1))) ⊆
      closedBall (e.val p) (r / 2) := closure_ball_subset_closedBall
  have hsub : closure (D : Set (ComplexModel (m + 1))) ⊆ (Ω : Set _) ∩ S :=
    hcl.trans ((closedBall_subset_ball (half_lt_self hr)).trans hball)
  refine ⟨e, Ω, hΩ, u, hu, D, hps, mem_ball_self (half_pos hr),
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl,
    (fun z hz ↦ (hsub hz).1), ?_, hread⟩
  exact fun z hz ↦ ⟨c, N, f, hSsub (hsub hz).2⟩

/-- Genuine original weak analytic local potentials internally select the
finite actual precompact chart atlas and the chart-smooth partition. -/
theorem exists_finite_precompact_potential_partition [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : HasWeakAnalyticLocalPotentials T) :
    ∃ (k : ℕ) (χ : Fin k → M → ℝ) (e : Fin k → ComplexChart (m + 1) M)
      (Ω D : Fin k → Opens (ComplexModel (m + 1)))
      (u : Fin k → ComplexModel (m + 1) → EReal),
      (∀ i, ∃ (_hΩ : Ω i ≤ chartTarget (e i)) (hu : LocalQuasiPshPotentialOn (u i) (Ω i)),
        IsCompact (closure (D i : Set (ComplexModel (m + 1)))) ∧
        closure (D i : Set (ComplexModel (m + 1))) ⊆ Ω i ∧
        (∀ z ∈ closure (D i : Set (ComplexModel (m + 1))),
          HasAnalyticSingularitiesSmoothOffPoleAt (u i) z) ∧
        ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω i, ℝ)),
          T.coefficients (canonicalBasis (m + 1)) (e i) w (TestFunction.monoCLM ℝ φ) =
            ddC (regularLocalQuasiPsh hu) w φ) ∧
      (∀ i, ChartSmooth (n := m + 1) (χ i)) ∧ (∀ i p, 0 ≤ χ i p) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).val.source ∩ (e i).val ⁻¹' D i) ∧
      (∀ i, IsCompact (tsupport (χ i))) ∧ ∀ p, ∑ i, χ i p = 1 := by
  classical
  let ι := {P : ComplexChart (m + 1) M × Opens (ComplexModel (m + 1)) ×
      (ComplexModel (m + 1) → EReal) × Opens (ComplexModel (m + 1)) //
    ∃ (hΩ : P.2.1 ≤ chartTarget P.1) (hu : LocalQuasiPshPotentialOn P.2.2.1 P.2.1),
      IsCompact (closure (P.2.2.2 : Set (ComplexModel (m + 1)))) ∧
      closure (P.2.2.2 : Set (ComplexModel (m + 1))) ⊆ P.2.1 ∧
      (∀ z ∈ closure (P.2.2.2 : Set (ComplexModel (m + 1))),
        HasAnalyticSingularitiesSmoothOffPoleAt P.2.2.1 z) ∧
      ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(P.2.1, ℝ)),
        T.coefficients (canonicalBasis (m + 1)) P.1 w (TestFunction.monoCLM ℝ φ) =
          ddC (regularLocalQuasiPsh hu) w φ}
  let S (P : ι) : Opens M := ⟨P.val.1.val.source ∩ P.val.1.val ⁻¹' P.val.2.2.2,
    P.val.1.val.isOpen_inter_preimage P.val.2.2.2.isOpen⟩
  have hcover (p : M) : ∃ P : ι, p ∈ S P := by
    obtain ⟨e, Ω, hΩ, u, hu, D, hps, hpD, hcpt, hsub, han, hread⟩ :=
      exists_precompact_data_at T hT p
    exact ⟨⟨(e, Ω, u, D), hΩ, hu, hcpt, hsub, han, hread⟩, hps, hpD⟩
  obtain ⟨k, χ, idx, hsm, h0, hsupp, hcpt, h1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m + 1) S hcover
  exact ⟨k, χ, (fun i ↦ (idx i).val.1), (fun i ↦ (idx i).val.2.1),
    (fun i ↦ (idx i).val.2.2.2), (fun i ↦ (idx i).val.2.2.1),
    (fun i ↦ (idx i).property), hsm, h0, hsupp, hcpt, h1⟩

end SGPT.Foundations.Analysis.Pending.ActualWeakAnalyticCurrentPotentialAtlas
