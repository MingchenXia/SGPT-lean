import SGPT.PSH.IntrinsicAnalyticPullback
import SGPT.Foundations.Analysis.Pending.ResidualNef
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section

universe u

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.ResidualNefReduction
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open scoped Topology ContDiff Manifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Bounded real remainders on original connected neighborhoods of every point,
including the actual divisor poles; no global residual is supplied. -/
def HasLocalDivisorLogType (D : MeteredEffectiveQDivisor n M) (u : M → EReal) : Prop :=
  ∀ x, ∃ (U : Set M) (b : M → ℝ) (C : ℝ),
    0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
      (∀ y ∈ U, |b y| ≤ C) ∧ EqOn u (fun y => D.weight y + (b y : EReal)) U

/-- Local boundedness and compactness manufacture a genuine globally bounded
REAL residual. At poles it is zero, and away from them it is a finite difference. -/
theorem HasLocalDivisorLogType.exists_bounded_divisorResidual [CompactSpace M]
    {D : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hu : HasLocalDivisorLogType D u) : Nonempty (HasLogSingularitiesAlong D u) := by
  classical
  let rho : M → ℝ := fun x => if D.weight x = ⊥ then 0 else (u x).toReal - (D.weight x).toReal
  have hwtop : ∀ x, D.weight x ≠ ⊤ :=
    (MeteredDivisorPositivity.thetaPlurisubharmonic_weight D).quasiPlurisubharmonic.ne_top
  have hlocal : ∀ x, ∃ (U : Set M) (C : ℝ),
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, |rho y| ≤ C ∧
        u y = D.weight y + (rho y : EReal) := by
    intro x
    obtain ⟨U, b, C, hC, hU, _hconn, hx, hb, heq⟩ := hu x
    refine ⟨U, C, hU, hx, ?_⟩
    intro y hy
    have hyEq : u y = D.weight y + (b y : EReal) := heq hy
    by_cases hwpole : D.weight y = ⊥
    · have hrho : rho y = 0 := by simp only [rho, hwpole, if_pos]
      have hupole : u y = ⊥ := by
        rw [hyEq, hwpole, EReal.bot_add]
      refine ⟨by simpa only [hrho, abs_zero] using hC, ?_⟩
      rw [hupole, hwpole, EReal.bot_add]
    · have hwreal : D.weight y = ((D.weight y).toReal : EReal) :=
        (EReal.coe_toReal (hwtop y) hwpole).symm
      have hureal : u y = (((D.weight y).toReal + b y : ℝ) : EReal) := by
        calc
          u y = D.weight y + (b y : EReal) := hyEq
          _ = ((D.weight y).toReal : EReal) + (b y : EReal) :=
            congrArg (fun t : EReal => t + (b y : EReal)) hwreal
          _ = (((D.weight y).toReal + b y : ℝ) : EReal) := (EReal.coe_add _ _).symm
      have hrho : rho y = b y := by
        simp only [rho, if_neg hwpole, hureal, EReal.toReal_coe]
        ring
      exact ⟨by rw [hrho]; exact hb y hy, by rw [hrho]; exact heq hy⟩
  have hbounded : Bornology.IsBounded (rho '' (univ : Set M)) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_univ (by
      intro x
      obtain ⟨U, C, hU, hx, hb⟩ := hlocal x
      refine ⟨U, hU.mem_nhds hx, isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      simpa only [Real.norm_eq_abs] using (hb y hy).1)
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  refine ⟨{ residual := rho, bound := B, residual_bound := ?_, weight_add := ?_ }⟩
  · intro x
    simpa only [Real.norm_eq_abs] using hB (rho x) (mem_image_of_mem rho (mem_univ x))
  · intro x
    obtain ⟨U, C, _hU, hx, hb⟩ := hlocal x
    exact (hb x hx).2

section Modification

variable {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual modification geometry produces the pulled-back divisor and all its
literal fields, then connected original source neighborhoods retain local type. -/
theorem HasLocalDivisorLogType.comp_analyticModification
    {D : MeteredEffectiveQDivisor n M} {u : M → EReal} {π : Y → M}
    (hu : HasLocalDivisorLogType D u) (hπ : IsAnalyticModification (n := n) π) :
    ∃ D' : MeteredEffectiveQDivisor n Y,
      D'.weight = D.weight ∘ π ∧
      D'.curvature = ClosedRealOneOneForm.pullback hπ.1 D.curvature ∧
      D'.support = π ⁻¹' D.support ∧ HasLocalDivisorLogType D' (u ∘ π) := by
  obtain ⟨A, _hAc, _hAa, hAi, _hinj, hnon⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hsub : exceptionalLocus n π ⊆ A := by
    intro y hy
    by_contra hyA
    exact hnon y hyA hy
  have hint : interior (exceptionalLocus n π) = ∅ :=
    subset_empty_iff.mp ((interior_mono hsub).trans hAi.subset)
  let D' := MeteredDivisorOperations.pullback hπ.1 hint D
  refine ⟨D', rfl, rfl, rfl, ?_⟩
  intro y
  obtain ⟨U, b, C, hC, hU, _hconn, hyU, hb, heq⟩ := hu (π y)
  let : LocallyConnectedSpace Y := ChartedSpace.locallyConnectedSpace (ComplexModel n) Y
  obtain ⟨V, ⟨hV, hyV, hconn⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis y).mem_iff.mp
      ((hU.preimage hπ.1.continuous).mem_nhds hyU)
  refine ⟨V, b ∘ π, C, hC, hV, hconn, hyV,
    fun z hz => hb (π z) (hVU hz), ?_⟩
  intro z hz
  exact heq (hVU hz)

/-- Pair the actual produced local divisor pullback with original global QPSH
pullback for the same literal potential, retaining every divisor field. -/
theorem IsQPSH.comp_localDivisorLogType
    {D : MeteredEffectiveQDivisor n M} {u : M → EReal} {π : Y → M}
    (hu : (ofFixedModel n M).IsQPSH u) (hlog : HasLocalDivisorLogType D u)
    (hπ : IsAnalyticModification (n := n) π) :
    ∃ D' : MeteredEffectiveQDivisor n Y,
      D'.weight = D.weight ∘ π ∧
      D'.curvature = ClosedRealOneOneForm.pullback hπ.1 D.curvature ∧
      D'.support = π ⁻¹' D.support ∧
      (ofFixedModel n Y).IsQPSH (u ∘ π) ∧ HasLocalDivisorLogType D' (u ∘ π) := by
  obtain ⟨D', hw, hc, hs, hl⟩ := hlog.comp_analyticModification hπ
  exact ⟨D', hw, hc, hs, hu.comp_analyticModification hπ, hl⟩

end Modification

section CompactConnected

variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- The original universal theta criterion and the internally produced residual
feed the genuine nef producer; no global bound or nef output is a premise. -/
theorem HasLocalDivisorLogType.nef_originalTheta_sub_divisorCurvature
    (omega : KahlerBackground n M) {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {D : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hlog : HasLocalDivisorLogType D u) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    NefWithRespectTo omega (atlasClosedFormToNative θ - D.curvature) := by
  obtain ⟨L⟩ := hlog.exists_bounded_divisorResidual
  exact ResidualNef.nefWithRespectTo_sub_curvature omega
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) L

/-- A genuine native Kahler-current hypothesis and local type internally yield
a chart-smooth Kahler representative of the literal original residual form. -/
theorem HasLocalDivisorLogType.kahler_originalTheta_sub_divisorCurvature
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {D : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hlog : HasLocalDivisorLogType D u)
    (hu : IsKahlerCurrentPotential (atlasClosedFormToNative θ) u) :
    ∃ (h : M → ℝ) (hh : ChartSmooth (n := n) h),
      ((atlasClosedFormToNative θ - D.curvature) + ddcClosedForm h hh).val.IsKahler := by
  obtain ⟨L⟩ := hlog.exists_bounded_divisorResidual
  exact ResidualNef.exists_chartSmooth_isKahler_sub_curvature hu L

end CompactConnected
end SGPT.PSH.VariableComplexAtlas
