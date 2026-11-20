import SGPT.Hodge.SourceFormNetLift
import SGPT.Foundations.Analysis.Pending.MovingBottChernRepresentativeLift
import SGPT.Foundations.Analysis.Pending.FixedBottChernClassCurrentCompactness
import SGPT.Foundations.Analysis.Pending.SmoothC0OriginalCurrentConvergence
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! ORIGINAL moving-class positive currents -> internally produced SAME-class
weak limit on ALL original full tests. Full BP statement and ENTIRE proof
precede this source. No chosen lift, bound, limit or weak class-closure input.
The class topology is the actual pure smooth quotient, not a finiteD claim. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Hodge.BDivChain.SourceAugmentedNetDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.PositiveClasses CurrentBottChernClass CanonicalCurrentFrame
  XiaoFormC0Topology XiaoPureSmoothBottChernClosure GlobalCurrentPotentials
  GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent LelongPoincareDivisor
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem globalDDC_zero
    (hu : IsGlobalQuasiPshPotential (n := m + 1) (M := M) (fun _ => 0)) :
    globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) (fun _ => 0) hu = 0 := by
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  rw [globalDDC_coefficients,GlobalCurrent.coefficients_zero]
  have hreg : regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (fun _ : M => (0 : EReal)) e z).toReal)
      (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
        (Nat.succ_pos m) (fun _ => 0) hu e) = 0 := by
    ext φ
    simp [regularDistribution_apply,chartFunction]
  change ddC _ = 0
  rw [hreg]
  ext v : 1
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,ddC_apply]
  simp

private theorem fullPositive_smooth
    (σ : ClosedRealOneOneForm (m + 1) M) (hσ : σ.val.IsSemipositive) :
    IsFullPositive (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) σ).val := by
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  have hp := (thetaPotentialCurrent_closed_type_positive σ.val (fun _ => 0) hu).2.2
  have heq : thetaPotentialCurrent σ.val (fun _ => 0) hu =
      (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) σ).val := by
    rw [thetaPotentialCurrent,globalDDC_zero hu.quasiPshPotential,add_zero]
    rfl
  rw [heq] at hp
  exact hp

variable [CompactSpace M] [ConnectedSpace M]

/-- Natural original moving classes and original full-positive currents produce
an actual SAME-class limit on ALL full tests along the SAME tail ultrafilter. -/
theorem exists_tendsto_moving_class_originalClosedPositiveCurrent
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ω : KahlerBackground (m + 1) M) (U : Ultrafilter ι) (hU : (U : Filter ι) ≤ l)
    (β : RealBottChern (m + 1) M)
    (T : ι → ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : ∀ j, IsFullPositive (T j).val)
    (hclass : Tendsto (fun j => bottChernClass (canonicalBasis (m + 1))
      (Nat.succ_pos m) (T j)) l
      (@nhds (RealBottChern (m + 1) M) (SGPT.BDivisor.euclideanTopology _) β)) :
    ∃ S : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m),
      IsFullPositive S.val ∧
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S = β ∧
      ∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        Tendsto (fun j => (T j).val.inChart e η) (U : Filter ι) (𝓝 (S.val.inChart e η)) := by
  classical
  let q := bottChernClassLinearMap (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)
  let reg := smoothClosedCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)
  obtain ⟨θ,θj,hθ,hθj,hlim⟩ :=
    SGPT.Hodge.BDivChain.SourceAugmentedDraft.exists_formNet_representatives_tendsto_C0 ω
      (fun j => bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (T j)) β hclass
  let W : Set ι := {j | formC0Seminorm ω (θj j - θ) < 1}
  have hevent : ∀ᶠ j in l, j ∈ W := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨j0,hj0⟩ := hevent.exists
  let γ := θ + ω.form
  let T' (j : ι) := if j ∈ W then T j else T j0
  let η (j : ι) := if j ∈ W then θj j else θj j0
  have hηclass (j : ι) : q (T' j) = RealBottChern.ofRepresentative (η j) := by
    dsimp [T',η,q]
    split_ifs with hj
    · exact (hθj j).symm
    · exact (hθj j0).symm
  have hsemi (j : ι) : (γ - η j).val.IsSemipositive := by
    have hi (k : ι) (hk : k ∈ W) : (γ - θj k).val.IsSemipositive := by
      have hs := isSemipositive_sub_add_smul_of_formC0_lt ω θ (θj k) hk
      have heq : θ - θj k + (1 : ℝ) • ω.form = γ - θj k := by dsimp [γ]; module
      rw [heq] at hs
      exact hs
    dsimp only [η]
    split_ifs with hj
    · exact hi j hj
    · exact hi j0 hj0
  have hT' (j : ι) : IsFullPositive (T' j).val := by
    dsimp only [T']
    split_ifs <;> exact hT _
  have htail : ∀ᶠ j in (U : Filter ι), j ∈ W := hU hevent
  have hηlim : Tendsto (fun j => formC0Seminorm ω (η j - θ)) (U : Filter ι) (𝓝 0) := by
    apply (hlim.mono_left hU).congr'
    filter_upwards [htail] with j hj
    simp only [η,if_pos hj]
  let K (j : ι) := T' j + reg (γ - η j)
  have hK (j : ι) : IsFullPositive (K j).val := by
    intro e α hα
    exact add_nonneg (hT' j e α hα) (fullPositive_smooth (γ - η j) (hsemi j) e α hα)
  have hKclass (j : ι) : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (K j) = RealBottChern.ofRepresentative γ := by
    change q (T' j + reg (γ - η j)) = _
    rw [map_add,hηclass]
    change RealBottChern.ofRepresentative (η j) + bottChernClass
      (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) (γ - η j)) = _
    rw [bottChernClass_smoothClosedCurrent]
    rw [← RealBottChern.ofRepresentative_add]
    congr 1
    module
  obtain ⟨L,hL,hLclass,hLlim⟩ :=
    FixedBottChernClassCurrentCompactness.exists_tendsto_same_class_originalClosedPositiveCurrent
      U (RealBottChern.ofRepresentative γ) K hK hKclass
  let S : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    L + (-1 : ℝ) • reg (γ - θ)
  have hSl (e : ComplexChart (m + 1) M)
      (α : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
      Tendsto (fun j => (T j).val.inChart e α) (U : Filter ι) (𝓝 (S.val.inChart e α)) := by
    have hsmall : Tendsto (fun j => formC0Seminorm ω
        ((γ - η j) - (γ - θ))) (U : Filter ι) (𝓝 0) := by
      have heq (j : ι) : (γ - η j) - (γ - θ) = -(η j - θ) := by module
      have hneg (a : ClosedRealOneOneForm (m + 1) M) :
          formC0Seminorm ω (-a) = formC0Seminorm ω a := by
        rw [formC0Seminorm_eq,map_neg,norm_neg]
        rfl
      simpa only [heq,hneg] using hηlim
    have hsmooth := SmoothC0OriginalCurrentConvergence.tendsto_smoothGlobalCurrent_of_C0
      ω (canonicalBasis (m + 1)) (fun j => γ - η j) (γ - θ) hsmall e α
    have hsub := (hLlim e α).sub hsmooth
    have hTlim : Tendsto (fun j => (T' j).val.inChart e α) (U : Filter ι)
        (𝓝 (S.val.inChart e α)) := by
      convert hsub using 1
      funext j
      change (T' j).val.inChart e α =
        ((T' j).val.inChart e α + (reg (γ - η j)).val.inChart e α) -
          (reg (γ - η j)).val.inChart e α
      ring
      congr 1
      change L.val.inChart e α + (-1 : ℝ) * (reg (γ - θ)).val.inChart e α =
        L.val.inChart e α - (reg (γ - θ)).val.inChart e α
      ring
    apply hTlim.congr'
    filter_upwards [htail] with j hj
    simp only [T',if_pos hj]
  refine ⟨S,?_,?_,hSl⟩
  · intro e α hα
    exact ge_of_tendsto (hSl e _) (Eventually.of_forall fun j => hT j e α hα)
  · change q (L + (-1 : ℝ) • reg (γ - θ)) = β
    rw [map_add,map_smul]
    change bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) L +
      (-1 : ℝ) • bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (reg (γ - θ)) = β
    rw [hLclass,bottChernClass_smoothClosedCurrent,neg_one_smul,← sub_eq_add_neg]
    have heq : RealBottChern.ofRepresentative γ - RealBottChern.ofRepresentative (γ - θ) =
        RealBottChern.ofRepresentative θ := by
      rw [sub_eq_add_neg,← RealBottChern.ofRepresentative_neg,← RealBottChern.ofRepresentative_add]
      congr 1
      module
    exact heq.trans hθ

end SGPT.Hodge.BDivChain.SourceAugmentedNetDraft
