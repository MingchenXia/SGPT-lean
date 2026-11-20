import SGPT.Hodge.ConePositive
import SGPT.Foundations.Analysis.Pending.KahlerCurrentRegularization
import SGPT.Foundations.Analysis.Pending.NonNefLocusLelong
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit
import SGPT.Foundations.Analysis.FirstPass.SmoothOffPole

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
  SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
  SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual smoothness off an actually empty polar set gives a genuine bounded
original potential on a compact source, without a supplied real lift or bound. -/
theorem isBoundedPotential_of_smoothOffPole_of_no_poles [CompactSpace X]
    {u : X → EReal} (hsm : SmoothOffPoleSet (n := n) u) (hpole : ∀ x,u x≠⊥) :
    IsBoundedPotential u := by
  let f := fun x => (u x).toReal
  have hf : ChartSmooth (n := n) f := by
    intro e z hz
    obtain ⟨g,hg,heq⟩ := hsm e z hz (hpole _)
    have heqreal : (fun y => (u (e.val.symm y)).toReal)=ᶠ[𝓝 z] g := by
      filter_upwards [heq] with y hy
      change (chartFunction u e y).toReal=g y
      rw [hy,EReal.toReal_coe]
    exact (hg.self_of_nhds.congr_of_eventuallyEq heqreal).contDiffWithinAt
  have huf (x : X) : u x=(f x : EReal) := by
    let e := complexChartAt (n := n) x
    have hx : x∈e.val.source := mem_complexChartAt_source x
    obtain ⟨g,-,heq⟩ := hsm e (e.val x) (e.val.map_source hx) (hpole _)
    have he : u x=(g (e.val x) : EReal) := by
      simpa only [chartFunction,e.val.left_inv hx] using heq.eq_of_nhds
    dsimp only [f]
    rw [he,EReal.toReal_coe]
  have hu : u=(fun x => (f x : EReal)) := funext huf
  rw [hu]
  exact GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
    (ProductTestForms.ChartSmooth.continuous hf)

variable [CompactSpace X] [ConnectedSpace X]

/-- Actual Demailly regularization and compactness produce a nef original class
from a genuine positive potential with every original point Lelong number zero. -/
theorem classNef_of_positive_potential_zero_lelong (ω : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hzero : ∀ x,lelongNumber (n := n) u x=0) :
    ClassNefWithRespectTo ω (RealBottChern.ofRepresentative θ) := by
  have hperturb (ε : ℝ) (hε : 0<ε) : ClassNefWithRespectTo ω
      (RealBottChern.ofRepresentative θ+ε • RealBottChern.ofRepresentative ω.form) := by
    let T := NonNefLocusLelong.kahlerCurrentAddSmul ω θ hu hε
    obtain ⟨S,-,hSsm,hSpole⟩ :=
      KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos T
    have hpole (x) : S.potential x≠⊥ := by
      intro hx
      have hp := hSpole hx
      change 0<lelongNumber (n := n) u x at hp
      rw [hzero x] at hp
      exact (lt_irrefl _ hp)
    have hb : IsBoundedPotential S.potential := isBoundedPotential_of_smoothOffPole_of_no_poles
      (SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole hSsm) hpole
    have hSpos : IsThetaPshPotential S.representative.val S.potential := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
        S.strictlyPsh S.lowerBound.isSemipositive
      simpa only [sub_add_cancel] using h
    have hn : ClassNefWithRespectTo ω (RealBottChern.ofRepresentative S.representative) :=
      nefWithRespectTo_of_isBoundedPotential ω hSpos.1 hb
    exact S.represents ▸ hn
  let c : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hc (k) : 0<c k := by dsimp [c]; positivity
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let : TopologicalSpace (RealBottChern n X) := SGPT.BDivisor.euclideanTopology _
  have hlim : Tendsto (fun k => RealBottChern.ofRepresentative θ+
      c k • RealBottChern.ofRepresentative ω.form) atTop
      (𝓝 (RealBottChern.ofRepresentative θ)) := by
    rw [SGPT.BDivisor.tendsto_euclideanTopology_iff]
    intro ℓ
    simpa only [map_add,map_smul,smul_eq_mul,zero_mul,add_zero] using
      tendsto_const_nhds.add (hc0.mul_const (ℓ (RealBottChern.ofRepresentative ω.form)))
  exact (SGPT.Hodge.isClosed_setOf_classNef ω).mem_of_tendsto hlim
    (Eventually.of_forall fun k => hperturb (c k) (hc k))

end SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
