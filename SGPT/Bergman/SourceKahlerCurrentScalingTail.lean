import SGPT.Bergman.SourceKahlerCurrentPositiveMass
import SGPT.Foundations.Analysis.Pending.SingularNativeScalingUniformBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SingularNativeScalingUniformBound SingularCanonicalSingularityDistance
open scoped Topology ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual original current and same representative, manufactured from
the original lower-Kahler potential hypothesis. No current/class witness
or positivity output certificate is supplied. Empty X remains allowed. -/
def nativeKahlerCurrentOfPotential (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi) :
    KahlerCurrent (RealBottChern.ofRepresentative theta) where
  representative := theta
  represents := rfl
  potential := phi
  lowerBound := Classical.choose hcurrent
  strictlyPsh := Classical.choose_spec hcurrent

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- A TRUE original Kahler current internally supplies an actual alpha
tail of theta-PSH potentials and genuine d_S-distance convergence. The
accepted uniform small-scaling theorem manufactures all admissibility
and distance bounds. No scaled-PSH, d_S bound/convergence or positive-mass
certificate is supplied; actual alpha is any source sequence below1
tending to1. This is the current/d_S producer, not envelope convergence. -/
theorem exists_native_scaled_tail_distance_tendsto
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi)
    (alpha : ℕ → ℝ) (hlt : ∀ k, alpha k < 1) (hlim : Tendsto alpha atTop (𝓝 1)) :
    ∃ N : ℕ,
      (∀ j : ℕ, IsThetaPshPotential theta.val
        (fun x => ((alpha (j + N) : ℝ) : EReal) * phi x)) ∧
      Tendsto (fun j : ℕ =>
        (singularityDistance omega theta
          (show IsBigClass (RealBottChern.ofRepresentative theta) from
            ⟨nativeKahlerCurrentOfPotential theta hcurrent⟩)
          (fun x => ((alpha (j + N) : ℝ) : EReal) * phi x) phi).toReal) atTop (𝓝 0) := by
  let big : IsBigClass (RealBottChern.ofRepresentative theta) :=
    ⟨nativeKahlerCurrentOfPotential theta hcurrent⟩
  obtain ⟨C, hC, hbound⟩ := exists_uniform_singularityDistance_current_scaling_bound omega theta big
  have hscaling := hbound (nativeKahlerCurrentOfPotential theta hcurrent) rfl
  dsimp only [nativeKahlerCurrentOfPotential] at hscaling
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have heps : Tendsto (fun k : ℕ => 1 - alpha k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using hone.sub hlim
    · exact Eventually.of_forall (fun k => sub_pos.mpr (hlt k))
  have hseq := heps.eventually hscaling
  have hparam (k : ℕ) : 1 - (1 - alpha k) = alpha k := by ring
  simp only [hparam] at hseq
  obtain ⟨N, hN⟩ := eventually_atTop.mp hseq
  refine ⟨N, (fun j => (hN (j + N) (Nat.le_add_left _ _)).1), ?_⟩
  have htail := hlim.comp (tendsto_add_atTop_nat N)
  have hupper : Tendsto (fun j : ℕ => C * (1 - alpha (j + N))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, mul_zero] using
      (hone.sub htail).const_mul C
  exact squeeze_zero (fun j => (hN (j + N) (Nat.le_add_left _ _)).2.1)
    (fun j => (hN (j + N) (Nat.le_add_left _ _)).2.2.1) hupper

end SGPT.Bergman.ReferenceEnvelopeConvergence
