import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularNativeScalingUniformBound

/-! # The original uniform small-scaling estimate

This is the source `lma:dSsmallmult` in `author/chapter_comp.tex:1142–1180`.
The constant precedes every original potential and every genuine Kähler-current
witness. The actual current produces eventual admissibility; neither a scaled
PSH condition nor a distance estimate is assumed. All functions, including their
poles, are the same original functions in the existing source dS carrier.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The whole original `lma:dSsmallmult`: one positive constant is chosen
before every original potential whose same current is Kähler. The actual current
internally supplies all sufficiently small positive scaling memberships and the
literal original extended-distance estimate, with no separate mass-positivity
premise beyond the original Kähler-current condition. -/
theorem exists_uniform_sourceSingularityDistance_current_scaling_bound
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SourceThetaPotentialL1 θ,
      (∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
        T.representative = atlasClosedFormToNative θ ∧ T.potential = u.val) →
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∃ hscaled : IsThetaPSH θ (fun x => ((1 - ε : ℝ) : EReal) * u.val x),
          sourceSingularityDistance ω θ hbig
            ⟨fun x => ((1 - ε : ℝ) : EReal) * u.val x, hscaled⟩ u ≤
              ((C * ε : ℝ) : EReal) := by
  obtain ⟨C, hC, hbound⟩ :=
    SingularNativeScalingUniformBound.exists_uniform_singularityDistance_current_scaling_bound
      ω (atlasClosedFormToNative θ) hbig
  refine ⟨C, hC, fun u hu => ?_⟩
  obtain ⟨T, hrep, hpot⟩ := hu
  have h := hbound T hrep
  rw [hpot] at h
  filter_upwards [h] with ε hε
  let hscaled : IsThetaPSH θ (fun x => ((1 - ε : ℝ) : EReal) * u.val x) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hε.1
  refine ⟨hscaled, ?_⟩
  exact (sourceSingularityDistance_eq_native ω θ hbig
    (⟨fun x => ((1 - ε : ℝ) : EReal) * u.val x, hscaled⟩ : SourceThetaPotentialL1 θ)
    u).trans_le hε.2.2.2

end SGPT.PSH.VariableComplexAtlas
