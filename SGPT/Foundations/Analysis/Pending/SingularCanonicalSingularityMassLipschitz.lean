import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

set_option autoImplicit false

/-! # Genuine quantitative and native mass continuity in the singularity distance

SGPT PDF0226 Corollary 6.2.5. Actual per-slot mass join-gap bounds and
the genuine defining-distance comparison produce an independent stronger
mixed-endpoint bound. The last actual endpoint is the diagonal mass and
gives the printed source constant and native uniform continuity.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  RelativeDarvasDistance ActualMixedMassJoinGap SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  ThetaPshL1Topology DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual per-slot mass bounds and the genuine defining-distance comparison
produce the independent stronger mixed-endpoint quantitative bound. -/
theorem abs_endpointMixedMass_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (k : Fin (n + 1)) :
    |(endpointMixedMass θ (thetaPshSupremum θ.val) u
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu k).toReal -
      (endpointMixedMass θ (thetaPshSupremum θ.val) v
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv k).toReal| ≤
      ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) *
        (singularityDistance omega θ hbig u v).toReal := by
  obtain ⟨m, _, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hbig hu hv
  have hJ := (singularityDistance_le_mixedMassJoinGap_le omega θ hbig hu hv).2
  rw [he, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hJ
  have hmass := ((mixedMassJoinGap_bounds omega
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu hv).2 k).1
  refine hmass.trans ?_
  rw [he, EReal.toReal_coe, mul_assoc]
  exact mul_le_mul_of_nonneg_left hJ (by positivity)

/-- Actual native singularity distance turns each actual endpoint real mass
map into a genuine native Lipschitz map on the full PSH carrier. -/
theorem endpointMixedMass_lipschitzWith (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (k : Fin (n + 1)) :
    letI := singularityPseudoMetricSpace omega θ hbig
    LipschitzWith ⟨((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)),
      by positivity⟩ (fun u : ThetaPshL1 θ.val =>
        (endpointMixedMass θ (thetaPshSupremum θ.val) u.val
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic u.property k).toReal) := by
  let := singularityPseudoMetricSpace omega θ hbig
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, dist_eq_singularityDistance_toReal omega θ hbig]
  exact abs_endpointMixedMass_sub_le omega θ hbig u.property v.property k

omit [BorelSpace M] [ConnectedSpace M] in
private theorem endpointMixedMass_last {θ : ClosedRealOneOneForm n M}
    {p u : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) :
    endpointMixedMass θ p u hp hu (Fin.last n) = diagonalPotentialMass θ u hu := by
  have ht : endpointMixedPotential (Fin.last n) u p = (fun _ : Fin n => u) := by
    funext i
    simp only [endpointMixedPotential, Fin.val_last, if_pos i.isLt]
  have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
    (endpointMixedPotential_thetaPlurisubharmonic θ (Fin.last n) u p hu hp)
    (fun _ : Fin n => hu.1)
  exact congrArg (fun μ : MeasureTheory.Measure M => μ univ) hm

/-- The last actual endpoint is the actual diagonal mass. The genuine
stronger bound implies the exact printed positive constant in Corollary 6.2.5. -/
theorem abs_diagonalPotentialMass_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    0 < 3 * ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) ∧
      |(diagonalPotentialMass θ u hu).toReal - (diagonalPotentialMass θ v hv).toReal| ≤
        (3 * ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1))) *
          (singularityDistance omega θ hbig u v).toReal := by
  have h := abs_endpointMixedMass_sub_le omega θ hbig hu hv (Fin.last n)
  rw [endpointMixedMass_last _ hu, endpointMixedMass_last _ hv] at h
  obtain ⟨m, hm, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hbig hu hv
  have hD : 0 ≤ (singularityDistance omega θ hbig u v).toReal := by
    rw [he, EReal.toReal_coe]
    exact hm
  have hK : 0 ≤ ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) := by
    positivity
  refine ⟨by positivity, h.trans (mul_le_mul_of_nonneg_right ?_ hD)⟩
  calc
    ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) ≤
        3 * (((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1))) := by linarith
    _ = 3 * ((n : ℝ) + 1) * (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) := by ring

/-- Actual last-slot measure congruence and genuine native endpoint
Lipschitz control give uniform continuity of the real actual top mass. -/
theorem diagonalPotentialMass_uniformContinuous (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : UniformSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace
    UniformContinuous (fun u : ThetaPshL1 θ.val =>
      (diagonalPotentialMass θ u.val u.property).toReal) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace
  have he : (fun u : ThetaPshL1 θ.val => (diagonalPotentialMass θ u.val u.property).toReal) =
      fun u : ThetaPshL1 θ.val => (endpointMixedMass θ (thetaPshSupremum θ.val) u.val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic u.property
        (Fin.last n)).toReal := by
    funext u
    rw [endpointMixedMass_last _ u.property]
  rw [he]
  exact (endpointMixedMass_lipschitzWith omega θ hbig (Fin.last n)).uniformContinuous

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
