import SGPT.Foundations.Analysis.Pending.QuasiEquisingularCommonRestrictionBackground
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularNativeRestrictionComparison
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingPNets

set_option autoImplicit false

/-! # Internally produced common native limits of actual restricted QEA families -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionSameLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  RelativeEnergy ThetaPshL1Topology PluripolarCapacityDichotomy
  SingularCanonicalSingularityDistance

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- All background, mass and genuine native limit data are internally
produced from the actual two QEA families and the natural generic infimum. -/
theorem exists_common_native_model_limit
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ u δ vSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ β : KahlerBackground k V,
      (∃ C : ℝ, 0 < C ∧ β.form = C • omegaV.form) ∧
      IsAdmissibleTraceBackground hι omega θ (fun j => max (ε j) (δ j)) β.form ∧
      ∃ hU : ∀ j, IsThetaPshPotential β.form.val (fun y => uSeq j (ι y)),
      ∃ hV : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)),
      ∃ hW : ∀ j, IsThetaPshPotential β.form.val
        (fun y => max (uSeq j (ι y)) (vSeq j (ι y))),
      ∃ A : ThetaPshL1 β.form.val, IsModelPotential β.form A.val ∧
      Tendsto (fun j => (⟨fun y => uSeq j (ι y), hU j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace A) ∧
      Tendsto (fun j => (⟨fun y => vSeq j (ι y), hV j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace A) ∧
      Tendsto (fun j => (⟨fun y => max (uSeq j (ι y)) (vSeq j (ι y)), hW j⟩ :
        ThetaPshL1 β.form.val)) atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace A) := by
  obtain ⟨C, hC, hadm, hU, hV, hW, b, hb, hbound⟩ :=
    QuasiEquisingularCommonRestrictionBackground.exists_common_background_uniform_positive_mass
      omegaV hu hv hι hgeneric
  let β : KahlerBackground k V := KahlerBackground.smul hC omegaV
  let U : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => uSeq j (ι y), hU j⟩
  let T : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => vSeq j (ι y), hV j⟩
  let W : ℕ → ThetaPshL1 β.form.val := fun j =>
    ⟨fun y => max (uSeq j (ι y)) (vSeq j (ι y)), hW j⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  have horderU (i j : ℕ) (hij : i ≤ j) : POrderWith β.form (U j).val (U i).val :=
    pOrderWith_of_moreSingular
      (MoreSingularOn.of_le fun y _ => hu.term_antitone (ι y) hij)
  have horderT (i j : ℕ) (hij : i ≤ j) : POrderWith β.form (T j).val (T i).val :=
    pOrderWith_of_moreSingular
      (MoreSingularOn.of_le fun y _ => hv.term_antitone (ι y) hij)
  have horderW (i j : ℕ) (hij : i ≤ j) : POrderWith β.form (W j).val (W i).val :=
    pOrderWith_of_moreSingular (MoreSingularOn.of_le fun y _ =>
      max_le_max (hu.term_antitone (ι y) hij) (hv.term_antitone (ι y) hij))
  obtain ⟨A, hA, _, hUA⟩ :=
    SingularCanonicalSingularityDecreasingPNets.exists_model_limit_of_antitone_pOrderWith_of_uniform_mass
      omegaV β.form (isBigClass_kahler β) U horderU hb (fun j => (hbound j).1)
  obtain ⟨B, _, _, hTB⟩ :=
    SingularCanonicalSingularityDecreasingPNets.exists_model_limit_of_antitone_pOrderWith_of_uniform_mass
      omegaV β.form (isBigClass_kahler β) T horderT hb (fun j => (hbound j).2.1)
  obtain ⟨D, _, _, hWD⟩ :=
    SingularCanonicalSingularityDecreasingPNets.exists_model_limit_of_antitone_pOrderWith_of_uniform_mass
      omegaV β.form (isBigClass_kahler β) W horderW hb (fun j => (hbound j).2.2)
  have hm := QuasiEquisingularMaximum.isQuasiEquisingularApproximation_max hu hv
  have hAD :=
    QuasiEquisingularNativeRestrictionComparison.singularityDistance_eq_zero_of_native_limits
      omegaV β hu hm ι hU hW (fun _ _ => le_max_left _ _) A D hUA hWD
  have hBD :=
    QuasiEquisingularNativeRestrictionComparison.singularityDistance_eq_zero_of_native_limits
      omegaV β hv hm ι hV hW (fun _ _ => le_max_right _ _) B D hTB hWD
  have hdistAD : dist A D = 0 := by
    rw [dist_eq_singularityDistance_toReal omegaV β.form (isBigClass_kahler β),
      hAD, EReal.toReal_zero]
  have hdistBD : dist B D = 0 := by
    rw [dist_eq_singularityDistance_toReal omegaV β.form (isBigClass_kahler β),
      hBD, EReal.toReal_zero]
  have hdistAB : dist A B = 0 := by
    apply le_antisymm _ dist_nonneg
    simpa only [hdistAD, dist_comm D B, hdistBD, zero_add] using dist_triangle A D B
  have hTA : Tendsto T atTop (𝓝 A) := by
    rwa [← (Metric.inseparable_iff.mpr hdistAB).nhds_eq] at hTB
  have hWA : Tendsto W atTop (𝓝 A) := by
    rwa [← (Metric.inseparable_iff.mpr hdistAD).nhds_eq] at hWD
  exact ⟨β, ⟨C, hC, rfl⟩, hadm, hU, hV, hW, A, hA, hUA, hTA, hWA⟩

/-- The actual common native limit internally produces both the true finite
real and the original defining extended singularity-distance zero limits. -/
theorem exists_common_background_restricted_distance_tendsto_zero
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ u δ vSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ β : KahlerBackground k V,
      (∃ C : ℝ, 0 < C ∧ β.form = C • omegaV.form) ∧
      IsAdmissibleTraceBackground hι omega θ (fun j => max (ε j) (δ j)) β.form ∧
      Tendsto (fun j => (singularityDistance omegaV β.form (isBigClass_kahler β)
        (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))).toReal) atTop (𝓝 0) ∧
      Tendsto (fun j => singularityDistance omegaV β.form (isBigClass_kahler β)
        (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))) atTop (𝓝 0) := by
  obtain ⟨β, hscale, hadm, hU, hV, _, A, _, hUA, hVA, _⟩ :=
    exists_common_native_model_limit omegaV hu hv hι hgeneric
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  let U : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => uSeq j (ι y), hU j⟩
  let T : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => vSeq j (ι y), hV j⟩
  have hUA' : Tendsto U atTop (𝓝 A) := hUA
  have hTA' : Tendsto T atTop (𝓝 A) := hVA
  have hdist : Tendsto (fun j => dist (U j) (T j)) atTop (𝓝 0) := by
    simpa only [dist_self] using hUA'.dist hTA'
  have hreal : Tendsto (fun j => (singularityDistance omegaV β.form (isBigClass_kahler β)
      (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))).toReal) atTop (𝓝 0) := by
    have heq : (fun j => dist (U j) (T j)) = fun j =>
        (singularityDistance omegaV β.form (isBigClass_kahler β)
          (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))).toReal :=
      funext fun j => dist_eq_singularityDistance_toReal omegaV β.form
        (isBigClass_kahler β) (U j) (T j)
    rw [← heq]
    exact hdist
  have hvalue (j : ℕ) :
      (((singularityDistance omegaV β.form (isBigClass_kahler β)
        (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))).toReal : ℝ) : EReal) =
      singularityDistance omegaV β.form (isBigClass_kahler β)
        (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y)) := by
    obtain ⟨r, _, _, _, hr⟩ := exists_tendsto_singularityDistance omegaV β.form
      (isBigClass_kahler β) (hU j) (hV j)
    rw [hr, EReal.toReal_coe]
  have hextended : Tendsto (fun j => singularityDistance omegaV β.form (isBigClass_kahler β)
      (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))) atTop (𝓝 0) := by
    simpa only [hvalue, EReal.coe_zero] using EReal.tendsto_coe.mpr hreal
  exact ⟨β, hscale, hadm, hreal, hextended⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionSameLimit
