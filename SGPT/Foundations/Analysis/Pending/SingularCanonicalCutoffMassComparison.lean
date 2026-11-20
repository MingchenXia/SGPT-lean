import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffJoin
import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinDistance
import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRayEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelFullMassRayRadialEnergy
import SGPT.Foundations.Analysis.Pending.ActualMixedMassJoinGap

set_option autoImplicit false

/-! # Genuine canonical cutoff-ray comparison with actual mixed mass, SGPT (6.9)

The actual ordered source-ray identity and radial mass formula identify the
sum of ordered distances with the genuine mass join gap. The actual maximum
join gives the source two-sided comparison and arbitrary-filter zero limit.
Inputs are arbitrary strong PSH below a genuine singular model, without
finite-energy or full-mass hypotheses on those inputs.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffMassComparison

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays ActualMixedMassJoinGap
  SingularCanonicalCutoffSlices SingularCanonicalCutoffRay SingularCanonicalCutoffRayEnergy
  SingularCanonicalCutoffConstantInvariance SingularCanonicalCutoffJoin SingularBoundedRayJoinSlices

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u v : M → EReal}

private theorem finiteEnergy_cutoffRay (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) {a : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hap : a ≤ φ) :
    IsFiniteEnergyRayFromModel θ φ hφ (cutoffSlice θ φ a) := by
  have hR := isBoundedRayFromModel_cutoffSlice omega hφ ha hap
  exact ⟨⟨hR.1.1, fun t ht =>
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (hR.1.2 t ht.le)⟩, hR.2⟩

/-- Actual ordered ray geometry and the actual radial mass formula give the
genuine finite mass identity for both ordered canonical maximum distances. -/
theorem rayD1_max_sum_eq_mixedMassJoinGap (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hup : u ≤ φ) (hvp : v ≤ φ) :
    rayD1 θ φ hφ (cutoffSlice θ φ u) (cutoffSlice θ φ (fun x => max (u x) (v x))) +
      rayD1 θ φ hφ (cutoffSlice θ φ v) (cutoffSlice θ φ (fun x => max (u x) (v x))) =
        (mixedMassJoinGap hφ.plurisubharmonic hu hv : EReal) := by
  have hmax := IsThetaPshPotential.max hu hv
  have hmaxp : (fun x => max (u x) (v x)) ≤ φ :=
    fun x => max_le (hup x) (hvp x)
  have hRu := finiteEnergy_cutoffRay omega hφ hu hup
  have hRv := finiteEnergy_cutoffRay omega hφ hv hvp
  have hRm := finiteEnergy_cutoffRay omega hφ hmax hmaxp
  rw [SingularModelFullMassRayRadialEnergy.rayD1_eq_radialEnergy_sub omega hRu.1 hRm.1
      (fun t _ => cutoffSlice_mono_input (fun x => le_max_left (u x) (v x)) t),
    SingularModelFullMassRayRadialEnergy.rayD1_eq_radialEnergy_sub omega hRv.1 hRm.1
      (fun t _ => cutoffSlice_mono_input (fun x => le_max_right (u x) (v x)) t),
    radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega hφ hmax hmaxp,
    radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega hφ hu hup,
    radialEnergy_cutoffSlice_eq_mixed_mass_deficit omega hφ hv hvp,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
  apply congrArg (fun r : ℝ => (r : EReal))
  unfold mixedMassJoinGap
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The actual maximum/join identity and the genuine bounded-join comparison
give the exact source constant for the actual mixed mass expression. -/
theorem rayD1_le_mixedMassJoinGap_le (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hup : u ≤ φ) (hvp : v ≤ φ) :
    rayD1 θ φ hφ (cutoffSlice θ φ u) (cutoffSlice θ φ v) ≤
        (mixedMassJoinGap hφ.plurisubharmonic hu hv : EReal) ∧
      (mixedMassJoinGap hφ.plurisubharmonic hu hv : EReal) ≤
        ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1) : ℝ) : EReal) *
          rayD1 θ φ hφ (cutoffSlice θ φ u) (cutoffSlice θ φ v) := by
  have hRu := isBoundedRayFromModel_cutoffSlice omega hφ hu hup
  have hRv := isBoundedRayFromModel_cutoffSlice omega hφ hv hvp
  have heq : cutoffSlice θ φ (fun x => max (u x) (v x)) =
      joinSlice θ φ (cutoffSlice θ φ u) (cutoffSlice θ φ v) := by
    funext t
    have h := cutoffSlice_max_eq_joinSlice omega hφ hu hv hup hvp (s := max t 0)
      (le_max_right t 0)
    unfold cutoffSlice joinSlice at h ⊢
    rw [max_eq_left (le_max_right t 0)] at h
    exact h
  have hs := rayD1_max_sum_eq_mixedMassJoinGap omega hφ hu hv hup hvp
  rw [heq] at hs
  have h := SingularBoundedRayJoinDistance.rayD1_join_two_sided omega hRu hRv
  rwa [hs] at h

/-- Actual finite radial limits reflect the genuine two-sided comparison to
real values and give the zero-limit equivalence for every filter. -/
theorem tendsto_rayD1_toReal_zero_iff_mixedMassJoinGap (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) {ι : Type*} (F : Filter ι) {w : ι → M → EReal}
    (hv : IsThetaPshPotential θ.val v) (hvp : v ≤ φ)
    (hw : ∀ i, IsThetaPshPotential θ.val (w i)) (hwp : ∀ i, w i ≤ φ) :
    Tendsto (fun i => (rayD1 θ φ hφ (cutoffSlice θ φ (w i))
      (cutoffSlice θ φ v)).toReal) F (𝓝 0) ↔
        Tendsto (fun i => mixedMassJoinGap hφ.plurisubharmonic (hw i) hv) F (𝓝 0) := by
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hb (i : ι) :
      0 ≤ (rayD1 θ φ hφ (cutoffSlice θ φ (w i)) (cutoffSlice θ φ v)).toReal ∧
      (rayD1 θ φ hφ (cutoffSlice θ φ (w i)) (cutoffSlice θ φ v)).toReal ≤
        mixedMassJoinGap hφ.plurisubharmonic (hw i) hv ∧
      mixedMassJoinGap hφ.plurisubharmonic (hw i) hv ≤ C *
        (rayD1 θ φ hφ (cutoffSlice θ φ (w i)) (cutoffSlice θ φ v)).toReal := by
    have hRi := finiteEnergy_cutoffRay omega hφ (hw i) (hwp i)
    have hRv := finiteEnergy_cutoffRay omega hφ hv hvp
    obtain ⟨m, hm, _, _, he⟩ := SingularModelSourceRayDistance.exists_tendsto_rayD1
      omega hRi.1 hRv.1 (hRi.2.trans hRv.2.symm)
    have h := rayD1_le_mixedMassJoinGap_le omega hφ (hw i) hv (hwp i) hvp
    rw [he, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff] at h
    simpa only [he, EReal.toReal_coe] using And.intro hm h
  constructor
  · intro h
    have hc : Tendsto (fun i => C * (rayD1 θ φ hφ
        (cutoffSlice θ φ (w i)) (cutoffSlice θ φ v)).toReal) F (𝓝 0) := by
      simpa only [mul_zero] using h.const_mul C
    exact squeeze_zero
      (fun i => (mixedMassJoinGap_bounds omega hφ.plurisubharmonic (hw i) hv).1)
      (fun i => (hb i).2.2) hc
  · intro h
    exact squeeze_zero (fun i => (hb i).1) (fun i => (hb i).2.1) h

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffMassComparison
