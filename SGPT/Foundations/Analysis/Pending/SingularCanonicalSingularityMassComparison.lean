import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffMassComparison
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance

set_option autoImplicit false

/-! # The literal all-input singularity-distance mixed mass comparison

Actual finite common shifts, genuine canonical constant invariance and the
true relative-model mass comparison give SGPT (6.8)--(6.9) on all genuine
PSH inputs. Actual distance-generated topology and finite mass convergence
are then characterized for arbitrary filters. P-equivalence is separate.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses RelativeGeodesicRays ActualMixedMassJoinGap
  SingularMinimalCanonicalRay SingularCanonicalCutoffSlices SingularCanonicalCutoffJoin
  SingularBoundedRayJoinSlices SingularCanonicalCutoffMassComparison
  SingularCanonicalSingularityDistance ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_common_shift_nonpositive {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    ∃ C : ℝ, (fun x => u x - (C : EReal)) ≤ 0 ∧
      (fun x => v x - (C : EReal)) ≤ 0 := by
  let U : ℝ := (⨆ x, u x).toReal
  let V : ℝ := (⨆ x, v x).toReal
  have huf := ModelRaySupremum.iSup_ne_top_ne_bot hu
  have hvf := ModelRaySupremum.iSup_ne_top_ne_bot hv
  have hU : (U : EReal) = ⨆ x, u x := EReal.coe_toReal huf.1 huf.2
  have hV : (V : EReal) = ⨆ x, v x := EReal.coe_toReal hvf.1 hvf.2
  refine ⟨max U V, sub_const_nonpositive_of_le (fun x => ?_),
    sub_const_nonpositive_of_le (fun x => ?_)⟩
  · exact (hU.symm ▸ le_iSup u x).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left U V))
  · exact (hV.symm ▸ le_iSup v x).trans
      (EReal.coe_le_coe_iff.mpr (le_max_right U V))

private theorem canonicalRay_eq_shifted_cutoff (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {C : ℝ}
    (h0 : (fun x => u x - (C : EReal)) ≤ 0) :
    canonicalRay θ u = cutoffSlice θ (thetaPshSupremum θ.val)
      (fun x => u x - (C : EReal)) :=
  (canonicalRay_sub_const_eq θ hu C).symm.trans
    (canonicalRay_eq_cutoffSlice_of_nonpositive omega θ hbig (hu.sub_const C) h0)

/-- Actual common finite shifts and genuine canonical constant invariance
transport the actual maximum/join identity to all genuine PSH inputs. -/
theorem canonicalRay_max_eq_joinSlice (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) {s : ℝ} (hs : 0 ≤ s) :
    canonicalRay θ (fun x => max (u x) (v x)) s =
      joinSlice θ (thetaPshSupremum θ.val) (canonicalRay θ u) (canonicalRay θ v) s := by
  obtain ⟨C, hu0, hv0⟩ := exists_common_shift_nonpositive hu hv
  have hmax : (fun x => max (u x) (v x) - (C : EReal)) =
      fun x => max (u x - (C : EReal)) (v x - (C : EReal)) := by
    funext x
    simp only [sub_eq_add_neg, ← EReal.coe_neg, ← max_add_coe]
  have hmax0 : (fun x => max (u x) (v x) - (C : EReal)) ≤ 0 := by
    rw [hmax]
    exact fun x => max_le (hu0 x) (hv0 x)
  have hcu := canonicalRay_eq_shifted_cutoff omega θ hbig hu hu0
  have hcv := canonicalRay_eq_shifted_cutoff omega θ hbig hv hv0
  have hcm := canonicalRay_eq_shifted_cutoff omega θ hbig
    (IsThetaPshPotential.max hu hv) hmax0
  rw [hmax] at hcm
  have h := cutoffSlice_max_eq_joinSlice omega
    (isModelPotential_thetaPshSupremum omega θ hbig) (hu.sub_const C) (hv.sub_const C)
    (le_thetaPshSupremum (hu.sub_const C) hu0)
    (le_thetaPshSupremum (hv.sub_const C) hv0) hs
  rwa [← hcu, ← hcv, ← hcm] at h

/-- Genuine common normalization, canonical invariance and actual mixed
mass invariance produce SGPT (6.9) for the full genuine PSH input domain. -/
theorem singularityDistance_le_mixedMassJoinGap_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    singularityDistance omega θ hbig u v ≤
        (mixedMassJoinGap (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
          hu hv : EReal) ∧
      (mixedMassJoinGap (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
        hu hv : EReal) ≤
        ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1) : ℝ) : EReal) *
          singularityDistance omega θ hbig u v := by
  obtain ⟨C, hu0, hv0⟩ := exists_common_shift_nonpositive hu hv
  have hcu := canonicalRay_eq_shifted_cutoff omega θ hbig hu hu0
  have hcv := canonicalRay_eq_shifted_cutoff omega θ hbig hv hv0
  have htu : SameSingularityTypeOn u (fun x => u x - (C : EReal)) univ := by
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
      (sameSingularityTypeOn_add_const u univ (-C)).symm
  have htv : SameSingularityTypeOn v (fun x => v x - (C : EReal)) univ := by
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
      (sameSingularityTypeOn_add_const v univ (-C)).symm
  have hJ := mixedMassJoinGap_eq_of_sameSingularityType omega
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
    hu hv (hu.sub_const C) (hv.sub_const C) htu htv
  have h := rayD1_le_mixedMassJoinGap_le omega
    (isModelPotential_thetaPshSupremum omega θ hbig) (hu.sub_const C) (hv.sub_const C)
    (le_thetaPshSupremum (hu.sub_const C) hu0)
    (le_thetaPshSupremum (hv.sub_const C) hv0)
  rwa [← hcu, ← hcv, ← hJ] at h

/-- Actual finite defining distances and the two-sided mass comparison give
the full endpoint/maximum mass convergence criterion for every filter. -/
theorem tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ι : Type*} (F : Filter ι) {w : ι → M → EReal} {v : M → EReal}
    (hw : ∀ i, IsThetaPshPotential θ.val (w i)) (hv : IsThetaPshPotential θ.val v) :
    Tendsto (fun i => (singularityDistance omega θ hbig (w i) v).toReal) F (𝓝 0) ↔
      ∀ k : Fin (n + 1),
        Tendsto (fun i => (endpointMixedMass θ (thetaPshSupremum θ.val) (w i)
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hw i) k).toReal)
          F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v
            (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv k).toReal) ∧
        Tendsto (fun i => (endpointMixedMass θ (thetaPshSupremum θ.val)
          (fun x => max (w i x) (v x))
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
          (IsThetaPshPotential.max (hw i) hv) k).toReal)
          F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v
            (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv k).toReal) := by
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hb (i : ι) : 0 ≤ (singularityDistance omega θ hbig (w i) v).toReal ∧
      (singularityDistance omega θ hbig (w i) v).toReal ≤
        mixedMassJoinGap (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
          (hw i) hv ∧
      mixedMassJoinGap (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
        (hw i) hv ≤ C * (singularityDistance omega θ hbig (w i) v).toReal := by
    obtain ⟨m, hm, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hbig (hw i) hv
    have h := singularityDistance_le_mixedMassJoinGap_le omega θ hbig (hw i) hv
    rw [he, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff] at h
    simpa only [he, EReal.toReal_coe] using And.intro hm h
  have hequiv :
      Tendsto (fun i => (singularityDistance omega θ hbig (w i) v).toReal) F (𝓝 0) ↔
        Tendsto (fun i => mixedMassJoinGap
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hw i) hv)
          F (𝓝 0) := by
    constructor
    · intro h
      have hc : Tendsto (fun i => C * (singularityDistance omega θ hbig (w i) v).toReal)
          F (𝓝 0) := by simpa only [mul_zero] using h.const_mul C
      exact squeeze_zero (fun i => (mixedMassJoinGap_bounds omega
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hw i) hv).1)
        (fun i => (hb i).2.2) hc
    · intro h
      exact squeeze_zero (fun i => (hb i).1) (fun i => (hb i).2.1) h
  exact hequiv.trans (tendsto_mixedMassJoinGap_zero_iff omega F
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv hw)

/-- With the actual distance-generated native topology explicitly selected,
singularity convergence is exactly convergence of the actual extended
endpoint and maximum masses. Their genuine finiteness is produced internally. -/
theorem tendsto_native_iff_endpointMixedMass (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ι : Type*} (F : Filter ι) (w : ι → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w F (𝓝 v) ↔ ∀ k : Fin (n + 1),
      Tendsto (fun i => endpointMixedMass θ (thetaPshSupremum θ.val) (w i).val
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (w i).property k)
        F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v.val
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property k)) ∧
      Tendsto (fun i => endpointMixedMass θ (thetaPshSupremum θ.val)
        (fun x => max ((w i).val x) (v.val x))
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
        (IsThetaPshPotential.max (w i).property v.property) k)
        F (𝓝 (endpointMixedMass θ (thetaPshSupremum θ.val) v.val
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic v.property k)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_singularityDistance_toReal omega θ hbig]
  rw [tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig F
    (fun i => (w i).property) v.property]
  have hfin {a : M → EReal} (ha : IsThetaPshPotential θ.val a) (k : Fin (n + 1)) :
      endpointMixedMass θ (thetaPshSupremum θ.val) a
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ha k ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ k a (thetaPshSupremum θ.val)
        ha (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic)).ne
  have hbridge {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (hf : ∀ i, f i ≠ ⊤) (ha : a ≠ ⊤) :
      Tendsto (fun i => (f i).toReal) F (𝓝 a.toReal) ↔ Tendsto f F (𝓝 a) := by
    constructor
    · intro h
      have h' := (ENNReal.continuous_ofReal.tendsto a.toReal).comp h
      simpa only [Function.comp_def, ENNReal.ofReal_toReal ha,
        ENNReal.ofReal_toReal (hf _)] using h'
    · intro h
      exact (ENNReal.continuousAt_toReal ha).tendsto.comp h
  apply forall_congr'
  intro k
  exact and_congr (hbridge (fun i => hfin (w i).property k) (hfin v.property k))
    (hbridge (fun i => hfin (IsThetaPshPotential.max (w i).property v.property) k)
      (hfin v.property k))

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
