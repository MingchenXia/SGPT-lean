import SGPT.PSH.VariableCoherentAnalyticType
import SGPT.PSH.CanonicalGrowthManifold

/-! # The literal original infinity germ ideal in varying dimensions -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Constants are genuine holomorphic germs on every original chart. -/
theorem AtlasHolomorphicAt.const (c : ℂ) (x : X) :
    A.AtlasHolomorphicAt (fun _ => c) x := by
  refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
  intro i
  exact differentiableOn_const c

/-- The actual open common neighborhood gives the original holomorphic sum. -/
theorem AtlasHolomorphicAt.add {h k : X → ℂ} {x : X}
    (hh : A.AtlasHolomorphicAt h x) (hk : A.AtlasHolomorphicAt k x) :
    A.AtlasHolomorphicAt (fun y => h y + k y) x := by
  obtain ⟨U, hU, hxU, hh⟩ := hh
  obtain ⟨V, hV, hxV, hk⟩ := hk
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro i
  exact ((hh i).mono fun _ hz => ⟨hz.1, hz.2.1⟩).add
    ((hk i).mono fun _ hz => ⟨hz.1, hz.2.2⟩)

/-- Products are actual original holomorphic germs on the common open set. -/
theorem AtlasHolomorphicAt.mul {h k : X → ℂ} {x : X}
    (hh : A.AtlasHolomorphicAt h x) (hk : A.AtlasHolomorphicAt k x) :
    A.AtlasHolomorphicAt (fun y => h y * k y) x := by
  obtain ⟨U, hU, hxU, hh⟩ := hh
  obtain ⟨V, hV, hxV, hk⟩ := hk
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro i
  exact ((hh i).mono fun _ hz => ⟨hz.1, hz.2.1⟩).mul
    ((hk i).mono fun _ hz => ⟨hz.1, hz.2.2⟩)

/-- Holomorphy respects equality of the actual original germs. -/
theorem AtlasHolomorphicAt.congr {h k : X → ℂ} {x : X}
    (hh : A.AtlasHolomorphicAt h x) (heq : h =ᶠ[𝓝 x] k) :
    A.AtlasHolomorphicAt k x := by
  obtain ⟨U, hU, hxU, hh⟩ := hh
  obtain ⟨V, hVe, hV, hxV⟩ := mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro i
  apply ((hh i).mono fun _ hz => ⟨hz.1, hz.2.1⟩).congr
  intro z hz
  exact (hVe hz.2.2).symm

/-- Genuine chart holomorphy supplies actual continuity at the original point. -/
theorem AtlasHolomorphicAt.continuousAt {h : X → ℂ} {x : X}
    (hh : A.AtlasHolomorphicAt h x) : ContinuousAt h x := by
  obtain ⟨U, hU, hxU, hh⟩ := hh
  obtain ⟨i, hi⟩ := A.cover x
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hU
  have hxD : A.chart i x ∈ D := by
    refine ⟨(A.chart i).map_source hi, ?_⟩
    change (A.chart i).symm ((A.chart i) x) ∈ U
    rw [(A.chart i).left_inv hi]
    exact hxU
  have hc := ((hh i).differentiableAt (hD.mem_nhds hxD)).continuousAt.comp
    ((A.chart i).continuousAt hi)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
  exact congrArg h ((A.chart i).left_inv hy).symm

/-- The exact original unnormalized logarithmic membership, on every actual
original atlas rather than one globally fixed native model dimension. -/
def atlasInftyIdeal (A : VariableComplexAtlas X) (u : X → EReal) : AtlasGermIdeal A where
  mem x h := A.AtlasHolomorphicAt h x ∧ MoreSingularAt (fun y => logNormSq (h y)) u x

private theorem singleton_log {T : Type*} (h : T → ℂ) (y : T) :
    generatorLog (fun _ : Fin 1 => h) y = logNormSq (h y) := by
  rw [generatorLog_eq_log_sum]
  simp [logNormSq]

private theorem sum_log_bound (z w : ℂ) (P : EReal) (C D : ℝ)
    (hz : logNormSq z ≤ P + (C : EReal))
    (hw : logNormSq w ≤ P + (D : EReal)) :
    logNormSq (z + w) ≤ P + ((max C D + Real.log 4 : ℝ) : EReal) := by
  have compare (a b : ℂ) (hab : ‖a‖ ≤ ‖b‖) :
      logNormSq (a + b) ≤ logNormSq b + (Real.log 4 : EReal) := by
    have hsq : generatorNormSq (fun _ : Fin 1 => fun _ : Unit => a + b) () ≤
        (4 : ℝ) * generatorNormSq (fun _ : Fin 1 => fun _ : Unit => b) () := by
      simp only [generatorNormSq, Fin.sum_univ_one]
      have hsum : ‖a + b‖ ≤ 2 * ‖b‖ := by linarith [norm_add_le a b]
      have hp := pow_le_pow_left₀ (norm_nonneg (a + b)) hsum 2
      nlinarith
    have hh := IdealWeightComparison.generatorLog_le_add_of_generatorNormSq_le
      (by norm_num : (0 : ℝ) < 4) hsq
    simpa only [singleton_log] using hh
  have upper (b : ℂ) (K : ℝ) (hK : K ≤ max C D)
      (hb : logNormSq b ≤ P + (K : EReal)) :
      logNormSq b + (Real.log 4 : EReal) ≤
        P + ((max C D + Real.log 4 : ℝ) : EReal) := by
    calc logNormSq b + (Real.log 4 : EReal) ≤
          (P + ((max C D : ℝ) : EReal)) + (Real.log 4 : EReal) :=
            add_le_add (hb.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hK))) le_rfl
      _ = _ := by rw [EReal.coe_add, add_assoc]
  by_cases hzw : ‖z‖ ≤ ‖w‖
  · exact (compare z w hzw).trans (upper w D (le_max_right C D) hw)
  · have h := compare w z (le_of_not_ge hzw)
    rw [add_comm w z] at h
    exact h.trans (upper z C (le_max_left C D) hz)

/-- The original logarithmic zero germ belongs even at all poles. -/
theorem atlasInftyIdeal_zero_mem (u : X → EReal) (x : X) :
    (atlasInftyIdeal A u).mem x (fun _ => 0) := by
  refine ⟨AtlasHolomorphicAt.const 0 x, 0, Eventually.of_forall ?_⟩
  intro y
  simp [logNormSq]

/-- Two actual original logarithmic germ bounds produce the genuine ideal sum. -/
theorem atlasInftyIdeal_add_mem {u : X → EReal} {x : X} {h k : X → ℂ}
    (hh : (atlasInftyIdeal A u).mem x h) (hk : (atlasInftyIdeal A u).mem x k) :
    (atlasInftyIdeal A u).mem x (fun y => h y + k y) := by
  obtain ⟨hh, C, hC⟩ := hh
  obtain ⟨hk, D, hD⟩ := hk
  refine ⟨hh.add hk, max C D + Real.log 4, ?_⟩
  filter_upwards [hC, hD] with y hCy hDy
  exact sum_log_bound (h y) (k y) (u y) C D hCy hDy

/-- The multiplier norm bound is produced from genuine holomorphic continuity. -/
theorem atlasInftyIdeal_mul_mem {u : X → EReal} {x : X} {a h : X → ℂ}
    (ha : A.AtlasHolomorphicAt a x) (hh : (atlasInftyIdeal A u).mem x h) :
    (atlasInftyIdeal A u).mem x (fun y => a y * h y) := by
  obtain ⟨hh, D, hD⟩ := hh
  have hab : ∀ᶠ y in 𝓝 x, ‖a y‖ ≤ ‖a x‖ + 1 :=
    (ha.continuousAt.norm.eventually
      (gt_mem_nhds (by linarith : ‖a x‖ < ‖a x‖ + 1))).mono fun _ hy => hy.le
  let K : ℝ := (‖a x‖ + 1) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨ha.mul hh, D + Real.log K, ?_⟩
  filter_upwards [hD, hab] with y hy hay
  have hsq : generatorNormSq (fun _ : Fin 1 => fun z => a z * h z) y ≤
      K * generatorNormSq (fun _ : Fin 1 => h) y := by
    simp only [generatorNormSq, Fin.sum_univ_one, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hay 2) (sq_nonneg _)
  have hl := IdealWeightComparison.generatorLog_le_add_of_generatorNormSq_le hK hsq
  simp only [singleton_log] at hl
  calc logNormSq (a y * h y) ≤ logNormSq (h y) + (Real.log K : EReal) := hl
    _ ≤ (u y + (D : EReal)) + (Real.log K : EReal) := add_le_add hy le_rfl
    _ = _ := by rw [EReal.coe_add, add_assoc]

/-- Membership depends only on the actual original holomorphic germ. -/
theorem atlasInftyIdeal_mem_congr {u : X → EReal} {x : X} {h k : X → ℂ}
    (heq : h =ᶠ[𝓝 x] k) :
    (atlasInftyIdeal A u).mem x h ↔ (atlasInftyIdeal A u).mem x k := by
  have transfer {f g : X → ℂ} (hfg : f =ᶠ[𝓝 x] g)
      (hf : (atlasInftyIdeal A u).mem x f) : (atlasInftyIdeal A u).mem x g := by
    obtain ⟨hf, C, hC⟩ := hf
    refine ⟨hf.congr hfg, C, ?_⟩
    filter_upwards [hfg, hC] with y hy hCy
    simpa only [← hy] using hCy
  exact ⟨transfer heq, transfer heq.symm⟩

/-- The SAME original representative remains a member throughout a neighborhood. -/
theorem atlasInftyIdeal_mem_eventually {u : X → EReal} {x : X} {h : X → ℂ}
    (hh : (atlasInftyIdeal A u).mem x h) :
    ∀ᶠ y in 𝓝 x, (atlasInftyIdeal A u).mem y h := by
  obtain ⟨⟨U, hU, hxU, hh⟩, C, hC⟩ := hh
  filter_upwards [hU.mem_nhds hxU, hC.eventually_nhds] with y hy hCy
  exact ⟨⟨U, hU, hy, hh⟩, C, hCy⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every actual native stalk is precisely the specialization of the original
varying-dimension logarithmic membership, with the same function and bound. -/
theorem atlasInftyIdeal_mem_iff_native {u : M → EReal} {x : M} {h : M → ℂ} :
    (atlasInftyIdeal (ofFixedModel n M) u).mem x h ↔
      (SGPT.PSH.inftyIdeal (n := n) u).mem x h := by
  change (ofFixedModel n M).AtlasHolomorphicAt h x ∧
    MoreSingularAt (fun y => logNormSq (h y)) u x ↔ _
  rw [atlasHolomorphicAt_iff_native, SGPT.PSH.mem_inftyIdeal_iff_log_bound]

/-- The entire ideal conversion is equal, not only a chosen generator family. -/
theorem atlasInftyIdeal_toNative_eq (u : M → EReal) :
    (atlasInftyIdeal (ofFixedModel n M) u).toNative = SGPT.PSH.inftyIdeal (n := n) u := by
  apply GermIdeal.ext
  funext x h
  exact propext atlasInftyIdeal_mem_iff_native

end SGPT.PSH.VariableComplexAtlas
